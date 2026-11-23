"""
Dynamic Magic Sets transformation for ASP programs in clingo.

Based on: Alviano et al., "Magic Sets for Disjunctive Datalog Programs",
          Artificial Intelligence 187-188 (2012) 156-192.

Usage:
    python dms.py [--sips {edb,alviano}] input.lp [output.lp]

Input format:
    #magic pred/arity.     % declares the MDB predicates to transform
    <ASP rules>

Terminology:
    EDB  - predicates defined by ground facts (empty body)
    IDB  - predicates defined by derivation rules (non-empty body)
    MDB  - subset of the IDB declared via #magic: the predicates that are
           rewritten with magic sets

SIPS (--sips):
    edb      EDB-first: non-MDB atoms bind before MDB atoms, and no bindings
             are passed between MDB atoms (default).
    alviano  scheme of the prototype of Alviano et al. (Sec. 4.1): a chain over
             all positive body atoms, picking first the one with most bound
             arguments. Magic rules may contain original (possibly
             non-deterministic) IDB atoms, which makes the magic sets dynamic.
    hybrid   most bound first as 'alviano', but ties are broken in favour of
             non-MDB atoms instead of by textual body order.
"""
from __future__ import annotations
import re
import sys
from collections import deque
from typing import Callable, NamedTuple
from clingo import ast as A

# ── Synthetic location for generated AST nodes ─────────────────────────────

_P = A.Position("<dms>", 1, 1)
LOC = A.Location(_P, _P)

# The #magic directive

_MAGIC_RE = re.compile(r"#magic\s+(\w+)/(\d+)\s*\.", re.IGNORECASE)


def parse_magic(text: str) -> set[tuple[str, int]]:
    """Return {(name, arity), ...} for every #magic pred/n directive."""
    return {(m.group(1), int(m.group(2))) for m in _MAGIC_RE.finditer(text)}


def strip_magic(text: str) -> str:
    return _MAGIC_RE.sub("", text)


# Variable collection


def _vars(node: A.AST) -> set[str]:
    """Recursively collect the names of all Variables in the AST."""
    if node.ast_type == A.ASTType.Variable:
        return {node.name}
    result: set[str] = set()
    for key in node.child_keys:
        child = getattr(node, key)
        if isinstance(child, A.AST):
            result |= _vars(child)
        else:
            try:
                for c in child:
                    if isinstance(c, A.AST):
                        result |= _vars(c)
            except TypeError:
                pass
    return result


# Literals


def _is_pos_sym(lit: A.AST) -> bool:
    """Positive symbolic literal: p(args)."""
    return (
        lit.ast_type == A.ASTType.Literal
        and lit.sign == A.Sign.NoSign
        and lit.atom.ast_type == A.ASTType.SymbolicAtom
        and lit.atom.symbol.ast_type == A.ASTType.Function
    )


def _is_neg_sym(lit: A.AST) -> bool:
    """Negated symbolic literal: not p(args)."""
    return (
        lit.ast_type == A.ASTType.Literal
        and lit.sign == A.Sign.Negation
        and lit.atom.ast_type == A.ASTType.SymbolicAtom
        and lit.atom.symbol.ast_type == A.ASTType.Function
    )


def _is_cmp(lit: A.AST) -> bool:
    """Comparison or arithmetic literal: X = ..., N > 0, etc."""
    return (
        lit.ast_type == A.ASTType.Literal
        and lit.atom.ast_type == A.ASTType.Comparison
    )


def _sig(atom: A.AST) -> tuple[str, int]:
    """(name, arity) of a SymbolicAtom node."""
    s = atom.symbol
    return s.name, len(s.arguments)


def _args(atom: A.AST) -> list:
    return list(atom.symbol.arguments)


# Unsupported uses of MDB predicates


class UnsupportedMDBUse(Exception):
    """An MDB atom occurs in a context the transformation does not handle."""


def _children(node: A.AST):
    for key in node.child_keys:
        child = getattr(node, key)
        if isinstance(child, A.AST):
            yield child
        else:
            try:
                for c in child:
                    if isinstance(c, A.AST):
                        yield c
            except TypeError:
                pass


def _sym_sigs(node: A.AST) -> set[tuple[str, int]]:
    """All (name, arity) of symbolic atoms anywhere below node."""
    if node.ast_type == A.ASTType.SymbolicAtom:
        s = node.symbol
        if s.ast_type == A.ASTType.Function:
            return {(s.name, len(s.arguments))}
        return set()
    out: set[tuple[str, int]] = set()
    for c in _children(node):
        out |= _sym_sigs(c)
    return out


def _condition_sigs(node: A.AST) -> set[tuple[str, int]]:
    """Signatures of the atoms in the conditions (':' parts) below node."""
    out: set[tuple[str, int]] = set()
    if node.ast_type == A.ASTType.ConditionalLiteral:
        for cond in node.condition:
            out |= _sym_sigs(cond)
    for c in _children(node):
        out |= _condition_sigs(c)
    return out


def _head_sigs(rule: A.AST) -> set[tuple[str, int]]:
    """Predicates defined by the rule head (conditions excluded)."""
    return _sym_sigs(rule.head) - _condition_sigs(rule.head)


def _body_sigs(rule: A.AST) -> set[tuple[str, int]]:
    """Predicates the rule depends on: body (aggregates included) and the
    conditions of its head elements."""
    out = _condition_sigs(rule.head)
    for lit in rule.body:
        out |= _sym_sigs(lit)
    return out


def _output_region(rules: list, others: list, mdb: set) -> set[tuple[str, int]]:
    """
    Predicates whose extension reaches the output without passing through an
    MDB predicate (the non-MDB call graph seen from the output).

    Roots: the #show'n predicates (every non-MDB predicate if there is no
    #show), the bodies of #show terms and the bodies of constraints. From a
    root we follow the rules defining it, but never expand an MDB predicate:
    the instances of an MDB predicate that matter are the ones its magic
    predicate selects, so what it depends on is handled by the rewriting.
    """
    shows = [s for s in others
             if s.ast_type in (A.ASTType.ShowSignature, A.ASTType.ShowTerm)]
    roots: set[tuple[str, int]] = set()
    if shows:
        for s in shows:
            if s.ast_type == A.ASTType.ShowSignature:
                roots.add((s.name, s.arity))
            else:
                for lit in s.body:
                    roots |= _sym_sigs(lit)
    else:
        for r in rules:
            roots |= (_head_sigs(r) | _body_sigs(r)) - mdb
    defs: dict[tuple[str, int], list] = {}
    for r in rules:
        heads = _head_sigs(r)
        if not heads:                      # constraint: always of interest
            roots |= _body_sigs(r)
        for h in heads:
            defs.setdefault(h, []).append(r)
    region, todo = set(), list(roots)
    while todo:
        p = todo.pop()
        if p in region:
            continue
        region.add(p)
        if p in mdb:
            continue
        for r in defs.get(p, []):
            # head-to-head: the other head atoms of a disjunction decide
            # whether the rule supports p
            todo.extend((_head_sigs(r) | _body_sigs(r)) - region)
    return region


def _check_free_calls(rules: list, others: list, mdb: set) -> None:
    """
    Reject an MDB call with all arguments free in a rule whose result reaches
    the output (see _output_region). Such a call produces no seed, so the rule
    would only see the instances needed by other calls and answers could be
    lost (e.g. b(X) :- p(X) with #show b/1). Calls outside that region, such
    as path(X,Y) :- sp(X,Y) in sp.lp, are allowed.
    """
    region = _output_region(rules, others, mdb)
    for rule in rules:
        heads = _head_sigs(rule)
        if heads & mdb:
            continue                       # rewritten by DMS itself
        if heads and not heads & region:
            continue                       # result does not reach the output
        bound: set[str] = set()
        for lit in rule.body:
            if _is_pos_sym(lit) and _sig(lit.atom) not in mdb:
                bound |= _vars(lit)
        for lit in rule.body:
            if not (_is_pos_sym(lit) or _is_neg_sym(lit)):
                continue
            if _sig(lit.atom) not in mdb:
                continue
            if "b" not in _adorn(_args(lit.atom), bound):
                n, a = _sig(lit.atom)
                raise UnsupportedMDBUse(
                    f"line {rule.location.begin.line}: MDB predicate {n}/{a} is "
                    f"called with all arguments free in a rule whose result "
                    f"reaches the output; no seed can be generated for this "
                    f"call and answers would be lost. Bind an argument or "
                    f"remove the #magic directive for {n}/{a}.")


def _check_unsupported(rules: list, others: list, mdb: set) -> None:
    """
    Reject MDB atoms inside aggregates, conditional literals or non-rule
    statements. The transformation only looks at plain body literals, so such
    occurrences would get no magic rules and the program would silently lose
    answers (e.g. #count{X : p(X)} evaluating to 0).
    """
    def fail(stm, sigs, where):
        names = ", ".join(f"{n}/{a}" for n, a in sorted(sigs))
        line = stm.location.begin.line
        raise UnsupportedMDBUse(
            f"line {line}: MDB predicate {names} used {where}; this is not "
            f"supported by the transformation. Remove the #magic directive "
            f"for {names}.")

    for rule in rules:
        for lit in rule.body:
            plain = (lit.ast_type == A.ASTType.Literal
                     and lit.atom.ast_type in (A.ASTType.SymbolicAtom,
                                               A.ASTType.Comparison,
                                               A.ASTType.BooleanConstant))
            if not plain:
                bad = _sym_sigs(lit) & mdb
                if bad:
                    fail(rule, bad, "inside an aggregate or conditional literal")
        bad = _condition_sigs(rule.head) & mdb
        if bad:
            fail(rule, bad, "in the condition of a head element")
    for stm in others:
        bad = _sym_sigs(stm) & mdb
        if bad:
            fail(stm, bad, f"in a {str(stm.ast_type).split('.')[-1]} statement")


# Adornment


def _adorn(args: list, bound: set) -> str:
    """'b' if all variables of the argument are in bound (always for ground
    terms), 'f' otherwise. So X+1 or f(X) with X free are not marked as
    bound."""
    return "".join("b" if _vars(a) <= bound else "f" for a in args)


def _bound_from(args: list, adorn: str) -> set:
    """Names of the variables in the 'b' positions of the adornment."""
    return {v for a, b in zip(args, adorn) if b == "b" for v in _vars(a)}


def _freshen_anon(node: A.AST, counter: list) -> A.AST:
    """Replace anonymous variables '_' with AnonVarN to avoid unsafe heads."""
    if node.ast_type == A.ASTType.Variable and node.name == "_":
        fresh = A.Variable(LOC, f"AnonVar{counter[0]}")
        counter[0] += 1
        return fresh
    if node.ast_type == A.ASTType.Function:
        new_args = [_freshen_anon(a, counter) for a in node.arguments]
        return A.Function(LOC, node.name, new_args, node.external)
    return node


# AST constructors


def _pos_lit(name: str, args: list) -> A.AST:
    """Positive literal: name(args)."""
    return A.Literal(
        LOC,
        A.Sign.NoSign,
        A.SymbolicAtom(A.Function(LOC, name, args, False)),
    )


def _magic_lit(pred: str, adorn: str, args: list) -> A.AST:
    """magic_pred_adorn(bound_args) as a positive literal."""
    bound = [a for a, b in zip(args, adorn) if b == "b"]
    return _pos_lit(f"magic_{pred}_{adorn}", bound)


def _rule(head: A.AST, body: list) -> A.AST:
    return A.Rule(LOC, head, body)


# Arithmetic (safety)


def _arith_binds(lit: A.AST, bound: set) -> set | None:
    """
    Decide whether a comparison can safely be included in a magic rule body.

    Returns the set of newly bound variables:
      - Pure restriction (all variables already bound, e.g. N > 0): {}
      - Simple equality X = expr(bound_vars): binds X, returns {X}
      - Any other case: None (it cannot be included safely)
    """
    if not _is_cmp(lit):
        return None
    all_v = _vars(lit)
    if all_v <= bound:
        return set()

    cmp = lit.atom
    guards = cmp.guards
    if (
        len(guards) == 1
        and guards[0].comparison == A.ComparisonOperator.Equal
    ):
        lhs = cmp.term
        if lhs.ast_type == A.ASTType.Variable and lhs.name not in bound:
            rhs_vars = _vars(guards[0].term)
            if rhs_vars <= bound:
                return {lhs.name}
    return None


def _safe_arith(arith: list, initial_bound: set) -> tuple[list, set]:
    """
    Process arithmetic literals in order and return (safe_lits, final_bound).
    Only literals whose right-hand-side variables are already bound are kept.
    """
    safe: list[A.AST] = []
    bound = set(initial_bound)
    for lit in arith:
        nb = _arith_binds(lit, bound)
        if nb is not None:
            safe.append(lit)
            bound.update(nb)
    return safe, bound


# Stratification


def _neg_cycle_exists(start: tuple, edges: dict) -> bool:
    """Return True if 'start' lies on a cycle with at least one negative edge.

    The state (node, has_neg) records whether a negative edge has been
    traversed on the current path from 'start'.
    """
    visited: set = set()
    stack = [(start, False)]
    while stack:
        node, has_neg = stack.pop()
        if (node, has_neg) in visited:
            continue
        visited.add((node, has_neg))
        for succ, is_neg in edges.get(node, set()):
            new_has_neg = has_neg or is_neg
            if succ == start and new_has_neg:
                return True
            if (succ, new_has_neg) not in visited:
                stack.append((succ, new_has_neg))
    return False


def _check_stratification(all_rules: list, mdb: set) -> list[str]:
    """Return warnings for MDB predicates involved in a non-stratified cycle."""
    edges: dict[tuple, set] = {}
    for rule in all_rules:
        head = rule.head
        head_sigs: list[tuple] = []
        if _is_pos_sym(head):
            head_sigs = [_sig(head.atom)]
        elif head.ast_type == A.ASTType.Disjunction:
            head_sigs = [
                _sig(e.literal.atom)
                for e in head.elements
                if _is_pos_sym(e.literal)
            ]
        for h in head_sigs:
            if h not in edges:
                edges[h] = set()
            for lit in rule.body:
                if _is_pos_sym(lit):
                    edges[h].add((_sig(lit.atom), False))
                elif _is_neg_sym(lit):
                    edges[h].add((_sig(lit.atom), True))

    warnings = []
    for pred in mdb:
        if _neg_cycle_exists(pred, edges):
            name, arity = pred
            warnings.append(
                f"warning: #magic {name}/{arity} is not stratified "
                f"(a cycle through negation was found). "
                f"The magic sets transformation may not preserve the semantics."
            )
    return warnings


# Classification of body literals


def _classify(body: list, mdb: set) -> tuple[list, list, list, list]:
    """
    Split the body literals into 4 groups (each element is (body_index, lit)):
      non_mdb_pos: positive symbolic atoms that are NOT MDB (EDB + non-MDB IDB)
      arith:       comparisons and arithmetic
      mdb_pos:     positive symbolic atoms that are MDB
      neg:         negated literals (MDB or not)
    """
    non_mdb_pos, arith, mdb_pos, neg = [], [], [], []
    for i, lit in enumerate(body):
        if _is_pos_sym(lit):
            (mdb_pos if _sig(lit.atom) in mdb else non_mdb_pos).append((i, lit))
        elif _is_neg_sym(lit):
            neg.append((i, lit))
        else:
            arith.append((i, lit))
    return non_mdb_pos, arith, mdb_pos, neg


# Extraction of MDB head atoms


def _mdb_heads(rule: A.AST, mdb: set) -> list[tuple[int, str, list]]:
    """
    Return [(elem_index, pred_name, args)] for every MDB atom in the head.
    Handles both simple and disjunctive heads.
    """
    head = rule.head
    res = []
    if _is_pos_sym(head):
        name, arity = _sig(head.atom)
        if (name, arity) in mdb:
            res.append((0, name, _args(head.atom)))
    elif head.ast_type == A.ASTType.Disjunction:
        for i, elem in enumerate(head.elements):
            lit = elem.literal
            if _is_pos_sym(lit):
                name, arity = _sig(lit.atom)
                if (name, arity) in mdb:
                    res.append((i, name, _args(lit.atom)))
    return res


# SIPS


class SipsStep(NamedTuple):
    """
    An MDB atom of the rule, adorned according to the SIPS.

      kind:   "pos" (positive body), "neg" (negated body) or "head" (another
              atom of a disjunctive head)
      idx:    index of the literal in the body or in the head
      lit:    the original literal
      adorn:  adornment of the atom
      before: literals that precede it in the SIPS (original positive atoms and
              safe arithmetic); they form the body of its magic rule (Fig. 4)
    """
    kind: str
    idx: int
    lit: A.AST
    adorn: str
    before: list


def _tail_steps(
    rule: A.AST, head_idx: int, mdb: set, bound: set, before: list,
) -> list[SipsStep]:
    """
    Negated MDB atoms and the other MDB atoms of the head. They provide no
    bindings (Def. 3.3, condition 1.b), so they go last, preceded by the whole
    positive body.
    """
    steps = []
    for i, lit in enumerate(rule.body):
        if _is_neg_sym(lit) and _sig(lit.atom) in mdb:
            steps.append(SipsStep(
                "neg", i, lit, _adorn(_args(lit.atom), bound), before))
    if rule.head.ast_type == A.ASTType.Disjunction:
        for j, elem in enumerate(rule.head.elements):
            lit = elem.literal
            if j == head_idx or not _is_pos_sym(lit) or _sig(lit.atom) not in mdb:
                continue
            steps.append(SipsStep(
                "head", j, lit, _adorn(_args(lit.atom), bound), before))
    return steps


def sips_edb(
    rule: A.AST, head_idx: int, head_args: list, head_adorn: str, mdb: set,
) -> list[SipsStep]:
    """
    EDB-first SIPS:
      1. Bindings from the head adornment
      2. Positive non-MDB atoms (EDB and non-MDB IDB): bind all their variables
      3. Safe arithmetic: X = expr(bound) binds X
      4. Positive MDB atoms: adorned with that bound set, with no bindings
         passed between them
      5. Negated MDB atoms and the other MDB atoms of the head
    """
    non_mdb_pos, arith_raw, mdb_pos, _ = _classify(list(rule.body), mdb)

    bound = _bound_from(head_args, head_adorn)
    for _, lit in non_mdb_pos:
        bound |= _vars(lit)
    safe_arith, bound = _safe_arith([lit for _, lit in arith_raw], bound)
    before = [lit for _, lit in non_mdb_pos] + safe_arith

    steps = [
        SipsStep("pos", i, lit, _adorn(_args(lit.atom), bound), before)
        for i, lit in mdb_pos
    ]
    return steps + _tail_steps(rule, head_idx, mdb, bound, before)


def sips_alviano(
    rule: A.AST, head_idx: int, head_args: list, head_adorn: str, mdb: set,
    prefer_non_mdb: bool = False,
) -> list[SipsStep]:
    """
    SIPS of the prototype of Alviano et al. (Sec. 4.1):
      - The positive body atoms (MDB or not) form a chain. At each step the
        atom with most bound arguments is picked; ties are broken by the
        original body order.
      - A positive atom binds its variables only if some argument is bound.
      - The magic rule of each atom contains the original atoms that precede
        it in the chain, MDB atoms included.
      - Negated MDB atoms and the other MDB atoms of the head go last.
    Safe arithmetic is added as soon as its variables are bound.
    """
    body = list(rule.body)
    _, arith_raw, _, _ = _classify(body, mdb)
    arith = [lit for _, lit in arith_raw]
    remaining = [(i, lit) for i, lit in enumerate(body) if _is_pos_sym(lit)]

    bound = _bound_from(head_args, head_adorn)
    chain: list[A.AST] = []
    steps: list[SipsStep] = []
    while remaining:
        safe_arith, cur = _safe_arith(arith, bound)
        best = max(
            remaining,
            key=lambda it: (
                _adorn(_args(it[1].atom), cur).count("b"),
                prefer_non_mdb and _sig(it[1].atom) not in mdb,
                -it[0],
            ),
        )
        remaining.remove(best)
        i, lit = best
        adorn = _adorn(_args(lit.atom), cur)
        if _sig(lit.atom) in mdb:
            steps.append(SipsStep("pos", i, lit, adorn, chain + safe_arith))
        chain.append(lit)
        if "b" in adorn:
            bound |= _vars(lit)

    safe_arith, bound = _safe_arith(arith, bound)
    return steps + _tail_steps(rule, head_idx, mdb, bound, chain + safe_arith)


def sips_hybrid(
    rule: A.AST, head_idx: int, head_args: list, head_adorn: str, mdb: set,
) -> list[SipsStep]:
    """
    Most bound first, as sips_alviano, but ties are broken in favour of
    non-MDB atoms (EDB and non-MDB IDB) instead of by textual body order, so
    the rewriting does not depend on how the body happens to be written.
    """
    return sips_alviano(rule, head_idx, head_args, head_adorn, mdb,
                        prefer_non_mdb=True)


SIPS: dict[str, Callable[..., list[SipsStep]]] = {
    "edb": sips_edb,
    "alviano": sips_alviano,
    "hybrid": sips_hybrid,
}


# Generate magic rules (Fig. 4)


def generate_magic(
    head_name: str, head_args: list, head_adorn: str, steps: list[SipsStep],
) -> list[str]:
    """
    For every MDB atom q^β of the adorned rule, emit:
        magic_q_β(bound) :- magic_head_α(bound), <literals that precede q>.
    """
    trigger = _magic_lit(head_name, head_adorn, head_args)
    out: list[str] = []
    for st in steps:
        name, _ = _sig(st.lit.atom)
        m_conseq = _magic_lit(name, st.adorn, _args(st.lit.atom))
        r = str(_rule(m_conseq, [trigger] + st.before))
        if r not in out:
            out.append(r)
    return out


# Modify rule (Fig. 5)


def modify_rule(
    rule: A.AST,
    head_name: str,
    head_args: list,
    head_adorn: str,
    head_idx: int,
    steps: list[SipsStep],
) -> str:
    """
    Build the modified rule (Fig. 5): the original, unadorned rule with a magic
    guard for every adorned head atom.

    Head and body keep the original predicates. Adorning them would split a
    disjunctive rule into independent disjunctions over different atoms and
    break minimality (Alviano et al. 2012, Sec. 3.1).

    Anonymous variables in the head are renamed (AnonVarN) so that the magic
    guard binds them and the rule is safe.
    """
    anon_ctr = [0]

    def fresh_lit(lit: A.AST) -> A.AST:
        sym = lit.atom.symbol
        args = [_freshen_anon(a, anon_ctr) for a in sym.arguments]
        new_sym = A.Function(LOC, sym.name, args, sym.external)
        return A.Literal(LOC, lit.sign, A.SymbolicAtom(new_sym))

    orig_head = rule.head
    if _is_pos_sym(orig_head):
        new_head = fresh_lit(orig_head)
        head_lits = [new_head]
    elif orig_head.ast_type == A.ASTType.Disjunction:
        head_lits = [
            fresh_lit(e.literal) if _is_pos_sym(e.literal) else e.literal
            for e in orig_head.elements
        ]
        new_head = A.Disjunction(
            LOC, [A.ConditionalLiteral(LOC, l, []) for l in head_lits]
        )
    else:
        new_head = orig_head
        head_lits = []

    guards = [_magic_lit(head_name, head_adorn,
                         _args(head_lits[head_idx].atom) if head_lits else head_args)]
    for st in steps:
        if st.kind == "head":
            name, _ = _sig(st.lit.atom)
            guards.append(_magic_lit(name, st.adorn, _args(head_lits[st.idx].atom)))

    return str(_rule(new_head, guards + list(rule.body)))


# DMS transformer


class DMSTransformer:
    """
    Performs the complete DMS transformation.

    The #magic pred/n directives declare the MDB, the subset of the IDB that
    is rewritten. Name and arity are both checked, so #magic f/1 does not
    affect f/2.
    """

    def __init__(self, sips: str = "edb"):
        self.sips = SIPS[sips]
        self.mdb: set[tuple[str, int]] = set()   # MDB predicates (via #magic)
        self.mdb_rules: list[A.AST] = []          # IDB rules with an MDB head
        self._all_rules: list[A.AST] = []         # all rules (for stratification)
        self.edb_stmts: list[str] = []
        self.query_stmts: list[str] = []
        self.other_stmts: list[str] = []
        self.query_seeds: list[tuple[str, list, str, list]] = []

        self.S: deque = deque()
        self.D: set = set()

        self.magic_out: list[str] = []
        self.modified_out: list[str] = []
        self._seen_magic: set[str] = set()
        self._seen_modified: set[str] = set()

    def _add_magic(self, s: str):
        if s not in self._seen_magic:
            self._seen_magic.add(s)
            self.magic_out.append(s)

    def _add_modified(self, s: str):
        if s not in self._seen_modified:
            self._seen_modified.add(s)
            self.modified_out.append(s)

    def parse(self, text: str):
        self.mdb = parse_magic(text)
        clean = strip_magic(text)

        all_rules: list[A.AST] = []
        passthrough: list[A.AST] = []

        _SKIP = {A.ASTType.Program, A.ASTType.Comment}

        def collect(stm):
            if stm.ast_type == A.ASTType.Rule:
                all_rules.append(stm)
            elif stm.ast_type not in _SKIP:
                passthrough.append(stm)

        A.parse_string(clean, collect)

        self._all_rules = all_rules
        _check_unsupported(all_rules, passthrough, self.mdb)
        _check_free_calls(all_rules, passthrough, self.mdb)

        # Classify rules as MDB (MDB head), EDB (facts) and non-MDB IDB
        idb_non_mdb: list[A.AST] = []
        for rule in all_rules:
            if _mdb_heads(rule, self.mdb):
                self.mdb_rules.append(rule)
            elif not list(rule.body):
                self.edb_stmts.append(str(rule))
            else:
                idb_non_mdb.append(rule)

        for stm in passthrough:
            self.other_stmts.append(str(stm))

        # Seeds: every non-MDB IDB rule that directly calls an MDB predicate
        # contributes a seed, using only the non-MDB atoms of that same body as
        # binding context. Bindings are not propagated through chains of
        # intermediate IDB predicates.
        for rule in idb_non_mdb:
            seeds = self._extract_seeds(rule)
            if seeds:
                self.query_seeds.extend(seeds)
                self.query_stmts.append(str(rule))
            else:
                self.edb_stmts.append(str(rule))

    def _extract_seeds(self, rule: A.AST) -> list:
        """
        Extract (pred, args, adorn, conds) for every direct MDB call in the body.

        'conds' are the positive non-MDB literals of the same body that provide
        bindings (used to build the magic seed rule).
        """
        body = list(rule.body)
        non_mdb_lits = [
            lit
            for lit in body
            if _is_pos_sym(lit) and _sig(lit.atom) not in self.mdb
        ]
        seeds = []
        for lit in body:
            is_mdb_pos = _is_pos_sym(lit) and _sig(lit.atom) in self.mdb
            is_mdb_neg = _is_neg_sym(lit) and _sig(lit.atom) in self.mdb
            if not (is_mdb_pos or is_mdb_neg):
                continue
            args = _args(lit.atom)
            name, _ = _sig(lit.atom)
            cond_vars: set[str] = set()
            for cond in non_mdb_lits:
                cond_vars |= _vars(cond)
            adorn = _adorn(args, cond_vars)
            if "b" in adorn:
                seeds.append((name, args, adorn, non_mdb_lits))
        return seeds

    def transform(self, text: str) -> str:
        self.parse(text)

        for w in _check_stratification(self._all_rules, self.mdb):
            print(w, file=sys.stderr)

        if not self.query_seeds:
            # No call with a bound argument: nothing to restrict. Return the
            # program unchanged but without the #magic directives, which
            # clingo does not accept.
            print("warning: no MDB call with a bound argument, no seed was "
                  "generated; the program is returned without #magic and is "
                  "not restricted.", file=sys.stderr)
            return strip_magic(text)

        for pred, args, adorn, conds in self.query_seeds:
            m_lit = _magic_lit(pred, adorn, args)
            self._add_magic(str(_rule(m_lit, conds)))
            ap = (pred, adorn)
            if ap not in self.D and ap not in list(self.S):
                self.S.append(ap)

        while self.S:
            ap = self.S.popleft()
            if ap in self.D:
                continue
            self.D.add(ap)
            pred, adorn = ap

            for rule in self.mdb_rules:
                matching = [
                    (idx, name, args)
                    for idx, name, args in _mdb_heads(rule, self.mdb)
                    if name == pred
                ]
                if not matching:
                    continue

                for head_idx, head_name, head_args in matching:
                    steps = self.sips(rule, head_idx, head_args, adorn, self.mdb)
                    for st in steps:
                        ap = (_sig(st.lit.atom)[0], st.adorn)
                        if ap not in self.D and ap not in self.S:
                            self.S.append(ap)
                    for ms in generate_magic(head_name, head_args, adorn, steps):
                        self._add_magic(ms)
                    self._add_modified(modify_rule(
                        rule, head_name, head_args, adorn, head_idx, steps,
                    ))

        return self._build_output()

    def _build_output(self) -> str:
        out: list[str] = []

        if self.edb_stmts:
            out.append("% -- EDB ---------------------------------")
            out.extend(self.edb_stmts)
            out.append("")

        out.append("% -- Magic seeds and magic rules --------")
        out.extend(self.magic_out)
        out.append("")

        out.append("% -- Modified MDB rules -----------------")
        out.extend(self.modified_out)
        out.append("")

        if self.query_stmts:
            out.append("% -- Non-MDB IDB rules (callers) --------")
            out.extend(self.query_stmts)
            out.append("")

        if self.other_stmts:
            out.append("% -- Directives -------------------------")
            out.extend(self.other_stmts)
            out.append("")

        return "\n".join(out)


# CLI


def main():
    import argparse

    ap = argparse.ArgumentParser(description="Dynamic Magic Sets transformation")
    ap.add_argument("input")
    ap.add_argument("output", nargs="?")
    ap.add_argument("--sips", choices=sorted(SIPS), default="edb")
    args = ap.parse_args()

    with open(args.input, encoding="utf-8") as f:
        text = f.read()
    try:
        result = DMSTransformer(args.sips).transform(text)
    except UnsupportedMDBUse as e:
        print(f"error: {e}", file=sys.stderr)
        sys.exit(1)
    print(result)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(result)


if __name__ == "__main__":
    main()
