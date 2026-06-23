"""
Transformación Magic Sets para programas ASP en clingo

Basado en: Alviano et al., "Magic Sets for Disjunctive Datalog Programs",
           AI 187-188 (2012) 156-192.

Uso:
    python dms.py input.lp [output.lp]

Formato de input:
    #magic pred/aridad.    % declara los predicados MDB a transformar
    <ASP rules>

Terminología:
    EDB  — hechos ground (cuerpo vacío)
    IDB  — reglas derivadas (cuerpo no vacío)
    MDB  — subconjunto del IDB declarado via #magic, son los predicados
           que se transforman con magic sets

SIPS: prioridad EDB (todos los átomos EDB/IDB-no-MDB antes que los MDB).
"""
from __future__ import annotations
import re
import sys
from collections import deque
from clingo import ast as A

# ── Localización sintética para nodos AST generados ─────────────────────────

_P = A.Position("<dms>", 1, 1)
LOC = A.Location(_P, _P)

# Directiva #magic

_MAGIC_RE = re.compile(r"#magic\s+(\w+)/(\d+)\s*\.", re.IGNORECASE)


def parse_magic(text: str) -> set[tuple[str, int]]:
    """Devuelve {(name, arity), ...} para todas las directivas #magic pred/n."""
    return {(m.group(1), int(m.group(2))) for m in _MAGIC_RE.finditer(text)}


def strip_magic(text: str) -> str:
    return _MAGIC_RE.sub("", text)


# Recolección de variables


def _vars(node: A.AST) -> set[str]:
    """Recopila de forma recursiva todos los nombres de Variables en el AST."""
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


# Literales


def _is_pos_sym(lit: A.AST) -> bool:
    """Literal simbólico positivo: p(args)."""
    return (
        lit.ast_type == A.ASTType.Literal
        and lit.sign == A.Sign.NoSign
        and lit.atom.ast_type == A.ASTType.SymbolicAtom
        and lit.atom.symbol.ast_type == A.ASTType.Function
    )


def _is_neg_sym(lit: A.AST) -> bool:
    """Literal simbólico negado: not p(args)."""
    return (
        lit.ast_type == A.ASTType.Literal
        and lit.sign == A.Sign.Negation
        and lit.atom.ast_type == A.ASTType.SymbolicAtom
        and lit.atom.symbol.ast_type == A.ASTType.Function
    )


def _is_cmp(lit: A.AST) -> bool:
    """Literal de comparación o aritmética: X = ..., N > 0, etc."""
    return (
        lit.ast_type == A.ASTType.Literal
        and lit.atom.ast_type == A.ASTType.Comparison
    )


def _sig(atom: A.AST) -> tuple[str, int]:
    """(name, arity) de un nodo SymbolicAtom."""
    s = atom.symbol
    return s.name, len(s.arguments)


def _args(atom: A.AST) -> list:
    return list(atom.symbol.arguments)


# Adornado


def _adorn(args: list, bound: set) -> str:
    """'b' si es constante o variable en bound, 'f' en cualquier otro caso."""
    return "".join(
        "b" if (a.ast_type != A.ASTType.Variable or a.name in bound) else "f"
        for a in args
    )


def _bound_from(args: list, adorn: str) -> set:
    """Nombres de variables en posiciones 'b' del adornado."""
    return {v for a, b in zip(args, adorn) if b == "b" for v in _vars(a)}


def _freshen_anon(node: A.AST, counter: list) -> A.AST:
    """Reemplaza variables anónimas '_' con AnonVarN para evitar unsafe heads."""
    if node.ast_type == A.ASTType.Variable and node.name == "_":
        fresh = A.Variable(LOC, f"AnonVar{counter[0]}")
        counter[0] += 1
        return fresh
    if node.ast_type == A.ASTType.Function:
        new_args = [_freshen_anon(a, counter) for a in node.arguments]
        return A.Function(LOC, node.name, new_args, node.external)
    return node


# Constructores de AST


def _pos_lit(name: str, args: list) -> A.AST:
    """Literal positivo: name(args)."""
    return A.Literal(
        LOC,
        A.Sign.NoSign,
        A.SymbolicAtom(A.Function(LOC, name, args, False)),
    )


def _magic_lit(pred: str, adorn: str, args: list) -> A.AST:
    """magic_pred_adorn(bound_args) como literal positivo."""
    bound = [a for a, b in zip(args, adorn) if b == "b"]
    return _pos_lit(f"magic_{pred}_{adorn}", bound)


def _adorned_lit(orig: A.AST, adorn: str) -> A.AST:
    """Renombra pred(args) pred_adorn(args) preservando el signo del literal."""
    sym = orig.atom.symbol
    new_sym = A.Function(LOC, f"{sym.name}_{adorn}", list(sym.arguments), False)
    return A.Literal(LOC, orig.sign, A.SymbolicAtom(new_sym))


def _rule(head: A.AST, body: list) -> A.AST:
    return A.Rule(LOC, head, body)


# Aritmética (safety)


def _arith_binds(lit: A.AST, bound: set) -> set | None:
    """
    Decide si una comparación es safe para inclir en el cuerpo de una magic rule.

    Devuelve el conjunto de nuevas variables bound:
      - Restricción pura (todas las variables ya bound, e.g. N > 0): return {}
      - Igualdad simple X = expr(bound_vars): bindea X, return {X}
      - Cualquier otro caso: return None (no se puede incluir de forma safe)
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
    Procesa literales aritméticos en orden y devuelve (safe_lits, final_bound).
    Solo incluye literales cuyas variables RHS (lado derecho) ya están bound.
    """
    safe: list[A.AST] = []
    bound = set(initial_bound)
    for lit in arith:
        nb = _arith_binds(lit, bound)
        if nb is not None:
            safe.append(lit)
            bound.update(nb)
    return safe, bound


# Estratificación


def _neg_cycle_exists(start: tuple, edges: dict) -> bool:
    """Devuelve True si 'start' participa en un ciclo con al menos una arista negativa.

    El estado (nodo, tiene_neg) registra si se ha atravesado alguna arista negativa
    en el camino actual desde 'start'.
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
    """Devuelve avisos para predicados MDB implicados en un ciclo no estratificado."""
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
                f"AVISO: #magic {name}/{arity} no está estratificado "
                f"(se detectó un ciclo a través de negación). "
                f"La transformación magic sets puede no preservar la semántica."
            )
    return warnings


# Clasificación de literales del cuerpo


def _classify(body: list, mdb: set) -> tuple[list, list, list, list]:
    """
    Clasifica los literales del cuerpo en 4 grupos (cada elemento es (body_index, lit)):
      non_mdb_pos: átomos simbólicos positivos que NO son MDB (EDB + IDB no magic)
      arith:       comparaciones y aritmética
      mdb_pos:     átomos simbólicos positivos que son MDB
      neg:         literales negados (MDB o no)
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


# Extracción de cabezas MDB


def _mdb_heads(rule: A.AST, mdb: set) -> list[tuple[int, str, list]]:
    """
    Devuelve [(elem_index, pred_name, args)] para cada átomo MDB en la cabeza.
    Maneja tanto cabezas simples como disjuntivas.
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


# Adornado (Fig. 3)


def adorn_rule(
    rule: A.AST,
    head_name: str,
    head_args: list,
    head_adorn: str,
    head_idx: int,
    mdb: set,
    S: deque,
    D: set,
) -> tuple[dict, dict, dict]:
    """
    Computa los adornados para los átomos del cuerpo usando SIPS con prioridad EDB.

    Orden del SIPS:
      1. Bindings del adornado de la cabeza
      2. Átomos no-MDB positivos (EDB y IDB no magic): ligan todas sus variables
      3. Aritmética safe: X = expr(bound) bindea X
      4. Átomos MDB positivos: adornados con el conjunto bound acumulado (fijo)
      5. Átomos MDB negados: consumen bindings, no producen

    Devuelve:
      body_adorns:       {body_index: adorn_str}  para átomos MDB positivos del cuerpo
      neg_adorns:        {body_index: adorn_str}  para átomos MDB negados del cuerpo
      other_head_adorns: {head_elem_idx: adorn_str} para otros átomos MDB de la cabeza
                         (solo se usa en reglas disjuntivas)
    """
    body = list(rule.body)
    non_mdb_pos, arith_raw, mdb_pos, neg = _classify(body, mdb)

    bound = _bound_from(head_args, head_adorn)

    # Paso 1: átomos no-MDB ligan todas sus variables
    for _, lit in non_mdb_pos:
        bound |= _vars(lit)

    # Paso 2: aritmética safe extiende bound antes de adornar los MDB
    arith_lits = [lit for _, lit in arith_raw]
    _, bound = _safe_arith(arith_lits, bound)

    # Paso 3: átomos MDB positivos, adornados con el conjunto bound fijo.
    # bound NO se actualiza entre llamadas MDB (sin propagación MDB-a-MDB).
    body_adorns: dict[int, str] = {}
    for i, lit in mdb_pos:
        args = _args(lit.atom)
        adorn = _adorn(args, bound)
        body_adorns[i] = adorn
        name, _ = _sig(lit.atom)
        if "b" in adorn:
            ap = (name, adorn)
            if ap not in D and ap not in list(S):
                S.append(ap)
        bound |= _vars(lit)

    # Paso 4: átomos MDB negados (procesados al final, no producen bindings)
    neg_adorns: dict[int, str] = {}
    for i, lit in neg:
        if not _is_neg_sym(lit):
            continue
        name, arity = _sig(lit.atom)
        if (name, arity) not in mdb:
            continue
        args = _args(lit.atom)
        adorn = _adorn(args, bound)
        neg_adorns[i] = adorn
        if "b" in adorn:
            ap = (name, adorn)
            if ap not in D and ap not in list(S):
                S.append(ap)

    # Paso 5: otros átomos MDB en cabezas disjuntivas
    other_head_adorns: dict[int, str] = {}
    if rule.head.ast_type == A.ASTType.Disjunction:
        for j, elem in enumerate(rule.head.elements):
            lit = elem.literal
            if j == head_idx or not _is_pos_sym(lit):
                continue
            name, arity = _sig(lit.atom)
            if (name, arity) not in mdb:
                continue
            args = _args(lit.atom)
            adorn = _adorn(args, bound)
            other_head_adorns[j] = adorn
            ap = (name, adorn)
            if ap not in D and ap not in list(S):
                S.append(ap)

    return body_adorns, neg_adorns, other_head_adorns


# Generar magic rules (Fig. 4)


def generate_magic(
    rule: A.AST,
    head_name: str,
    head_args: list,
    head_adorn: str,
    head_idx: int,
    body_adorns: dict,
    neg_adorns: dict,
    other_head_adorns: dict,
    mdb: set,
) -> list[str]:
    """
    Para cada átomo MDB adornado q^β en el cuerpo, emite:
        magic_q_β(ligado) :- magic_head_α(ligado), <átomos no-MDB>, <aritmética safe>.

    La aritmética safe se incluye para que las variables ligadas de llamadas
    recursivas queden ground (e.g. N1 = N-1 para factorial/2).
    """
    out: list[str] = []
    seen: set[str] = set()

    body = list(rule.body)
    non_mdb_pos, arith_raw, mdb_pos, neg = _classify(body, mdb)

    m_trigger = _magic_lit(head_name, head_adorn, head_args)

    bound_init = _bound_from(head_args, head_adorn)
    for _, lit in non_mdb_pos:
        bound_init |= _vars(lit)
    all_non_mdb = [lit for _, lit in non_mdb_pos]
    arith_lits = [lit for _, lit in arith_raw]
    safe_arith, _ = _safe_arith(arith_lits, bound_init)

    def _emit(r: A.AST):
        s = str(r)
        if s not in seen:
            seen.add(s)
            out.append(s)

    # Átomos MDB positivos en el cuerpo
    for i, lit in mdb_pos:
        adorn = body_adorns.get(i)
        if adorn is None or "b" not in adorn:
            continue
        name, _ = _sig(lit.atom)
        args = _args(lit.atom)
        m_conseq = _magic_lit(name, adorn, args)
        _emit(_rule(m_conseq, [m_trigger] + all_non_mdb + safe_arith))

    # Átomos MDB negados en el cuerpo
    for i, lit in neg:
        if not _is_neg_sym(lit):
            continue
        name, arity = _sig(lit.atom)
        if (name, arity) not in mdb:
            continue
        adorn = neg_adorns.get(i)
        if adorn is None or "b" not in adorn:
            continue
        args = _args(lit.atom)
        m_conseq = _magic_lit(name, adorn, args)
        _emit(_rule(m_conseq, [m_trigger]))

    # Cabezas disjuntivas: propagación cruzada entre átomos MDB hermanos
    if rule.head.ast_type == A.ASTType.Disjunction:
        all_context = all_non_mdb + safe_arith
        for j, elem in enumerate(rule.head.elements):
            lit = elem.literal
            if j == head_idx or not _is_pos_sym(lit):
                continue
            adorn = other_head_adorns.get(j)
            if not adorn or "b" not in adorn:
                continue
            name, _ = _sig(lit.atom)
            args = _args(lit.atom)
            m_conseq = _magic_lit(name, adorn, args)
            _emit(_rule(m_conseq, [m_trigger] + all_context))
            if "b" in head_adorn:
                m_main = _magic_lit(head_name, head_adorn, head_args)
                _emit(_rule(m_main, [m_conseq] + all_context))

    return out


# Modificar regla (Fig. 5)


def modify_rule(
    rule: A.AST,
    head_name: str,
    head_args: list,
    head_adorn: str,
    head_idx: int,
    body_adorns: dict,
    neg_adorns: dict,
    other_head_adorns: dict,
    mdb: set,
) -> str:
    """
    Construye la regla modificada:
      - Cabeza renombrada a pred_adorn
      - Magic guard(s) antepuestos al cuerpo
      - Átomos MDB del cuerpo renombrados a su versión adornada
      - EDB, IDB no-MDB y aritmética copiados sin cambios
      - Orden original del cuerpo preservado
    """
    body = list(rule.body)
    non_mdb_pos, arith_raw, mdb_pos, neg = _classify(body, mdb)

    _anon_ctr = [0]
    fresh_head_args = [_freshen_anon(a, _anon_ctr) for a in head_args]

    # Nueva cabeza
    orig_head = rule.head
    if _is_pos_sym(orig_head):
        sym = orig_head.atom.symbol
        new_sym = A.Function(LOC, f"{sym.name}_{head_adorn}", fresh_head_args, sym.external)
        new_head = A.Literal(LOC, orig_head.sign, A.SymbolicAtom(new_sym))
    elif orig_head.ast_type == A.ASTType.Disjunction:
        new_elems = []
        for j, elem in enumerate(orig_head.elements):
            lit = elem.literal
            if j == head_idx:
                sym = lit.atom.symbol
                new_sym = A.Function(LOC, f"{sym.name}_{head_adorn}", fresh_head_args, sym.external)
                new_lit = A.Literal(LOC, lit.sign, A.SymbolicAtom(new_sym))
            elif _is_pos_sym(lit) and _sig(lit.atom) in mdb and j in other_head_adorns:
                new_lit = _adorned_lit(lit, other_head_adorns[j])
            else:
                new_lit = lit
            new_elems.append(A.ConditionalLiteral(LOC, new_lit, []))
        new_head = A.Disjunction(LOC, new_elems)
    else:
        new_head = orig_head

    # Magic guard(s)
    guards = [_magic_lit(head_name, head_adorn, fresh_head_args)]
    if orig_head.ast_type == A.ASTType.Disjunction:
        for j, elem in enumerate(orig_head.elements):
            lit = elem.literal
            if j == head_idx or not _is_pos_sym(lit):
                continue
            adorn = other_head_adorns.get(j)
            if adorn and "b" in adorn:
                name, _ = _sig(lit.atom)
                args = _args(lit.atom)
                guards.append(_magic_lit(name, adorn, args))

    # Nuevo cuerpo: renombrar átomos MDB, copiar todo lo demás
    mdb_pos_idx = {i for i, _ in mdb_pos}
    neg_mdb_idx = {
        i
        for i, lit in neg
        if _is_neg_sym(lit) and _sig(lit.atom) in mdb
    }
    new_body: list[A.AST] = []
    for i, lit in enumerate(body):
        if i in mdb_pos_idx:
            adorn = body_adorns.get(i, "f" * len(_args(lit.atom)))
            if "b" in adorn:
                new_body.append(_adorned_lit(lit, adorn))
            else:
                new_body.append(lit)
        elif i in neg_mdb_idx:
            adorn = neg_adorns.get(i, "f" * len(_args(lit.atom)))
            if "b" in adorn:
                new_body.append(_adorned_lit(lit, adorn))
            else:
                new_body.append(lit)
        else:
            new_body.append(lit)

    return str(_rule(new_head, guards + new_body))


# Transformador DMS


class DMSTransformer:
    """
    Realiza la transformación DMS completa.

    Las directivas #magic pred/n declaran el MDB, el subconjunto del IDB
    que se transforma. Se verifica nombre y aridad, por lo que #magic f/1
    no afecta a f/2.
    """

    def __init__(self):
        self.mdb: set[tuple[str, int]] = set()   # predicados MDB (via #magic)
        self.mdb_rules: list[A.AST] = []          # reglas IDB con cabeza MDB
        self._all_rules: list[A.AST] = []         # todas las reglas (para estratificación)
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
        self._deadorn: set[tuple[str, str, int]] = set()

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

        # Clasificar reglas en MDB (cabeza MDB), EDB (hechos) e IDB no-MDB
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

        # Seeds: toda regla IDB no-MDB que llame directamente a un predicado MDB
        # contribuye una seed usando solo los átomos no-MDB de ese mismo cuerpo
        # como contexto de binding. No se propagan bindings a través de cadenas
        # de predicados IDB intermedios.
        for rule in idb_non_mdb:
            seeds = self._extract_seeds(rule)
            if seeds:
                self.query_seeds.extend(seeds)
                self.query_stmts.append(str(rule))
            else:
                self.edb_stmts.append(str(rule))

    def _extract_seeds(self, rule: A.AST) -> list:
        """
        Extrae (pred, args, adorn, conds) para cada llamada MDB directa en el cuerpo.

        'conds' son los literales no-MDB positivos del mismo cuerpo que proveen
        bindings (usados para construir la magic seed rule).
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
            return text

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
                    b_adorns, n_adorns, o_adorns = adorn_rule(
                        rule, head_name, head_args, adorn,
                        head_idx, self.mdb, self.S, self.D,
                    )
                    for ms in generate_magic(
                        rule, head_name, head_args, adorn,
                        head_idx, b_adorns, n_adorns, o_adorns, self.mdb,
                    ):
                        self._add_magic(ms)

                    self._add_modified(modify_rule(
                        rule, head_name, head_args, adorn,
                        head_idx, b_adorns, n_adorns, o_adorns, self.mdb,
                    ))
                    self._deadorn.add((pred, adorn, len(head_args)))

        return self._build_output()

    def _build_output(self) -> str:
        out: list[str] = []

        if self.edb_stmts:
            out.append("% -- EDB ---------------------------------")
            out.extend(self.edb_stmts)
            out.append("")

        out.append("% -- Magic seed y reglas mágicas ----------")
        out.extend(self.magic_out)
        out.append("")

        out.append("% -- Reglas MDB modificadas ---------------")
        out.extend(self.modified_out)
        out.append("")

        if self._deadorn:
            out.append("% -- De-adornado --------------------------")
            for pred, adorn, arity in sorted(self._deadorn):
                vs = [A.Variable(LOC, f"V{i}") for i in range(arity)]
                orig_head = _pos_lit(pred, vs)
                adorned_body = _pos_lit(f"{pred}_{adorn}", vs)
                out.append(str(_rule(orig_head, [adorned_body])))
            out.append("")

        if self.query_stmts:
            out.append("% -- Reglas IDB no-MDB (callers) ----------")
            out.extend(self.query_stmts)
            out.append("")

        if self.other_stmts:
            out.append("% -- Directivas --------------------------")
            out.extend(self.other_stmts)
            out.append("")

        return "\n".join(out)


# CLI


def main():
    if len(sys.argv) < 2:
        print("Uso: python dms.py input.lp [output.lp]")
        return
    with open(sys.argv[1]) as f:
        text = f.read()
    result = DMSTransformer().transform(text)
    print(result)
    if len(sys.argv) > 2:
        with open(sys.argv[2], "w") as f:
            f.write(result)


if __name__ == "__main__":
    main()
