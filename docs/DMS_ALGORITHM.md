# DMS Magic Sets Algorithm — Code Correspondence

> Referencia principal: Alviano, Faber, Greco, Leone. *Magic Sets for Disjunctive Datalog Programs.*
> Artificial Intelligence 187–188 (2012) 156–192.

---

## 1. Introduction


The Magic Sets transformation (Dynamic Magic Sets in the paper) rewrites a Datalog program so that only the atoms relevant to a given query are derived.  It does so by inserting special **magic** predicates that carry binding information, thereby simulating a top-down evaluation of the program — similar to how a Prolog interpreter would proceed, but without abandoning the declarative semantics of the ASP program.

Concretely, given a program `P` and a query `Q = p(t)` (asking for ground instances of predicate `p`), DMS produces a program `DMS(Q, P)` that is *query-equivalent* to `P` but with the advantage of a significantly smaller *grounding* step.

La salida tendrá tres tipos de reglas generadas, más el resto del programa original:

| Tipo | Propósito |
|------|-----------|
|**Magic seed**    | un hecho *ground* que determina qué átomo es el inicial a la hora de comenzar el proceso de eliminación de variables para las reglas mágicas (**magic rules**), generalmente contendrá los átomos instanciados de la *query* |
| **Magic Rules** | propagan la información de forma *top-down* a través de llamadas recursivas |
| **Reglas transformadas**| Se tratan de las reglas originales del programa, adornadas y modificadas con sus respectivo **magic predicates**| 


---

## 2. Key Concepts

### 2.1 EDB, IDB, and what `#magic pred/n` selects

The standard Datalog distinction:
- **EDB** (*Extensional Database*): stores **facts** — rules with an empty body.  Example: `parent(juan, antonio). parent(maria, fernando).` are ground facts in the EDB.
- **IDB** (*Intensional Database*): holds the rules that *derive* facts.  Any rule with a non-empty head that refers to other predicates in its body belongs to the IDB.  Example: `son(X,Y) :- parent(Y,X).` makes `son/2` an IDB member.


**The `#magic pred/arity` directive** selects which IDB predicate(s) will be transformed — typically recursive predicates operating over a large EDB whose *grounding* we want to restrict.
#### Cómo el transformador particiona el programa

```python
# DMSTransformer.parse()
for rule in all_rules:
    if _idb_heads(rule, self.idb):   # predicado declarado via #magic
        self.idb_rules.append(rule)  # -> se adornará y modificará
    elif not list(rule.body):
        self.edb_stmts.append(...)   # hecho ground
    else:
        non_idb.append(rule)         # regla IDB NO SELECCIONADA para transformar
                                     # (IDB en términos de datalog, pero no relevante al programa)
```

`non_idb` rules include ordinary predicates that are preserved verbatim in the output, as well as any directives not needed for the transformation.

In the code, `self.idb` always means **"the IDB predicates selected for transformation"** — a subset of the program's full IDB.

> **Arity check** — `self.idb` stores `(name, arity)` pairs, so `#magic reach/2` only transforms `reach/2` and leaves a hypothetical `reach/1` untouched.  The helper `_idb_heads()` checks `(name, arity) in idb`, not just the name.

### 2.2 Adornments

An **adornment** is a string over `{b, f}` with one character per argument of the predicate:
- `b`, **bound**: the argument is a constant at the call site, or has become ground through a preceding atom in the SIPS ordering.
- `f`, **free**: the argument is unconstrained.

`path_bb(X, Y)` means both arguments of `path/2` are bound;  
`reach_bf(X, Y)` means only the first is.

En `dms.py`:

```python
def _adorn(args: list, bound: set) -> str:
    return "".join(
        "b" if (a.ast_type != A.ASTType.Variable or a.name in bound) else "f"
        for a in args
    )

def _bound_from(args: list, adorn: str) -> set:
    return {
        a.name for a, b in zip(args, adorn)
        if b == "b" and a.ast_type == A.ASTType.Variable
    }
```

### 2.3 Magic predicates
For an adorned predicate `p_a`, its **magic version** `magic_p_a(t_b)` is a new predicate whose arguments are only the `b`-adorned arguments of `p`.  If all arguments are free, the magic predicate is propositional (arity 0) and carries no binding information.

```python
def _magic_lit(pred: str, adorn: str, args: list) -> A.AST:
    bound = [a for a, b in zip(args, adorn) if b == "b"]
    return _pos_lit(f"magic_{pred}_{adorn}", bound)
```

### 2.4 SIPS (Sideways Information Passing Strategy)

The SIPS is a rule-level specification of the order in which body atoms are processed
and how variable bindings flow from one atom to the next.  The paper supports arbitrary
SIPSes (Definition 2.2 / 3.3); this implementation uses the **EDB-first** strategy:

> Process non-magic body atoms first (EDB atoms — base facts and non-selected
> derived predicates — provide ground bindings), then arithmetic, then the
> magic-selected IDB atoms whose recursive calls we are restricting.

In a rule body, "EDB atom" from the SIPS point of view means any positive atom
whose predicate is **not** in `self.idb` — including atoms like `son(X, Y)` that
are IDB in the Datalog sense but not targeted by the transformation.  Their
groundings are taken as given, just like base facts.

This is the strategy used in the running example of Section 2.3 and is sound for
any Datalog^{∨,¬s} program.

---

## 3. Algorithm Structure (Fig. 1 — `DMS`)

The paper's main algorithm (Fig. 1, p. 163):

```
Algorithm DMS(Q, P)
var S, D : set of adorned predicates
    modifiedRules, magicRules : set of rules
begin
  S := ∅;  D := ∅;  modifiedRules := ∅
  magicRules := { BuildQuerySeed(Q, S) }          -- § 4 below

  while S ≠ ∅ do
    p^α := pop(S);   D := D ∪ {p^α}
    for each rule r ∈ P, for each p(t) ∈ H(r) do
      r^a    := Adorn(r, p^α(t), S, D)            -- § 5 below
      magicRules    += Generate(r, p^α(t), r^a)   -- § 6 below
      modifiedRules += { Modify(r, r^a) }          -- § 7 below
    end for
  end while

  DMS(Q,P) := magicRules ∪ modifiedRules ∪ EDB(P)
end
```

The corresponding code is in `DMSTransformer.transform()`:

```python
def transform(self, text: str) -> str:
    self.parse(text)          # classifies rules; extracts seeds (§ 4)

    for pred, args, adorn, conds in self.query_seeds:
        m_lit = _magic_lit(pred, adorn, args)
        self._add_magic(str(_rule(m_lit, conds)))  # seed fact / rule
        ap = (pred, adorn)
        
        if ap not in self.D and ap not in list(self.S):
            self.S.append(ap)

    while self.S:                         # main loop — Fig. 1, lines 2–9
        ap = self.S.popleft()
        if ap in self.D:
            continue
        self.D.add(ap)
        pred, adorn = ap

        for rule in self.idb_rules:
            matching = [(idx, name, args)
                        for idx, name, args in _idb_heads(rule, self.idb)
                        if name == pred]
            for head_idx, head_name, head_args in matching:
                b_adorns, n_adorns, o_adorns = adorn_rule(...)   # Adorn
                for ms in generate_magic(...):                    # Generate
                    self._add_magic(ms)
                self._add_modified(modify_rule(...))              # Modify
```

Sets `S` and `D` are managed via a `deque` and a `set` respectively.  Deduplication
of generated rules is handled by `_seen_magic` and `_seen_modified`.

---

## 4. Seeding — `BuildQuerySeed` (Fig. 2)

### 4.1 The paper's version

The paper assumes a classical Datalog query of the form `Q = p(t̄)` where `t̄`
is a tuple of **constants**.  `BuildQuerySeed` computes the adornment by inspecting
each argument: constants get `b`, variables get `f`.  It emits a ground magic fact:

```
magic_p_α(t̄_b).     -- e.g.  magic_path_bb(1, 5).
```

and pushes `p^α` onto `S`.

### 4.2 The clingo adaptation — why it is different

Clingo/ASP has **no query syntax**.  There is no `?- reach(a, X).`.  Instead, the
"query" is encoded implicitly as an ordinary rule:

```prolog
reachable(Y)  :- source(X), reach(X, Y).
result(X)     :- factorial(5, X).
```

These rules are the *interface* between the user and the IDB.  They are not base
facts, but they carry the initial binding information that would have been a query
in Datalog.

The implementation detects these **query rules** automatically:

> A **query rule** is a non-IDB rule whose head predicate is not called by any other
> non-IDB rule in the program.  In other words, its head is a "root" — it is only
> consumed by the user (e.g., shown via `#show`), not by further rules.

```python
# In DMSTransformer.parse():
called_sigs: set[tuple[str, int]] = set()
for rule in non_idb:
    for lit in rule.body:
        if _is_pos_sym(lit):
            called_sigs.add(_sig(lit.atom))

for rule in non_idb:
    head = rule.head
    is_root = (not _is_pos_sym(head)) or (_sig(head.atom) not in called_sigs)
    if is_root:
        seeds = self._extract_seeds(rule)
        ...
```

Once a query rule is identified, `_extract_seeds()` plays the role of `BuildQuerySeed`:

```python
def _extract_seeds(self, rule: A.AST) -> list:
    body = list(rule.body)
    # "context literals": all non-magic positive atoms in the same rule body.
    # These may be EDB facts (source/1) or non-selected derived predicates —
    # either way their variables are treated as ground at the call site.
    context_lits = [lit for lit in body
                    if _is_pos_sym(lit) and _sig(lit.atom) not in self.idb]
    seeds = []
    for lit in body:
        if not _is_pos_sym(lit) or _sig(lit.atom) not in self.idb:
            continue
        args = _args(lit.atom)
        name, _ = _sig(lit.atom)
        cond_vars: set[str] = set()
        for cond in context_lits:
            cond_vars |= _vars(cond)     # variables made ground by context atoms
        adorn = _adorn(args, cond_vars)
        if "b" in adorn:
            seeds.append((name, args, adorn, context_lits))
    return seeds
```

The adornment is computed from:
- **constants** in the magic-IDB call's argument list (always `b`), and
- **variables** that appear in any non-magic atom in the same rule body
  (whether that atom is a base fact like `source(X)` or a derived predicate).

| Query rule | Magic IDB call | Bound by | Adornment | Seed emitted |
|-----------|---------|---------|-----------|-------------|
| `result(X) :- factorial(5, X).` | `factorial(5, X)` | constant `5` | `bf` | `magic_factorial_bf(5).` |
| `reachable(Y) :- source(X), reach(X, Y).` | `reach(X, Y)` | `source(X)` binds `X` | `bf` | `magic_reach_bf(X) :- source(X).` |

When the seed has conditions (like `source(X)` for reach), the magic seed is emitted
as a **rule** rather than a ground fact:

```python
m_lit = _magic_lit(pred, adorn, args)
self._add_magic(str(_rule(m_lit, conds)))
# conds=[]  → "magic_factorial_bf(5)."        (fact)
# conds=[source(X)] → "magic_reach_bf(X) :- source(X)."  (rule)
```

The query rule itself is then preserved as-is in the output (under `% -- Query rules`),
referring to the original (de-adorned) predicate name.

---

## 5. Adorn (Fig. 3) — `adorn_rule()`

The paper's `Adorn(r, p^α(t̄), S, D)` (Fig. 3, p. 165) iterates over every IDB atom
`p_i(t̄_i)` in `H(r) ∪ B⁺(r) ∪ B⁻(r)`.  For each argument:
- If it is a **constant** → `b`
- If it is a **variable** X → `b` if X is made ground by the SIPS ordering (either
  it comes from the head's bound variables, or from a preceding non-magic atom in
  the body — which may be a base fact or any derived predicate not selected for
  magic sets); `f` otherwise.

Newly adorned predicates not yet in `D` are pushed onto `S`.

### 5.1 EDB-first SIPS (our implementation)

The implementation follows an EDB-first strategy in three steps:

```
Step 1: variables bound by head adornment
Step 2: all non-magic body atoms — their variables are added to bound
        (includes base EDB facts AND any derived predicate not in #magic)
Step 3: (extension) safe arithmetic literals — may bind one more variable
Step 4: magic-IDB body atoms — adorned with accumulated bound set
Step 5: negated magic-IDB body atoms — processed last, consume but do not produce bindings
```

Step 3 is **our addition** for numeric recursion (see § 5.2).

```python
def adorn_rule(rule, head_name, head_args, head_adorn, head_idx, idb, S, D):
    body = list(rule.body)
    edb_pos, arith_raw, idb_pos, neg = _classify(body, idb)
    # _classify puts into edb_pos any positive atom NOT in self.idb —
    # this includes both true EDB facts and non-magic derived predicates.

    bound = _bound_from(head_args, head_adorn)       # Step 1

    for _, lit in edb_pos:                           # Step 2
        bound |= _vars(lit)

    arith_lits = [lit for _, lit in arith_raw]
    _, bound = _safe_arith(arith_lits, bound)        # Step 3

    body_adorns: dict[int, str] = {}
    for i, lit in idb_pos:                           # Step 4
        args = _args(lit.atom)
        adorn = _adorn(args, bound)
        body_adorns[i] = adorn
        name, _ = _sig(lit.atom)
        ap = (name, adorn)
        if ap not in D and ap not in list(S):
            S.append(ap)
        bound |= _vars(lit)
    ...
```

For disjunctive rules, the paper also propagates the binding **across head atoms**:
once the full body has been processed, sibling head IDB atoms are adorned with the
accumulated bound set (Section 3.1, p. 162).  This is implemented in Step 5 of
`adorn_rule()` (the `other_head_adorns` computation).

### 5.2 Arithmetic extension for numeric recursion

The paper's SIPS was designed for pure Datalog (no arithmetic).  In clingo programs
like `factorial/2`, arithmetic literals such as `N > 0` and `N1 = N-1` carry
essential binding information that must be seen before adorning the recursive call.

Without this extension, for the recursive rule:

```prolog
factorial(N, F) :- N > 0, N1 = N-1, factorial(N1, F1), F = N*F1.
```

the recursive call `factorial(N1, F1)` would be adorned `ff` (both free), since `N1`
appears to be unbound if arithmetic is ignored.  This generates an unbounded
`magic_factorial_ff` predicate — clingo cannot ground it without a finite domain.

`_safe_arith()` processes arithmetic literals in program order, including a literal
only when it is **safe**:

| Pattern | Condition | Effect |
|---------|-----------|--------|
| `N > 0` | all variables (`N`) already bound | pure constraint — include, no new bindings |
| `N1 = N-1` | RHS variables (`N`) all bound, LHS (`N1`) is a variable | assignment — include, `N1` becomes bound |
| `F = N*F1` | `F1` not yet bound | unsafe — exclude from magic rule body |

```python
def _arith_binds(lit: A.AST, bound: set) -> set | None:
    if not _is_cmp(lit):
        return None
    all_v = _vars(lit)
    if all_v <= bound:
        return set()                      # pure constraint, all vars already bound

    cmp = lit.atom
    guards = cmp.guards
    if (len(guards) == 1
            and guards[0].comparison == A.ComparisonOperator.Equal):
        lhs = cmp.term
        if lhs.ast_type == A.ASTType.Variable and lhs.name not in bound:
            rhs_vars = _vars(guards[0].term)
            if rhs_vars <= bound:
                return {lhs.name}         # X = expr(bound) — binds X
    return None                           # cannot include safely
```

After applying safe arithmetic, `N1` is in `bound` and the recursive call gets
adornment `bf` — only the first argument (`N1`, the input) is bound.  This is
the correct adornment for factorial's recursive case.

---

## 6. Generate (Fig. 4) — `generate_magic()`

The paper's `Generate(r, p^α(t̄), r^a)` (Fig. 4, p. 167) produces, for each adorned
magic-IDB atom `q^β_i(t̄_i)` in the adorned rule `r^a` (that is not the current head),
a magic rule of the form:

```
magic_q_β(t̄_i,b)  :-  magic_p_α(t̄_b),  <non-magic atoms preceding q_i in SIPS order>.
```

The body contains the trigger (`magic_p_α`) plus all non-magic atoms that precede `q_i`
in the SIPS ordering — these are the atoms (EDB facts or non-selected derived
predicates) that provide the bindings captured in `β`.

### 6.1 Non-magic-first: all context atoms precede all magic-IDB atoms

Under the EDB-first SIPS, every non-magic atom precedes every magic-IDB atom.
Therefore the "preceding context" for any magic-IDB body atom is simply *all*
non-magic atoms in the rule body.

### 6.2 Our extension: safe arithmetic in magic rule bodies

For the same reason as in § 5.2, safe arithmetic literals are also included in the
magic rule body.  Without them, the magic rule for the recursive factorial call would be:

```prolog
magic_factorial_bf(N1) :- magic_factorial_bf(N).   % WRONG — N1 is free!
```

With safe arithmetic included:

```prolog
magic_factorial_bf(N1) :- magic_factorial_bf(N), N > 0, N1 = (N-1).  % correct
```

This rule, together with the seed `magic_factorial_bf(5).`, generates the finite
descending chain `5 → 4 → 3 → 2 → 1 → 0` without requiring an explicit domain fact
like `num(0..5)`.

```python
def generate_magic(rule, head_name, head_args, head_adorn, head_idx,
                   body_adorns, neg_adorns, other_head_adorns, idb):
    body = list(rule.body)
    edb_pos, arith_raw, idb_pos, neg = _classify(body, idb)

    m_trigger = _magic_lit(head_name, head_adorn, head_args)

    bound_init = _bound_from(head_args, head_adorn)
    for _, lit in edb_pos:
        bound_init |= _vars(lit)
    all_edb = [lit for _, lit in edb_pos]
    safe_arith, _ = _safe_arith([lit for _, lit in arith_raw], bound_init)

    for i, lit in idb_pos:              # for each adorned IDB body atom
        adorn = body_adorns.get(i)
        if adorn is None or "b" not in adorn:
            continue
        name, _ = _sig(lit.atom)
        args = _args(lit.atom)
        m_conseq = _magic_lit(name, adorn, args)
        # magic rule body = trigger + EDB + safe arithmetic
        _emit(_rule(m_conseq, [m_trigger] + all_edb + safe_arith))
```

For **negated** IDB body atoms, the paper propagates the magic guard but not the
EDB body (the negated atom is processed last in the SIPS; bindings come entirely
from positive atoms already in `bound`).

For **disjunctive head** rules, cross-propagation rules are also generated between
sibling head atoms (Section 3.1 of the paper), handled in the final block of
`generate_magic()`.

---

## 7. Modify (Fig. 5) — `modify_rule()`

The paper's `Modify(r, r^a)` (Fig. 5, p. 168) is straightforward:

> Take the adorned rule `r^a`.  For each adorned head atom `p^α(t̄)` occurring in
> `H(r^a)`, add `magic(p^α(t̄))` to the body.  Strip adornments from non-magic
> predicates in the head.

The result is a rule of the form:

```
p(t̄) ∨ p₁(t̄₁) ∨ ⋯ ∨ pₙ(t̄ₙ)  :-  magic(p^α(t̄)),  magic(p₁^α₁(t̄₁)),  …,
                                      q₁(s̄₁),  …,  qⱼ(s̄ⱼ),  not qⱼ₊₁(s̄ⱼ₊₁),  …
```

where `q₁, …, qⱼ` are the body atoms that are **not** magic-selected IDB — they may
be base EDB facts, non-selected derived predicates, or arithmetic.  All of these are
copied unchanged into the modified rule.  Only the magic-IDB atoms in the body are
renamed to their adorned versions.

Note: the head atoms keep their *original* (non-adorned) names — the adornments are
an internal artefact.  De-adornment rules (§ 8) then link adorned and original predicates.

In `dms.py` the head *is* renamed to the adorned name (e.g., `factorial_bf`), and
then de-adornment rules map back: `factorial(V0,V1) :- factorial_bf(V0,V1).`  This
achieves the same semantics and keeps the query rules referencing the original names.

```python
def modify_rule(rule, head_name, head_args, head_adorn, head_idx,
                body_adorns, neg_adorns, other_head_adorns, idb):
    body = list(rule.body)
    ...
    # Rename head to adorned version
    if _is_pos_sym(orig_head):
        new_head = _adorned_lit(orig_head, head_adorn)   # p → p_bf

    # Prepend magic guard(s)
    guards = [_magic_lit(head_name, head_adorn, head_args)]

    # Rename magic-IDB body atoms to adorned versions; everything else unchanged.
    # "Everything else" = base facts, non-magic derived predicates, arithmetic.
    for i, lit in enumerate(body):
        if i in idb_pos_idx:
            adorn = body_adorns.get(i, "f" * len(_args(lit.atom)))
            new_body.append(_adorned_lit(lit, adorn))    # q → q_bf
        else:
            new_body.append(lit)                         # preserved as-is

    return str(_rule(new_head, guards + new_body))
```

The original order of body literals is preserved, which is important for readability
and for keeping the arithmetic conditions next to the atoms they constrain.

---

## 8. De-adornment and Output

After the main loop, for every adorned predicate `p_α/n` that was produced,
a **de-adornment rule** is emitted:

```prolog
p(V0, V1, …, Vn-1) :- p_α(V0, V1, …, Vn-1).
```

This allows the query rules — which reference original predicate names — to fire
correctly, and lets the user query `p` without knowing which adornments were generated.

```python
for pred, adorn, arity in sorted(self._deadorn):
    vs = [A.Variable(LOC, f"V{i}") for i in range(arity)]
    orig_head   = _pos_lit(pred, vs)
    adorned_body = _pos_lit(f"{pred}_{adorn}", vs)
    out.append(str(_rule(orig_head, [adorned_body])))
```

---

## 9. Complete Worked Example — `factorial/2`

**Input (`factorial.lp`):**
```prolog
#magic factorial/2.

factorial(0, 1).
factorial(N, F) :- N > 0, N1 = N-1, factorial(N1, F1), F = N*F1.

result(X) :- factorial(5, X).
```

**Step-by-step:**

### Seeding
- Query rule: `result(X) :- factorial(5, X).` (root: `result` not called by other rules)
- IDB call: `factorial(5, X)`.  No EDB conditions.  `5` is a constant → `b`; `X` is free → `f`.
- Adornment: **`bf`**
- Seed emitted: `magic_factorial_bf(5).`  → push `(factorial, bf)` onto S.

### Process `(factorial, bf)`:

**Rule 1:** `factorial(0, 1).`
- Head args `[0, 1]`, adorn `bf` → bound = `{}` (constants, no variable names)
- No body atoms → no magic rules
- Modified: `factorial_bf(0,1) :- magic_factorial_bf(0).`
  *(guard: first arg `0` is at `b` position → `magic_factorial_bf(0)`)*

**Rule 2:** `factorial(N, F) :- N > 0, N1 = N-1, factorial(N1, F1), F = N*F1.`
- Head adorn `bf` → bound = `{N}`
- EDB: none
- Safe arithmetic:
  - `N > 0`: vars `{N}` ⊆ `{N}` → safe constraint, bound stays `{N}`
  - `N1 = N-1`: lhs=`N1`, rhs vars `{N}` ⊆ `{N}` → binds `N1`, bound = `{N, N1}`
  - `F = N*F1`: rhs vars include `F1` ∉ `{N, N1}` → **excluded**
- IDB: `factorial(N1, F1)` with bound `{N, N1}` → adorn **`bf`** (already in D, skip enqueue)
- Magic rule: `magic_factorial_bf(N1) :- magic_factorial_bf(N), N>0, N1=(N-1).`
- Modified: `factorial_bf(N,F) :- magic_factorial_bf(N), N>0, N1=(N-1), factorial_bf(N1,F1), F=(N*F1).`

### Output
```prolog
% -- Magic seed & rules ------------------
magic_factorial_bf(5).
magic_factorial_bf(N1) :- magic_factorial_bf(N); N > 0; N1 = (N-1).

% -- Modified rules ----------------------
factorial_bf(0,1) :- magic_factorial_bf(0).
factorial_bf(N,F) :- magic_factorial_bf(N); N > 0; N1 = (N-1); factorial_bf(N1,F1); F = (N*F1).

% -- De-adornment rules ------------------
factorial(V0,V1) :- factorial_bf(V0,V1).

% -- Query rules -------------------------
result(X) :- factorial(5,X).
```

The magic chain `5 → 4 → 3 → 2 → 1 → 0` is generated at grounding time solely
from the seed and the magic rule.  Clingo grounds a finite program with no domain
predicate needed.

---

## 10. Implementation Notes

### Use of clingo AST

All parsing and code generation uses `clingo.ast`:
- **Input**: `clingo.ast.parse_string()` — handles all valid clingo syntax correctly
- **Construction**: `ast.Rule()`, `ast.Literal()`, `ast.Function()`, `ast.SymbolicAtom()`, etc.
- **Output**: `str(ast_node)` — produces valid clingo syntax (clingo uses `;` as the
  body conjunction separator internally; this is accepted by all clingo versions ≥ 5)

The `#magic` directives are not standard clingo syntax and are stripped with a regex
before passing the program to `parse_string`.

### Function–figure correspondence

| Paper | Code |
|-------|------|
| Algorithm DMS (Fig. 1) | `DMSTransformer.transform()` |
| BuildQuerySeed (Fig. 2) | `DMSTransformer.parse()` + `_extract_seeds()` |
| Adorn (Fig. 3) | `adorn_rule()` |
| Generate (Fig. 4) | `generate_magic()` |
| Modify (Fig. 5) | `modify_rule()` |
| Adornment string | `_adorn()`, `_bound_from()` |
| SIPS ordering | `_classify()`, `_safe_arith()` (non-magic atoms → arithmetic → magic IDB atoms) |
| magic(p^α(t̄)) | `_magic_lit()` |
| p^α(t̄) (adorned atom) | `_adorned_lit()` |
