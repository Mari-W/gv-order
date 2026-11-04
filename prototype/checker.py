"""Prototype of the bidirectional checker of docs/extensions/algorithmic-bidir.md
and of the decision procedures of docs/extensions/algorithmic-decidable.md.

Run `python3 -I prototype/checker.py`. It types the hand-encoded examples of
prototype/examples.py and prints one line per example.

Points are (name, offset). A name is ('c', k) for a constant, ('v', k) for a
point variable (de Bruijn as in the Rocq development, 0 the innermost), or
('s', parent_name, b, i) for the payload point (parent, b)[i]. Terms are the
annotated terms of theories/algorithmic/Algorithmic.v. Boxes are not terms
here. Their constraints are checked at the constraint level (uniform_strict,
schema_entails) on the schemas the examples state.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Union, Callable
import itertools

# ---------------------------------------------------------------- points

def pvar(a, o=0): return (('v', a), o)
def pconst(a, o=0): return (('c', a), o)
def shift(x, k=1): return (x[0], x[1] + k)
def slot(x, i): return (('s', x[0], x[1], i), 0)

def name_root(n):
    while n[0] == 's':
        n = n[1]
    return n

def root(x): return name_root(x[0])

def pname_inst(sigma, n):
    """Instantiate point variables in a name. sigma maps variable index to a point."""
    if n[0] == 'c': return (n, 0)
    if n[0] == 'v': return sigma(n[1])
    p = pname_inst(sigma, n[1])
    return slot((p[0], p[1] + n[2]), n[3])

def pinst(sigma, x):
    p = pname_inst(sigma, x[0])
    return (p[0], p[1] + x[1])

def pshift(m):
    return lambda a: pvar(a + m)

def plist(xs):
    return lambda a: xs[a] if a < len(xs) else pvar(a - len(xs))

def pt_str(x):
    n, o = x
    def ns(n):
        if n[0] == 'c': return f"c{n[1]}"
        if n[0] == 'v': return f"ι{n[1]}"
        return f"({ns(n[1])}+{n[2]})[{n[3]}]" if n[2] else f"{ns(n[1])}[{n[3]}]"
    return f"{ns(n)}+{o}" if o else ns(n)

# ---------------------------------------------------------------- types

@dataclass(frozen=True)
class TUnit: pass
@dataclass(frozen=True)
class TLolli:
    ub: Optional[tuple]; lb: Optional[tuple]; T: object; U: object
@dataclass(frozen=True)
class TProd: T: object; U: object
@dataclass(frozen=True)
class TSum: T: object; U: object
@dataclass(frozen=True)
class TSess: s: object; x: tuple
@dataclass(frozen=True)
class TBox:
    n: int; C: object; T: object          # □(∀ι₀…ιₙ₋₁. C. T), T a thunk type

# session types: ('end',) ('snd', m, T) ('rcv', m, T) ('mu', s) ('var', a) ('skip',) ('seq', s1, s2)
# ('plus', s1, s2) ('with', s1, s2); payload binds m points.

def dual(s):
    k = s[0]
    if k == 'end': return s
    if k == 'snd': return ('rcv', s[1], s[2])
    if k == 'rcv': return ('snd', s[1], s[2])
    if k == 'mu': return ('mu', dual(s[1]))     # polarity flip not needed: payloads carry no session variables here
    if k == 'var': return ('dvar', s[1])
    if k == 'dvar': return ('var', s[1])
    if k == 'skip': return s
    if k == 'seq': return ('seq', dual(s[1]), dual(s[2]))
    if k == 'plus': return ('with', dual(s[1]), dual(s[2]))
    if k == 'with': return ('plus', dual(s[1]), dual(s[2]))
    raise ValueError(s)

def sinst(s, d, r):
    """substitute r for variable d in s"""
    k = s[0]
    if k in ('end', 'skip'): return s
    if k in ('snd', 'rcv'): return s
    if k == 'mu': return ('mu', sinst(s[1], d + 1, r))
    if k == 'var': return r if s[1] == d else s
    if k == 'dvar': return dual(r) if s[1] == d else s
    return (k, sinst(s[1], d, r), sinst(s[2], d, r))

def hd(s, fuel=50):
    """head normal form unr(S): ('skip',) | ('snd'/'rcv', m, T, tail) | ('plus'|'with', s1, s2) | ('end',)"""
    if fuel == 0: raise ValueError("not contractive")
    k = s[0]
    if k == 'skip': return ('skip',)
    if k == 'end': return ('end',)
    if k in ('snd', 'rcv'): return (k, s[1], s[2], ('skip',))
    if k in ('plus', 'with'): return s
    if k == 'mu': return hd(sinst(s[1], 0, s), fuel - 1)
    if k == 'seq':
        h = hd(s[1], fuel - 1)
        if h[0] == 'skip': return hd(s[2], fuel - 1)
        if h[0] in ('snd', 'rcv'):
            tail = h[3]
            return (h[0], h[1], h[2], s[2] if tail == ('skip',) else ('seq', tail, s[2]))
        if h[0] in ('plus', 'with'):
            return (h[0], ('seq', h[1], s[2]), ('seq', h[2], s[2]))
        return h
    raise ValueError(s)

def tinst(sigma, T):
    if isinstance(T, TUnit): return T
    if isinstance(T, TLolli):
        return TLolli(pinst(sigma, T.ub) if T.ub else None, pinst(sigma, T.lb) if T.lb else None,
                      tinst(sigma, T.T), tinst(sigma, T.U))
    if isinstance(T, TProd): return TProd(tinst(sigma, T.T), tinst(sigma, T.U))
    if isinstance(T, TSum): return TSum(tinst(sigma, T.T), tinst(sigma, T.U))
    if isinstance(T, TSess): return TSess(T.s, pinst(sigma, T.x))
    if isinstance(T, TBox):
        up = lambda a: pvar(a) if a < T.n else pinst(pshift(T.n), sigma(a - T.n))
        return TBox(T.n, T.C.inst(sigma), tinst(up, T.T))
    raise ValueError(T)

def payload_at(m, T, x):
    return tinst(plist([slot(x, i) for i in range(m)]), T)

def heads(T):
    if isinstance(T, TSess): return {T.x}
    if isinstance(T, TLolli): return {T.lb} if T.lb else set()
    if isinstance(T, (TProd, TSum)): return heads(T.T) | heads(T.U)
    return set()

def tmatch(T, U):
    """≡ atoms making T and U equal, or None"""
    if type(T) is not type(U): return None
    if isinstance(T, TUnit): return []
    if isinstance(T, TLolli):
        if (T.ub is None) != (U.ub is None) or (T.lb is None) != (U.lb is None): return None
        r = []
        if T.ub: r.append(('eq', T.ub, U.ub))
        if T.lb: r.append(('eq', T.lb, U.lb))
        a, b = tmatch(T.T, U.T), tmatch(T.U, U.U)
        return None if a is None or b is None else r + a + b
    if isinstance(T, (TProd, TSum)):
        a, b = tmatch(T.T, U.T), tmatch(T.U, U.U)
        return None if a is None or b is None else a + b
    if isinstance(T, TSess):
        return [('eq', T.x, U.x)] if T.s == U.s else None
    if isinstance(T, TBox):
        return [] if T == U else None
    return None

# ---------------------------------------------------------------- constraints

@dataclass
class Schema:
    """∀k. lhs(k) R rhs(k) with lhs, rhs functions from the counter to points, or a ground fact
    when counter is False. kind is 'lt' or 'eq'."""
    kind: str
    lhs: Callable[[int], tuple]
    rhs: Callable[[int], tuple]
    counter: bool = True
    label: str = ""
    def inst(self, sigma):
        return Schema(self.kind, lambda k: pinst(sigma, self.lhs(k)), lambda k: pinst(sigma, self.rhs(k)),
                      self.counter, self.label)
    def ground(self, bound):
        ks = range(bound) if self.counter else [0]
        return [(self.kind, self.lhs(k), self.rhs(k)) for k in ks]

@dataclass
class Bcs:
    """A constraint over the variables 0..n-1 (fresh) and outer env points shifted past them."""
    env: list
    schemas: list
    def inst(self, sigma):
        return Bcs([pinst(sigma, x) for x in self.env], self.schemas)
    def at(self, xs):
        """the facts C[xs/ιs], as schemas over ground points"""
        sig = plist(xs + self.env)
        return [s.inst(sig) for s in self.schemas]

def fact(kind, x, y, label=""):
    return Schema(kind, lambda k: x, lambda k: y, False, label)

# ---------------------------------------------------------------- 𝔇₁: the alias structure and cycles

class Theory:
    """The fact theory generated by ground facts (𝔇₁), with the 𝔇₂ schemas unrolled to a bound
    for the strictness checks that algorithmic-decidable.md Section 2 covers exactly."""
    def __init__(self, facts):
        self.ltf = [(x, y) for (k, x, y) in facts if k == 'lt']
        self.eqf = [(x, y) for (k, x, y) in facts if k == 'eq']
        self.names = set()
        for (x, y) in self.ltf + self.eqf:
            for p in (x, y):
                n = p[0]
                while True:
                    self.names.add(n)
                    if n[0] != 's': break
                    n = n[1]
        self.consistent = True
        self._closure()

    def _closure(self):
        names = list(self.names)
        idx = {n: i for i, n in enumerate(names)}
        N = len(names)
        INF = float('inf')
        # D[i][j] potential, T[i][j] threshold in i's offset coordinate; None when unrelated
        D = [[None] * N for _ in range(N)]
        Tm = [[INF] * N for _ in range(N)]
        for i in range(N):
            D[i][i] = 0; Tm[i][i] = 0
        edges = list(self.eqf)
        def add(p, a, q, b):
            i, j = idx[p], idx[q]
            for (u, v, d, t) in ((i, j, b - a, a), (j, i, a - b, b)):
                if D[u][v] is None:
                    D[u][v] = d; Tm[u][v] = t
                elif D[u][v] != d:
                    self.consistent = False
                else:
                    Tm[u][v] = min(Tm[u][v], t)
        for (x, y) in edges:
            add(x[0], x[1], y[0], y[1])
        changed = True
        while changed and self.consistent:
            # Floyd–Warshall with max-threshold composition
            for k in range(N):
                for i in range(N):
                    if D[i][k] is None: continue
                    for j in range(N):
                        if D[k][j] is None: continue
                        d = D[i][k] + D[k][j]
                        t = max(Tm[i][k], Tm[k][j] - D[i][k])
                        if D[i][j] is None:
                            D[i][j] = d; Tm[i][j] = t
                        elif D[i][j] != d:
                            self.consistent = False
                        elif t < Tm[i][j]:
                            Tm[i][j] = t
            changed = False
            # payload congruence: parents ≡ at the stored base offsets → payload names ≡ at threshold 0
            for p in names:
                for q in names:
                    if p[0] == 's' and q[0] == 's' and p != q and p[3] == q[3]:
                        i, j = idx[p], idx[q]
                        if D[i][j] is None and self._eq_pts((p[1], p[2]), (q[1], q[2]), D, Tm, idx):
                            D[i][j] = 0; D[j][i] = 0; Tm[i][j] = 0; Tm[j][i] = 0
                            changed = True
        self.D, self.T, self.idx = D, Tm, idx

    def _eq_pts(self, x, y, D, Tm, idx):
        i, j = idx[x[0]], idx[y[0]]
        return D[i][j] is not None and y[1] == x[1] + D[i][j] and x[1] >= Tm[i][j]

    def equiv(self, x, y):
        if x == y: return True
        if x[0] not in self.idx or y[0] not in self.idx: return False
        return self._eq_pts(x, y, self.D, self.T, self.idx)

    def weak(self, x, y):
        """x (≡ ∪ ≤po)* y; returns None, 'weak' or 'strict' (Lemma 2 of algorithmic-decidable.md)"""
        if x[0] == y[0] and x[0] not in self.idx:
            return None if y[1] < x[1] else ('weak' if x[1] == y[1] else 'strict')
        if x[0] not in self.idx or y[0] not in self.idx:
            return None
        i, j = self.idx[x[0]], self.idx[y[0]]
        if self.D[i][j] is None: return None
        best = None
        for p in self.idx.values():
            if self.D[i][p] is None or self.D[j][p] is None: continue
            if x[1] >= self.T[i][p] and y[1] >= self.T[j][p]:
                a, b = x[1] + self.D[i][p], y[1] + self.D[j][p]
                if a < b: return 'strict'
                if a == b: best = 'weak'
        return best

    def lt(self, x, y):
        """x ≺ y in the generated order"""
        if not self.consistent: return True
        M = {x, y} | {p for e in self.ltf for p in e}
        # search for a path x ⇝ y with a strict step
        from collections import deque
        seen = set()
        dq = deque([(x, False)])
        while dq:
            u, strict = dq.popleft()
            if (u, strict) in seen: continue
            seen.add((u, strict))
            for v in M:
                w = self.weak(u, v)
                if w is None: continue
                s2 = strict or w == 'strict'
                if v == y and s2: return True
                if (v, s2) not in seen: dq.append((v, s2))
                for (a, b) in self.ltf:
                    if a == v:
                        if b == y: return True
                        dq.append((b, True))
        return False

    def strict(self):
        """Theorem 1 of algorithmic-decidable.md"""
        if not self.consistent: return False
        M = sorted({p for e in self.ltf for p in e} | {p for e in self.eqf for p in e}, key=str)
        for x in M:
            if self.lt(x, x): return False
        return True

    def le(self, x, y):
        return self.equiv(x, y) or self.lt(x, y)

# ---------------------------------------------------------------- creation constraints (shape A)

def cc_ok(outer: Theory, C: Bcs, fresh_root, bound=4):
    """Theorem 2 of algorithmic-decidable.md for shape A. The constraint is given already
    instantiated at the fresh point (root fresh_root) and the outer points."""
    facts = []
    for s in C.at([(fresh_root, 0)]):
        facts += s.ground(bound)
    if len(C.schemas) == 1 and C.schemas[0].kind == 'eq' and not C.schemas[0].counter:
        (k, x, w) = facts[0]
        if x == (fresh_root, 0) and root(w) != fresh_root:
            return True, "shape B, one alias"           # cc_ok_alias of static/Fundamental.v
    if any(k == 'eq' for (k, _, _) in facts):
        return False, "alias facts are outside shapes A and B"
    lo = [(u, p) for (k, u, p) in facts if root(u) != fresh_root and root(p) == fresh_root]
    hi = [(q, v) for (k, q, v) in facts if root(q) == fresh_root and root(v) != fresh_root]
    inn = [(k, x, y) for (k, x, y) in facts if root(x) == fresh_root and root(y) == fresh_root]
    bad = [(x, y) for (k, x, y) in facts if root(x) != fresh_root and root(y) != fresh_root]
    for (x, y) in bad:
        if not outer.lt(x, y): return False, f"outer fact {pt_str(x)} ≺ {pt_str(y)} not in Γ"
    R = Theory(inn)
    if not R.strict(): return False, "cycle inside the fresh point"
    for (u, p) in lo:
        for (q, v) in hi:
            if p == q or R.lt(p, q):
                if not outer.lt(u, v):
                    return False, f"not conservative: {pt_str(u)} ≺ {pt_str(v)} via the fresh point"
    return True, "ok"

# ---------------------------------------------------------------- 𝔇₂ᵘ: uniform shift schemas

def uniform_strict(schemas):
    """Theorem 3: every component of the weighted name graph has cycles of one strict sign."""
    edges = {}
    names = set()
    for s in schemas:
        assert s.kind == 'lt' and s.counter
        x0, y0, x1, y1 = s.lhs(0), s.rhs(0), s.lhs(1), s.rhs(1)
        assert x1[0] == x0[0] and y1[0] == y0[0] and x1[1] == x0[1] + 1 and y1[1] == y0[1] + 1, "not a shift schema"
        names |= {x0[0], y0[0]}
        edges.setdefault(x0[0], []).append((y0[0], y0[1] - x0[1]))
    for n in names:
        edges.setdefault(n, []).append((n, 1))      # program order
    # strongly connected components (Tarjan)
    index, low, onstack, stack, comps = {}, {}, set(), [], []
    counter = itertools.count()
    def sc(v):
        index[v] = low[v] = next(counter); stack.append(v); onstack.add(v)
        for (w, _) in edges[v]:
            if w not in index:
                sc(w); low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = set()
            while True:
                w = stack.pop(); onstack.discard(w); comp.add(w)
                if w == v: break
            comps.append(comp)
    for v in names:
        if v not in index: sc(v)
    def no_cycle_at_most_zero(comp, sign):
        # all simple cycles have weight ≥ 1 (sign=+1) or ≤ -1 (sign=-1): Bellman–Ford on w' = n·sign·w − 1
        n = len(comp)
        dist = {v: 0 for v in comp}
        for _ in range(n):
            for v in comp:
                for (w, d) in edges[v]:
                    if w in comp:
                        nd = dist[v] + n * sign * d - 1
                        if nd < dist[w]: dist[w] = nd
        for v in comp:
            for (w, d) in edges[v]:
                if w in comp and dist[v] + n * sign * d - 1 < dist[w]:
                    return False
        return True
    for comp in comps:
        if not (no_cycle_at_most_zero(comp, +1) or no_cycle_at_most_zero(comp, -1)):
            return False
    return True

def schema_entails(gamma_schemas, goal: Schema, bound=6):
    """entailment of a shift schema from shift schemas and ground facts, checked on the
    instances up to a bound (sufficient in 𝔇₂ᵘ and 𝔇₂ᵐ when the bound exceeds every constant,
    algorithmic-decidable.md Section 2.3)"""
    facts = []
    for s in gamma_schemas:
        facts += s.ground(bound + 2)
    th = Theory(facts)
    for k in range(bound):
        if not th.lt(goal.lhs(k), goal.rhs(k)): return False
    return True

# ---------------------------------------------------------------- terms

@dataclass
class Var: x: int
@dataclass
class Unit: pass
@dataclass
class Konst: k: str
@dataclass
class Lam: ub: Optional[tuple]; lb: Optional[tuple]; T: object; e: object
@dataclass
class App: e1: object; e2: object
@dataclass
class Pair: e1: object; e2: object
@dataclass
class LetU: e1: object; e2: object
@dataclass
class LetP: e1: object; e2: object
@dataclass
class Inj1: U: object; e: object
@dataclass
class Inj2: T: object; e: object
@dataclass
class Case: e: object; e1: object; e2: object
@dataclass
class New: S: object; C: Bcs; e: object          # let (a, b) = new in e: a at 1, b at 0

def occ(x, e):
    if isinstance(e, Var): return e.x == x
    if isinstance(e, (Unit, Konst)): return False
    if isinstance(e, Lam): return occ(x + 1, e.e)
    if isinstance(e, (App, Pair, LetU)): return occ(x, e.e1) or occ(x, e.e2)
    if isinstance(e, LetP): return occ(x, e.e1) or occ(x + 2, e.e2)
    if isinstance(e, (Inj1, Inj2)): return occ(x, e.e)
    if isinstance(e, Case): return occ(x, e.e) or occ(x + 1, e.e1) or occ(x + 1, e.e2)
    if isinstance(e, New): return occ(x + 4, e.e)
    raise ValueError(e)

def unlimited(T): return isinstance(T, TBox)

def split(e1, x1, e2, x2, Delta):
    """occurrence split; raises on a linear variable used twice or never"""
    d1, d2 = [], []
    for i, T in enumerate(Delta):
        if T is None:
            d1.append(None); d2.append(None); continue
        a, b = occ(x1 + i, e1), occ(x2 + i, e2)
        if unlimited(T):
            d1.append(T); d2.append(T); continue
        if a == b:
            raise TypeError(f"linear variable {i} used {'twice' if a else 'never'}")
        d1.append(T if a else None); d2.append(T if b else None)
    return d1, d2

def lenv_heads(Delta):
    return set().union(*[heads(T) for T in Delta if T is not None]) if Delta else set()

class Synth:
    """The synthesis judgment. Atoms are collected into self.atoms as tuples:
    ('lt', x, y), ('eq', x, y), ('le', x, y), ('known', x), ('cc', C, depth), ('false', why),
    ('hold', C, xs) for the instance of a box constraint at a force.
    Point variables are de Bruijn; self.depth counts binders so that atoms can be
    reported with stable names."""
    def __init__(self):
        self.atoms = []
        self.fresh = 0

    def emit(self, a): self.atoms.append(a)

    def gate(self, Phi, u, F):
        if u is None: return
        pts, fv = F
        for y in pts: self.emit(('lt', u, y))
        if fv is None: return
        if fv == 'bot': self.emit(('false', 'a call under the ⊥ flag')); return
        hyp = Phi.get(fv, 'absent')
        if hyp == 'absent' or hyp is None: self.emit(('false', 'a call inside a non-blocking λ')); return
        self.emit(('le', u, hyp))

    def synth(self, Phi, Delta, F, Psi, e):
        """Psi: list of (Bcs, xs) hypotheses in scope (for box-constraint containment checks)."""
        if isinstance(e, Var):
            T = Delta[e.x]
            if T is None: raise TypeError(f"variable {e.x} spent")
            for i, U in enumerate(Delta):
                if i != e.x and U is not None and not unlimited(U): raise TypeError(f"variable {i} unused")
            return T
        if isinstance(e, Unit):
            if any(U is not None and not unlimited(U) for U in Delta): raise TypeError("unused variable at ∗")
            return TUnit()
        if isinstance(e, Konst):
            raise TypeError("bare constant")
        if isinstance(e, Lam):
            phi = self.fresh; self.fresh += 1
            H = lenv_heads(Delta)
            if e.lb is None:
                if H: raise TypeError("closure without lower point captures channels")
            else:
                for h in H: self.emit(('le', e.lb, h))
            U = self.synth({**Phi, phi: e.ub}, [e.T] + Delta, (set(), phi), Psi, e.e)
            return TLolli(e.ub, e.lb, e.T, U)
        if isinstance(e, App) and isinstance(e.e1, Konst):
            A = self.synth(Phi, Delta, F, Psi, e.e2)
            return self.konst(Phi, F, e.e1.k, A)
        if isinstance(e, App):
            d1, d2 = split(e.e1, 0, e.e2, 0, Delta)
            Tf = self.synth(Phi, d1, (F[0] | lenv_heads(d2), F[1]), Psi, e.e1)
            if not isinstance(Tf, TLolli): raise TypeError("application of a non-function")
            Ta = self.synth(Phi, d2, (F[0] | ({Tf.lb} if Tf.lb else set()), F[1]), Psi, e.e2)
            m = tmatch(Ta, Tf.T)
            if m is None: raise TypeError(f"argument type mismatch {Ta} vs {Tf.T}")
            for a in m: self.emit(a)
            self.gate(Phi, Tf.ub, F)
            return Tf.U
        if isinstance(e, Pair):
            d1, d2 = split(e.e1, 0, e.e2, 0, Delta)
            T = self.synth(Phi, d1, (F[0] | lenv_heads(d2), F[1]), Psi, e.e1)
            U = self.synth(Phi, d2, (F[0] | heads(T), F[1]), Psi, e.e2)
            return TProd(T, U)
        if isinstance(e, LetU):
            d1, d2 = split(e.e1, 0, e.e2, 0, Delta)
            T = self.synth(Phi, d1, (F[0] | lenv_heads(d2), F[1]), Psi, e.e1)
            if not isinstance(T, TUnit): raise TypeError("let () of a non-unit")
            return self.synth(Phi, d2, F, Psi, e.e2)
        if isinstance(e, LetP):
            d1, d2 = split(e.e1, 0, e.e2, 2, Delta)
            T = self.synth(Phi, d1, (F[0] | lenv_heads(d2), F[1]), Psi, e.e1)
            if not isinstance(T, TProd): raise TypeError("let pair of a non-pair")
            return self.synth(Phi, [T.U, T.T] + d2, F, Psi, e.e2)
        if isinstance(e, Inj1):
            return TSum(self.synth(Phi, Delta, F, Psi, e.e), e.U)
        if isinstance(e, Inj2):
            return TSum(e.T, self.synth(Phi, Delta, F, Psi, e.e))
        if isinstance(e, Case):
            d1, d2 = split(e.e, 0, Lam(None, None, None, Pair(e.e1, e.e2)), 0, Delta)
            T = self.synth(Phi, d1, (F[0] | lenv_heads(d2), F[1]), Psi, e.e)
            if not isinstance(T, TSum): raise TypeError("case of a non-sum")
            T1 = self.synth(Phi, [T.T] + d2, F, Psi, e.e1)
            T2 = self.synth(Phi, [T.U] + d2, F, Psi, e.e2)
            m = tmatch(T2, T1)
            if m is None: raise TypeError("branch types differ")
            for a in m: self.emit(a)
            return T1
        if isinstance(e, New):
            self.emit(('cc', e.C, len(Psi)))
            for x in e.C.env: self.emit(('known', x))
            sh = pshift(1)
            Phi2 = {k: (pinst(sh, v) if v else None) for k, v in Phi.items()}
            Delta2 = [TSess(dual(e.S), pvar(0)), TSess(e.S, pvar(0)), None, None] + \
                     [tinst(sh, T) if T is not None else None for T in Delta]
            F2 = ({pinst(sh, y) for y in F[0]}, F[1])
            Psi2 = [(C.inst(sh), [pinst(sh, x) for x in xs]) for (C, xs) in Psi] + [(e.C.inst(sh), [pvar(0)])]
            self.emit(('open', len(Psi)))
            U = self.synth(Phi2, Delta2, F2, Psi2, e.e)
            self.emit(('close', len(Psi)))
            return tinst(lambda a: pvar(a - 1), U)
        raise ValueError(e)

    def konst(self, Phi, F, k, A):
        if k == 'spawn':
            if isinstance(A, TLolli) and isinstance(A.T, TUnit) and isinstance(A.U, TUnit): return TUnit()
            raise TypeError("spawn of a non-thunk")
        if k == 'recv':
            if not isinstance(A, TSess): raise TypeError("recv on a non-channel")
            h = hd(A.s)
            if h[0] != 'rcv': raise TypeError(f"recv on {h}")
            _, m, T, tail = h
            self.gate(Phi, A.x, F)
            return TProd(payload_at(m, T, A.x), TSess(tail, shift(A.x)))
        if k == 'send':
            if not (isinstance(A, TProd) and isinstance(A.U, TSess)): raise TypeError("send on a non-channel")
            h = hd(A.U.s)
            if h[0] != 'snd': raise TypeError(f"send on {h}")
            _, m, T, tail = h
            P = payload_at(m, T, A.U.x)
            mm = tmatch(A.T, P)
            if mm is None: raise TypeError(f"payload mismatch {A.T} vs {P}")
            for a in mm: self.emit(a)
            for hp in heads(P): self.emit(('lt', A.U.x, hp))
            self.gate(Phi, A.U.x, F)
            return TSess(tail, shift(A.U.x))
        if k == 'close':
            if not isinstance(A, TSess) or hd(A.s)[0] != 'end': raise TypeError("close on a non-Close")
            self.gate(Phi, A.x, F)
            return TUnit()
        if k in ('sel1', 'sel2'):
            if not isinstance(A, TSess): raise TypeError("select on a non-channel")
            h = hd(A.s)
            if h[0] != 'plus': raise TypeError("select on a non-choice")
            i = 0 if k == 'sel1' else 1
            self.emit(('lt', A.x, slot(A.x, i)))
            self.gate(Phi, A.x, F)
            return TSess(h[1 + i], slot(A.x, i))
        if k == 'branch':
            if not isinstance(A, TSess): raise TypeError("branch on a non-channel")
            h = hd(A.s)
            if h[0] != 'with': raise TypeError("branch on a non-choice")
            self.emit(('lt', A.x, slot(A.x, 0))); self.emit(('lt', A.x, slot(A.x, 1)))
            self.gate(Phi, A.x, F)
            return TSum(TSess(h[1], slot(A.x, 0)), TSess(h[2], slot(A.x, 1)))
        if k == 'link':
            if not (isinstance(A, TProd) and isinstance(A.T, TSess) and isinstance(A.U, TSess)): raise TypeError("link")
            if A.U.s != dual(A.T.s): raise TypeError("link of non-dual sessions")
            self.emit(('eq', A.T.x, A.U.x))
            return TUnit()
        raise TypeError(f"unknown constant {k}")

# ---------------------------------------------------------------- deciding the constraint of a program

def decide(atoms, C0: Bcs, n0: int, bound=4):
    """Walk the atoms in order, maintaining the stack of hypotheses as the binders open
    (algorithmic-bidir.md Section 3). Returns (ok, message). The theory at each depth is the
    𝔇₁ theory of the ground facts of the hypotheses in scope with every schema unrolled to a
    bound, which is exact for 𝔇₁ and for the entailments of 𝔇₂ᵘ, 𝔇₂ᵐ below the bound."""
    # hypotheses are kept at their own depth; a point at depth d is shifted to the current depth
    hyps = [(C0, [pvar(i) for i in range(n0)], 0)]
    depth = 0
    def theory_at(depth):
        facts = []
        for (C, xs, d) in hyps:
            sh = pshift(depth - d)
            for s in C.at(xs):
                facts += s.inst(sh).ground(bound)
        return Theory(facts)
    pending_cc = {}
    for a in atoms:
        kind = a[0]
        if kind == 'open':
            C = pending_cc.pop(a[1])
            hyps.append((C.inst(pshift(1)), [pvar(0)], depth + 1)); depth += 1; continue
        if kind == 'close':
            hyps.pop(); depth -= 1; continue
        th = theory_at(depth)
        if not th.strict(): return False, "the context is not strict"
        if kind == 'cc':
            C, d = a[1], a[2]
            # the fresh root is variable 0 after the shift; outer points shift by one
            outer = theory_at(depth + 1)
            ok, why = cc_ok(outer, C.inst(pshift(1)), ('v', 0), bound)
            if not ok: return False, f"creation constraint rejected: {why}"
            pending_cc[d] = C
        elif kind == 'lt':
            if not th.lt(a[1], a[2]): return False, f"missing fact {pt_str(a[1])} ≺ {pt_str(a[2])}"
        elif kind == 'eq':
            if not th.equiv(a[1], a[2]): return False, f"missing alias {pt_str(a[1])} ≡ {pt_str(a[2])}"
        elif kind == 'le':
            if not th.le(a[1], a[2]): return False, f"missing fact {pt_str(a[1])} ≼ {pt_str(a[2])}"
        elif kind == 'known':
            if not any(root(a[1]) == root(x) for (_, xs, d) in hyps for x in xs): return False, f"unknown point {pt_str(a[1])}"
        elif kind == 'false':
            return False, a[1]
        elif kind == 'hold':
            C, xs = a[1], a[2]
            for s in C.at(xs):
                for (k, x, y) in s.ground(bound):
                    if k == 'lt' and not th.lt(x, y): return False, f"force: missing {pt_str(x)} ≺ {pt_str(y)}"
                    if k == 'eq' and not th.equiv(x, y): return False, f"force: missing {pt_str(x)} ≡ {pt_str(y)}"
    return True, "ok"

def check(name, term, C0=Bcs([], []), n0=0, expect=True):
    s = Synth()
    try:
        T = s.synth({}, [], (set(), None), [(C0, [pvar(i) for i in range(n0)])], term)
    except (TypeError, NotImplementedError) as ex:
        print(f"{name:14s} REJECTED by synthesis: {ex}")
        assert not expect
        return
    ok, why = decide(s.atoms, C0, n0)
    verdict = "accepted" if ok else "rejected"
    print(f"{name:14s} {verdict:9s} type {T.__class__.__name__:6s} {len(s.atoms)} atoms  {why}")
    assert ok == expect, (name, ok, expect, why)
