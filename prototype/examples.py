"""Hand-encoded examples for prototype/checker.py. Run `python3 -I prototype/examples.py`.

The terms follow theories/examples with the indices of [let_new]: inside
New(S, C, e) the end at S sits at 1, the dual end at 0, and the outer
variables start at 4."""

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from checker import *

U = TUnit()
Close = ('end',)
def sndclose(): return ('seq', ('snd', 0, U), Close)          # !∗.Close

def thunk(ub, lb, body): return Lam(ub, lb, U, LetU(Var(0), body))
def spawn(t): return App(Konst('spawn'), t)
def close(e): return App(Konst('close'), e)
def send(v, c): return App(Konst('send'), Pair(v, c))
def recv(c): return App(Konst('recv'), c)
nofacts = Bcs([], [])

# sync: let (c, d) = new in spawn (λ(). close (send ⟨∗, c⟩)); let (x, d) = recv d in let () = x in close d
sync = New(sndclose(), nofacts,
    LetU(spawn(thunk(pvar(0, 1), pvar(0), close(send(Unit(), Var(2))))),
         LetP(recv(Var(0)), LetU(Var(1), close(Var(0))))))

# cycle: both threads close c before d; d is created under γ ≺ ε
cycle = New(Close, nofacts,
    New(Close, Bcs([pvar(0)], [fact('lt', pvar(1), pvar(0), "γ ≺ ε")]),
        LetU(spawn(thunk(pvar(0), pvar(1), LetU(close(Var(5)), close(Var(1))))),
             LetU(close(Var(5)), close(Var(1))))))

# blocked: the spawned thread closes d before c, the main thread c before d.
# With the same annotation as cycle the fact ε ≺ γ is missing; with the opposite
# annotation γ ≺ ε is missing. No creation constraint makes both hold.
blocked = New(Close, nofacts,
    New(Close, Bcs([pvar(0)], [fact('lt', pvar(1), pvar(0), "γ ≺ ε")]),
        LetU(spawn(thunk(pvar(1), pvar(0), LetU(close(Var(1)), close(Var(5))))),
             LetU(close(Var(5)), close(Var(1))))))

# delegation: c : !(∃ι. (!∗.Close)@ι).Close at ι, created under {ι ≺ ι[0], ι[0]+1 ≺ ι+1};
# d created by the alias at ι[0]. Receiver: recv c′, send ∗ on the received e and close it, close c′.
# Sender: send d on c, recv on d′, close d′, close c.
Sdel = ('seq', ('snd', 1, TSess(sndclose(), pvar(0))), Close)
dl_C = Bcs([], [fact('lt', pvar(0), slot(pvar(0), 0), "ι ≺ ι[0]"),
                fact('lt', shift(slot(pvar(0), 0)), pvar(0, 1), "ι[0]+1 ≺ ι+1")])
alias_C = Bcs([slot(pvar(0), 0)], [fact('eq', pvar(0), pvar(1), "ι ≡ w")])
delegation = New(Sdel, dl_C,
    New(sndclose(), alias_C,
        # indices: d = 1, d′ = 0, c = 5, c′ = 4
        LetU(spawn(thunk(pvar(1, 1), pvar(1),
                 LetP(recv(Var(5)), LetU(close(send(Unit(), Var(1))), close(Var(0)))))),
             LetP(Pair(send(Var(1), Var(5)), Unit()),
                  LetU(Var(0),
                       LetP(recv(Var(2)), LetU(Var(1), LetU(close(Var(0)), close(Var(3))))))))))

# request and reply, at the level of its constraints (the box is not a term of the prototype).
# C = {ι+k ≺ ι′+k, ι′+k ≺ ι+k+1}: strict as a uniform one-counter constraint, closed under the
# shift σ = (ι+1, ι′+1) of the recursive call, and it entails the facts the two bodies ask for.
rq_C = [Schema('lt', lambda k: pvar(0, k), lambda k: pvar(1, k), True, "ι+k ≺ ι′+k"),
        Schema('lt', lambda k: pvar(1, k), lambda k: pvar(0, k + 1), True, "ι′+k ≺ ι+k+1")]
rq_call = [Schema('lt', lambda k: pvar(0, k + 1), lambda k: pvar(1, k + 1), True),
           Schema('lt', lambda k: pvar(1, k + 1), lambda k: pvar(0, k + 2), True)]
rq_body_atoms = [fact('lt', pvar(0), pvar(1)),          # recv a at ι while b is held at ι′
                 fact('lt', pvar(1), pvar(0, 1)),       # send on b at ι′ while a is held at ι+1
                 fact('lt', pvar(1), pvar(1, 1))]       # the thunk's upper point ι′+1 above its gate
rq_rejected = [Schema('lt', lambda k: pvar(0, k), lambda k: pvar(1, k), True, "ι+k ≺ ι′+k"),
               Schema('lt', lambda k: pvar(1, k), lambda k: pvar(0, k), True, "ι′+k ≺ ι+k")]

if __name__ == "__main__":
    check("sync", sync)
    check("cycle", cycle)
    check("blocked", blocked, expect=False)
    check("delegation", delegation)
    print(f"{'rq_C strict':14s} {uniform_strict(rq_C)}")
    print(f"{'rq_C[σ] ⊆ C':14s} {all(schema_entails(rq_C, s) for s in rq_call)}")
    print(f"{'rq body atoms':14s} {all(schema_entails(rq_C, s) for s in rq_body_atoms)}")
    print(f"{'rr_call ι+1≺ι′':14s} {schema_entails(rq_C, fact('lt', pvar(0, 1), pvar(1)))}  (rejected in Rejected.v)")
    print(f"{'rq_rejected':14s} {uniform_strict(rq_rejected)}  (a zero cycle, not strict)")
    assert uniform_strict(rq_C) and not uniform_strict(rq_rejected)
    assert not schema_entails(rq_C, fact('lt', pvar(0, 1), pvar(1)))
    print("all checks passed")
