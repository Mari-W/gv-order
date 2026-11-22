// Examples of what lock freedom rules out beyond deadlock freedom: one per mechanism.
// Each program steps forever without a deadlock while some thread waits forever.
const { examples } = require('./core');

examples.push(
  { id: 'rx-postpone', title: 'Postponement, a holding thread that never serves', modes: ['lf'],
    code: `chat = !(f = λa. let a = send ⟨∗, a⟩ in (force f) a)
loop = !(f = λ⟨a, b⟩. let ⟨u, a⟩ = recv a in let ∗ = u in (force f) ⟨a, b⟩)
main = let ⟨a, a′⟩ = new in let ⟨b, b′⟩ = new in
       let ∗ = spawn (λ_. (force chat) a′) in
       let ∗ = spawn (λ_. close b′) in
       (force loop) ⟨a, b⟩            -- holds b forever, close b′ waits forever`,
    shows: "$\\mathsf{loop}$ holds $b$ across a loop that never returns, so $\\mathsf{close}\\,b'$ waits while the process keeps stepping. Aging asks $c \\leq a$ of every held end, and the loop has cost $c = \\infty$.",
    rocq: 'to be mechanized',
    accepts: { lf: { ok: false, part: 'aging' } } },
  { id: 'rx-delegate', title: 'Endless delegation, an end that travels forever', modes: ['lf'],
    code: `pass = !(f = λ⟨e, x, y⟩. let x = send ⟨e, x⟩ in let ⟨e, y⟩ = recv y in (force f) ⟨e, x, y⟩)
back = !(f = λ⟨x, y⟩. let ⟨e, x⟩ = recv x in let y = send ⟨e, y⟩ in (force f) ⟨x, y⟩)
main = let ⟨e, e′⟩ = new in let ⟨x, x′⟩ = new in let ⟨y, y′⟩ = new in
       let ∗ = spawn (λ_. close e′) in       -- waits for e forever
       let ∗ = spawn (λ_. (force back) ⟨x′, y′⟩) in
       (force pass) ⟨e, x, y⟩                -- e goes back and forth forever`,
    shows: "$e$ travels between two threads forever and its partner $e'$ waits. Each send transfers $e$ on with its counter minus one, so after finitely many transfers no credit is left to send it again.",
    rocq: 'to be mechanized',
    accepts: { lf: { ok: false, part: 'payload credit' } } },
  { id: 'rx-relink', title: 'Link refresh, a waiting thread that always faces a fresh end', modes: ['lf'],
    code: `refresh = !(f = λ⟨w, k⟩. let ⟨c, c′⟩ = new in
                     let ∗ = link ⟨w, c⟩ in          -- the waiting thread now talks to c′
                     let k = send ⟨∗, k⟩ in           -- one step on another channel
                     (force f) ⟨c′, k⟩)
sink    = !(f = λk. let ⟨u, k⟩ = recv k in let ∗ = u in (force f) k)
main = let ⟨w, w′⟩ = new in let ⟨k, k′⟩ = new in
       let ∗ = spawn (λ_. close w′) in              -- waits forever
       let ∗ = spawn (λ_. (force sink) k′) in
       (force refresh) ⟨w, k⟩`,
    shows: "Each round links the partner of the waiting end to a fresh channel, so the waiting thread always faces a fresh end with a full counter and no counter runs out. E-Link asks the credit of each linked end to exceed the partner bound $N - m$ of the other, and a fresh end with a full counter fails it.",
    rocq: 'to be mechanized',
    accepts: { lf: { ok: false, part: 'tickets' } } },
  { id: 'rx-chain', title: 'A waiting chain that grows forever', modes: ['lf'],
    code: `grow = !(f = λw. let ⟨c, c′⟩ = new in                 -- c below the point of w
                 let ⟨d, d′⟩ = new in let ∗ = spawn (λ_. recvclose d′) in
                 let ∗ = close (send ⟨∗, d⟩) in              -- one session action
                 let ∗ = spawn (λ_. (force f) c′) in
                 let ∗ = close c in close w)                 -- waits on its child
main = let ⟨w, w′⟩ = new in let ∗ = spawn (λ_. close w′) in (force grow) w
-- every thread waits on the one it spawned, close w′ never proceeds`,
    shows: "Each thread waits on a point below the point of its predecessor, and new threads keep appearing. At a fresh root the creation states a fact from the new point down to the point of $w$, and $\\mathsf{wf\\_new}$ forbids it. At a field the box needs that fact one level lower in every round, so the tree of the root of main holds an infinite descending chain, and E-New rejects main.",
    rocq: 'static/Contexts.v: gen_new, new_ok; examples/ForkJoin.v: fj_wait_needs',
    accepts: { lf: { ok: false, part: 'E-New' } } }
);
