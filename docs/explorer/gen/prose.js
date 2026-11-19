// The text a reader sees first: section intros, block captions and the notes behind block titles.
// It overrides what the section files set, so the reader-facing prose is written in one place.
// Writing rules: docs/explorer/BLOCKS.md and the pl-paper-writing skill of sill-obs.
const { sections } = require('./core');

const INTRO = {}, CAP = {}, WHY = {}, EX = {};

// ---- syntax ----
INTRO.syntax = 'Programs are terms of a call-by-value $\\lambda$-calculus with session-typed channels. Terms never mention points. Points appear in types and in the relation, where they order the waits of threads.';
CAP['syn-terms'] = 'Thirteen term formers with de Bruijn variables. A box $!e$ binds itself in $e$, and $k$ ranges over the constants.';
WHY['syn-terms'] = 'Typing has one rule per term former, and the semantics one head step per redex.';
CAP['syn-let'] = 'The one-variable $\\mathsf{let}$ is notation for a pair followed by a unit elimination, with $u$ fresh.';
WHY['syn-let'] = 'Examples read better with a one-variable $\\mathsf{let}$. As notation it needs no typing rule of its own.';
CAP['syn-prims'] = 'The channel operations are constants. $\\mathsf{send}$ takes a pair $\\langle v, o\\rangle$, $\\mathsf{link}$ a pair of ends and $\\mathsf{spawn}$ a thunk.';
WHY['syn-prims'] = 'As constants applied to values, the channel operations need no syntax of their own, and each has an ordinary function type.';
CAP['syn-values'] = 'Unit, ends, constants, abstractions and boxes are values, and so are pairs and injections of values.';
WHY['syn-values'] = 'A thread that is a value has finished. The value relation $V$ is defined on values.';
CAP['syn-ends'] = 'An end $o$ belongs to the channel $\\mathsf{ech}\\,o$, and $\\overline{o}$ is the other end of that channel.';
WHY['syn-ends'] = 'Two threads hold the two ends of a channel. Naming ends instead of channels gives each end its own type, point and counter.';
CAP['syn-fends'] = '$\\mathsf{fends}(e)$ is the set of ends in $e$, and $\\mathsf{fchans}(e)$ the set of their channels.';
WHY['syn-fends'] = 'The relation reads ownership off terms. A closure or a payload owns exactly the ends in it, and the relation checks this when a value is spawned or sent.';
CAP['syn-procs'] = 'A process is a finite set $C$ of restricted channels and a finite multiset $E$ of threads. A configuration names its threads by $i \\in \\mathrm{dom}\\,M$.';
WHY['syn-procs'] = 'A running program is a set of threads together with its private channels. A channel is restricted when both of its ends are inside the process.';
CAP['syn-points'] = 'A point $x$ has a root, a constant $a$ or a variable $\\iota$. $\\overline{x}$ flips its polarity, $x^{+}$ raises its offset, and $x\\cdot\\kappa$ is one of its fields.';
WHY['syn-points'] = 'Points order the waits of threads. Each end has a point, and a thread may wait at a point only below the points of the ends it still holds.';
CAP['syn-moves'] = 'An action moves an end from $x$ to $x^{+}$, and a choice moves it to a field of $x$. The $j$-th payload end of a message at $x$ arrives at $x\\cdot j$.';
WHY['syn-moves'] = 'The point of an end changes as its protocol advances. One point per end therefore describes a whole protocol, and no action needs a point of its own.';
CAP['syn-labels'] = 'Field labels $\\kappa$ are natural numbers, and $x\\cdot\\kappa$ is the field $\\kappa$ of the point $x$.';
WHY['syn-labels'] = 'Fields give payload ends and the continuations of a choice points of their own, each related to the point of the carrier.';
CAP['syn-csub'] = 'A link of $o_1$ and $o_2$ renames $\\overline{o_1}$ to $o_2$ in the other threads, so that the two remaining ends form one channel.';
WHY['syn-csub'] = 'After a link, the threads holding $\\overline{o_1}$ and $\\overline{o_2}$ communicate with each other directly.';

// ---- semantics ----
INTRO.semantics = 'A thread steps with a label, and a process steps by one or two thread steps. The section ends with the three properties the theorems establish, deadlock freedom, absence of internal divergence and lock freedom.';
CAP['sem-labels'] = 'The label $\\beta$ stands for application, unit and pair elimination, case and force. A session label $\\sigma$ is an action offered on an end.';
WHY['sem-labels'] = 'An internal step needs no other thread. A session label must be matched by the dual label of another thread.';
CAP['sem-head'] = 'One head step per redex. $\\mathsf{recv}\\,o$ has a step for each value $v$ it may receive.';
WHY['sem-head'] = 'Because a receive steps for each possible value, the step of a thread is defined without the other thread of the channel.';
CAP['sem-ctx'] = 'Steps lift through one evaluation frame $f$ at a time, never under $\\lambda$ or $!$.';
WHY['sem-ctx'] = 'Evaluation is call by value from left to right. A $\\lambda$ or a box delays its body until it is applied or forced.';
CAP['sem-proc'] = 'Each rule combines the steps of one or two threads into a step of the configuration $(C, M)$.';
WHY['sem-proc'] = 'A message pairs a send and a receive on the two ends of one channel. Internal steps involve one thread.';
CAP['sem-events'] = 'An event records the threads $\\mathsf{parts}(ev)$ that took part in a step, and the channel or ends of the step.';
WHY['sem-events'] = 'Lock freedom is stated in terms of the threads that take part in steps, which the event of each step records.';
CAP['sem-props'] = 'A process is deadlock free when each reachable process has terminated or can step. \\annp{It has no internal divergence when no reachable process runs internal steps forever. It is lock free when, on each weakly fair maximal run, a waiting thread later takes part in a step.}';
WHY['sem-props'] = 'The theorems establish these properties for typed processes.';

EX['syn-moves'] = 'An end at $x$ that sends twice is at $x^{++}$ afterwards.';

// ---- types and worlds ----
INTRO.types = 'Types give each end a session type and a point. Worlds order the points, and typing and the relation read the order of one world. \\annp{Lock-free types add credits to ends and closures, and costs and ticket needs to arrows and judgments.}';
CAP['ty-grammar'] = '$S@x$ is an end with session type $S$ at the point $x$. An arrow has an upper point $u$ and a lower bound $l$, and a box quantifies over points and session types under a constraint $C$. \\annp{Credits $a$ appear on ends and on closures, the two kinds of value that hold ends themselves. The credit of an end is a lower bound on its counter. The credit of a closure is a lower bound on its captured counters above the floor $h$.}';
WHY['ty-grammar'] = 'A type says what a value is and, for an end, at which point it waits. \\annp{A credit bounds how long the holder of an end may postpone it.}';
CAP['ty-session'] = 'Session types with sequencing $S.S$ and recursion, read through $\\mathsf{unfold}(S)$. A payload binds point variables $\\bar\\iota$, which stand for the fields of the carrier.';
WHY['ty-session'] = 'A session type describes the protocol of one end. The typing rules read its first action after unfolding recursion and leading $\\mathsf{Skip}$.';
CAP['ty-dual'] = '$\\mathsf{dual}$ swaps sending and receiving and keeps payloads, $\\mathsf{Skip}$ and $\\mathsf{Close}$. We write $\\overline{S}$ for $\\mathsf{dual}\\,S$.';
WHY['ty-dual'] = 'The two ends of a channel follow dual protocols. Creation, linking and composition check duality.';
CAP['ty-equiv'] = '$S \\simeq S\'$ when the two session types describe the same protocol. $\\approx$ is $\\simeq$ after erasing annotations, and $\\mathsf{sdual}$ is duality up to annotations.';
WHY['ty-equiv'] = 'With recursion and $\\mathsf{Skip}$ one protocol has many spellings, and the rules compare session types up to $\\simeq$.';
CAP['ty-heads'] = '$\\mathsf{heads}(T)$ is the set of partner points of the ends in a value of $T$. A thread holding such a value may wait only below these points. Hidden ends contribute $\\bot$, which no fact orders against a point, so a check against a value with hidden ends fails.';
WHY['ty-heads'] = 'A thread that waits while it holds a value must wait below the partner points of the ends in that value, and $\\mathsf{heads}$ computes these points from the type.';
CAP['ty-payload'] = 'A payload $!(\\bar\\iota.\\,T)$ mentions only its own point variables $\\iota_0, \\ldots, \\iota_{m-1}$. A message at the carrier point $x$ places them at the fields $x\\cdot 0, \\ldots, x\\cdot(m{-}1)$.';
WHY['ty-payload'] = 'A payload is described relative to the end that sends it, so one session type serves each point the end may have.';
CAP['ty-ann'] = 'Credits $a$, costs $c$, floors $h$ and the refill $N$ are numbers or $\\infty$. A term that must keep $r$ link tickets needs $\\vartheta(r)$ tickets when it starts, and $tk$ tickets suffice when $\\vartheta(r) \\leq tk$. A link adds one to the need, a spawn doubles the rest, and sequencing composes needs. With every annotation at $\\infty$, written $\\mathsf{ty\\_df}$, lock-free typing is deadlock-free typing.';
WHY['ty-ann'] = 'These are the numbers lock-free typing adds to types and judgments. At $\\infty$ each premise about them holds.';
CAP['ty-kinds'] = '$\\mathsf{prim}\\,T$ holds for the result types of processes. $\\mathsf{unlimited}\\,T$ holds for the types that may be copied and dropped, and $\\mathsf{tfree}\\,T$ for the types whose values hold no end.';
WHY['ty-kinds'] = 'Process results are first order, only unlimited types may be copied or dropped, and values without ends do not age.';
CAP['w-world'] = 'A world $W$ has a set of roots $A$ and facts $\\prec_A$ between points with roots in $A$.';
WHY['w-world'] = 'Typing and the relation read the order of one world. Each creation adds roots and facts.';
CAP['w-order'] = '$\\prec_W$ is the transitive closure $\\mathsf{tc}$ of the facts together with $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$.';
WHY['w-order'] = 'Besides the stated facts, the order says that an end moves up as its protocol advances.';
CAP['w-wf'] = 'Each result asks for a strict world. \\annp{Lock freedom also asks for a well-founded one.}';
WHY['w-wf'] = 'In a cyclic order two threads waiting on each other would both count as ready, so the results ask for strict worlds. \\annp{Lock-free adequacy proceeds by induction along the order, which needs well-foundedness.}';
CAP['w-ext'] = 'Extension $\\sqsubseteq$, growth $W \\oplus C$ by the facts of a creation, and the join $\\sqcup$. A join is strict when both worlds are and their restrictions to the shared roots $S = A_1 \\cap A_2$ join strictly.';
WHY['w-ext'] = 'Worlds grow during a run, and the relation holds in each larger world. Composition joins two worlds and checks only their shared roots.';

// ---- typing ----
INTRO.typing = 'The typing judgment assigns each term a type under a context of facts, ends and variables, and a future, the points at which the context acts after the term. Its rules check the order facts a thread needs when it waits. Process typing builds processes from typed threads. \\annp{Lock-free typing adds credits, costs and ticket needs at a finite refill $N$, and the guard.}';
CAP['t-lf-intro'] = 'A deadlock-free program can keep one thread waiting forever while other threads step. Each row names one device that rules out one way of doing so. The note of each row gives the intuition and the example it rejects.';
WHY['t-lf-intro'] = 'Lock freedom requires that a waiting thread eventually takes part in a step. The rows list what typing adds to deadlock-free typing to establish this.';
CAP['t-judgment'] = '$\\Gamma$ holds facts, $\\Delta$ the ends and variables, and $F$ is the future. $\\parallel H$ names what the thread holds while $e$ runs. \\annp{The world $W$ and the refill $N$ are fixed for a derivation, and $\\varepsilon$ is the effect of $e$.}';
WHY['t-judgment'] = 'Several rules run one subterm while the thread holds the values of others. $\\parallel H$ states once what these rules need, the future of the running subterm \\annp{and the aging of the held values}.';
EX['t-judgment'] = 'E-App runs $e_1$ while holding $\\Delta_2$, written $\\Gamma ; \\Delta_1 \\parallel \\Delta_2 \\vdash^{F} e_1 : \\ldots$';
CAP['t-contexts'] = 'The rules read order facts only through $\\Gamma \\vdash x \\prec y$. It is the least transitive relation containing $\\prec_W$, the facts $C[\\bar x]$ of the instances in $\\Gamma$, and $u \\prec \\varphi$ for the future variables $\\varphi \\mapsto u$ in $\\Gamma$.';
WHY['t-contexts'] = 'The rules split $\\Delta$ between subterms and extend $\\Gamma$ under boxes and existentials. The block defines the two contexts and the order judgment $\\Gamma \\vdash x \\prec y$.';
CAP['t-side'] = '$u \\prec F$ says that $u$ lies below the points of $F$. $x \\prec T$ says that $x$ lies below the partner points of the ends in $T$. $l \\preccurlyeq \\Delta$ says that $l$ lies at or below the partner points of $\\Delta$, and $\\Gamma \\vdash C[\\bar x]$ that the facts of $C$ at $\\bar x$ are derivable.';
WHY['t-side'] = 'These are the order checks of typing. A term never waits above a point at which its context acts later, and a thread waits only below the partner points of the values it holds.';
CAP['t-agecap'] = '$T - c$ lowers the credits of the ends and closures in $T$ by $c$. It requires $c \\leq a$ for ends that are not idle and for closures, and leaves $\\mathsf{tfree}$ types unchanged. A captured end needs credit $h + a$, and the body of the closure sees it at credit $h$.';
WHY['t-agecap'] = 'An action of the thread postpones the ends the thread holds by one step. Aging records this on the types of held values, and capture records it for the ends a closure takes along.';
CAP['r-base'] = '$\\ast$ uses no entry of $\\Delta$, and a variable or an end is typed by its own entry. The remaining entries must be unlimited.';
WHY['r-base'] = 'Unused unlimited entries are dropped at the leaves of a derivation, so the rules need no weakening rule.';
CAP['r-fun'] = 'E-Abs types the body under a fresh future variable $\\varphi$ above the upper point $u$, and requires $l$ at or below the partner points of the captured entries. E-App holds $\\Delta_2$ while $e_1$ runs and the closure while $e_2$ runs, and the call requires $u \\prec F$. \\annp{The closure records the effect of its body. Holding it while $e_2$ runs ages it by the cost of $e_2$.}';
WHY['r-fun'] = 'A closure delays its body until a call. Its type records the bounds the body needs, and the call site checks them against its own future.';
CAP['r-data'] = 'E-Pair holds the value of $e_1$ while $e_2$ runs. \\annp{The held value ages by the cost of $e_2$.} The derived $\\mathsf{let}$ is typed by E-Pair, E-LetP and E-LetU. Both branches of a case are typed under one context at one result type.';
WHY['r-data'] = 'A pair is the simplest place where a thread holds a value while other code runs, and E-Pair checks the order this requires.';
CAP['r-boxes'] = 'E-Box types the body once, with fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$ and a fresh future variable above $u$, for each allowed session instance $\\bar s$. The context is unlimited, because a box may be copied. E-Force picks points $\\bar x$ and session types $\\bar s$, requires $C[\\bar x]$ and $u[\\bar x] \\prec F$, and gives the instantiated result type.';
WHY['r-boxes'] = 'Boxes provide recursion and polymorphism over points and session types. Each force chooses an instance.';
CAP['r-ex'] = 'E-Pack chooses witness points $\\bar x$ with $\\Gamma \\vdash C[\\bar x]$. E-Open names the witnesses by fresh point variables $\\bar\\iota$ with the hypothesis $C(\\bar\\iota)$.';
WHY['r-ex'] = 'An existential hides the points of a created channel behind the facts it states about these points.';
CAP['t-consts'] = 'Each constant has the type of its eta-expansion $\\lambda y.\\,k\\,y$, for each instance of its variables that meets the side conditions. An action on an end at $x$ has upper point $x$. $\\mathsf{new}$ is a term and is typed by E-New. \\annp{The types are shown without credits, cost and ticket need.}';
WHY['t-consts'] = 'Constants are values and therefore need types. The upper point $x$ means that a caller may apply an action at $x$ only while its future lies above $x$.';
CAP['r-act'] = 'An action on an end at $x$ waits at $x$ while the thread holds the rest of $\\Delta$. The rules therefore require $x$ below the future and below the partner points of the held values. Send and receive move the end to $x^{+}$ and the payload to the fields of $x$, a choice moves the end to the field of the branch, and a link requires no order fact. \\annp{An action costs one and returns the end with credit $N$, and a link uses one ticket.}';
WHY['r-act'] = 'A thread waits only at actions, so the order facts of the type system are required here.';
CAP['r-threads'] = 'E-SpawnLam types the child body under the empty future, and E-Spawn spawns a closure value with the ends it captured. \\annp{The handed entries age by one step.}';
WHY['r-threads'] = 'A spawned thread has no code after it, so the child body is typed at the empty future.';
CAP['r-new'] = 'The two ends of a new channel are at a fresh root $\\rho$ and its dual, or at a field $x\\cdot\\kappa$ and its dual. The facts $C$ keep the order strict, and the lower bound is $\\bot$.';
WHY['r-new'] = 'Creation places a new channel in the order. Later rules may use the facts $C$ about the new points.';
CAP['t-subs'] = 'Subtyping is $\\approx$ on session types, and an existential may drop facts. \\annp{Credits may decrease, and costs, ticket needs and floors may increase.} Weakening and contraction are admissible, because they are renamings of variables.';
WHY['t-subs'] = 'A value may forget facts it does not need. Admissible weakening and contraction keep the rule set free of structural rules.';
CAP['p-typing'] = 'P-Term types one thread $t$ that holds both ends of each channel in $C_0$, at dual types and points, over an interface $\\Sigma$ without partner pairs. P-Connect cuts two components at $\\Sigma_C$ against $\\overline{\\Sigma_C}$ and compares only the shared roots of the two worlds. \\annp{Lock-free process typing is process typing at a finite refill $N$ with each thread guarded.}';
WHY['p-typing'] = 'Processes are built from single threads by P-Term and composed by P-Connect.';
CAP['g-guard'] = '$\\mathsf{acts}\\,e$ holds when each evaluation of $e$ to a value performs a session action. The guard marks the variable of a box as unusable until the body has acted. A process is guarded when each of its threads is.';
WHY['g-guard'] = 'A thread that recurses without a session action makes internal steps forever. The guard rejects such recursion.';

// ---- semantic typing ----
INTRO.semantic = 'The logical relation defines when a value, a term and a process are safe, by induction on a step index. Typed programs are safe by the fundamental theorems, and safe closed processes are deadlock free by adequacy. \\annp{For lock freedom we read the same relation with other step costs, add fuel to each thread, and combine the two in the soup.}';
CAP['sr-reading'] = 'The relations are indexed by a world $W$, whose order they read, and a level $n$, the number of steps for which they guarantee safety. A term is safe when it is a safe value, or when it is ready and each of its steps leads to a safe term one level lower. Readiness says that a stuck term waits below the partner points of the ends it holds. Processes are safe in the same way and remain safe when their ends are fused, so composing two safe processes needs no further proof. \\annp{Fuel is a second predicate on each thread, and the soup requires both of every thread.}';
WHY['sr-reading'] = 'Each row says in words what one judgment of this section means.';
CAP['ct-costs'] = 'The number of levels each kind of step consumes in the deadlock-free relation. \\annp{A cost table $\\kappa$ assigns these numbers subject to three conditions. The lock-free relation uses $\\kappa_L$, in which internal steps are free.}';
WHY['ct-costs'] = 'The costs fix how far the level drops at a step. \\annp{A step of cost $0$ is read at the same level, so a thread cannot take infinitely many of them.}';
CAP['v-rel'] = 'Each rule is one clause of $V$, by recursion on the type within a level, and $\\Theta$ maps exactly the ends the value owns. A closure is safe when its body is safe in each larger world, at each lower level, for each argument and each future of the caller above $u$. A thunk, the closure that $\\mathsf{spawn}$ runs, is read at the empty future. A box owns no end, and it is safe when $\\mathsf{thunk}(e) = \\lambda\\_.\\,e[!e]$ is safe at each instance. An existential value is a value of the body at witness points whose facts hold.';
WHY['v-rel'] = 'The clauses for closures, thunks and boxes quantify over larger worlds and lower levels. This quantification makes the relation compositional.';
CAP['e-rel'] = 'A term in $E$ is a value in $V$ when it is irreducible and ready when it is reducible, and each of its steps meets its obligation. The successor is read one level lower, or at the same level after a free step.';
WHY['e-rel'] = 'The term relation is the center of the logical relation. Values, obligations and readiness are its three clauses.';
CAP['e-obl'] = 'Each step $e \\xrightarrow{\\alpha} e\'$ of a term holding $\\Theta$ must meet $\\mathsf{Obl}_\\alpha(e\')$. A $\\beta$ step keeps the ends. A spawn gives the child exactly the ends of its thunk, and a creation adds two dual ends at a fresh root or at a field. A send gives away exactly the ends of its payload, and a receive is safe for each value that may arrive. A close removes the end, a choice moves it to the field of the branch, and a link removes two dual ends.';
WHY['e-obl'] = 'The obligations say how each step changes ownership and points. The relation reads step labels only here.';
CAP['rd'] = 'Readiness constrains a stuck term, one that can only offer actions. A stuck term has finished when it offers nothing, and each end it offers lies below the partner points of the ends it keeps and below its future. A stuck process is at a link, or has finished when it offers nothing, and each interface end it keeps has an offered end below its partner point. Internal channels have no points.';
WHY['rd'] = 'In a strict order some stuck thread waits at a minimal point, and the holder of the partner end can act with that thread. Adequacy uses this argument to derive deadlock freedom from readiness.';
CAP['p-rel'] = 'A process satisfies the three clauses of a term, stop, ready and step, in each strict larger world and after each admissible fusion of its held ends. An admissible fusion $(h, D)$ renames held ends injectively, except for the new pairs it restricts in $D$.';
WHY['p-rel'] = 'Composition fuses ends of two processes. Building fusion into the relation lets the semantic P-Connect hold without further proof.';
CAP['p-obls'] = 'Internal steps, including messages between two threads of $p$, keep the interface. A message with the outside moves ends across the interface. A send gives away its payload ends, including the ends $\\Theta_e$ of internal channels, and a receive must be safe for each value that may arrive at each lower level.';
WHY['p-obls'] = 'Each case says how the interface changes at a step and where the successor must be safe.';
CAP['fu-vs'] = 'Fuel is a second predicate on a thread, separate from the relation and with the same shape, a value clause and one obligation per step. The relation gives each end a point, $S@x$, and fuel gives it a counter, $S^f$, and also counts link tickets $tk$. The soup requires both of each thread. The relation makes a stuck thread ready, and fuel bounds how often the holder of a partner end acts on other ends first.';
WHY['fu-vs'] = 'This table compares what the relation and fuel read and guarantee, and shows that the soup is where they meet.';
CAP['fu'] = '$e \\in F^N_n\\llbracket \\Phi ; tk \\vdash \\sigma\\ !\\ (d, r)\\rrbracket$ says that the thread $e$, holding the ends $\\Phi$ and $tk$ link tickets, has fuel for $n$ more steps. It returns at $\\sigma$ within $d$ actions and keeps $r$ tickets. An action on $o$ requires $o$ held and not idle and a spare unit on the other ends and on the frame. Afterwards $o$ has counter $N$ again and the other counters drop by one. $\\mathsf{fsem}$ is fuel at each level with each end at $N$. Fuel reads no point and no world.';
WHY['fu'] = 'Fuel bounds how long a thread may postpone an end it holds. Lock-free adequacy measures waits with these counters and tickets.';
CAP['fu-obls'] = 'Internal steps tick no counter. A new channel starts both ends at $N$, a spawn gives the child the ends of the thunk one lower and half the tickets, and a link removes two dual ends and uses one ticket. An action uses one unit of the frame, advances the protocol of $o$, sets its counter to $N$ and ticks the other ends. A send gives away its payload ends one lower, and a receive continues for each fueled value that may arrive.';
WHY['fu-obls'] = 'Each kind of step changes the held ends, counters and tickets in one way, the same at each level.';
CAP['fv'] = 'Fueled values by recursion on the type. The counter of an end is at least its credit. A closure keeps its captured counters at least at the floor $h$ plus its credit, and its body has fuel at each call. A box holds no end, and its body has fuel at each force.';
WHY['fv'] = 'Fueled values connect credits in types with counters at run time.';
CAP['soup'] = 'A soup state $a = (q, K, tk)$ is a configuration with an ownership map $K$, which gives each held end its holder, point and counter, and a ticket count per thread. The state is in the soup at level $n$ when each thread is in $E[\\kappa_L]$ at the ends it owns and has fuel at their counters. $\\mathsf{consistent}$ keeps $K$, the environment $A$ and the protocols $\\Pi$ in agreement. Fuel is used only here.';
WHY['soup'] = 'The soup combines the relation and the fuel of each thread over one ownership map, fixed for all levels. Lock-free adequacy reads the counters and points it records.';
CAP['sj-all'] = 'The semantic judgments quantify over levels, larger worlds and substitutions, and read the static future at each of its denotations. \\annp{The lock-free judgment fixes the refill and the soup state once, for all levels.}';
WHY['sj-all'] = 'The fundamental theorems conclude the semantic judgments, and adequacy takes a semantic judgment as its premise.';

// ---- theorems ----
INTRO.theorems = 'Typed closed processes are deadlock free, and the proof goes through the logical relation. The section opens with the chain of results and then states each of them for processes. The lemmas about terms come last. \\annp{The lock-free results sit next to their deadlock-free counterparts.}';
CAP['th-chain'] = 'Typing implies the semantic judgment, and the semantic judgment implies deadlock freedom. Both steps use the relation $(V, E, P)$ at the step costs $\\kappa_{DF}$. \\annp{Lock freedom uses the same relation at $\\kappa_L$, which excludes internal divergence, together with fuel. The soup combines both for each thread. Lock-free adequacy measures a wait on $o$ by $\\mu(t) = (\\sum_s tk_s, \\varphi(\\overline{o}))$. A step of the holder of $\\overline{o}$ on another end decreases $\\varphi(\\overline{o})$, which F-Tick keeps at $1$ or more. A link uses one ticket. So the holder acts on $\\overline{o}$ after finitely many steps.}';
WHY['th-chain'] = 'Each arrow is one theorem of this section. \\annp{The lock-free rows show what lock freedom adds to the deadlock-free proof.}';
CAP['th-sound'] = 'A closed typed process is deadlock free in a strict world. \\annp{A closed process typed at a finite refill, with each thread guarded, is lock free in a strict and well-founded world.}';
WHY['th-sound'] = 'These are the main results.';
CAP['th-compose'] = 'A safe thread is a safe process, and two safe processes connected at dual interfaces form a safe process. A component proved safe without typing therefore composes with typed components. \\annp{The same holds for the soup.}';
WHY['th-compose'] = 'P-Term and P-Connect hold in the relation, which makes the approach compositional.';
CAP['th-fund-proc'] = 'A typed process is in the semantic judgment. The proof is by induction over P-Term and P-Connect and uses the composition rules.';
WHY['th-fund-proc'] = 'The fundamental theorem connects typing with the relation.';
CAP['th-adeq'] = 'In a strict world, a closed process in the semantic judgment is deadlock free. \\annp{In a strict and well-founded world, a closed process in the lock-free judgment is lock free, and each thread progresses on each weakly fair maximal run.}';
WHY['th-adeq'] = 'Adequacy connects the relation with the safety property.';
CAP['th-conserv'] = 'The annotated judgment at $N = \\infty$ types the same terms as deadlock-free typing, and erasing the annotations of a lock-free typing gives a deadlock-free typing.';
WHY['th-conserv'] = 'Lock-free typing therefore rejects no deadlock-free program.';
CAP['th-terms'] = 'A closed program is sound as a one-thread process. Typing a term implies the semantic term judgment, and $E$ is closed under evaluation frames. \\annp{With the guard a typed term is in the relation at $\\kappa_L$, and a typed term at a finite refill has fuel.}';
WHY['th-terms'] = 'The proofs of the process results use these lemmas, each proved rule by rule.';

// ---- apply ----
function apply() {
  for (const s of sections) {
    if (INTRO[s.id] !== undefined) s.intro = INTRO[s.id];
    for (const b of s.blocks) {
      if (CAP[b.id] !== undefined) b.caption = CAP[b.id];
      if (WHY[b.id] !== undefined) b.about = { ...(b.about || {}), why: WHY[b.id] };
      if (EX[b.id] !== undefined) b.about = { ...(b.about || {}), example: EX[b.id] };
    }
  }
}
module.exports = { apply };
