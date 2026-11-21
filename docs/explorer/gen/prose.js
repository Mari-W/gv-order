// The text a reader sees first: section intros, block captions and the notes behind block titles.
// It overrides what the section files set, so the reader-facing prose is written in one place.
// Writing rules: docs/explorer/BLOCKS.md and the pl-paper-writing skill of sill-obs.
const { sections, examples } = require('./core');

const INTRO = {}, CAP = {}, WHY = {}, EX = {}, SHOWS = {}, LEAD = {};

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
INTRO.types = 'Types give each end a session type and a point. Worlds order the points, and typing and the relation read the order of one world. \\annp{Lock-free types add credits to ends and closures, tickets to ends, and costs to arrows and judgments.}';
CAP['ty-grammar'] = '$S@x$ is an end with session type $S$ at the point $x$. An arrow has an upper point $u$ and a lower bound $l$, and a box quantifies over points and session types under a constraint $C$. \\annp{Credits $a$ appear on ends and on closures, the two kinds of value that hold ends themselves. An end has its credit as lower bound on its counter and its tickets $m$ as upper bound. The credit of a closure is a lower bound on its captured counters above the floor $h$.}';
WHY['ty-grammar'] = 'A type says what a value is and, for an end, at which point it waits. \\annp{A credit bounds how long the thread holding an end may postpone it.}';
CAP['ty-session'] = 'Session types with sequencing $S.S$ and recursion, read through $\\mathsf{unfold}(S)$. A payload binds point variables $\\bar\\iota$, which stand for the fields of the carrier.';
WHY['ty-session'] = 'A session type describes the protocol of one end. The typing rules read its first action after unfolding recursion and leading $\\mathsf{Skip}$.';
CAP['ty-dual'] = '$\\mathsf{dual}$ swaps sending and receiving and keeps payloads, $\\mathsf{Skip}$ and $\\mathsf{Close}$. We write $\\overline{S}$ for $\\mathsf{dual}\\,S$.';
WHY['ty-dual'] = 'The two ends of a channel follow dual protocols. Creation, linking and composition check duality.';
CAP['ty-equiv'] = '$S \\simeq S\'$ when the two session types describe the same protocol. $\\approx$ is $\\simeq$ after erasing annotations, and $\\mathsf{sdual}$ is duality up to annotations.';
WHY['ty-equiv'] = 'With recursion and $\\mathsf{Skip}$ one protocol has many spellings, and the rules compare session types up to $\\simeq$.';
CAP['ty-heads'] = '$\\mathsf{ap}(T)$ is the set of dual points of the ends in a value of $T$. A thread holding such a value may wait only below these points. Hidden ends contribute $\\bot$, which no fact orders against a point, so a check against a value with hidden ends fails.';
WHY['ty-heads'] = 'A thread that waits while it holds a value must wait below the dual points of the ends in that value, and $\\mathsf{ap}$ computes these points from the type.';
CAP['ty-payload'] = 'A payload $!(\\bar\\iota.\\,T)$ mentions only its own point variables $\\iota_0, \\ldots, \\iota_{m-1}$. A message at the carrier point $x$ places them at the fields $x\\cdot 0, \\ldots, x\\cdot(m{-}1)$.';
WHY['ty-payload'] = 'A payload is described relative to the end that sends it, so one session type serves each point the end may have.';
CAP['ty-ann'] = 'Credits $a$, costs $c$, floors $h$, tickets $m$ and the bound $N$ are numbers or $\\infty$. An end has $m$ tickets with $a \\leq m$, and the tickets of the two ends of a channel sum to at most $N$, so an end with $m$ tickets has a partner with at most $N - m$. With every annotation at $\\infty$, written $\\mathsf{ty\\_df}$, lock-free typing is deadlock-free typing.';
WHY['ty-ann'] = 'These are the numbers lock-free typing adds to types and judgments. At $\\infty$ each premise about them holds.';
CAP['ty-kinds'] = '$\\mathsf{tfree}\\,T$ holds for the types whose values hold no end, and P-Term asks it of the result type of a process. $\\mathsf{unlimited}\\,T$ holds for the types that may be copied and dropped.';
WHY['ty-kinds'] = 'Process results hold no end, only unlimited types may be copied or dropped, and values without ends do not age.';
CAP['w-world'] = 'A world $W$ has a set of roots $A$ and facts $\\prec_A$ between points with roots in $A$.';
WHY['w-world'] = 'Typing and the relation read the order of one world. Each creation adds roots and facts.';
CAP['w-order'] = '$\\prec_W$ is the transitive closure $\\mathsf{tc}$ of the facts together with $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$.';
WHY['w-order'] = 'Besides the stated facts, the order says that an end moves up as its protocol advances.';
CAP['w-wf'] = 'Each result asks for a strict world. \\annp{Lock freedom also asks for a well-founded one.}';
WHY['w-wf'] = 'In a cyclic order two threads waiting on each other would both count as ready, so the results ask for strict worlds. \\annp{Lock-free adequacy proceeds by induction along the order, which needs well-foundedness.}';
CAP['w-ext'] = 'Extension $\\sqsubseteq$, growth $W \\oplus C$ by the facts of a creation, and the join $\\sqcup$. A join is strict when both worlds are and their restrictions to the shared roots $S = A_1 \\cap A_2$ join strictly.';
WHY['w-ext'] = 'Worlds grow during a run, and the relation holds in each larger world. Composition joins two worlds and checks only their shared roots.';

// ---- typing ----
INTRO.typing = 'The typing judgment assigns each term a type under a context of facts, ends and variables, and a future, the points at which the context acts after the term. Its rules check the order facts a thread needs when it waits. Process typing builds processes from typed threads. \\annp{Lock-free typing adds credits, tickets and costs at a finite bound $N$, and the guard.}';
CAP['t-judgment'] = '$\\Gamma$ holds facts, $\\Delta$ the ends and variables, and $F$ is the future. $F \\triangleleft H$ adds to the future the active points of what the thread holds while $e$ runs. The world $W$ and the bound $N$ stay fixed for a whole derivation, and the rules leave them implicit. In the lock-free mode $\\varepsilon$ is the cost of $e$.';
WHY['t-judgment'] = 'Several rules run one subterm while the thread holds the values of others. Writing the future as $F \\triangleleft H$ states once what these rules need, the future of the running subterm extended by the active points of the held values.';
EX['t-judgment'] = 'E-App runs $e_1$ while holding $\\Delta_2$, written $\\Gamma ; \\Delta_1 \\vdash^{F \\triangleleft \\Delta_2} e_1 : \\ldots$';
CAP['t-contexts'] = 'The rules read order facts only through $\\Gamma \\vdash x \\prec y$. It is the least transitive relation containing $\\prec_W$, the facts $C[\\bar x]$ of the instances in $\\Gamma$, and $u \\prec \\varphi$ for the future variables $\\varphi \\mapsto u$ in $\\Gamma$.';
WHY['t-contexts'] = 'The rules split $\\Delta$ between subterms and extend $\\Gamma$ under boxes and existentials. The block defines the two contexts and the order judgment $\\Gamma \\vdash x \\prec y$.';
CAP['t-side'] = '$u \\prec F$ says that $u$ lies below the points of $F$. $x \\prec T$ says that $x$ lies below the dual points of the ends in $T$. $l \\preccurlyeq \\Delta$ says that $l$ lies at or below the dual points of $\\Delta$, and $\\Gamma \\vdash C[\\bar x]$ that the facts of $C$ at $\\bar x$ are derivable.';
WHY['t-side'] = 'These are the order checks of typing. A term never waits above a point at which its context acts later, and a thread waits only below the dual points of the values it holds.';
CAP['t-agecap'] = '$T - c$ lowers the credits of the ends and closures in $T$ by $c$. It requires $c \\leq a$ for ends that are not idle and for closures, and leaves $\\mathsf{tfree}$ types unchanged. A captured end needs credit $h + a$, and the body of the closure sees it at credit $h$.';
WHY['t-agecap'] = 'An action of the thread postpones the ends the thread holds by one step. Aging records this on the types of held values, and capture records it for the ends a closure takes along.';
CAP['r-base'] = '$\\ast$ uses no entry of $\\Delta$, and a variable or an end is typed by its own entry. The remaining entries must be unlimited.';
WHY['r-base'] = 'Unused unlimited entries are dropped at the leaves of a derivation, so the rules need no weakening rule.';
CAP['r-fun'] = 'E-Abs types the body under a fresh future variable $\\varphi$ above the upper point $u$, and requires $l$ at or below the dual points of the captured entries. E-App holds $\\Delta_2$ while $e_1$ runs and the closure while $e_2$ runs, and the call requires $u \\prec F$. \\annp{The closure records the effect of its body. Holding it while $e_2$ runs ages it by the cost of $e_2$.}';
WHY['r-fun'] = 'A closure delays its body until a call. Its type records the bounds the body needs, and the call site checks them against its own future.';
CAP['r-data'] = 'E-Pair holds the value of $e_1$ while $e_2$ runs. \\annp{The held value ages by the cost of $e_2$.} The derived $\\mathsf{let}$ is typed by E-Pair, E-LetP and E-LetU. Both branches of a case are typed under one context at one result type.';
WHY['r-data'] = 'A pair is the simplest place where a thread holds a value while other code runs, and E-Pair checks the order this requires.';
CAP['r-boxes'] = 'E-Box types the body once, with fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$ and a fresh future variable above $u$, for each allowed session instance $\\bar s$. The context is unlimited, because a box may be copied. E-Force picks points $\\bar x$ and session types $\\bar s$, requires $C[\\bar x]$ and $u[\\bar x] \\prec F$, and gives the instantiated result type.';
WHY['r-boxes'] = 'Boxes provide recursion and polymorphism over points and session types. Each force chooses an instance.';
CAP['r-ex'] = 'E-Pack chooses witness points $\\bar x$ with $\\Gamma \\vdash C[\\bar x]$. E-Open names the witnesses by fresh point variables $\\bar\\iota$ with the hypothesis $C(\\bar\\iota)$.';
WHY['r-ex'] = 'An existential hides the points of a created channel behind the facts it states about these points.';
CAP['t-consts'] = 'Each constant has the type of its eta-expansion $\\lambda y.\\,k\\,y$, for each instance of its variables that meets the side conditions. An action on an end at $x$ has upper point $x$. $\\mathsf{new}$ is a term and is typed by E-New. \\annp{The types are shown without credits, tickets and cost.}';
WHY['t-consts'] = 'Constants are values and therefore need types. The upper point $x$ means that a caller may apply an action at $x$ only while its future lies above $x$.';
CAP['r-act'] = 'An action on an end at $x$ waits at $x$ while the thread holds the rest of $\\Delta$. The rules therefore require $x$ below the future and below the dual points of the held values. Send and receive move the end to $x^{+}$ and the payload to the fields of $x$, a choice moves the end to the field of the branch, and a link requires no order fact. \\annp{An action costs one and returns the end with credit $m$, its tickets. A link asks the credit of each linked end to exceed the partner bound $N - m$ of the other.}';
WHY['r-act'] = 'A thread waits only at actions, so the order facts of the type system are required here.';
CAP['r-threads'] = 'E-SpawnLam types the child body under the empty future, and E-Spawn spawns a closure value with the ends it captured. \\annp{The transferred entries age by one step.}';
WHY['r-threads'] = 'A spawned thread has no code after it, so the child body is typed at the empty future.';
CAP['r-new'] = 'The two ends of a new channel are at a fresh root $\\rho$ and its dual, or at a field $x\\cdot\\kappa$ and its dual. The facts $C$ keep the order strict, and the lower bound is $\\bot$. \\annp{The creation picks tickets $m_1$ and $m_2$ with $m_1 + m_2 \\leq N$, and each end starts at credit equal to its tickets.}';
WHY['r-new'] = 'Creation places a new channel in the order. Later rules may use the facts $C$ about the new points.';
CAP['t-subs'] = 'Subtyping is $\\approx$ on session types, and an existential may drop facts. \\annp{Credits may decrease, and costs and floors may increase.} Weakening and contraction are admissible, because they are renamings of variables.';
WHY['t-subs'] = 'A value may forget facts it does not need. Admissible weakening and contraction keep the rule set free of structural rules.';
CAP['p-typing'] = 'P-Term types one thread $t$ that holds both ends of each channel in $C_0$, at dual types and points, over an interface $\\Sigma$ without partner pairs. P-Connect cuts two components at $\\Sigma_C$ against $\\overline{\\Sigma_C}$ and compares only the shared roots of the two worlds. \\annp{Lock-free process typing is process typing at a finite bound $N$ with each thread guarded. The ends of a restricted channel have tickets of sum at most $N$, and each interface end has $N/2$.}';
WHY['p-typing'] = 'Processes are built from single threads by P-Term and composed by P-Connect.';
CAP['g-guard'] = '$\\mathsf{acts}\\,e$ holds when each evaluation of $e$ to a value performs a session action. The guard marks the variable of a box as unusable until the body has acted. A process is guarded when each of its threads is.';
WHY['g-guard'] = 'A thread that recurses without a session action makes internal steps forever. The guard rejects such recursion.';

// ---- semantic typing ----
INTRO.semantic = 'The logical relation defines when a value, a term and a process are safe, by induction on a step index. Typed programs are safe by the fundamental theorems, and safe closed processes are deadlock free by adequacy. \\annp{For lock freedom we read the same relation with other step costs, add fuel to each thread, and combine the two in the lock-free process relation.}';
CAP['sr-reading'] = 'The relations are indexed by a world $W$, whose order they read, and an ordinal index $\\alpha$. A term is safe when it is a safe value, or when it is ready and each of its steps leads to a safe term at every lower index the cost of the step allows. Readiness says that a stuck term waits below the dual points of the ends it holds. Processes are safe in the same way and remain safe when their ends are fused, so composing two safe processes needs no further proof. \\annp{Fuel is a second predicate on each thread, and the lock-free process relation requires both of every thread.}';
WHY['sr-reading'] = 'Each row says in words what one judgment of this section means.';
CAP['ct-costs'] = 'The number of levels each kind of step consumes in the deadlock-free relation. \\annp{A cost table $\\kappa$ assigns these numbers subject to three conditions. The lock-free relation uses $\\kappa_L$, in which internal steps are free.}';
WHY['ct-costs'] = 'The costs fix how far the level drops at a step. \\annp{A step of cost $0$ is read at the same level, so a thread cannot take infinitely many of them.}';
CAP['v-rel'] = 'Each rule is one clause of $V$, by recursion on the type within a level, and $\\Theta$ maps exactly the ends the value owns. A closure is safe when its body is safe in each larger world, at each lower level, for each argument and each future of the caller above $u$. A thunk, the closure that $\\mathsf{spawn}$ runs, is read at the empty future. A box owns no end, and it is safe when $\\mathsf{thunk}(e) = \\lambda\\_.\\,e[!e]$ is safe at each instance. An existential value is a value of the body at witness points whose facts hold.';
WHY['v-rel'] = 'The clauses for closures, thunks and boxes quantify over larger worlds and lower levels. This quantification makes the relation compositional.';
CAP['e-rel'] = 'A term in $E$ is a value in $V$ when it is irreducible and ready when it is reducible, and each of its steps meets its obligation. After a step of cost $c > 0$ at the ordinal index $\\alpha$ the successor is read at every $\\beta$ with $\\beta + c \\leq \\alpha$, and after a free step at $\\alpha$ itself. At a limit index this is every smaller index.';
WHY['e-rel'] = 'The term relation is the center of the logical relation. Values, obligations and readiness are its three clauses.';
CAP['e-obl'] = 'Each step $e \\xrightarrow{\\alpha} e\'$ of a term holding $\\Theta$ must meet $\\mathsf{Obl}_\\alpha(e\')$. A $\\beta$ step keeps the ends. A spawn gives the child exactly the ends of its thunk, and a creation adds two dual ends at a fresh root or at a field. A send gives away exactly the ends of its payload, and a receive is safe for each value that may arrive. A close removes the end, a choice moves it to the field of the branch, and a link removes two dual ends.';
WHY['e-obl'] = 'The obligations say how each step changes ownership and points. The relation reads step labels only here.';
CAP['rd'] = 'Readiness constrains a stuck term, one that can only offer actions. A stuck term has finished when it offers nothing, and each end it offers lies below the dual points of the ends it keeps and below its future. A stuck process is at a link, or has finished when it offers nothing, and each interface end it keeps has an offered end below its dual point. Internal channels have no points.';
WHY['rd'] = 'In a strict order some stuck thread waits at a minimal point, and the thread holding the dual end can act with that thread. Adequacy uses this argument to derive deadlock freedom from readiness.';
CAP['p-rel'] = 'A process satisfies the three clauses of a term, stop, ready and step, in each strict larger world and after each admissible fusion of its held ends. An admissible fusion $(h, D)$ renames held ends injectively, except for the new pairs it restricts in $D$.';
WHY['p-rel'] = 'Composition fuses ends of two processes. Building fusion into the relation lets the semantic P-Connect hold without further proof.';
CAP['p-obls'] = 'Internal steps, including messages between two threads of $p$, keep the interface. A message with the outside moves ends across the interface. A send gives away its payload ends, including the ends $\\Theta_e$ of internal channels, and a receive must be safe for each value that may arrive at each lower level.';
WHY['p-obls'] = 'Each case says how the interface changes at a step and where the successor must be safe.';
CAP['fu-vs'] = 'Fuel is a second predicate on a thread, separate from the relation and with the same shape, a value clause and one obligation per step. The relation gives each end a point, $S@x$, and fuel gives it a counter and tickets, $S^f_m$. The lock-free process relation requires both of each thread. The relation makes a stuck thread ready, and fuel bounds how often the thread holding a dual end acts on other ends first.';
WHY['fu-vs'] = 'This table compares what the relation and fuel read and guarantee, and shows that the lock-free process relation is where they meet.';
CAP['fu'] = 'Fuel has the shape of the term relation $E$ without the ready clause. $e \\in F^N_\\alpha\\llbracket \\Phi \\vdash \\sigma\\ !\\ d\\rrbracket$ says that the thread $e$, which holds the ends $\\Phi$ with their counters and tickets, has fuel at the ordinal index $\\alpha$. When $e$ is a value it is in $FV$ at $\\sigma$. Otherwise each step meets its fuel obligation at every smaller index. The clauses hold for each larger counter bound $N\'$ and each injective renaming $g$ of ends, because a link in another thread renames ends. $\\mathsf{fsem}$ is fuel at each index with each counter at its tickets, and it is the only fuel statement independent of the index.';
WHY['fu'] = 'Fuel bounds how often a thread acts on other ends before it acts on an end it holds. Lock-free adequacy measures waits with these counters.';
CAP['fu-obls'] = 'An action on $o$ requires $o$ held and not idle, and a positive counter on the other ends that are not idle and on the frame. It uses one unit of the frame, advances the protocol of $o$, resets the counter of $o$ to its tickets $m$ and decrements the other counters, written $\\Phi{\\downarrow}[o \\mapsto S^{m}_{m}]$. Internal steps decrement no counter. A new channel starts each end at its tickets, which sum to at most $N$. A spawn transfers the ends of the thunk to the child with counters one lower. A link removes two dual ends, and the counter of each exceeds the partner bound $N - m$ of the other. A send transfers its payload ends with counters one lower, and a receive continues for each value in $FV$ that may arrive.';
WHY['fu-obls'] = 'Each kind of step changes the held ends and counters in one way, the same at each index.';
CAP['fv'] = 'Values with fuel by recursion on the type. The counter of an end is at least its credit, and its tickets are those of its type. A closure keeps its captured counters at least at the floor $h$ plus its credit, and its body has fuel at each call. A box holds no end, and its body has fuel at each force.';
WHY['fv'] = 'Values with fuel connect credits in types with counters at run time.';
CAP['soup'] = 'An annotated configuration $a = (q, K)$ is a configuration $q$ with an ownership map $K$. $K$ gives each held end the thread that holds it, its point, its counter and its tickets. The configuration is in the lock-free process relation at the ordinal index $\\alpha$ when each thread is in $E[\\kappa_L]$ at the ends it owns and has fuel at their counters. $A$ and $\\Phi$ describe the held ends for the relation and for fuel, and $\\mathsf{consistent}$ requires $A$, $\\Phi$ and $K$ to agree. It also bounds each counter by its tickets and the tickets of the two ends of an internal channel by $N$. Fuel occurs only in this definition.';
WHY['soup'] = 'The lock-free process relation combines the relation and the fuel of each thread over one ownership map. Lock-free adequacy reads the points and counters that $K$ records, and the invariant on tickets makes the measure fall at a link.';
CAP['sj-all'] = 'The semantic judgments quantify over ordinal indices, larger worlds and substitutions, and read the static future at each of its denotations. \\annp{The lock-free judgment fixes the bound $N$ once and chooses the annotated configuration at each index. The creation choice of each channel is an existential inside O-New.}';
WHY['sj-all'] = 'The fundamental theorems conclude the semantic judgments, and adequacy takes a semantic judgment as its premise.';

// ---- theorems ----
INTRO.theorems = 'Typed closed processes are deadlock free, and the proof goes through the logical relation. The section opens with the chain of results and then states each of them for processes. The lemmas about terms come last. \\annp{The lock-free results sit next to their deadlock-free counterparts.}';
CAP['th-chain'] = 'Typing implies the semantic judgment, and the semantic judgment implies deadlock freedom. Both steps use the relation $(V, E, P)$ at the step costs $\\kappa_{DF}$. \\annp{Lock freedom uses the same relation at $\\kappa_L$, which excludes internal divergence, together with fuel. The lock-free process relation combines both for each thread. Lock-free adequacy measures a wait on $o$ by $\\mu(t) = f$, the counter of the dual end $\\overline{o}$. A step of the thread holding $\\overline{o}$ on another end decreases $f$, which F-Count keeps at $1$ or more. A link gives the waiting thread a partner with a lower counter, by the premise of E-Link and the invariant on tickets. Lock-free adequacy takes excluded middle and choice as hypotheses. The thread holding $\\overline{o}$ therefore acts on $\\overline{o}$ after finitely many steps.}';
WHY['th-chain'] = 'Each arrow is one theorem of this section. \\annp{The lock-free rows show what lock freedom adds to the deadlock-free proof.}';
CAP['th-sound'] = 'A closed typed process is deadlock free in a strict world. \\annp{Under excluded middle and choice, a closed process typed at a finite bound $N$, with each thread guarded, is lock free in a strict and well-founded world.}';
WHY['th-sound'] = 'These are the main results.';
CAP['th-compose'] = 'A safe thread is a safe process, and two safe processes connected at dual interfaces form a safe process. A component proved safe without typing therefore composes with typed components. \\annp{The same holds for the lock-free process relation.}';
WHY['th-compose'] = 'P-Term and P-Connect hold in the relation, which makes the approach compositional.';
CAP['th-fund-proc'] = 'A typed process is in the semantic judgment. The proof is by induction over P-Term and P-Connect and uses the composition rules.';
WHY['th-fund-proc'] = 'The fundamental theorem connects typing with the relation.';
CAP['th-adeq'] = 'In a strict world, a closed process in the semantic judgment is deadlock free. \\annp{Under excluded middle and choice, in a strict and well-founded world, a closed process in the lock-free judgment is lock free, and each thread progresses on each weakly fair maximal run.}';
WHY['th-adeq'] = 'Adequacy connects the relation with the safety property.';
CAP['th-conserv'] = 'The annotated judgment at $N = \\infty$ types the same terms as deadlock-free typing, and erasing the annotations of a lock-free typing gives a deadlock-free typing.';
WHY['th-conserv'] = 'Lock-free typing therefore rejects no deadlock-free program.';
CAP['th-terms'] = 'A closed program is sound as a one-thread process. Typing a term implies the semantic term judgment, and $E$ is closed under evaluation frames. \\annp{With the guard a typed term is in the relation at $\\kappa_L$, and a typed term at a finite bound $N$ has fuel.}';
WHY['th-terms'] = 'The proofs of the process results use these lemmas, each proved rule by rule.';

// ---- examples ----
SHOWS['ex-cs'] = 'A client sends on $a$ and then receives on $b$, and a server receives on $a$ and then sends on $b$, both forever. The second $\\mathsf{new}$ places $b$ at the field $\\rho\\cdot 0$ of the root of $a$ and states the facts $C$ at $(\\rho, \\rho\\cdot 0, \\rho\\cdot 1)$. Each recursive call is at the next points $(\\iota^{+}, \\kappa^{+}, \\zeta)$, where $C$ states the same facts again.';
SHOWS['ex-flag'] = 'The flag is always $\\mathsf{inj}_1\\,\\ast$, so the thread closes $c$ before $d$. E-Case types both arms in one world. The first arm asks $x \\prec \\overline{y}$, the second asks $y \\prec \\overline{x}$, and the partner asks $\\overline{x} \\prec y$. The joint world has the cycle $y \\prec \\overline{x} \\prec y$, and P-Connect asks a strict world. The relation reads only the steps the thread takes. After three $\\beta$ steps the thread is in the first arm, which the fundamental theorem places in $E$ in a world with $x \\prec \\overline{y}$ alone. Semantic P-Connect joins it with the partner, the joint world has no cycle, and adequacy gives deadlock freedom. The rejection holds whatever points $c$ and $d$ get, and the map records it as an argument, with no Rocq proof.';
SHOWS['ex-flagpair'] = 'Both threads get the same flag, so they close $a$ and $b$ in the same order in every run. A received flag is any value of $V$ at $\\ast \\oplus \\ast$, so each thread has to be in $E$ for both flags. With $\\mathsf{inl}$ thread A closes $a$ while it holds $b$ and asks $x \\prec \\overline{y}$. With $\\mathsf{inr}$ thread B closes $\\overline{b}$ while it holds $\\overline{a}$ and asks $\\overline{y} \\prec x$. The join of the two worlds then has a cycle, and P-Connect asks a strict join. One such thread alone fits in a strict world, the pair does not. The flag travels on an internal channel, so the process relation of the closed process reads only its actual reductions, in which both threads take the same branch. Following them puts the process in $P$ directly.';
SHOWS['ex-cycle'] = 'Main closes $c$ and then $d$, and the spawned thread closes $c\'$ and then $d\'$. Each thread waits on one channel while it holds an end of the other. The second $\\mathsf{new}$ states exactly the two facts this requires, $\\rho \\prec \\overline{\\rho\\cdot 0}$ for main and $\\overline{\\rho} \\prec \\rho\\cdot 0$ for the spawned thread.';
SHOWS['ex-between'] = 'The box creates a channel $d$ while it holds two arguments $c$ and $e$, and closes $c$, $d$ and $e$ in this order. E-New places $d$ at the field $\\iota\\cdot 0$ of the point of $c$. The facts of the box constraint then order $d$ between $c$ and $e$, and no point between two box points is needed.';
SHOWS['ex-many'] = 'The new end $d$ sends twice and closes while the box holds $e$. The constraint of the box is infinite, one pair of facts for each offset of $\\delta$, so $d$ may act at $\\delta$, $\\delta^{+}$ and $\\delta^{++}$ below the point $\\kappa$ of $e$.';
SHOWS['ex-factory'] = 'Each box creates a channel, spawns a sender on one end and returns the other end. $\\mathsf{mk}_0$ places the channel at a fresh root and returns it packed in an existential. $\\mathsf{mk}_1$ places it at a field of the end it receives. The two boxes type one creation in the two ways E-New allows.';
SHOWS['ex-ring'] = 'Each round of the ring receives an end $z$ on $x$, spawns two copies of itself, and so the ring grows forever. E-New places $b$ at $\\iota_1\\cdot 1$ while $x$ is held at $\\iota_1$, before the receive on $x$. The ring is lock free, with lock-free typing at $N = 4$.';
SHOWS['ex-close'] = 'Two threads each close one end of $c$. P-Term types each thread over its end, and P-Connect cuts $c$ at dual types in a world without facts. It is the smallest use of the two process rules.';
SHOWS['ex-guard-neg'] = 'Each box uses its own variable before its first session action. The first loops on $\\beta$ steps, the second is $\\mathsf{fix}\\,\\lambda x.\\,x$, the third recurses before it returns, and the fourth spawns forever. The guard rejects all four, so they are outside lock-free typing.';
SHOWS['ex-guard-pos'] = 'In both boxes a $\\mathsf{recv}$ comes before the recursive call. A receive is a session action, so the guard checks the rest of the body under $\\varnothing$, where the variable of the box is usable again.';
SHOWS['ex-forwarder'] = 'The forwarder receives a closure on $o$ and spawns the closure as a new thread. $\\mathsf{dead\\_thunk}\\,q$ mentions the end $q$ without owning it, so it is not a value in $FV$ and cannot arrive on $o$. Each closure the forwarder receives therefore owns its ends, and $\\mathsf{fw}$ has fuel at each counter bound.';
SHOWS['ex-controller'] = 'The client sends on $a$ and receives on $b$ in each round, and holds the end $k$ at $\\mathsf{Skip}@\\chi$ throughout. Aging requires $c \\leq a$ only of ends that are not idle. The idle end $k$ therefore has credit $0$ across rounds of unbounded cost.';
SHOWS['rx-postpone'] = 'Main holds $b$ while it runs a loop that never returns, and the thread with $b\'$ waits forever while other threads step. Aging requires $c \\leq a$ of each held end that is not idle. The loop has cost $\\infty$, and $b$ has a finite credit, so the program has no lock-free typing.';
SHOWS['rx-delegate'] = 'Two threads send the end $e$ back and forth forever, and the thread with $e\'$ waits. Each send passes $e$ on with its counter one lower. After finitely many sends no credit remains to send $e$ again, so the program has no lock-free typing.';
SHOWS['rx-relink'] = 'Each round links the partner of the waiting end to a new channel. The waiting thread then faces a new end with a full counter, and no counter decreases to $0$. E-Link asks the credit of the linked end to exceed the partner bound of the new end. After the send that credit is too low for the recursive call, so the program has no lock-free typing.';
SHOWS['rx-chain'] = 'Each thread spawns a child, waits on it, and the child does the same. Each wait is at a point below the point of the previous one, and the chain grows forever. A well-founded world has no infinite descending chain, and lock-free soundness assumes a well-founded world.';

// one sentence above the code: what the example demonstrates
LEAD['ex-cs'] = 'Two loops that call themselves forever over the same two channels are deadlock free, because one constraint orders the points of all their rounds at once.';
LEAD['ex-flag'] = 'A thread that branches on a flag it computes itself is deadlock free, and only semantic typing shows it, because static typing checks the arm that never runs.';
LEAD['ex-flagpair'] = 'Two threads that branch on one flag sent by a third thread are deadlock free. A proof that follows the reductions of the whole process shows it, and a proof that puts each thread into the relation on its own fails.';
LEAD['ex-cycle'] = 'Two threads that use two channels in the same order type, because creating the second channel states the two order facts the threads need.';
LEAD['ex-between'] = 'A procedure can create a channel whose point lies between the points of two channels it receives as arguments.';
LEAD['ex-many'] = 'A new channel can act several times while an older end is held, because a box constraint may state infinitely many facts.';
LEAD['ex-factory'] = 'One way of creating a channel admits two typings, at a fresh root hidden in an existential or at a field of an end the creator holds.';
LEAD['ex-ring'] = 'A ring of threads that grows forever is lock free.';
LEAD['ex-close'] = 'The smallest process built from two typed threads by the process rules.';
LEAD['ex-guard-neg'] = 'Recursion that can run forever without a session action is outside lock-free typing.';
LEAD['ex-guard-pos'] = 'Recursion that performs a session action before each recursive call passes the guard.';
LEAD['ex-forwarder'] = 'A thread that receives closures and spawns them is lock free, because a received closure owns the ends it mentions.';
LEAD['ex-controller'] = 'An end that no thread ever acts on may be held across a loop of unbounded length.';
LEAD['rx-postpone'] = 'A deadlock-free program in which one thread waits forever, because the thread holding its dual end never acts on that end.';
LEAD['rx-delegate'] = 'A deadlock-free program in which an end is sent back and forth forever while its partner waits.';
LEAD['rx-relink'] = 'A deadlock-free program in which links keep replacing the end a thread waits on.';
LEAD['rx-chain'] = 'A deadlock-free program in which a chain of waiting threads grows forever.';

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
  for (const x of examples) { if (SHOWS[x.id] !== undefined) x.shows = SHOWS[x.id]; if (LEAD[x.id] !== undefined) x.lead = LEAD[x.id]; }
}
module.exports = { apply };
