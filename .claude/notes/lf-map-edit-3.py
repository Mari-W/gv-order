import json
P='docs/explorer/map.json'
m=json.load(open(P)); B={b['id']:b for s in m['sections'] for b in s['blocks']}; N=m['notes']
def sub(s,o,n):
    assert s.count(o)==1,(o[:60],s.count(o)); return s.replace(o,n)
d=B['t-lf-wf']['deviations'][0]
d['reason']=r"The Rocq asks `wok N W` of process typing, which is `swf W` at a finite bound. The induction behind the fundamental theorems reads worlds under `wfit N W`, which is `wstrict W`, or `wranked W` with $N$ finite and excluded middle. The lock-free view shows the ranked case only."
sp=B['soup']
sp['caption']=sub(sp['caption'],r"An annotated configuration $a = (q, K, W_a)$ is in the lock-free process relation at the ordinal index $\alpha$ when each thread is in $E[\kappa_L]$ at the ends it owns and has [[fu|fuel]] at their counters, the two columns of [[fu-vs]].",
 r"An annotated configuration $a = (q, K, W_a)$ is in the lock-free process relation at the ordinal index $\alpha$ when each thread is in $E[\kappa_L]$ at the ends it owns and has [[fu|fuel]] at their counters. These are the two columns of [[fu-vs]].")
for dv in sp['deviations']:
    if dv['kind']=='simplified': dv['reason']=r"$\mathsf{wa}$ names the other eleven conjuncts of `soup_consistent`, the fields `sp_owner` to `sp_sigcap` of `soup_gen`. Its note lists each conjunct."
N['sp.delta']['deviations'][0]['reason']=r"The Rocq keeps an environment `A` of the relation and a protocol map `Π` of fuel, chosen per index, and the counters and tickets in `K`. `sp_pts` and `sp_dom` give the three maps one domain and the points of `K`, so one map $\Delta$ states all three."
sd=B['th-sound']
sd['caption']=sub(sd['caption'],r"The Rocq also proves soundness for n-ary composites and for one closed thread\inmode{lf}{, the absence of divergence by free steps, the existence of a weakly fair maximal run and lock freedom in reachability form}.",
 r"The Rocq also proves soundness for n-ary composites and for one closed thread.\inmode{lf}{ It also proves the absence of divergence by free steps, a weakly fair maximal run and lock freedom in reachability form.}")
B['th-chain']['caption']=sub(B['th-chain']['caption'],"the case of P-Term rests on [[th-terms]]","the case of P-Term uses [[th-terms]]")
B['w-wf']['usedIn']=[u for u in B['w-wf']['usedIn'] if u!='th-sound']
for k in ["w.wok","fu.rename","cs.csem","sp.pts","sp.dom","sp.owner","sp.closed","sp.pair","sp.sdual","sp.pdual","sp.sig","sp.psig","sp.fin","sp.next","sp.cap","sp.tsum","th.lf-thread-progress","th.fundamental-typed","th.live-fundamental","th.live-fundamental-typed","th.soundness-source","th.lf-soundness-source","th.lf-padovani","th.cost-fundamental","th.em","th.ac","th.live-fundamental-proc","th.connect-n","th.live-soundness","th.lf-connect-n","th.dc","th.pcomps","th.live-sub-df","th.boxfree","th.lf-tp-gen","th.linksr","th.wfit","th.lf-soup-term","th.chprem","th.tpr","th.lf-soundness-run"]:
    del N[k]
json.dump(m,open(P,'w'),ensure_ascii=False,indent=1); open(P,'a').write('\n'); print('ok')
