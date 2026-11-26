### OOPSLA Revision

- Removed c ∈ C from P-Act-Msg and R-Com. Proved it correct in Rocq.
- Improved explanation of LTS rules
- Removed table of LOC of mechanization
- Reformulated E-Step and P-Step unpacking the two cases irred/not irred
- Made figures uniform. Fig 1 may be merged into Fig 2
- O-Fork now relies on the no-clash/freshness conventions, so c is assumed to not clash with the environment by convention (similar considerations apply for other rules)
- Overhauled macros (was giving me garbled fonts)
- Rule names now link to the rule
- Added an explanation of syntactic `sentc` in LTS and its fallout
- Moved P-Act-Session as last rule of fig 3 so the explanation flows better


Todo:

- Sync all mentions of figures of the paper in the mechanization's comment