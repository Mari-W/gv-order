# Renames of phase 3

`scripts/rename-phase3.py` performs every rename in this file except the
judgment merge. Run it without arguments to rewrite all of `theories/`, or
with file names to rewrite files added later. It is idempotent.

## Rules

- Every identifier containing `slot` or `Slot` takes `payload` or `Payload`
  in its place (`pt_slot` becomes `pt_payload`). Three names clash with
  existing ones and are renamed by hand: `slots` and `slots_sw` (the list
  x[0], …, x[m-1]) become `payload_pts` and `payload_pts_sw`, and `fslot`
  (the variable-or-flag part of a future) becomes `futrest`.
- Identifiers that name the future of a term (formerly frame) take
  `future`. The evaluation frames of `lang/Semantics.v` (`frame`,
  `fill_frame`, `frame_val`, `ectx_val_frame`) and the multiset frame lemma
  `msb_frame` keep their names.
- In comments the word frame (future sense) becomes future, outside
  `theories/lang/`. Phrases about evaluation frames keep the word.
- Typing constructors follow the rule names of the paper.
- Notations `x ·[ j ]` for `pt_payload x j` (the paper's p[j]) and
  `x +ₚ k` for `pt_shift k x` (the paper's p+k), in `types/Types.v`.

## Table

| old | new |
|-----|-----|
| `below_rest_frame` | `below_rest_future` |
| `cpt_slot` | `cpt_payload` |
| `den_slot` | `den_payload` |
| `den_X_slot` | `den_X_payload` |
| `Erel_frame` | `Erel_future` |
| `frame_pinst` | `future_pinst` |
| `frame_roots` | `future_roots` |
| `frame_roots_sw` | `future_roots_sw` |
| `fslot` | `futrest` |
| `ga_slot` | `ga_payload` |
| `geq_slot` | `geq_payload` |
| `he_slot` | `he_payload` |
| `Hslot` | `Hpayload` |
| `jpath_slot` | `jpath_payload` |
| `NSlot` | `NPayload` |
| `op_ub_frame` | `op_ub_future` |
| `po_frame` | `po_future` |
| `pt_inst_slot` | `pt_inst_payload` |
| `pt_root_slot` | `pt_root_payload` |
| `pt_slot` | `pt_payload` |
| `pt_slot_root` | `pt_payload_root` |
| `pteqW_slot` | `pteqW_payload` |
| `ptsw_slot` | `ptsw_payload` |
| `ready_t_frame` | `ready_t_future` |
| `same_slot_cycle` | `same_payload_cycle` |
| `same_slot_not_acyclic` | `same_payload_not_acyclic` |
| `sdepth_slotv` | `sdepth_payloadv` |
| `se_slot` | `se_payload` |
| `sframe` | `sfuture` |
| `skn_slot` | `skn_payload` |
| `slot_respect` | `payload_respect` |
| `slots` | `payload_pts` |
| `slots_sw` | `payload_pts_sw` |
| `slotv` | `payloadv` |
| `slotv_inst` | `payloadv_inst` |
| `t_box` | `t_exp` |
| `t_chan` | `t_ch` |
| `t_konst` | `t_const` |
| `t_lam` | `t_abs` |
| `t_letp` | `t_letpair` |
| `t_letu` | `t_letstar` |
| `t_wk` | `t_weak` |
| `th_slot` | `th_payload` |
| `V_slot` | `V_payload` |
| `wf_eq_slot` | `wf_eq_payload` |

The constructors `t_unit`, `t_var`, `t_app`, `t_pair`, `t_inj1`, `t_inj2`,
`t_case`, `t_contract`, `t_conv`, `t_pack`, `t_open`, `pt_term` and
`pt_connect` already match E-Unit, E-Var, E-App, E-Pair, E-Inj, E-Case,
E-Contract, E-Conv, E-Pack, E-Open, P-Term and P-Connect.

## Judgment merge

The inductive `styped` of `static/Source.v` and its constructors `st_unit`,
`st_konst`, `st_var`, `st_lam`, `st_app`, `st_pair`, `st_letu`, `st_letp`,
`st_inj1`, `st_inj2`, `st_case`, `st_box`, `st_wk`, `st_contract`,
`st_conv`, `st_pack`, `st_open` are gone. `styped Φ Ψ Δ F t T` is now the
definition `typed wnil Φ Ψ ∅ Δ F t T`, the source instance of the one
judgment `typed`. `wnil`, `wnil_strict` and `wnil_names` moved from
`static/Fundamental.v` to `static/Source.v`. `typed_world_transfer` is new
and replaces the two inductions of `styped_typed` and `typed_styped`, which
remain as corollaries with the same statements (docs/SHARP-EDGES.md, entry 153).
