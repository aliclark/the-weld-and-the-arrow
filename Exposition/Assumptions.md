<!-- GENERATED from WeldAndArrow/Meta/AssumptionLedger.lean by `lake exe exposition_gen` - do not edit -->

# Assumptions

Generated from `WeldAndArrow/Meta/AssumptionLedger.lean` by `lake exe exposition_gen`. `WeldAndArrow/Signature/Assumptions.lean` holds the compile-checked anchor pins; statement prose is canonical here.

## A. What Is Asserted

### A.1 No prior agent

A weld is the primitive occurrence. `Grid.index` and `Grid.share` are projections from a completed `RawWeld`, not fields recovered from a separate performer or act. `no_agent_recovery_of_field_collision` records the internal obstruction: the same call-response field residue can be produced by distinct actual agents.

**Checked anchors (Signature):** `WAA.RawWeld` (proof), `WAA.Grid.index` (proof), `WAA.Grid.share` (proof), `WAA.no_agent_recovery_of_field_collision` (witness)

### A.2 Nothing self-indexed is stored

`Config` stores only `tendency : Contrib`. It has no owner, being, weld, or field-residue slot. `rePitch` uses the received weld's share and ignores the prior configuration value. The checked claim is architectural and definability-level: the record has no `Being`-typed slot, relabelling agents acts trivially on configurations and commutes with `rePitch`, and no relabelling-equivariant recovery of an agent from a configuration exists. It is not an information-flow claim; see the declined entry below.

**Checked anchors (Signature):** `WAA.Config` (proof), `WAA.Config.tendency` (proof), `WAA.Grid.rePitch` (proof), `WAA.RawWeld.mapAgent` (proof)

**Downstream elaboration:** `WAA.Config.relabel_fixed` (proof), `WAA.Grid.relabel_rePitch` (proof), `WAA.Grid.no_natural_agent_recovery_from_config` (witness), `WAA.ConfigLeakWitness.no_agent_recovery_from_config_of_share_collision` (witness)

### A.3 The self-pole index is just live share

`HasSelfPoleIndex w` is `not AtBot (share w)`, and when the predicate is live the carried `selfPoleIndex` is the weld's agent tag.

**Checked anchors (Signature):** `WAA.Grid.HasSelfPoleIndex` (proof), `WAA.Grid.selfPoleIndex_eq_agent_of_hasSelfPoleIndex` (proof), `WAA.Grid.no_self_pole_index_of_atBot` (proof)

### A.4 Stone and terminus split function from share

A `Stone` mounts no response. A `Terminus` may mount responses, but every mounted response is at the pole-class. `AtPoleClass` intentionally includes the vacuous stone case.

**Checked anchors (Signature):** `WAA.Grid.Stone` (proof), `WAA.Grid.Terminus` (proof), `WAA.Grid.AtPoleClass` (proof), `WAA.Grid.stone_is_terminus_vacuously` (proof), `WAA.clockGrid_function_share_split_witness` (witness)

### A.5 Self-lines are permitted, not built in

The bare signature does not impose irreflexivity on `conditions`; a model may supply reflexive delivery, and then the directed vocabulary can read a self-line.

**Checked anchors (Signature):** `WAA.Grid.conditions` (proof), `WAA.Grid.DirectedConvention.DeliveredTo` (proof), `WAA.Grid.DirectedConvention.LandsAt` (proof), `WAA.AssumptionLocalWitnesses.signature_self_line_permitted` (witness)

**Downstream elaboration:** `WAA.SelfLineWitness.selfLine_landsAt_self` (witness), `WAA.SelfLineWitness.selfLine_waaOwnershipFace_self` (witness)

## B. What Is Deliberately Declined

### B.1 No arrow in `conditions`

The signature assumes no asymmetry, irreflexivity, or transitivity for `conditions`. `ConditionsEither` is the symmetric field fact; direction enters only in `Grid.DirectedConvention`. The downstream `DirectionNegative` witness elaborates this as non-recovery from symmetric closure.

**Checked anchors (Signature):** `WAA.Grid.ConditionsEither` (proof), `WAA.Grid.conditionsEither_symm` (proof), `WAA.Grid.DirectedConvention.TimeDirection` (proof), `WAA.Grid.transpose` (witness), `WAA.Grid.transpose_conditionsEither_iff` (witness), `WAA.Grid.DirectedConvention.transpose_deliveredTo_iff` (witness), `WAA.RawWeld.transposeCR` (witness), `WAA.AssumptionLocalWitnesses.no_direction_recovery_from_conditionsEither` (witness), `WAA.InteriorDirectionNegative.no_interior_direction_recovery` (witness)

**Downstream elaboration:** `WAA.DirectionNegative.no_direction_recovery_from_conditionsEither` (witness)

### B.2 No `PreorderTop`

The signature supplies only `PreorderBot`. The share-zero pole is an attained bottom order-class (`AtBot`); the total-share or solipsist pole is an asymptote, not an element of the interface. `StrongSelfConditioningTag` is named and shelved in the being convention for the same reason.

**Checked anchors (Signature):** `WAA.PreorderBot` (proof), `WAA.AtBot` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.StrongSelfConditioningTag` (proof), `WAA.AssumptionLocalWitnesses.nat_preorderBot_has_no_top` (witness)

### B.3 No privileged person-partition

A being boundary is supplied by a diagnosis-time `BeingCoarsening`, not stored as a field of `Grid`. The signature already admits both identity and total coarsenings for any grid; the downstream `BeingNegative` witness elaborates this as non-recovery of a unique partition from grid data.

**Checked anchors (Signature):** `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.InFiber` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.SameFiber` (proof), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id` (witness), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total` (witness), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.total_sameFiber` (witness), `WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.id_not_sameFiber_of_ne` (witness), `WAA.AssumptionLocalWitnesses.partition_merge_split_disagree` (witness)

**Downstream elaboration:** `WAA.BeingNegative.no_partition_recovery` (witness)

### B.4 Direction resolution is display, not signature furniture

A clock's finite delivery-axis resolution is supplied by a diagnosis-time `DirectionCoarsening`, not by a `Grid` field and not by any pole or legitimacy predicate.

**Checked anchors (Signature):** `WAA.Grid.DirectedConvention.DirectionCoarsening` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.SameTick` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.ResolutionBounded` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton` (proof), `WAA.Grid.DirectedConvention.DirectionCoarsening.transpose_subTickDelivery` (witness)

**Downstream elaboration:** `WAA.DirectionCoarseningWitness.registerClock_unitTick_not_resolutionBounded` (witness), `WAA.DirectionCoarseningWitness.unit_directionVoid_via_mergeToUnit` (witness), `WAA.DirectionCoarseningWitness.fullyCoarseRegisterClock_no_timeDirection` (witness), `WAA.DirectionCoarseningWitness.registerClock_directionCoarsening_independence` (witness)

### B.5 Contribution values are display, not operational tokens

The Signature layer itself uses only order and pole vocabulary around `share`. The downstream `DisplayReparam` / `InvarianceNegative` modules give the full transport discipline: order- and pole-preserving display changes preserve the legal predicates, while equality to the chosen bottom does not.

**Checked anchors (Signature):** `WAA.Grid.share_eq_grade_check` (proof), `WAA.AtBot` (proof), `WAA.OrderEq` (proof), `WAA.Grid.Terminus` (proof)

**Downstream elaboration:** `WAA.DisplayReparam` (proof), `WAA.DisplayReparam.atBot_iff` (proof), `WAA.InvarianceNegative.oldEqTerminus_not_invariant` (witness)

### B.6 Standing full enlightenment is display and faith-object only

The operational, assertable content of full enlightenment is per-occurrence: `WaaEnlightenedOccurrence` states an actual pole-deed landing as a share-drop against a live prior tendency. The standing universal `WaaFullyEnlightened` remains legal as run-display and faith-object, but no estimator from actual-run response/share data decides it. The sealed-regime route is vacuous and is fenced from the enacted form by `WaaEnlightenmentEnacted` and `not_enacted_of_undelivered`.

**Checked anchors (Signature):** None.

**Downstream elaboration:** `WAA.Grid.DirectedConvention.WaaEnlightenedOccurrence` (proof), `WAA.Grid.DirectedConvention.WaaEnlightenmentEnacted` (proof), `WAA.Grid.DirectedConvention.not_enacted_of_undelivered` (proof), `WAA.FullEnlightenmentNegative.actual_run_data_underdetermines_fullEnlightenment` (witness), `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.waa_enlightened_occurrence_voice_assertable` (proof), `WAA.Grid.DirectedConvention.BeingConvention.GridConvention.waa_standing_enlightenment_voice_displayable` (proof)

### B.7 No blanket noninterference for the contribution carrier

Grading may depend on the agent — `gradingCollisionGrid` grades by being deliberately (cetanā) — so a model's stored tendency may extensionally coincide with an agent tag; `registerClockGrid` witnesses the coincidence. The signature therefore declines the information-flow reading of non-storage. `Grid.rePitch_forgets` bounds the coincidence to a single reception's footprint: nothing accumulates into a diachronic bearer, and the configuration is fibered over no being. The asserted claim is typing plus relabelling equivariance.

**Checked anchors (Signature):** `WAA.gradingCollisionGrid` (witness), `WAA.registerClockGrid` (witness)

**Downstream elaboration:** `WAA.ConfigLeakWitness.registerClock_config_recovers_agent` (witness), `WAA.Config.relabel_fixed` (proof), `WAA.Grid.relabel_rePitch` (proof), `WAA.Grid.rePitch_forgets` (proof)

## C. Conveniences and Stand-Ins

### C.1 Hand-rolled order classes

`Preorder` and `PreorderBot` are hand-rolled to keep assumptions visible and dependency-free. They play the local role Mathlib order classes would play, without importing Mathlib.

**Checked anchors (Signature):** `WAA.Preorder` (proof), `WAA.PreorderBot` (proof), `WAA.shareBot` (proof), `WAA.shareBot_le` (proof)

### C.2 `_before` is retained but currently ignored by `rePitch`

`rePitch` keeps a `_before` slot because the operation is conceptually a re-pitch from a prior configuration. The current implementation ignores that slot; the proof anchor below is a tripwire for the day that changes.

**Checked anchors (Signature):** `WAA.Grid.rePitch` (proof)

> Note: The signature file keeps an `rfl` example showing that two prior configurations produce the same re-pitch for the same received weld.

### C.3 The scalar is display over a partial order

`WaaMismatchGrade` lives in `Doctrines`, so this Signature module does not import it; the Signature-side checked fact is that `share` is the only contribution value exported by a weld.

**Checked anchors (Signature):** `WAA.Grid.share` (proof), `WAA.Grid.share_eq_grade_check` (proof)

**Downstream elaboration:** `WAA.Grid.WaaMismatchGrade` (proof), `WAA.Grid.waaMismatchGrade_eq_share` (proof)

### C.4 `Models.lean` witnesses are illustrative

The clock and register-clock models anchor possibility checks and taxonomy examples; they are not uniqueness claims.

**Checked anchors (Signature):** `WAA.clockGrid` (witness), `WAA.registerClockGrid` (witness), `WAA.registerClock_macro_sentient` (witness), `WAA.registerClock_macro_selfConditioning` (witness)

## Axiom audit

- `WAA.no_agent_recovery_of_field_collision` -- pinned by `#guard_msgs` in `WeldAndArrow/Signature/Assumptions.lean` to depend on no axioms.
- `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_within_tick` -- pinned by `#guard_msgs` in `WeldAndArrow/Signature/Assumptions.lean` to depend on no axioms.
- `WAA.Grid.DirectedConvention.DirectionCoarsening.no_timeDirection_of_resolutionBounded_subsingleton` -- pinned by `#guard_msgs` in `WeldAndArrow/Signature/Assumptions.lean` to depend on no axioms.
