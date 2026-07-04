/-
================================================================================
  The Weld and the Arrow — IV. Invariance
  Display reparameterization for the contribution carrier
================================================================================

This file is the admission criterion for future grade-facing predicates:
anything that depends on `Contrib` owes a transport lemma here, or it is
operational residue by definition. The theorems below are the formal content
of treating contribution values as display conventions over the preorder.
-/

import WeldAndArrow.Identification

namespace WAA

/-- A display-reparameterization: preserves and reflects the ordering and the
    pole-class. The invariance theorems below are the formal content of
    "display conventions over that partial order". -/
structure DisplayReparam (Contrib Contrib' : Type)
    [PreorderBot Contrib] [PreorderBot Contrib'] where
  toFun     : Contrib → Contrib'
  le_iff    : ∀ a b, a ≼ b ↔ toFun a ≼ toFun b
  atBot_bot : AtBot (toFun shareBot)

namespace DisplayReparam

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']
variable (f : DisplayReparam Contrib Contrib')

/-- Reparameterization preserves and reflects the pole-class. -/
theorem atBot_iff (a : Contrib) :
    AtBot (f.toFun a) ↔ AtBot a := by
  constructor
  · intro h
    exact (f.le_iff a shareBot).mpr
      (Preorder.le_trans h (shareBot_le (f.toFun shareBot)))
  · intro h
    exact Preorder.le_trans ((f.le_iff a shareBot).mp h) f.atBot_bot

/-- Reparameterization preserves and reflects order-equivalence. -/
theorem orderEq_iff (a b : Contrib) :
    OrderEq (f.toFun a) (f.toFun b) ↔ OrderEq a b := by
  constructor
  · intro h
    exact ⟨(f.le_iff a b).mpr h.left, (f.le_iff b a).mpr h.right⟩
  · intro h
    exact ⟨(f.le_iff a b).mp h.left, (f.le_iff b a).mp h.right⟩

end DisplayReparam

namespace Config

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']

/-- Transport a stored display tendency along a display reparameterization. -/
def map (before : Config Contrib) (f : DisplayReparam Contrib Contrib') :
    Config Contrib' :=
  { tendency := f.toFun before.tendency }

theorem map_tendency (before : Config Contrib)
    (f : DisplayReparam Contrib Contrib') :
    (before.map f).tendency = f.toFun before.tendency :=
  rfl

end Config

namespace Grid

variable {Contrib Contrib' : Type} [PreorderBot Contrib] [PreorderBot Contrib']

/-- Transport a grid by reparameterizing only its Row-2 display carrier. -/
def map (G : Grid Contrib) (f : DisplayReparam Contrib Contrib') :
    Grid Contrib' where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := G.respondsTo
  grade      := fun b c r => f.toFun (G.grade b c r)
  conditions := G.conditions

variable (G : Grid Contrib) (f : DisplayReparam Contrib Contrib')

theorem map_grade (b : G.Being) (c : G.Call) (r : G.Response) :
    (G.map f).grade b c r = f.toFun (G.grade b c r) :=
  rfl

theorem map_share (w : G.Weld) :
    (G.map f).share w = f.toFun (G.share w) :=
  rfl

/-- Function-side predicates do not mention the contribution carrier, so they
    transport by definitional unfolding. -/
theorem map_actual_iff (w : G.Weld) :
    (G.map f).Actual w ↔ G.Actual w :=
  Iff.rfl

theorem map_mountsAt_iff (b : G.Being) (c : G.Call) :
    (G.map f).MountsAt b c ↔ G.MountsAt b c :=
  Iff.rfl

theorem map_mountsSomewhere_iff (b : G.Being) :
    (G.map f).MountsSomewhere b ↔ G.MountsSomewhere b :=
  Iff.rfl

theorem map_respondsToEveryCall_iff (b : G.Being) :
    (G.map f).RespondsToEveryCall b ↔ G.RespondsToEveryCall b :=
  Iff.rfl

theorem map_stone_iff (b : G.Being) :
    (G.map f).Stone b ↔ G.Stone b :=
  Iff.rfl

namespace DirectedConvention

theorem map_deliveredTo_iff (deed reception : G.Weld) :
    DeliveredTo (G.map f) deed reception ↔ DeliveredTo G deed reception :=
  Iff.rfl

theorem map_landsAt_iff (deed reception : G.Weld) :
    LandsAt (G.map f) deed reception ↔ LandsAt G deed reception :=
  Iff.rfl

theorem map_environsLine_iff
    (b : G.Being) (deed reception : G.Weld) :
    EnvironsLine (G.map f) b deed reception ↔ EnvironsLine G b deed reception :=
  Iff.rfl

end DirectedConvention

theorem map_terminus_iff (b : G.Being) :
    (G.map f).Terminus b ↔ G.Terminus b := by
  constructor
  · intro h c r hresp
    exact (f.atBot_iff (G.grade b c r)).mp (h c r hresp)
  · intro h c r hresp
    exact (f.atBot_iff (G.grade b c r)).mpr (h c r hresp)

theorem map_liveTerminus_iff (b : G.Being) :
    (G.map f).LiveTerminus b ↔ G.LiveTerminus b := by
  constructor
  · intro h
    exact ⟨(G.map_mountsSomewhere_iff f b).mp h.left,
      (G.map_terminus_iff f b).mp h.right⟩
  · intro h
    exact ⟨(G.map_mountsSomewhere_iff f b).mpr h.left,
      (G.map_terminus_iff f b).mpr h.right⟩

theorem map_responsiveTerminus_iff (b : G.Being) :
    (G.map f).ResponsiveTerminus b ↔ G.ResponsiveTerminus b := by
  constructor
  · intro h
    exact ⟨(G.map_respondsToEveryCall_iff f b).mp h.left,
      (G.map_terminus_iff f b).mp h.right⟩
  · intro h
    exact ⟨(G.map_respondsToEveryCall_iff f b).mpr h.left,
      (G.map_terminus_iff f b).mpr h.right⟩

theorem map_atPoleClass_iff (b : G.Being) :
    (G.map f).AtPoleClass b ↔ G.AtPoleClass b := by
  constructor
  · intro h
    exact h.elim
      (fun hstone => Or.inl ((G.map_stone_iff f b).mp hstone))
      (fun hterm => Or.inr ((G.map_terminus_iff f b).mp hterm))
  · intro h
    exact h.elim
      (fun hstone => Or.inl ((G.map_stone_iff f b).mpr hstone))
      (fun hterm => Or.inr ((G.map_terminus_iff f b).mpr hterm))

theorem map_hasSelfPoleIndex_iff (w : G.Weld) :
    (G.map f).HasSelfPoleIndex w ↔ G.HasSelfPoleIndex w := by
  constructor
  · intro h hbot
    exact h ((f.atBot_iff (G.share w)).mpr hbot)
  · intro h hbot
    exact h ((f.atBot_iff (G.share w)).mp hbot)

theorem map_probeConstant_iff (b : G.Being) (cs : G.Call → Prop) :
    (G.map f).ProbeConstant b cs ↔ G.ProbeConstant b cs := by
  constructor
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    exact (f.orderEq_iff (G.grade b c₁ r₁) (G.grade b c₂ r₂)).mp
      (h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂)
  · intro h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂
    exact (f.orderEq_iff (G.grade b c₁ r₁) (G.grade b c₂ r₂)).mpr
      (h c₁ c₂ hc₁ hc₂ r₁ r₂ hr₁ hr₂)

theorem map_stateToolFits_iff (w : G.Weld) :
    (G.map f).StateToolFits w ↔ G.StateToolFits w := by
  constructor
  · intro h hidx
    exact h ((G.map_hasSelfPoleIndex_iff f w).mpr hidx)
  · intro h hidx
    exact h ((G.map_hasSelfPoleIndex_iff f w).mp hidx)

namespace Tier

/-- Transport a diagnostic tier along a grid reparameterization. -/
def map {G : Grid Contrib} (f : DisplayReparam Contrib Contrib') :
    Tier G → Tier (G.map f)
  | .floor => .floor
  | .actTime w => .actTime w

end Tier

theorem map_tier_hasLiveShare_iff :
    ∀ t : Tier G,
      Tier.hasLiveShare (G.map f) (Tier.map f t) ↔
        Tier.hasLiveShare G t
  | .floor => Iff.rfl
  | .actTime w => G.map_hasSelfPoleIndex_iff f w

theorem map_rePitch (before : Config Contrib) (received : G.Weld) :
    (G.map f).rePitch (before.map f) received =
      (G.rePitch before received).map f :=
  rfl

theorem map_isShareDrop_iff
    (before : Config Contrib) (received : G.Weld) :
    (G.map f).IsShareDrop (before.map f) received ↔
      G.IsShareDrop before received := by
  constructor
  · intro h
    exact ⟨(f.le_iff (G.share received) before.tendency).mpr h.left,
      fun hle => h.right ((f.le_iff before.tendency (G.share received)).mp hle)⟩
  · intro h
    exact ⟨(f.le_iff (G.share received) before.tendency).mp h.left,
      fun hle => h.right ((f.le_iff before.tendency (G.share received)).mpr hle)⟩

namespace DirectedConvention

theorem map_landsWithShareDrop_iff
    (before : Config Contrib) (deed reception : G.Weld) :
    LandsWithShareDrop (G.map f) (before.map f) deed reception ↔
      LandsWithShareDrop G before deed reception := by
  constructor
  · intro h
    exact ⟨(map_landsAt_iff G f deed reception).mp h.left,
      (G.map_isShareDrop_iff f before reception).mp h.right⟩
  · intro h
    exact ⟨(map_landsAt_iff G f deed reception).mpr h.left,
      (G.map_isShareDrop_iff f before reception).mpr h.right⟩

theorem map_shareDropLine_iff
    (before : Config Contrib) (b : G.Being) (deed reception : G.Weld) :
    ShareDropLine (G.map f) (before.map f) b deed reception ↔
      ShareDropLine G before b deed reception := by
  constructor
  · intro h
    exact ⟨(map_environsLine_iff G f b deed reception).mp h.left,
      (G.map_isShareDrop_iff f before reception).mp h.right⟩
  · intro h
    exact ⟨(map_environsLine_iff G f b deed reception).mpr h.left,
      (G.map_isShareDrop_iff f before reception).mpr h.right⟩

end DirectedConvention

/- --------------------------------------------------------------------------
   Direction-smuggling detector: reverse only `conditions`
-------------------------------------------------------------------------- -/

/-- Reverse the argument order of `conditions`, leaving every other part of the
    grid untouched. Direction-neutral facts should transport across this;
    delivery-facing facts should either reverse or declare the model-side
    asymmetry hypothesis they need. -/
def transpose (G : Grid Contrib) : Grid Contrib where
  Being      := G.Being
  Call       := G.Call
  Response   := G.Response
  respondsTo := G.respondsTo
  grade      := G.grade
  conditions := fun w₁ w₂ => G.conditions w₂ w₁

theorem transpose_conditions (w₁ w₂ : G.Weld) :
    G.transpose.conditions w₁ w₂ = G.conditions w₂ w₁ :=
  rfl

theorem transpose_conditionsEither_iff (w₁ w₂ : G.Weld) :
    G.transpose.ConditionsEither w₁ w₂ ↔ G.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim Or.inr Or.inl,
   fun h => h.elim Or.inr Or.inl⟩

namespace DirectedConvention

theorem transpose_deliveredTo_iff (deed reception : G.Weld) :
    DeliveredTo G.transpose deed reception ↔ DeliveredTo G reception deed :=
  Iff.rfl

end DirectedConvention

end Grid

/- ==============================================================================
   Negative example: equality-at-bottom does not transport
============================================================================== -/

namespace InvarianceNegative

inductive TwoBottom
  | chosen
  | other

instance : PreorderBot TwoBottom where
  le       := fun _ _ => True
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot      := TwoBottom.chosen
  bot_le   := fun _ => True.intro

instance : PreorderBot Unit where
  le       := fun _ _ => True
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ => True.intro
  bot      := ()
  bot_le   := fun _ => True.intro

def mergeToUnit : DisplayReparam TwoBottom Unit where
  toFun _ := ()
  le_iff _ _ := ⟨fun _ => True.intro, fun _ => True.intro⟩
  atBot_bot := True.intro

def twoBottomGrid : Grid TwoBottom where
  Being      := Unit
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := TwoBottom.other
  conditions _ _ := False

/-- The old, equality-token version of terminus, kept only for this
    counterexample. It is not the system predicate. -/
def OldEqTerminus {Contrib : Type} [PreorderBot Contrib]
    (G : Grid Contrib) (b : G.Being) : Prop :=
  ∀ c r, G.respondsTo b c = some r → G.grade b c r = shareBot

example : twoBottomGrid.Terminus () :=
  fun _ _ _ => True.intro

example : ¬ OldEqTerminus twoBottomGrid () := by
  intro h
  have hbad : TwoBottom.other = TwoBottom.chosen := h () () rfl
  cases hbad

example : OldEqTerminus (twoBottomGrid.map mergeToUnit) () :=
  fun _ _ _ => rfl

/-- The new predicate transports across the merge, while the old equality-token
    predicate would hold after the merge and fail before it. -/
example :
    ((twoBottomGrid.map mergeToUnit).Terminus () ↔ twoBottomGrid.Terminus ()) ∧
      OldEqTerminus (twoBottomGrid.map mergeToUnit) () ∧
      ¬ OldEqTerminus twoBottomGrid () :=
  ⟨twoBottomGrid.map_terminus_iff mergeToUnit (),
    fun _ _ _ => rfl,
    by
      intro h
      have hbad : TwoBottom.other = TwoBottom.chosen := h () () rfl
      cases hbad⟩

end InvarianceNegative

/- ==============================================================================
   §N  Direction-underdetermination: the arrow's retype, witnessed

   Theory: Karma ("the arrow retyped") demotes before/after from carried
   structure to display. The checkable content is an underdetermination
   fact in the same family as `no_agent_recovery_of_field_collision`:
   the symmetric closure `ConditionsEither` does not determine `conditions`.
   The two grids below agree on `ConditionsEither` at EVERY pair of welds and
   disagree on `conditions` at a witness pair, so no function of the
   symmetric structure returns the direction. Honest scope, as with the
   agent-recovery theorem: this is not a claim about every grid, it is
   the internal witness that symmetric delivery-structure under-
   determines the arrow. Nothing here consumes physics; thermodynamics
   enters the prose as the mechanism of the READING, never as a premise
   of any theorem.
============================================================================== -/

namespace DirectionNegative

/-- One being, two calls, one response: the smallest web on which a
    direction can be drawn two ways. -/
abbrev W := RawWeld Unit Bool Unit

/-- The weld at the `false` call. -/
def wFalse : W := ⟨(), false, ()⟩

/-- The weld at the `true` call. -/
def wTrue : W := ⟨(), true, ()⟩

/-- The web read one way: the `false`-weld conditions the `true`-weld. -/
def forwardGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions w₁ w₂ := w₁.call = false ∧ w₂.call = true

/-- The same web read the other way: only `conditions` is reversed. -/
def backwardGrid : Grid Nat where
  Being      := Unit
  Call       := Bool
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 0
  conditions w₁ w₂ := w₁.call = true ∧ w₂.call = false

/-- The two readings agree on the symmetric closure at every pair:
    forgetting direction erases exactly the difference between them. -/
theorem conditionsEither_agrees (w₁ w₂ : W) :
    forwardGrid.ConditionsEither w₁ w₂ ↔ backwardGrid.ConditionsEither w₁ w₂ :=
  ⟨fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩),
   fun h => h.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                   (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)⟩

/-- And they disagree on the direction itself at the witness pair. -/
theorem conditions_disagree :
    forwardGrid.conditions wFalse wTrue ∧
      ¬ backwardGrid.conditions wFalse wTrue := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro h
    cases h.left

/-- No function of the symmetric structure recovers the direction: any
    candidate correct on both grids would force their `conditions` to
    coincide, and they do not. The direction is the reading's, never
    the closure's — `no_agent_recovery` run at the arrow. -/
theorem no_direction_recovery_from_conditionsEither :
    ¬ ∃ recover : (W → W → Prop) → (W → W → Prop),
        recover forwardGrid.ConditionsEither = forwardGrid.conditions ∧
        recover backwardGrid.ConditionsEither = backwardGrid.conditions := by
  rintro ⟨recover, hf, hb⟩
  have hsame : forwardGrid.ConditionsEither = backwardGrid.ConditionsEither := by
    funext w₁ w₂
    exact propext (conditionsEither_agrees w₁ w₂)
  have hcond : forwardGrid.conditions = backwardGrid.conditions := by
    rw [← hf, hsame, hb]
  exact conditions_disagree.right (hcond ▸ conditions_disagree.left)

/-- The equilibrium-pole face, on the existing negative carrier: where
    everything is order-equivalent, nothing is directed. -/
example (a b : InvarianceNegative.TwoBottom) : ¬ Directed a b :=
  no_direction_of_all_orderEq (fun _ _ => ⟨True.intro, True.intro⟩) a b

end DirectionNegative

/- ==============================================================================
   Self-line witness: permitted by the signature, not forced by it

   The signature permits self-lines by decision, not oversight: irreflexivity of
   delivery is a contingent regime fact, never structure carried by
   `conditions`. A self-line is a correlation on which direction-reading gets no
   grip; `not_directed_self` is the order-side display of the same strictness
   point. This does not collide with shushō-ittō, which is typed as one weld
   rather than two acts joined. Whether any real regime draws self-lines is a
   delivery-question the grid declines.
============================================================================== -/

namespace SelfLineWitness

inductive Being
  | one

inductive Call
  | call

inductive Response
  | response

def selfLineGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo _ _ := some Response.response
  grade _ _ _ := 1
  conditions _ _ := True

def w : selfLineGrid.Weld :=
  ⟨Being.one, Call.call, Response.response⟩

theorem w_has_live_share : selfLineGrid.waa_Appropriates w := by
  intro hbot
  cases hbot

example : selfLineGrid.conditions w w :=
  True.intro

example : Grid.DirectedConvention.LandsAt selfLineGrid w w :=
  ⟨True.intro, rfl⟩

example : Grid.DirectedConvention.waa_OwnershipFace selfLineGrid w w :=
  ⟨⟨True.intro, rfl⟩, w_has_live_share⟩

end SelfLineWitness

end WAA
