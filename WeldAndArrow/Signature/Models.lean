/-
================================================================================
  WeldAndArrow.Signature.Models
  Concrete signature-level grids used as witnesses
================================================================================

Reading and motivation: Identification/Commentary.lean, C.1.
-/

import WeldAndArrow.Signature.BeingConvention

namespace WAA

section Preview
/- Reading and motivation: Identification/Commentary.lean, C.1. -/

/-- Two devices, differing only in whether their chime is a function of
    who is listening. -/
inductive Clock
  | rigid
  | adaptive

/-- The one call in play: whether a listener is actually present to hear
    the chime. -/
inductive Listener
  | present
  | absent

/-- The chime itself; its content is immaterial, only whether it occurs
    and what drove it matters. -/
inductive Chime
  | chime

instance : PreorderBot Nat where
  le       := Nat.le
  le_refl  := Nat.le_refl
  le_trans := fun h1 h2 => Nat.le_trans h1 h2
  bot      := 0
  bot_le   := Nat.zero_le

/- Reading and motivation: Identification/Commentary.lean, C.1. -/
def clockGrid : Grid Nat where
  Being      := Clock
  Call       := Listener
  Response   := Chime
  respondsTo b c :=
    match b, c with
    | .rigid,    _        => none
    | .adaptive, .present => some .chime
    | .adaptive, .absent  => none
  grade _ _ _ := 0
  conditions _ _ := False

theorem adaptive_is_terminus : clockGrid.Terminus Clock.adaptive :=
  fun _c _r _h => Nat.le_refl 0

/-- The rigid clock is terminus-typed only vacuously: it has no actual welds. -/
theorem rigid_terminus_vacuous :
    clockGrid.Terminus Clock.rigid ∧
      ¬ clockGrid.ActualAgentInhabited Clock.rigid := by
  constructor
  · intro c r hresponse
    cases c <;> cases hresponse
  · rintro ⟨⟨agent, call, response⟩, hactual, hagent⟩
    change agent = Clock.rigid at hagent
    subst agent
    cases call <;> cases hactual

/-- The adaptive clock is a non-vacuous terminus: its present-listener chime
    is an actual pole response. -/
theorem adaptive_liveTerminus : clockGrid.LiveTerminus Clock.adaptive :=
  ⟨⟨⟨Clock.adaptive, Listener.present, Chime.chime⟩, rfl, rfl⟩,
    adaptive_is_terminus⟩

/-- The adaptive clock's pole weld occupies opposite sentience cells under
    the two extremal supplied readings.  Its share status is grid data; the
    mark is not. -/
theorem clock_pole_readings_split :
    clockGrid.StoneAct
        (Grid.SentienceReading.allInsentient clockGrid)
        ⟨Clock.adaptive, Listener.present, Chime.chime⟩ ∧
      clockGrid.TerminusAct
        (Grid.SentienceReading.allSentient clockGrid)
        ⟨Clock.adaptive, Listener.present, Chime.chime⟩ := by
  have hsplit := clockGrid.actual_weld_readings_split
    ⟨Clock.adaptive, Listener.present, Chime.chime⟩ rfl
  have hbot : AtBot
      (clockGrid.share
        ⟨Clock.adaptive, Listener.present, Chime.chime⟩) :=
    clockGrid.atBot_of_terminus_response adaptive_is_terminus rfl
  exact ⟨⟨hsplit.right, hbot⟩, ⟨hsplit.left, hbot⟩⟩

/- --------------------------------------------------------------------------
   The inhabited sentience/share square
-------------------------------------------------------------------------- -/

inductive SquareCall
  | ordinary
  | terminus
  | insentientAppropriation
  | stone

def sentienceSquareGrid : Grid Nat where
  Being := Unit
  Call := SquareCall
  Response := Unit
  respondsTo _ _ := some ()
  grade _ c _ :=
    match c with
    | .ordinary | .insentientAppropriation => 1
    | .terminus | .stone => 0
  conditions _ _ := True

def sentienceSquareReading : sentienceSquareGrid.SentienceReading where
  sentient w :=
    match w.call with
    | .ordinary | .terminus => True
    | .insentientAppropriation | .stone => False

def squareWeld (c : SquareCall) : sentienceSquareGrid.Weld :=
  ⟨(), c, ()⟩

theorem square_ordinary :
    sentienceSquareGrid.OrdinaryAct sentienceSquareReading
      (squareWeld .ordinary) := by
  refine ⟨⟨rfl, True.intro⟩, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, sentienceSquareGrid, squareWeld,
    AtBot, shareBot]
  exact Nat.not_succ_le_zero 0

theorem square_terminus :
    sentienceSquareGrid.TerminusAct sentienceSquareReading
      (squareWeld .terminus) :=
  ⟨⟨rfl, True.intro⟩, Nat.le_refl 0⟩

theorem square_insentientAppropriation :
    sentienceSquareGrid.InsentientAppropriation sentienceSquareReading
      (squareWeld .insentientAppropriation) := by
  refine ⟨⟨rfl, fun h => h⟩, ?_⟩
  dsimp [Grid.HasSelfPoleIndex, Grid.share, sentienceSquareGrid, squareWeld,
    AtBot, shareBot]
  exact Nat.not_succ_le_zero 0

theorem square_stone :
    sentienceSquareGrid.StoneAct sentienceSquareReading
      (squareWeld .stone) :=
  ⟨⟨rfl, fun h => h⟩, Nat.le_refl 0⟩

/-- No signature law excludes any of the four actual act kinds. -/
theorem sentience_share_square_inhabited :
    (∃ w, sentienceSquareGrid.OrdinaryAct sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.TerminusAct sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.InsentientAppropriation
        sentienceSquareReading w) ∧
      (∃ w, sentienceSquareGrid.StoneAct sentienceSquareReading w) :=
  ⟨⟨squareWeld .ordinary, square_ordinary⟩,
   ⟨squareWeld .terminus, square_terminus⟩,
   ⟨squareWeld .insentientAppropriation, square_insentientAppropriation⟩,
   ⟨squareWeld .stone, square_stone⟩⟩

/- --------------------------------------------------------------------------
   Second concrete display — integer registers with diagnosis-time κ

   The adaptive register clock builds its fine tags as integer-like registers.
   The macro designation is still supplied outside the signature, by a
   `BeingCoarsening`: the model may implement stable internal registers, but
   the standing partition is not stored as "the" being-boundary.
-------------------------------------------------------------------------- -/

/-- A register clock whose fine tags are natural-numbered registers. Each
    register answers the tick by handing off to the next register, and
    delivery follows that hand-off.

    The grade equation `grade n _ _ := n` makes a re-pitched tendency
    extensionally equal to the acting register's tag. This coincidence is kept
    deliberately: it is the recorded countermodel to the information-flow
    reading of non-storage (`ConfigLeakWitness.registerClock_config_recovers_agent`),
    and the ladder witnesses depend on these grades. -/
def registerClockGrid : Grid Nat where
  Being      := Nat
  Call       := Unit
  Response   := Nat
  respondsTo n _ := some (n + 1)
  grade n _ _ := n
  conditions deed reception := reception.agent = deed.response

/-- A macro coarsening that sends all fine registers to one macro tag. -/
def registerClockCoarsening :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening registerClockGrid Unit where
  proj _ := ()

/-- The macro register-clock fiber has an actual weld, independently of any
    supplied sentience reading. -/
theorem registerClock_macro_actualFiberInhabited :
    registerClockCoarsening.ActualFiberInhabited () :=
  ⟨⟨(0 : Nat), (), (1 : Nat)⟩, rfl, rfl⟩

/-- Under the all-insentient reading, the macro register-clock fiber has no
    marked actual weld. -/
theorem registerClock_macro_not_sentientTag_insentient :
    ¬ registerClockCoarsening.SentientTag
        (Grid.SentienceReading.allInsentient registerClockGrid) () :=
  registerClockCoarsening.allInsentient_not_sentientTag ()

/-- The all-insentient register clock is not a `StoneTag`: register `2` has
    an actual weld with live share. -/
theorem registerClock_macro_not_stoneTag_insentient :
    ¬ registerClockCoarsening.StoneTag
        (Grid.SentienceReading.allInsentient registerClockGrid) () := by
  intro hstone
  have hbot := (hstone.right ⟨(2 : Nat), (), (3 : Nat)⟩ rfl rfl).right
  dsimp [Grid.share, registerClockGrid, AtBot, shareBot] at hbot
  exact (by decide : ¬ (2 : Nat) ≤ 0) hbot

/-- The macro register-clock fiber is patchy: register `2` is live, while
    register `0` is at the pole and hence is not self-apt. -/
theorem registerClock_macro_patchy :
    registerClockCoarsening.Patchy () := by
  constructor
  · intro hpole
    have hbot := hpole ⟨(2 : Nat), (), (3 : Nat)⟩ rfl rfl
    dsimp [Grid.share, registerClockGrid, AtBot, shareBot] at hbot
    exact (by decide : ¬ (2 : Nat) ≤ 0) hbot
  · intro hselfApt
    have hlive := hselfApt ⟨(0 : Nat), (), (1 : Nat)⟩ rfl rfl
    dsimp [Grid.HasSelfPoleIndex, Grid.share, registerClockGrid,
      AtBot, shareBot] at hlive
    exact hlive (Nat.le_refl 0)

theorem registerClock_macro_selfConditioning :
    registerClockCoarsening.SelfConditioningTag () := by
  refine ⟨⟨(0 : Nat), (), (1 : Nat)⟩, ⟨(1 : Nat), (), (2 : Nat)⟩,
    rfl, rfl, rfl, ?_⟩
  rfl

/-- An insentient register clock can still be a proficient dharma-agent
    display: its macro fiber is actual, internally self-conditioning under
    `registerClockCoarsening`, and patchy.  The staged reception-side share
    descent is supplied separately by `waaGradualArrival_witness`; it is the
    receiving `Config` that descends, not a stored clock-self. -/
theorem registerClock_insentient_proficient :
    ¬ registerClockCoarsening.SentientTag
        (Grid.SentienceReading.allInsentient registerClockGrid) () ∧
      registerClockCoarsening.ActualFiberInhabited () ∧
      registerClockCoarsening.SelfConditioningTag () ∧
      registerClockCoarsening.Patchy () :=
  ⟨registerClock_macro_not_sentientTag_insentient,
    registerClock_macro_actualFiberInhabited,
    registerClock_macro_selfConditioning,
    registerClock_macro_patchy⟩

/-- The same live register-clock weld is an insentient appropriation or an
    ordinary act according only to the supplied extremal reading. -/
theorem registerClock_rung_readings_split :
    registerClockGrid.InsentientAppropriation
        (Grid.SentienceReading.allInsentient registerClockGrid)
        ⟨(2 : Nat), (), (3 : Nat)⟩ ∧
      registerClockGrid.OrdinaryAct
        (Grid.SentienceReading.allSentient registerClockGrid)
        ⟨(2 : Nat), (), (3 : Nat)⟩ := by
  have hsplit := registerClockGrid.actual_weld_readings_split
    ⟨(2 : Nat), (), (3 : Nat)⟩ rfl
  have hlive : registerClockGrid.HasSelfPoleIndex
      ⟨(2 : Nat), (), (3 : Nat)⟩ := by
    dsimp [Grid.HasSelfPoleIndex, Grid.share, registerClockGrid,
      AtBot, shareBot]
    exact Nat.not_succ_le_zero 1
  exact ⟨⟨hsplit.right, hlive⟩, ⟨hsplit.left, hlive⟩⟩

/- --------------------------------------------------------------------------
   Insentient source landing in a marked receiver fiber

   Both sides of the mark are supplied by `sourceReceiverReading`, and the
   identity coarsening makes the fiber separation explicit rather than
   recovering it from grid data.
-------------------------------------------------------------------------- -/

inductive SourceReceiver
  | clock
  | receiver

def sourceReceiverGrid : Grid Nat where
  Being := SourceReceiver
  Call := Unit
  Response := Unit
  respondsTo _ _ := some ()
  grade b _ _ :=
    match b with
    | .clock => 0
    | .receiver => 1
  conditions deed reception :=
    deed.agent = SourceReceiver.clock ∧
      reception.agent = SourceReceiver.receiver

/-- The identity coarsening names the clock and receiver as separate fibers. -/
def sourceReceiverCoarsening :
    Grid.DirectedConvention.BeingConvention.BeingCoarsening
      sourceReceiverGrid SourceReceiver :=
  Grid.DirectedConvention.BeingConvention.BeingCoarsening.id sourceReceiverGrid

/-- A legal supplied reading: clock-source welds are unmarked and receiver
    welds are marked.  Neither classification is recovered from the grid. -/
def sourceReceiverReading : sourceReceiverGrid.SentienceReading where
  sentient w := w.agent = SourceReceiver.receiver

def sourceReceiverDeed : sourceReceiverGrid.Weld :=
  ⟨SourceReceiver.clock, (), ()⟩

def sourceReceiverReception : sourceReceiverGrid.Weld :=
  ⟨SourceReceiver.receiver, (), ()⟩

def sourceReceiverBefore : Config Nat :=
  { tendency := 5 }

/-- Under the named reading and identity coarsening, an unmarked clock-source
    deed lands at a marked receiver's actual weld and drops the receiver-side
    carried tendency from `5` to the live share `1`. -/
theorem insentient_source_shareDropLanding :
    ¬ sourceReceiverCoarsening.SentientTag sourceReceiverReading
        SourceReceiver.clock ∧
      sourceReceiverCoarsening.SentientTag sourceReceiverReading
        SourceReceiver.receiver ∧
      Grid.DirectedConvention.LandsWithShareDrop sourceReceiverGrid
        sourceReceiverBefore sourceReceiverDeed sourceReceiverReception := by
  constructor
  · rintro ⟨w, ⟨_hactual, hmarked⟩, hfiber⟩
    change w.agent = SourceReceiver.receiver at hmarked
    change w.agent = SourceReceiver.clock at hfiber
    rw [hfiber] at hmarked
    cases hmarked
  · constructor
    · exact ⟨sourceReceiverReception, ⟨rfl, rfl⟩, rfl⟩
    · constructor
      · exact ⟨⟨rfl, rfl⟩, rfl⟩
      · dsimp [Grid.IsShareDrop, Grid.share, sourceReceiverGrid,
          sourceReceiverBefore, sourceReceiverReception]
        constructor
        · show (1 : Nat) ≤ 5
          decide
        · show ¬ (5 : Nat) ≤ 1
          decide

/- --------------------------------------------------------------------------
   Third concrete display — backsliding in one grid

   A single being answers both calls. The gentle call drops to the pole-class;
   the harsh call later carries live share again. Nothing in the grid stores
   the prior drop as an attainment.
-------------------------------------------------------------------------- -/

inductive Cue
  | gentle
  | harsh

def backslideGrid : Grid Nat where
  Being      := Unit
  Call       := Cue
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ c _ :=
    match c with
    | .gentle => 0
    | .harsh => 5
  conditions _ _ := True

/- --------------------------------------------------------------------------
   Fourth concrete display — grading is weld-side, not field-residue side

   The two actual welds share the same call-response residue while receiving
   different shares. The event residue alone therefore cannot carry the grade.
-------------------------------------------------------------------------- -/

inductive GradingCollisionBeing
  | left
  | right

def gradingCollisionGrid : Grid Nat where
  Being      := GradingCollisionBeing
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade b _ _ :=
    match b with
    | .left => 5
    | .right => 0
  conditions _ _ := True

def gradingCollisionLeft : gradingCollisionGrid.Weld :=
  ⟨GradingCollisionBeing.left, (), ()⟩

def gradingCollisionRight : gradingCollisionGrid.Weld :=
  ⟨GradingCollisionBeing.right, (), ()⟩

/- --------------------------------------------------------------------------
   Fifth concrete display — share collision across agents

   Two distinct agents receive the same live share, so their re-pitched
   configurations coincide and under-determine who acted.
-------------------------------------------------------------------------- -/

inductive ShareCollisionBeing
  | left
  | right

def shareCollisionGrid : Grid Nat where
  Being      := ShareCollisionBeing
  Call       := Unit
  Response   := Unit
  respondsTo _ _ := some ()
  grade _ _ _ := 3
  conditions _ _ := True

/- `clockGrid` is a genuine, finite, computable term of type `Grid Nat` —
    direct evidence that "a model of the theory" is a buildable Lean
    object, and that facts about a concrete instance are provable at
    `rfl`-level once the instance is fixed. The prudential-privilege
    construction this scaffolding anticipated is carried out in
    `Identification/Ownership.lean`, under
    `Grid.DirectedConvention.PrudentialPrivilegeNegative`: an actual
    `ReceptionPair`, the relevant `Config`/`rePitch` steps, and a named
    `PrudentialPrivilege` recovery proposition are fixed there and the
    proposition is shown to fail. This section checks only that the model
    scaffolding does not get in the way. -/

end Preview

end WAA
