import Definitions.Def_NoUniversalFSigma261031052
import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false

namespace NoBorelUpperBoundFSigma
universe u v

def IsBorelRelation {X : Type u} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  @MeasurableSet (X × X) (borel (X × X)) {p | E p.1 p.2}

def BorelReducible {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, NoUniversalFSigma.IsBorelMeasurable f ∧ NoUniversalFSigma.IsReduction f E F

def IsFSigmaUpperBound {Y : Type u} [TopologicalSpace Y] (F : Y → Y → Prop) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] (E : Setoid X),
    NoUniversalFSigma.IsFSigmaRelation E.r → BorelReducible E.r F

abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

def LinearCosetRelation (H : Submodule ℝ RealL1) (x y : RealL1) : Prop :=
  y - x ∈ H

end NoBorelUpperBoundFSigma
