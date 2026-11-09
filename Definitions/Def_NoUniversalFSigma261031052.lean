import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.MetricSpace.Polish

/-!
# Definitions for Theorem 1.1 of arXiv:2610.31052

The topology on the real Hilbert space `RealL2` is its native norm topology.
The property of Baire is expressed using Mathlib's `BaireMeasurableSet`.
All Borel measurability assertions use the Borel sigma algebras of the
specified topologies explicitly.
-/

namespace NoUniversalFSigma

/-- The real Hilbert space of square-summable sequences, indexed by the naturals. -/
abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2

/-- A countable union of closed subsets of the given topological space. -/
def IsFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ s = ⋃ n, C n

/-- A binary relation whose graph is a countable union of closed sets. -/
def IsFSigmaRelation {X : Type*} [TopologicalSpace X] (E : X → X → Prop) : Prop :=
  IsFSigma {p : X × X | E p.1 p.2}

/-- A function is Baire measurable if every inverse image of an open set
has the property of Baire. This does not mean the Baire sigma algebra. -/
def IsBaireMeasurable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- Borel measurability for the specified domain and codomain topologies. -/
def IsBorelMeasurable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  @Measurable X Y (borel X) (borel Y) f

/-- A reduction preserves and reflects the two binary relations. -/
def IsReduction {X Y : Type*} (f : X → Y) (E : X → X → Prop)
    (F : Y → Y → Prop) : Prop :=
  ∀ x y, E x y ↔ F (f x) (f y)

/-- The coset equivalence relation induced by a real linear subspace of `RealL2`. -/
def CosetRelation (H : Submodule ℝ RealL2) (x y : RealL2) : Prop :=
  x - y ∈ H

/-- Universality among F-sigma equivalence relations on Polish spaces,
with respect to Borel reductions. -/
def IsUniversalFSigma {Y : Type} [TopologicalSpace Y] (F : Y → Y → Prop) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [PolishSpace X] (E : X → X → Prop),
    Equivalence E → IsFSigmaRelation E →
      ∃ f : X → Y, IsBorelMeasurable f ∧ IsReduction f E F

theorem cosetRelation_equivalence (H : Submodule ℝ RealL2) :
    Equivalence (CosetRelation H) := by
  constructor
  · intro x
    simpa [CosetRelation] using H.zero_mem
  · intro x y h
    simpa [CosetRelation, neg_sub] using H.neg_mem h
  · intro x y z hxy hyz
    simpa [CosetRelation, sub_add_sub_cancel] using H.add_mem hxy hyz

theorem isBorelMeasurable_isBaireMeasurable {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsBorelMeasurable f) : IsBaireMeasurable f := by
  letI : MeasurableSpace X := borel X
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace X := ⟨rfl⟩
  letI : BorelSpace Y := ⟨rfl⟩
  intro U hU
  exact (hf hU.measurableSet).baireMeasurableSet

end NoUniversalFSigma
