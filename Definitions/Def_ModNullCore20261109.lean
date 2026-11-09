import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.GDelta.Basic
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace ModNullUniversality

def IsFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ s = ⋃ n, C n

def IsKSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsCompact (C n)) ∧ s = ⋃ n, C n

def IsSigma3 {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsGδ (C n)) ∧ s = ⋃ n, C n

def IsPi3 {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ C : ℕ → Set X, (∀ n, IsFSigma (C n)) ∧ s = ⋂ n, C n

def IsDelta3 {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  IsSigma3 s ∧ IsPi3 s

def DifferenceFSigma {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ A B : Set X, IsFSigma A ∧ IsFSigma B ∧ s = A \ B

def BorelReducible {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x y, E x y ↔ F (f x) (f y)

structure StandardBorelEquivalence where
  Carrier : Type
  [measurable : MeasurableSpace Carrier]
  [standard : StandardBorelSpace Carrier]
  rel : Carrier → Carrier → Prop
  equivalence : Equivalence rel
  measurable_graph : MeasurableSet {p : Carrier × Carrier | rel p.1 p.2}

attribute [instance] StandardBorelEquivalence.measurable StandardBorelEquivalence.standard

abbrev Node := List ℕ

def PrefixClosed (T : Node → Bool) : Prop :=
  ∀ s n, T (s ++ [n]) = true → T s = true

def TreeSpace := {T : Node → Bool // PrefixClosed T}

def HasBranch (T : TreeSpace) : Prop :=
  ∃ b : ℕ → ℕ, ∀ n, T.val (List.ofFn (fun i : Fin n => b i)) = true

def WF := {T : TreeSpace // ¬ HasBranch T}

def IsInvariant {X : Type*} (E : X → X → Prop) (C : Set X) : Prop :=
  ∀ x y, E x y → (x ∈ C ↔ y ∈ C)

def LInfinityRelation (x y : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n, |x n - y n| ≤ M

end ModNullUniversality
