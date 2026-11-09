import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.MetricSpace.Polish

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.BorelCodes

variable (G : Type*) [TopologicalSpace G] [SecondCountableTopology G]

/-- Countably many open sets, coded using a fixed countable topological basis. -/
def Code := (ℕ × ℕ × countableBasis G) → Bool

instance : TopologicalSpace (Code G) := inferInstanceAs (TopologicalSpace ((_ × _ × _) → Bool))
instance : PolishSpace (Code G) where
  toSecondCountableTopology := inferInstanceAs (SecondCountableTopology ((_ × _ × _) → Bool))
  toIsCompletelyMetrizableSpace := inferInstanceAs
    (IsCompletelyMetrizableSpace ((_ × _ × _) → Bool))
instance : MeasurableSpace (Code G) := borel (Code G)
instance : BorelSpace (Code G) := ⟨rfl⟩

variable {G}

def eligible (c : Code G) (g : G) (n j : ℕ) : Prop :=
  ∃ b : countableBasis G, c (n,j,b) = true ∧ g ∈ (b : Set G)

private theorem exists_candidate (c : Code G) (g : G) (n : ℕ) :
    ∃ j, eligible c g n j ∨ ¬ ∃ k, eligible c g n k := by
  by_cases h : ∃ j, eligible c g n j
  · obtain ⟨j,hj⟩ := h
    exact ⟨j,Or.inl hj⟩
  · exact ⟨0,Or.inr h⟩

def selected (c : Code G) (g : G) (n : ℕ) : ℕ := Nat.find (exists_candidate c g n)

theorem eligible_selected (c : Code G) (g : G) (n : ℕ)
    (h : ∃ j, eligible c g n j) : eligible c g n (selected c g n) := by
  exact (Nat.find_spec (exists_candidate c g n)).resolve_right (not_not.mpr h)

variable [MeasurableSpace G] [BorelSpace G]

theorem measurableSet_eligible (n j : ℕ) :
    MeasurableSet {p : Code G × G | eligible p.1 p.2 n j} := by
  have hb (b : countableBasis G) : MeasurableSet
      {p : Code G × G | p.1 (n,j,b) = true ∧ p.2 ∈ (b : Set G)} := by
    have hc : Measurable (fun c : Code G => c (n,j,b)) :=
      (show Continuous (fun c : Code G => c (n,j,b)) from continuous_apply _).measurable
    exact ((isClosed_discrete ({true} : Set Bool)).measurableSet.preimage
      (hc.comp measurable_fst)).inter
      ((isOpen_of_mem_countableBasis b.property).measurableSet.preimage measurable_snd)
  simpa only [eligible, setOf_exists] using MeasurableSet.iUnion hb

theorem measurable_selected (n : ℕ) :
    Measurable (fun p : Code G × G => selected p.1 p.2 n) := by
  apply measurable_find (fun p : Code G × G => exists_candidate p.1 p.2 n)
  intro j
  have hex : MeasurableSet {p : Code G × G | ∃ k, eligible p.1 p.2 n k} := by
    simpa only [setOf_exists] using
      MeasurableSet.iUnion (fun k => measurableSet_eligible (G := G) n k)
  exact (measurableSet_eligible n j).union hex.compl

variable {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]

def approximation (c : Code G) (g : G) (n : ℕ) : Y :=
  denseSeq Y (selected c g n)

def eval (c : Code G) (g : G) : Y :=
  limUnder atTop (fun n : ℕ => approximation c g n)

variable [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_approximation (n : ℕ) :
    Measurable (fun p : Code G × G => (approximation p.1 p.2 n : Y)) := by
  exact (measurable_of_countable (denseSeq Y)).comp (measurable_selected n)

theorem measurable_eval :
    Measurable (fun p : Code G × G => (eval p.1 p.2 : Y)) := by
  exact (StronglyMeasurable.limUnder
    (fun n : ℕ => (measurable_approximation (Y := Y) (G := G) n).stronglyMeasurable)).measurable

end NoBorelUpperBoundFSigma.BorelCodes
