import NoBorelUpperBound.L1Coordinates
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section
open Set Filter TopologicalSpace Topology
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.L1Coordinates
universe u

instance {I : Type u} [Countable I] : SeparableSpace (L1 I) := by
  classical
  let S : Submodule ℝ (L1 I) := Submodule.span ℝ (range (fun i : I => lp.single 1 i (1 : ℝ)))
  have hs : IsSeparable (S : Set (L1 I)) := (countable_range _).isSeparable.span
  have hd : closure (S : Set (L1 I)) = univ := by
    apply eq_univ_of_forall
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) x)
    apply Eventually.of_forall
    intro s
    apply subset_closure
    apply Submodule.sum_mem S
    intro i _
    have heq : (lp.single 1 i (x i) : L1 I) = (x i) • (lp.single 1 i (1 : ℝ) : L1 I) := by
      ext j
      by_cases h : j = i
      · subst j; simp
      · simp [lp.single_apply, h]
    rw [heq]
    exact S.smul_mem (x i) (Submodule.subset_span (mem_range_self i))
  have h := hs.closure
  rw [hd] at h
  exact isSeparable_univ_iff.mp h

end NoBorelUpperBoundFSigma.L1Coordinates
