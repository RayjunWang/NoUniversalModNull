import ModNullProof.CompactEmbedding
import ModNullProof.BorelComplexity
import ModNullProof.TensorFamily

set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace

namespace ModNullUniversality.CompactTensor

def push (x : Space) : Target := Multiplicative.ofAdd (sourceEmbedding x)

theorem continuous_push : Continuous push := continuous_sourceEmbedding

theorem push_injective : Function.Injective push := sourceEmbedding_injective

def compactSubgroup (H : Submodule ℝ Space) : Subgroup Target :=
  H.toAddSubgroup.toSubgroup.map sourceEmbedding.toMultiplicative

theorem compactSubgroup_carrier (H : Submodule ℝ Space) :
    (compactSubgroup H : Set Target) = push '' (H : Set Space) := by
  ext y
  rfl

theorem coset_push_iff (H : Submodule ℝ Space) (x y : Space) :
    CosetRelation compactGroup (compactSubgroup H) (push x) (push y) ↔ y-x ∈ H := by
  change -sourceEmbedding x + sourceEmbedding y ∈
    (H.toAddSubgroup.map sourceEmbedding : Set AddTarget) ↔ y-x ∈ H
  rw [← sub_eq_neg_add,← map_sub]
  exact AddSubgroup.mem_map_iff_mem sourceEmbedding_injective

theorem source_reduces_compact (T : WF) :
    BorelReducible (sourceRelation T)
      (CosetRelation compactGroup (compactSubgroup (tensorSubspace T))) := by
  exact ⟨push,continuous_push.measurable,fun x y => (coset_push_iff _ x y).symm⟩

def ambientPush (x : Ambient) : Target := Multiplicative.ofAdd (embedding x)

theorem continuous_ambientPush : Continuous ambientPush := continuous_embedding

theorem ambientPush_injective : Function.Injective ambientPush := embedding_injective

theorem compactSubgroup_differenceFSigma (H : Submodule ℝ Space)
    (hH : ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (H : Set Space) = A \ B) :
    DifferenceFSigma (compactSubgroup H : Set Target) := by
  obtain ⟨A,B,hA,hB,hEq⟩ := hH
  have heq : (compactSubgroup H : Set Target) = ambientPush '' (A \ B) := by
    rw [← hEq,compactSubgroup_carrier,image_image]
    rfl
  rw [heq]
  exact differenceFSigma_image_of_ksigma ambientPush continuous_ambientPush
    ambientPush_injective A B hA hB

theorem compactSubgroup_graph_differenceFSigma (H : Submodule ℝ Space)
    (hH : DifferenceFSigma (compactSubgroup H : Set Target)) :
    DifferenceFSigma {p : Target × Target |
      CosetRelation compactGroup (compactSubgroup H) p.1 p.2} := by
  exact differenceFSigma_preimage hH (fun p : Target × Target => p.1⁻¹ * p.2)
    (continuous_fst.inv.mul continuous_snd)

theorem compactSubgroup_lowComplexity (H : WF → Submodule ℝ Space)
    (hH : ∀ T, ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (H T : Set Space) = A \ B) :
    LowComplexityFamily compactGroup (fun T => compactSubgroup (H T)) := by
  have hd (T : WF) := compactSubgroup_differenceFSigma (H T) (hH T)
  have hg (T : WF) := compactSubgroup_graph_differenceFSigma (H T) (hd T)
  exact ⟨fun T => differenceFSigma_isDelta3 (hd T),
    fun T => differenceFSigma_isDelta3 (hg T),hg⟩

end ModNullUniversality.CompactTensor
