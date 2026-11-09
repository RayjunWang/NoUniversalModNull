import ModNullProof.CompactCosets
import ModNullProof.OrdinaryUnbounded

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

theorem compact_family_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ BorelReducible
      (CosetRelation compactGroup (compactSubgroup (tensorSubspace T))) F.rel := by
  obtain ⟨T,hT⟩ := source_family_unbounded F
  refine ⟨T,?_⟩
  rintro ⟨f,hf,hred⟩
  obtain ⟨g,hg,hgrel⟩ := source_reduces_compact T
  apply hT
  exact ⟨f ∘ g,hf.comp hg,fun x y => (hgrel x y).trans (hred (g x) (g y))⟩

end ModNullUniversality.CompactTensor
