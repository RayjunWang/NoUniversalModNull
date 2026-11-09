import ModNullProof.CompactFamily
import ModNullProof.ConullAssembly

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality

/-- Theorem 1.1: the fixed compact Haar family is unbounded on all conull sets. -/
theorem theorem1_1 :
    ∃ K : CompactMetrizableHaarGroup, IsAbelian K ∧
      ∃ H : WF → Subgroup K.Carrier, LowComplexityFamily K H ∧
        ∀ F : StandardBorelEquivalence, ∃ T : WF,
          ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
            ¬ BorelReducible
              (fun x y : C => CosetRelation K (H T) x.val y.val) F.rel := by
  refine ⟨CompactTensor.compactGroup,CompactTensor.compactGroup_abelian,
    CompactTensor.compactFamily,CompactTensor.compactFamily_lowComplexity,?_⟩
  exact conull_unbounded_of_unbounded CompactTensor.compactGroup CompactTensor.compactFamily
    CompactTensor.compactFamily_measurable CompactTensor.compactFamily_unbounded

end ModNullUniversality
