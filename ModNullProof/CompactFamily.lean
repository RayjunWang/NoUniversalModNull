import ModNullProof.CompactUnbounded
import ModNullProof.TensorCompact

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

def compactFamily (T : WF) : Subgroup compactGroup.Carrier :=
  compactSubgroup (tensorSubspace T)

theorem tensorSubspace_coordinate_complexity (T : WF) :
    ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (tensorSubspace T : Set Space) = A \ B :=
  image_coordinates_difference_ksigma (treeOperator T) (treeOperator_injective T) []

theorem compactFamily_lowComplexity : LowComplexityFamily compactGroup compactFamily :=
  compactSubgroup_lowComplexity tensorSubspace tensorSubspace_coordinate_complexity

theorem compactFamily_measurable (T : WF) :
    MeasurableSet (compactFamily T : Set compactGroup.Carrier) := by
  change MeasurableSet (compactSubgroup (tensorSubspace T) : Set Target)
  exact differenceFSigma_measurableSet
    (compactSubgroup_differenceFSigma (tensorSubspace T) (tensorSubspace_coordinate_complexity T))

theorem compactFamily_unbounded (F : StandardBorelEquivalence) :
    ∃ T : WF, ¬ BorelReducible (CosetRelation compactGroup (compactFamily T)) F.rel :=
  compact_family_unbounded F

end ModNullUniversality.CompactTensor
