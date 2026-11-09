import ModNullProof.Coordinates
import NoBorelUpperBound.Construction

set_option autoImplicit false
noncomputable section

namespace ModNullUniversality.CompactTensor

def oldTree (T : WF) : NoBorelUpperBoundFSigma.Trees.TreeSpace :=
  ⟨T.val.val,T.val.property⟩

def treeOperator (T : WF) :
    NoBorelUpperBoundFSigma.L1Coordinates.L1 S →L[ℝ]
      NoBorelUpperBoundFSigma.L1Coordinates.L1 S :=
  NoBorelUpperBoundFSigma.TreeOperators.operator (oldTree T)

theorem treeOperator_injective (T : WF) : Function.Injective (treeOperator T) := by
  apply NoBorelUpperBoundFSigma.TreeOperators.operator_injective_of_not_hasBranch (oldTree T)
  exact T.property

def tensorSubspace (T : WF) : Submodule ℝ Space :=
  NoBorelUpperBoundFSigma.SymmetricTensor.imageSubmodule (treeOperator T) []

def sourceRelation (T : WF) (x y : Space) : Prop := y-x ∈ tensorSubspace T

end ModNullUniversality.CompactTensor
