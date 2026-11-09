import NoBorelUpperBound.Construction
import NoBorelUpperBound.IllFoundedNonBorel

noncomputable section
set_option maxHeartbeats 800000
open Set Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.Construction
open L1Coordinates SymmetricTensor TreeOperators Trees

abbrev Axis := Multiplicative A

instance : PolishSpace Axis := inferInstanceAs (PolishSpace A)

def graphHom (D : A →L[ℝ] A) : Axis →* Multiplicative X :=
  (graphMap D).toLinearMap.toAddMonoidHom.toMultiplicative

def family (n : ℕ) (T : TreeSpace) : Axis →* G :=
  if n = 0 then (CentralExtension.leftHom beta).comp (graphHom (operator T))
  else (CentralExtension.rightHom beta).comp (graphHom (operator T))

@[simp] theorem family_zero (T : TreeSpace) (a : Axis) :
    family 0 T a = CentralExtension.left beta (graphMap (operator T) a.toAdd) := by
  simp [family,graphHom,CentralExtension.leftHom]

theorem family_of_ne_zero {n : ℕ} (hn : n ≠ 0) (T : TreeSpace) (a : Axis) :
    family n T a = CentralExtension.right beta (graphMap (operator T) a.toAdd) := by
  simp [family,hn,graphHom,CentralExtension.rightHom]

theorem generatedSubgroup_family (T : TreeSpace) :
    GeneratedSubgroup family T = subgroup (operator T) := by
  apply congrArg Subgroup.closure
  ext g
  constructor
  · rintro ⟨_,⟨n,rfl⟩,a,rfl⟩
    by_cases hn : n = 0
    · subst n
      exact Or.inl ⟨a.toAdd,(family_zero T a).symm⟩
    · exact Or.inr ⟨a.toAdd,(family_of_ne_zero hn T a).symm⟩
  · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact mem_iUnion.mpr ⟨0,⟨Multiplicative.ofAdd a,family_zero T _⟩⟩
    · exact mem_iUnion.mpr ⟨1,⟨Multiplicative.ofAdd a,family_of_ne_zero (by decide) T _⟩⟩

theorem continuous_graph_family : Continuous (fun p : TreeSpace × Axis =>
    graphMap (operator p.1) p.2.toAdd) := by
  change Continuous (fun p : TreeSpace × Axis =>
    (p.2.toAdd,operator p.1.val p.2.toAdd))
  have h1 : Continuous (fun p : TreeSpace × Axis => (p.1.val : Code)) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun p : TreeSpace × Axis => p.2.toAdd) := continuous_snd
  have hp : Continuous (fun p : TreeSpace × Axis => (p.1.val,p.2.toAdd)) := h1.prodMk h2
  have ho := continuous_operator.comp hp
  exact h2.prodMk ho

theorem continuous_family (n : ℕ) :
    Continuous (fun p : TreeSpace × Axis => family n p.1 p.2) := by
  by_cases hn : n = 0
  · subst n
    simp only [family_zero]
    change Continuous (fun p : TreeSpace × Axis =>
      (graphMap (operator p.1) p.2.toAdd, (0 : X), (0 : C)))
    exact continuous_graph_family.prodMk (continuous_const.prodMk continuous_const)
  · simp only [family_of_ne_zero hn]
    change Continuous (fun p : TreeSpace × Axis =>
      ((0 : X), graphMap (operator p.1) p.2.toAdd, (0 : C)))
    exact continuous_const.prodMk (continuous_graph_family.prodMk continuous_const)

theorem continuous_family_fixed (n : ℕ) (T : TreeSpace) : Continuous (family n T) := by
  have hc : Continuous (fun a : Axis => (T,a)) := continuous_const.prodMk continuous_id
  have hf := (continuous_family n).comp hc
  exact hf

theorem membershipSet_family : MembershipSet family (fun _ => designated) = IF := by
  ext T
  change designated ∈ GeneratedSubgroup family T ↔ HasBranch T
  rw [generatedSubgroup_family,designated_mem_tree_iff]

end NoBorelUpperBoundFSigma.Construction
