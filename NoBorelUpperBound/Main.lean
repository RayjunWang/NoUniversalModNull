import NoBorelUpperBound.ConstructionFamily
import NoBorelUpperBound.CategoryTransferFinal

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

/-- A common upper bound has nonempty underlying space, since even the
one-point equivalence relation must reduce to it. -/
theorem nonempty_of_isFSigmaUpperBound {Y : Type u} [TopologicalSpace Y]
    {F : Y → Y → Prop} (hF : IsFSigmaUpperBound F) : Nonempty Y := by
  let E : Setoid Unit := ⟨fun _ _ => True,⟨fun _ => trivial,
    fun _ => trivial,fun _ _ => trivial⟩⟩
  have hE : NoUniversalFSigma.IsFSigmaRelation E.r := by
    refine ⟨fun _ => Set.univ,fun _ => isClosed_univ,?_⟩
    ext p
    simp [E]
  obtain ⟨f,_,_⟩ := hF Unit E hE
  exact ⟨f ()⟩

/-- The explicit tree construction contradicts a Borel common upper bound. -/
theorem not_isFSigmaUpperBound
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : IsBorelRelation F.r) : ¬ IsFSigmaUpperBound F.r := by
  intro hbound
  letI : MeasurableSpace Trees.TreeSpace := borel Trees.TreeSpace
  letI : BorelSpace Trees.TreeSpace := ⟨rfl⟩
  letI : MeasurableSpace Construction.G := borel Construction.G
  letI : BorelSpace Construction.G := ⟨rfl⟩
  letI : MeasurableSpace Construction.Axis := borel Construction.Axis
  letI : BorelSpace Construction.Axis := ⟨rfl⟩
  have hm := category_transfer Construction.family
    (fun n => (Construction.continuous_family n).measurable)
    Construction.continuous_family_fixed (fun _ => Construction.designated)
    measurable_const F hF
    (by
      intro T hT
      rw [Construction.generatedSubgroup_family]
      have hT' : ¬ Trees.HasBranch T := by
        simpa only [Construction.membershipSet_family,Trees.IF,mem_setOf_eq] using hT
      exact hbound Construction.G (Construction.cosetSetoid (TreeOperators.operator T))
        (Construction.isFSigma_cosetGraph _
          (TreeOperators.operator_injective_of_not_hasBranch T hT')))
  rw [Construction.membershipSet_family] at hm
  exact Trees.not_borel_IF hm

/-- Main Theorem 1: no Borel equivalence relation on a Polish space is an
upper bound under Borel reducibility for all F-sigma equivalence relations. -/
theorem theorem1 {Y : Type u} [TopologicalSpace Y] [PolishSpace Y] :
    ¬ ∃ F : Setoid Y, IsBorelRelation F.r ∧ IsFSigmaUpperBound F.r := by
  rintro ⟨F,hF,hbound⟩
  exact not_isFSigmaUpperBound F hF hbound

end NoBorelUpperBoundFSigma
