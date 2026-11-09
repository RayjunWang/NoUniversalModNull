import ModNullProof.WeakTensorCoordinates
import ModNullProof.WeakTensorCharts
import ModNullProof.KSigmaComplexity

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped Topology BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor

theorem matrix_eq_iff_coordinates (A B : MatrixL1 S S) :
    A = B ↔ ∀ i j : S, A (i,j) = B (i,j) := by
  constructor
  · intro h i j
    exact congrArg (fun K : MatrixL1 S S => K (i,j)) h
  · intro h
    ext ij
    exact h ij.1 ij.2

theorem isGdelta_chartEquations (D : L1 S →L[ℝ] L1 S) (o : S) (M : ℝ)
    {r : ℕ} (rows qs : Fin r → S) :
    IsGδ {u : coordinateBall M | ChartEquations D o rows qs (ballSource M u)} := by
  have heq : {u : coordinateBall M | ChartEquations D o rows qs (ballSource M u)} =
      (⋂ i : S, ⋂ j : S, {u : coordinateBall M |
        (pivotD D rows qs (ballMatrix M u)).det * ballMatrix M u (i,j) =
          mapLeft D (liftNumerator D rows qs (ballMatrix M u)) (i,j)}) ∩
      (⋂ i : S, ⋂ j : S, {u : coordinateBall M |
        liftNumerator D rows qs (ballMatrix M u) (j,i) =
          liftNumerator D rows qs (ballMatrix M u) (i,j)}) ∩
      {u : coordinateBall M |
        (pivotD D rows qs (ballMatrix M u)).det * (ballSource M u).1 =
          liftNumerator D rows qs (ballMatrix M u) (o,o)} := by
    ext u
    simp only [mem_setOf_eq,ChartEquations,mem_inter_iff,mem_iInter,
      matrix_eq_iff_coordinates]
    exact and_assoc.symm
  rw [heq]
  apply IsGδ.inter
  · apply IsGδ.inter
    · exact IsGδ.iInter (fun i => IsGδ.iInter (fun j =>
        ((baireOne_pivotDet D M rows qs).mul (baireOne_matrix M (i,j))).isGdelta_eq
          (baireOne_mapLeft_lift D M rows qs i j)))
    · exact IsGδ.iInter (fun i => IsGδ.iInter (fun j =>
        (baireOne_lift D M rows qs j i).isGdelta_eq (baireOne_lift D M rows qs i j)))
  · exact ((baireOne_pivotDet D M rows qs).mul (baireOne_scalar M)).isGdelta_eq
      (baireOne_lift D M rows qs o o)

theorem isGdelta_allRankCharts (D : L1 S →L[ℝ] L1 S) (o : S) (M : ℝ) :
    IsGδ {u : coordinateBall M | AllRankCharts D o (ballSource M u)} := by
  have heq : {u : coordinateBall M | AllRankCharts D o (ballSource M u)} =
      ⋂ r : ℕ, ⋂ rows : Fin r → S, ⋂ qs : Fin r → S,
        ({u : coordinateBall M | ¬ RankLE r u.val} ∪
         {u : coordinateBall M | (pivotD D rows qs (ballMatrix M u)).det = 0} ∪
         {u : coordinateBall M | ChartEquations D o rows qs (ballSource M u)}) := by
    ext u
    simp only [mem_setOf_eq,AllRankCharts,coordinates_ballSource,mem_iInter,mem_union]
    change (∀ (r : ℕ) (rows qs : Fin r → S), RankLE r u.val →
      (pivotD D rows qs (ballMatrix M u)).det ≠ 0 →
        ChartEquations D o rows qs (ballSource M u)) ↔ _
    simp only [imp_iff_not_or,not_not,or_assoc]
  rw [heq]
  apply IsGδ.iInter
  intro r
  apply IsGδ.iInter
  intro rows
  apply IsGδ.iInter
  intro qs
  apply IsGδ.union
  · apply IsGδ.union
    · exact ((isClosed_rankLE r).preimage continuous_subtype_val).isOpen_compl.isGδ
    · exact (baireOne_pivotDet D M rows qs).isGdelta_zero
  · exact isGdelta_chartEquations D o M rows qs

/-- The countable union of bounded finite-rank coordinate sets. -/
def tensorEnvelope : Set Ambient :=
  ⋃ M : ℕ, ⋃ r : ℕ, coordinateBall M ∩ {u | RankLE r u}

/-- Every failed universal consistency test is removed, on every l1 ball. -/
def tensorObstruction (D : L1 S →L[ℝ] L1 S) (o : S) : Set Ambient :=
  ⋃ M : ℕ, Subtype.val '' {u : coordinateBall (M : ℝ) |
    ¬ AllRankCharts D o (ballSource M u)}

theorem isKSigma_tensorEnvelope : IsKSigma tensorEnvelope := by
  apply isKSigma_iUnion_nat
  intro M
  apply isKSigma_iUnion_nat
  intro r
  exact isKSigma_of_isCompact
    ((isCompact_coordinateBall M).inter_right (isClosed_rankLE r))

theorem isKSigma_tensorObstruction (D : L1 S →L[ℝ] L1 S) (o : S) :
    IsKSigma (tensorObstruction D o) := by
  apply isKSigma_iUnion_nat
  intro M
  exact isKSigma_subtype_image_of_isFSigma (isCompact_coordinateBall M)
    (isFSigma_compl_of_isGdelta (isGdelta_allRankCharts D o M))

theorem image_coordinates_eq_difference (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) :
    coordinates '' (imageSubmodule D o : Set Space) = tensorEnvelope \ tensorObstruction D o := by
  ext u
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨hfinite,hall⟩ := (mem_image_iff_finiteRank_allRankCharts D hD o p).mp hp
    obtain ⟨M,hM⟩ := exists_coordinateBall p
    obtain ⟨r,hr⟩ := hfinite
    refine ⟨mem_iUnion.mpr ⟨M,mem_iUnion.mpr ⟨r,hM,hr⟩⟩,?_⟩
    rintro hbad
    obtain ⟨N,v,hv,hvu⟩ := mem_iUnion.mp hbad
    have hpv : ballSource N v = p :=
      coordinates_injective ((coordinates_ballSource N v).trans hvu)
    exact hv (hpv.symm ▸ hall)
  · rintro ⟨henv,hnot⟩
    obtain ⟨M,henv⟩ := mem_iUnion.mp henv
    obtain ⟨r,hM,hr⟩ := mem_iUnion.mp henv
    let v : coordinateBall (M : ℝ) := ⟨u,hM⟩
    have hall : AllRankCharts D o (ballSource M v) := by
      by_contra hbad
      apply hnot
      exact mem_iUnion.mpr ⟨M,v,hbad,rfl⟩
    refine ⟨ballSource M v,?_,coordinates_ballSource M v⟩
    apply (mem_image_iff_finiteRank_allRankCharts D hD o _).mpr
    refine ⟨⟨r,?_⟩,hall⟩
    rw [coordinates_ballSource]
    exact hr

/-- Actual compact coordinate complexity of every scalar-tagged tensor subgroup. -/
theorem image_coordinates_difference_ksigma (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) :
    ∃ A B : Set Ambient, IsKSigma A ∧ IsKSigma B ∧
      coordinates '' (imageSubmodule D o : Set Space) = A \ B :=
  ⟨tensorEnvelope,tensorObstruction D o,isKSigma_tensorEnvelope,
    isKSigma_tensorObstruction D o,image_coordinates_eq_difference D hD o⟩

end ModNullUniversality.CompactTensor
