import ModNullProof.WeakTensorRank
import NoBorelUpperBound.SymmetricTensorImage

set_option autoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators

namespace ModNullUniversality.CompactTensor
open NoBorelUpperBoundFSigma.L1Coordinates
open NoBorelUpperBoundFSigma.SymmetricTensor
open NoBorelUpperBoundFSigma.TensorAlgebra

/-- The three reconstruction identities, without a lower determinant cutoff. -/
def ChartEquations (D : L1 S →L[ℝ] L1 S) (o : S) {r : ℕ}
    (rows qs : Fin r → S) (p : Space) : Prop :=
  (pivotD D rows qs p.2).det • p.2 = mapLeft D (liftNumerator D rows qs p.2) ∧
  transpose (liftNumerator D rows qs p.2) = liftNumerator D rows qs p.2 ∧
  (pivotD D rows qs p.2).det * p.1 = liftNumerator D rows qs p.2 (o,o)

/-- Every full-rank coordinate chart obeys the reconstruction identities. -/
def AllRankCharts (D : L1 S →L[ℝ] L1 S) (o : S) (p : Space) : Prop :=
  ∀ (r : ℕ) (rows qs : Fin r → S),
    RankLE r (coordinates p) → (pivotD D rows qs p.2).det ≠ 0 →
      ChartEquations D o rows qs p

/-- A nonzero D-pivot of the full coordinate rank selects an actual row basis. -/
theorem row_basis_of_rankLE_pivot (D : L1 S →L[ℝ] L1 S) {r : ℕ}
    (rows qs : Fin r → S) (R : MatrixL1 S S)
    (hR : RankLE r (coordinates (0,R))) (hdet : (pivotD D rows qs R).det ≠ 0) :
    LinearIndependent ℝ (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) ∧
    Submodule.span ℝ (range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R)) =
      rowSpace R := by
  classical
  let E : L1 S →ₗ[ℝ] (Fin r → ℝ) :=
    { toFun := fun v j => D v (qs j)
      map_add' := by intro v w; funext j; simp; rfl
      map_smul' := by intro c v; funext j; simp }
  have hpivot := Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hli : LinearIndependent ℝ
      (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R) :=
    LinearIndependent.of_comp E hpivot
  refine ⟨hli, ?_⟩
  letI := finiteDimensional_rowSpace_rankLE r R hR
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact row_mem_rowSpace R (rows t)
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact finrank_rowSpace_le_rankLE r R hR

/-- All full-rank charts of a genuine symmetric tensor image reconstruct it. -/
theorem chartEquations_of_mem_image (D : L1 S →L[ℝ] L1 S) (hD : Function.Injective D)
    (o : S) {p : Space} (hp : p ∈ imageSubmodule D o) {r : ℕ}
    (rows qs : Fin r → S) (hR : RankLE r (coordinates p))
    (hdet : (pivotD D rows qs p.2).det ≠ 0) : ChartEquations D o rows qs p := by
  classical
  obtain ⟨K,hK,rfl⟩ := hp
  let R := mapLeft D K
  let a : Fin r → L1 S := fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R
  have hKalg := symmetricSpan_le_algebraicSpan hK
  have hR0 : RankLE r (coordinates (0,R)) := hR
  have hspan := (row_basis_of_rankLE_pivot D rows qs R hR0 hdet).2
  have hcol (j : S) : NoBorelUpperBoundFSigma.L1Coordinates.col j K ∈
      Submodule.span ℝ (range a) := by
    change NoBorelUpperBoundFSigma.L1Coordinates.col j K ∈
      Submodule.span ℝ (range (fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) R))
    rw [hspan]
    have hc : NoBorelUpperBoundFSigma.L1Coordinates.col j K =
        NoBorelUpperBoundFSigma.L1Coordinates.row j K := by
      ext i
      exact symmetric_of_mem hK i j
    rw [hc]
    exact rowSpace_le_rowSpace_mapLeft D hD hKalg (row_mem_rowSpace K j)
  have hscaled : (pivotD D rows qs R).det • K = liftNumerator D rows qs R := by
    ext ij
    change (pivotD D rows qs R).det * K ij = liftNumerator D rows qs R ij
    rw [show ij = (ij.1,ij.2) from rfl,liftNumerator_apply]
    apply (reconstruction_from_image D a qs K hcol ij.1 ij.2).trans
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    change (a t ij.1) * ((pivotD D rows qs R).adjugate t s * R (qs s,ij.2)) = _
    change R (rows t,ij.1) * ((pivotD D rows qs R).adjugate t s * R (qs s,ij.2)) = _
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (pivotD D rows qs R).det • R = mapLeft D (liftNumerator D rows qs R)
    rw [← hscaled,map_smul]
  · change transpose (liftNumerator D rows qs R) = liftNumerator D rows qs R
    rw [← hscaled,map_smul,transpose_eq_of_mem_symmetricSpan hK]
  · have h := congrArg (lp.evalCLM ℝ (fun _ : S×S => ℝ) 1 (o,o)) hscaled
    simpa only [map_smul,smul_eq_mul] using h

theorem allRankCharts_of_mem_image (D : L1 S →L[ℝ] L1 S) (hD : Function.Injective D)
    (o : S) {p : Space} (hp : p ∈ imageSubmodule D o) : AllRankCharts D o p :=
  fun _ rows qs hR hdet => chartEquations_of_mem_image D hD o hp rows qs hR hdet

/-- On finite-rank matrices the universal rank-chart equations suffice for membership. -/
theorem mem_image_of_finiteRank_allRankCharts (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) {p : Space}
    (hfinite : ∃ r, RankLE r (coordinates p)) (hall : AllRankCharts D o p) :
    p ∈ imageSubmodule D o := by
  classical
  obtain ⟨b,hb⟩ := hfinite
  have hb0 : RankLE b (coordinates (0,p.2)) := hb
  letI := finiteDimensional_rowSpace_rankLE b p.2 hb0
  obtain ⟨r,rows,hli,hspan⟩ := exists_row_basis_of_finiteDimensional p.2
  let a : Fin r → L1 S := fun t => NoBorelUpperBoundFSigma.L1Coordinates.row (rows t) p.2
  have hliD : LinearIndependent ℝ (fun t i => D (a t) i) :=
    independent_coordinates (fun t => D (a t))
      (hli.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD))
  obtain ⟨qs,hdet⟩ := exists_coordinate_pivot (fun t i => D (a t) i) hliD
  have hrank : Module.finrank ℝ (rowSpace p.2) ≤ r := by
    rw [← hspan,finrank_span_eq_card hli,Fintype.card_fin]
  have hR0 := rankLE_of_finrank_rowSpace_le r p.2 hrank
  have hR : RankLE r (coordinates p) := hR0
  have hd : (pivotD D rows qs p.2).det ≠ 0 := hdet
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hd)
  apply imageChart_subset_image D o rows qs m
  exact ⟨hm.le,hall r rows qs hR hd⟩

/-- Finite coordinate rank plus universal chart equations characterize the tensor image. -/
theorem mem_image_iff_finiteRank_allRankCharts (D : L1 S →L[ℝ] L1 S)
    (hD : Function.Injective D) (o : S) (p : Space) :
    p ∈ imageSubmodule D o ↔
      (∃ r, RankLE r (coordinates p)) ∧ AllRankCharts D o p := by
  constructor
  · intro hp
    refine ⟨?_,allRankCharts_of_mem_image D hD o hp⟩
    obtain ⟨K,hK,hKp⟩ := hp
    have hRalg := mapLeft_mem_algebraicSpan D (symmetricSpan_le_algebraicSpan hK)
    obtain ⟨r,hr⟩ := exists_rankLE_of_mem_algebraicSpan hRalg
    refine ⟨r,?_⟩
    have hRp : mapLeft D K = p.2 := congrArg Prod.snd hKp
    rw [hRp] at hr
    exact hr
  · rintro ⟨hfinite,hall⟩
    exact mem_image_of_finiteRank_allRankCharts D hD o hfinite hall

end ModNullUniversality.CompactTensor
