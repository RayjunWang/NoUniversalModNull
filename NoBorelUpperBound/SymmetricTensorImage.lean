import NoBorelUpperBound.SymmetricTensorCharts
import NoBorelUpperBound.SymmetricTensorRank

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

theorem reconstruction_from_image {r : ℕ} (D : L1 I →L[ℝ] L1 I)
    (a : Fin r → L1 I) (qs : Fin r → I) (K : MatrixL1 I I)
    (hcol : ∀ j, L1Coordinates.col j K ∈ Submodule.span ℝ (range a)) (i j : I) :
    Matrix.det (fun s t => D (a t) (qs s)) * K (i,j) =
      (fun t => a t i) ⬝ᵥ
        ((Matrix.adjugate (fun s t => D (a t) (qs s))) *ᵥ
          (fun s => mapLeft D K (qs s,j))) := by
  classical
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hcol j)
  have heq (k : I) : ∑ t, c t * a t k = K (k,j) := by
    have h := congrArg (lp.evalCLM ℝ (fun _ : I => ℝ) 1 k) hc
    simpa only [map_sum,map_smul,smul_eq_mul] using h
  have hvec : (fun s => mapLeft D K (qs s,j)) =
      (fun s t => D (a t) (qs s)) *ᵥ c := by
    funext s
    change D (L1Coordinates.col j K) (qs s) = _
    rw [← hc,map_sum]
    change (lp.evalCLM ℝ (fun _ : I => ℝ) 1 (qs s)) (∑ t, D (c t • a t)) = _
    simp only [map_sum,map_smul,smul_eq_mul,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro t _
    change c t * D (a t) (qs s) = D (a t) (qs s) * c t
    ring
  rw [hvec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,
    Matrix.one_mulVec,dotProduct_smul]
  congr 1
  simpa only [dotProduct,mul_comm] using (heq i).symm

theorem liftNumerator_apply (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I)
    (R : MatrixL1 I I) (i j : I) :
    liftNumerator D rows qs R (i,j) =
      ∑ t, ∑ s, (pivotD D rows qs R).adjugate t s *
        (R (rows t,i) * R (qs s,j)) := by
  change (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (i,j)) (liftNumerator D rows qs R) = _
  simp only [liftNumerator,map_sum,map_smul,smul_eq_mul]
  rfl

/-- Actual finite-row reconstruction of every member of the symmetric image. -/
theorem exists_imageChart_of_mem (D : L1 I →L[ℝ] L1 I) (hD : Function.Injective D)
    (o : I) {p : ℝ × MatrixL1 I I} (hp : p ∈ imageSubmodule D o) :
    ∃ r : ℕ, ∃ rows qs : Fin r → I, ∃ m : ℕ, p ∈ imageChart D o rows qs m := by
  classical
  obtain ⟨K,hK,rfl⟩ := hp
  let R := mapLeft D K
  have hKalg := symmetricSpan_le_algebraicSpan hK
  have hRalg : R ∈ algebraicSpan := mapLeft_mem_algebraicSpan D hKalg
  obtain ⟨r,rows,hli,hspan⟩ := exists_row_basis hRalg
  let a : Fin r → L1 I := fun t => L1Coordinates.row (rows t) R
  have hcol (j : I) : L1Coordinates.col j K ∈ Submodule.span ℝ (range a) := by
    change L1Coordinates.col j K ∈ Submodule.span ℝ (range (fun t => L1Coordinates.row (rows t) R))
    rw [hspan]
    have hc : L1Coordinates.col j K = L1Coordinates.row j K := by
      ext i
      exact symmetric_of_mem hK i j
    rw [hc]
    exact rowSpace_le_rowSpace_mapLeft D hD hKalg (row_mem_rowSpace K j)
  have hliD : LinearIndependent ℝ (fun t i => D (a t) i) :=
    independent_coordinates (fun t => D (a t))
      (hli.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD))
  obtain ⟨qs,hdet⟩ := exists_coordinate_pivot (fun t i => D (a t) i) hliD
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
  have hd : (pivotD D rows qs R).det ≠ 0 := hdet
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hd)
  refine ⟨r,rows,qs,m,hm.le,?_,?_,?_⟩
  · change (pivotD D rows qs R).det • R = mapLeft D (liftNumerator D rows qs R)
    rw [← hscaled,map_smul]
  · change L1Coordinates.transpose (liftNumerator D rows qs R) = liftNumerator D rows qs R
    rw [← hscaled,map_smul,transpose_eq_of_mem_symmetricSpan hK]
  · have h := congrArg (lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (o,o)) hscaled
    simpa only [map_smul,smul_eq_mul] using h

/-- Lemma 3: injectivity alone makes the scalar-tagged symmetric finite
tensor image an F-sigma real linear subspace of R times the matrix l1 space. -/
theorem isFSigma_imageSubmodule [Countable I]
    (D : L1 I →L[ℝ] L1 I) (hD : Function.Injective D) (o : I) :
    NoUniversalFSigma.IsFSigma (imageSubmodule D o : Set (ℝ × MatrixL1 I I)) :=
  isFSigma_image_of_chart_coverage D o (fun _ hp => exists_imageChart_of_mem D hD o hp)

end NoBorelUpperBoundFSigma.SymmetricTensor
