import Definitions.Def_NoBorelUpperBound20261101
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.L1Coordinates
universe u v

abbrev L1 (I : Type u) := lp (fun _ : I => ℝ) 1
abbrev MatrixL1 (I : Type u) (J : Type v) := L1 (I × J)
variable {I : Type u} {J : Type v}

theorem summable_norm (x : L1 I) : Summable (fun i => ‖x i‖) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

theorem norm_eq_tsum (x : L1 I) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

def restrict (e : I → J) (he : Function.Injective e) (x : L1 J) : L1 I :=
  ⟨fun i => x (e i), memℓp_gen (by
    simpa using (summable_norm x).comp_injective he)⟩

@[simp] theorem restrict_apply (e : I → J) (he : Function.Injective e) (x : L1 J) (i : I) :
    restrict e he x i = x (e i) := rfl

theorem norm_restrict_le (e : I → J) (he : Function.Injective e) (x : L1 J) :
    ‖restrict e he x‖ ≤ ‖x‖ := by
  classical
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg x)
  intro s
  have hsum : ∑ i ∈ s, ‖x (e i)‖ ^ (1 : ℝ≥0∞).toReal =
      ∑ j ∈ s.image e, ‖x j‖ ^ (1 : ℝ≥0∞).toReal := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => he h
  change ∑ i ∈ s, ‖x (e i)‖ ^ (1 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (1 : ℝ≥0∞).toReal
  rw [hsum]
  exact lp.sum_rpow_le_norm_rpow (by norm_num) x (s.image e)

def restrictCLM (e : I → J) (he : Function.Injective e) : L1 J →L[ℝ] L1 I :=
  ({ toFun := restrict e he
     map_add' := by intro x y; ext i; rfl
     map_smul' := by intro c x; ext i; rfl } : L1 J →ₗ[ℝ] L1 I).mkContinuous 1
    (by intro x; simpa using norm_restrict_le e he x)

@[simp] theorem restrictCLM_apply (e : I → J) (he : Function.Injective e) (x : L1 J) (i : I) :
    restrictCLM e he x i = x (e i) := rfl

def reindex {K : Type*} (e : I ≃ K) : L1 I ≃ₗᵢ[ℝ] L1 K where
  toFun := restrict e.symm e.symm.injective
  invFun := restrict e e.injective
  left_inv x := by ext i; simp
  right_inv x := by ext j; simp
  map_add' x y := by ext j; rfl
  map_smul' a x := by ext j; rfl
  norm_map' x := by
    apply le_antisymm (norm_restrict_le _ _ _)
    have h := norm_restrict_le e e.injective (restrict e.symm e.symm.injective x)
    have he : restrict e e.injective (restrict e.symm e.symm.injective x) = x := by ext i; simp
    rwa [he] at h

@[simp] theorem reindex_apply {K : Type*} (e : I ≃ K) (x : L1 I) (k : K) :
    reindex e x k = x (e.symm k) := rfl

def row (i : I) : MatrixL1 I J →L[ℝ] L1 J :=
  restrictCLM (fun j => (i, j)) (fun _ _ h => (Prod.mk.inj h).2)
def col (j : J) : MatrixL1 I J →L[ℝ] L1 I :=
  restrictCLM (fun i => (i, j)) (fun _ _ h => (Prod.mk.inj h).1)

@[simp] theorem row_apply (i : I) (x : MatrixL1 I J) (j : J) : row i x j = x (i, j) := rfl
@[simp] theorem col_apply (j : J) (x : MatrixL1 I J) (i : I) : col j x i = x (i, j) := rfl

theorem summable_norm_outer (x : L1 I) (y : L1 J) :
    Summable (fun p : I × J => ‖x p.1 * y p.2‖) := by
  simpa only [norm_mul] using
    (summable_norm x).mul_of_nonneg (summable_norm y)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

def outer (x : L1 I) (y : L1 J) : MatrixL1 I J :=
  ⟨fun p => x p.1 * y p.2, memℓp_gen (by simpa using summable_norm_outer x y)⟩

@[simp] theorem outer_apply (x : L1 I) (y : L1 J) (p : I × J) :
    outer x y p = x p.1 * y p.2 := rfl

theorem norm_outer (x : L1 I) (y : L1 J) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
  rw [norm_eq_tsum, norm_eq_tsum, norm_eq_tsum,
    (summable_norm x).tsum_mul_tsum (summable_norm y)
      ((summable_norm x).mul_of_nonneg (summable_norm y)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))]
  simp only [outer_apply, norm_mul]

@[simp] theorem outer_zero_left (y : L1 J) : outer (0 : L1 I) y = 0 := by
  ext p; change 0 * y p.2 = 0; exact zero_mul _
@[simp] theorem outer_zero_right (x : L1 I) : outer x (0 : L1 J) = 0 := by
  ext p; change x p.1 * 0 = 0; exact mul_zero _
@[simp] theorem outer_add_left (x x' : L1 I) (y : L1 J) :
    outer (x + x') y = outer x y + outer x' y := by
  ext p; change (x p.1 + x' p.1) * y p.2 = x p.1 * y p.2 + x' p.1 * y p.2; ring
@[simp] theorem outer_add_right (x : L1 I) (y y' : L1 J) :
    outer x (y + y') = outer x y + outer x y' := by
  ext p; change x p.1 * (y p.2 + y' p.2) = x p.1 * y p.2 + x p.1 * y' p.2; ring
@[simp] theorem outer_smul_left (c : ℝ) (x : L1 I) (y : L1 J) :
    outer (c • x) y = c • outer x y := by
  ext p; change (c * x p.1) * y p.2 = c * (x p.1 * y p.2); ring
@[simp] theorem outer_smul_right (c : ℝ) (x : L1 I) (y : L1 J) :
    outer x (c • y) = c • outer x y := by
  ext p; change x p.1 * (c * y p.2) = c * (x p.1 * y p.2); ring

def outerBilinear : L1 I →L[ℝ] L1 J →L[ℝ] MatrixL1 I J :=
  ({ toFun := fun x =>
       { toFun := outer x
         map_add' := outer_add_right x
         map_smul' := by intro c y; exact outer_smul_right c x y }
     map_add' := by intro x x'; apply LinearMap.ext; intro y; exact outer_add_left x x' y
     map_smul' := by intro c x; apply LinearMap.ext; intro y; exact outer_smul_left c x y } :
    L1 I →ₗ[ℝ] L1 J →ₗ[ℝ] MatrixL1 I J).mkContinuous₂ 1
      (by intro x y; simpa using (norm_outer x y).le)

@[simp] theorem outerBilinear_apply (x : L1 I) (y : L1 J) : outerBilinear x y = outer x y := rfl
theorem continuous_outer : Continuous (fun p : L1 I × L1 J => outer p.1 p.2) := by
  simpa only [Function.uncurry_def, outerBilinear_apply] using
    (outerBilinear (I := I) (J := J)).continuous₂

@[simp] theorem row_outer (i : I) (x : L1 I) (y : L1 J) :
    row i (outer x y) = (x i) • y := by ext j; simp
@[simp] theorem col_outer (j : J) (x : L1 I) (y : L1 J) :
    col j (outer x y) = (y j) • x := by ext i; simp [mul_comm]

def transpose : MatrixL1 I J ≃ₗᵢ[ℝ] MatrixL1 J I := reindex (Equiv.prodComm I J)

@[simp] theorem transpose_apply (R : MatrixL1 I J) (j : J) (i : I) :
    transpose R (j,i) = R (i,j) := rfl

@[simp] theorem transpose_outer (x : L1 I) (y : L1 J) : transpose (outer x y) = outer y x := by
  ext p
  rcases p with ⟨j,i⟩
  simp [transpose_apply, mul_comm]

theorem summable_norm_row (R : MatrixL1 I J) : Summable (fun i => ‖row i R‖) := by
  have h := (summable_prod_of_nonneg (fun p : I × J => norm_nonneg (R p))).mp (summable_norm R)
  simp_rw [norm_eq_tsum, row_apply]
  exact h.2

theorem tsum_norm_row (R : MatrixL1 I J) : (∑' i, ‖row i R‖) = ‖R‖ := by
  simp only [norm_eq_tsum, row_apply]
  exact (summable_norm R).tsum_prod.symm

theorem summable_norm_applyRight (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) :
    Summable (fun p : I × J => ‖D (row p.1 R) p.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun i => summable_norm (D (row i R)), ?_⟩
  have h : Summable (fun i => ‖D (row i R)‖) :=
    ((summable_norm_row R).mul_left ‖D‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun i => D.le_opNorm (row i R))
  simpa only [norm_eq_tsum] using h

def applyRight (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) : MatrixL1 I J :=
  ⟨fun p => D (row p.1 R) p.2, memℓp_gen (by simpa using summable_norm_applyRight D R)⟩

@[simp] theorem applyRight_apply (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) (i : I) (j : J) :
    applyRight D R (i,j) = D (row i R) j := rfl

theorem norm_applyRight_le (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) :
    ‖applyRight D R‖ ≤ ‖D‖ * ‖R‖ := by
  rw [norm_eq_tsum]
  change (∑' p : I × J, ‖D (row p.1 R) p.2‖) ≤ _
  rw [(summable_norm_applyRight D R).tsum_prod]
  change (∑' i, ∑' j, ‖D (row i R) j‖) ≤ _
  simp only [← norm_eq_tsum]
  calc
    (∑' i, ‖D (row i R)‖) ≤ ∑' i, ‖D‖ * ‖row i R‖ := by
      apply Summable.tsum_le_tsum (fun i => D.le_opNorm (row i R))
      · exact ((summable_norm_row R).mul_left ‖D‖).of_nonneg_of_le
          (fun _ => norm_nonneg _) (fun i => D.le_opNorm (row i R))
      · exact (summable_norm_row R).mul_left ‖D‖
    _ = ‖D‖ * ‖R‖ := by rw [tsum_mul_left, tsum_norm_row]

def mapRight (D : L1 J →L[ℝ] L1 J) : MatrixL1 I J →L[ℝ] MatrixL1 I J :=
  ({ toFun := applyRight D
     map_add' := by
       intro R Q; ext p
       change D (row p.1 (R+Q)) p.2 = D (row p.1 R) p.2 + D (row p.1 Q) p.2
       rw [map_add, map_add]
       rfl
     map_smul' := by intro c R; ext p; simp [applyRight] } :
    MatrixL1 I J →ₗ[ℝ] MatrixL1 I J).mkContinuous ‖D‖ (norm_applyRight_le D)

@[simp] theorem mapRight_apply (D : L1 J →L[ℝ] L1 J) (R : MatrixL1 I J) (i : I) (j : J) :
    mapRight D R (i,j) = D (row i R) j := rfl

@[simp] theorem mapRight_outer (D : L1 J →L[ℝ] L1 J) (x : L1 I) (y : L1 J) :
    mapRight D (outer x y) = outer x (D y) := by
  ext p
  rcases p with ⟨i,j⟩
  simp [mapRight_apply, row_outer]

def mapLeft (D : L1 I →L[ℝ] L1 I) : MatrixL1 I J →L[ℝ] MatrixL1 I J :=
  (transpose (I := I) (J := J)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mapRight (I := J) D).comp
      (transpose (I := I) (J := J)).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem mapLeft_apply (D : L1 I →L[ℝ] L1 I) (R : MatrixL1 I J) (i : I) (j : J) :
    mapLeft D R (i,j) = D (col j R) i := rfl

@[simp] theorem mapLeft_outer (D : L1 I →L[ℝ] L1 I) (x : L1 I) (y : L1 J) :
    mapLeft D (outer x y) = outer (D x) y := by
  ext p
  rcases p with ⟨i,j⟩
  simp [mapLeft_apply, col_outer, mul_comm]

end NoBorelUpperBoundFSigma.L1Coordinates
