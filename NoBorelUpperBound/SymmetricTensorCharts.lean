import NoBorelUpperBound.SymmetricTensor

noncomputable section
open Set Matrix
open scoped BigOperators

namespace NoBorelUpperBoundFSigma.SymmetricTensor
open L1Coordinates TensorAlgebra
universe u
variable {I : Type u}

def pivotD (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I)
    (R : MatrixL1 I I) : Matrix (Fin r) (Fin r) ℝ :=
  fun j i => D (row (rows i) R) (qs j)

def liftNumerator (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I)
    (R : MatrixL1 I I) : MatrixL1 I I :=
  ∑ i, ∑ j, (pivotD D rows qs R).adjugate i j • outer (row (rows i) R) (row (qs j) R)

theorem liftNumerator_mem_algebraicSpan (D : L1 I →L[ℝ] L1 I) {r : ℕ}
    (rows qs : Fin r → I) (R : MatrixL1 I I) : liftNumerator D rows qs R ∈ algebraicSpan := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (outer_mem _ _)

theorem continuous_pivotD (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I) :
    Continuous (pivotD D rows qs) :=
  continuous_pi fun j => continuous_pi fun i =>
    (lp.evalCLM ℝ (fun _ : I => ℝ) 1 (qs j)).continuous.comp
      (D.continuous.comp (row (rows i)).continuous)

theorem continuous_liftNumerator (D : L1 I →L[ℝ] L1 I) {r : ℕ} (rows qs : Fin r → I) :
    Continuous (liftNumerator D rows qs) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  apply Continuous.smul
  · exact (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_pivotD D rows qs).matrix_adjugate)
  · exact continuous_outer.comp ((row (rows i)).continuous.prodMk (row (qs j)).continuous)

/-- Closed reconstruction charts. Both matrix reconstruction and symmetry
are polynomial identities, so no closed-range assumption on D is used. -/
def imageChart (D : L1 I →L[ℝ] L1 I) (o : I) {r : ℕ} (rows qs : Fin r → I) (m : ℕ) :
    Set (ℝ × MatrixL1 I I) :=
  {p | (1 : ℝ)/(m+1) ≤ |(pivotD D rows qs p.2).det| ∧
    (pivotD D rows qs p.2).det • p.2 = mapLeft D (liftNumerator D rows qs p.2) ∧
    transpose (liftNumerator D rows qs p.2) = liftNumerator D rows qs p.2 ∧
    (pivotD D rows qs p.2).det * p.1 = liftNumerator D rows qs p.2 (o,o)}

theorem isClosed_imageChart (D : L1 I →L[ℝ] L1 I) (o : I) {r : ℕ}
    (rows qs : Fin r → I) (m : ℕ) : IsClosed (imageChart D o rows qs m) := by
  have hp : Continuous (fun p : ℝ × MatrixL1 I I => (pivotD D rows qs p.2).det) :=
    (continuous_pivotD D rows qs).matrix_det.comp continuous_snd
  have hl : Continuous (fun p : ℝ × MatrixL1 I I => liftNumerator D rows qs p.2) :=
    (continuous_liftNumerator D rows qs).comp continuous_snd
  apply IsClosed.inter (isClosed_le continuous_const hp.abs)
  apply IsClosed.inter (isClosed_eq (hp.smul continuous_snd) ((mapLeft D).continuous.comp hl))
  apply IsClosed.inter (isClosed_eq (transpose.continuous.comp hl) hl)
  exact isClosed_eq (hp.mul continuous_fst)
    ((lp.evalCLM ℝ (fun _ : I×I => ℝ) 1 (o,o)).continuous.comp hl)

theorem imageChart_subset_image (D : L1 I →L[ℝ] L1 I) (o : I) {r : ℕ}
    (rows qs : Fin r → I) (m : ℕ) : imageChart D o rows qs m ⊆ imageSubmodule D o := by
  rintro ⟨lam,R⟩ ⟨hd,hrec,hsym,hscalar⟩
  let d := (pivotD D rows qs R).det
  have hd0 : d ≠ 0 := abs_pos.mp ((by positivity : (0:ℝ)<1/(m+1)).trans_le hd)
  let K := d⁻¹ • liftNumerator D rows qs R
  have hK : K ∈ symmetricSpan := by
    apply mem_symmetricSpan_iff.mpr
    refine ⟨Submodule.smul_mem _ _ (liftNumerator_mem_algebraicSpan D rows qs R), ?_⟩
    change transpose (d⁻¹ • liftNumerator D rows qs R) = _
    rw [map_smul,hsym]
  refine ⟨K,hK,Prod.ext ?_ ?_⟩
  · change d⁻¹ * liftNumerator D rows qs R (o,o) = lam
    change d * lam = liftNumerator D rows qs R (o,o) at hscalar
    rw [← hscalar,← mul_assoc,inv_mul_cancel₀ hd0,one_mul]
  · change mapLeft D (d⁻¹ • liftNumerator D rows qs R) = R
    rw [map_smul,← hrec,smul_smul,inv_mul_cancel₀ hd0,one_smul]

abbrev ChartIndex (I : Type u) := Σ r : ℕ, (Fin r → I) × (Fin r → I) × ℕ

/-- Explicit infrastructure statement: the algebraic coverage argument is
the remaining premise; closedness of every actual chart is already proved. -/
theorem isFSigma_image_of_chart_coverage [Countable I]
    (D : L1 I →L[ℝ] L1 I) (o : I)
    (hcoverage : ∀ p ∈ imageSubmodule D o, ∃ r : ℕ, ∃ rows qs : Fin r → I,
      ∃ m : ℕ, p ∈ imageChart D o rows qs m) :
    NoUniversalFSigma.IsFSigma (imageSubmodule D o : Set (ℝ × MatrixL1 I I)) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat (Option (ChartIndex I))
  let C : Option (ChartIndex I) → Set (ℝ × MatrixL1 I I) := fun k =>
    match k with
    | none => ∅
    | some ⟨_,rows,qs,m⟩ => imageChart D o rows qs m
  refine ⟨fun n => C (e n), ?_, ?_⟩
  · intro n
    rcases h : e n with _ | ⟨r,rows,qs,m⟩
    · simpa only [h,C] using (isClosed_empty : IsClosed (∅ : Set (ℝ × MatrixL1 I I)))
    · simpa only [h,C] using isClosed_imageChart D o rows qs m
  · ext p
    constructor
    · intro hp
      obtain ⟨r,rows,qs,m,hm⟩ := hcoverage p hp
      obtain ⟨n,hn⟩ := he (some ⟨r,rows,qs,m⟩)
      exact mem_iUnion.mpr ⟨n,by simpa only [hn,C] using hm⟩
    · intro hp
      obtain ⟨n,hn⟩ := mem_iUnion.mp hp
      rcases h : e n with _ | ⟨r,rows,qs,m⟩
      · simpa only [h,C,mem_empty_iff_false] using hn
      · exact imageChart_subset_image D o rows qs m (by simpa only [h,C] using hn)

end NoBorelUpperBoundFSigma.SymmetricTensor
