import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
An explicit Borel coding of measurable real functions, using rapidly convergent
approximations from a fixed countable dense subset of L¹.  Codes themselves are
Baire space; every code has a jointly Borel interpretation (by pointwise limsup).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ModNullUniversality.AEPower

abbrev Code := ℕ → ℕ

local instance : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

section RealCodes

variable {T : Type*} [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T]
variable (μ : Measure T) [IsFiniteMeasure μ]

/-- A fixed dense sequence in real L¹. -/
noncomputable def centers : ℕ → T →₁[μ] ℝ :=
  TopologicalSpace.denseSeq (T →₁[μ] ℝ)

theorem dense_centers : DenseRange (centers μ) :=
  TopologicalSpace.denseRange_denseSeq _

theorem measurable_centers :
    Measurable (fun p : ℕ × T => centers μ p.1 p.2) :=
  measurable_from_prod_countable_right (fun j => L1.measurable_coeFn (centers μ j))

/-- All Baire codes are interpreted, whether or not their approximants converge. -/
noncomputable def realDecode (s : Code) (t : T) : ℝ :=
  (limsup (fun n => (centers μ (s n) t : EReal)) atTop).toReal

theorem measurable_realDecode :
    Measurable (fun p : Code × T => realDecode μ p.1 p.2) := by
  apply Measurable.ereal_toReal
  apply Measurable.limsup
  intro n
  have h : Measurable (fun p : Code × T => centers μ (p.1 n) p.2) :=
    (measurable_centers μ).comp (show Measurable (fun p : Code × T => (p.1 n, p.2)) by
      exact ((measurable_pi_apply n).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def] using
    measurable_coe_real_ereal.comp h

/-- Summable L¹ errors force the Borel interpretation to recover the given function a.e. -/
theorem realDecode_eq_ae_of_summable {s : Code} {a : T → ℝ} (ha : Measurable a)
    (hs : (∑' n, ∫⁻ t, edist (centers μ (s n) t) (a t) ∂μ) ≠ ∞) :
    realDecode μ s =ᵐ[μ] a := by
  have hm (n : ℕ) : Measurable (fun t => edist (centers μ (s n) t) (a t)) :=
    (L1.measurable_coeFn _).edist ha
  have ht : (∫⁻ t, ∑' n, edist (centers μ (s n) t) (a t) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
    exact hs
  filter_upwards [ae_lt_top (Measurable.tsum hm) ht] with t ht
  have hzero := ENNReal.tendsto_atTop_zero_of_tsum_ne_top ht.ne
  have hdist : Tendsto (fun n => dist (centers μ (s n) t) (a t)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, ← dist_edist] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hzero
  have hconv : Tendsto (fun n => centers μ (s n) t) atTop (𝓝 (a t)) :=
    tendsto_iff_dist_tendsto_zero.mpr hdist
  have he := (continuous_coe_real_ereal.tendsto (a t)).comp hconv
  change Tendsto (fun n => (centers μ (s n) t : EReal)) atTop (𝓝 (a t : EReal)) at he
  rw [realDecode, he.limsup_eq, EReal.toReal_coe]

/-- The error used in the least-index coding procedure. -/
noncomputable def approxError {X : Type*} (a : X × T → ℝ) (x : X) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ t, edist (centers μ j t) (a (x, t)) ∂μ

theorem measurable_approxError {X : Type*} [MeasurableSpace X]
    {a : X × T → ℝ} (ha : Measurable a) (j : ℕ) :
    Measurable (fun x => approxError μ a x j) := by
  exact (((L1.measurable_coeFn (centers μ j)).comp measurable_snd).edist ha).lintegral_prod_right

theorem exists_approxError_lt {X : Type*} {a : X × T → ℝ} (x : X)
    (ha : Integrable (fun t => a (x, t)) μ) (n : ℕ) :
    ∃ j, approxError μ a x j < (2⁻¹ : ℝ≥0∞) ^ n := by
  let b := ha.toL1 (fun t => a (x, t))
  obtain ⟨j, hj⟩ := (dense_centers μ).exists_dist_lt b
    (show 0 < (2⁻¹ : ℝ) ^ n by positivity)
  refine ⟨j, ?_⟩
  have he : approxError μ a x j = edist (centers μ j) b := by
    rw [L1.edist_def]
    apply lintegral_congr_ae
    filter_upwards [ha.coeFn_toL1] with t ht
    rw [ht]
  rw [he, edist_dist, dist_comm]
  have hε : ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) = (2⁻¹ : ℝ≥0∞) ^ n := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [← hε]
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hj

/-- Measurable rapidly converging codes for a jointly Borel integrable family. -/
theorem exists_measurable_realCode {X : Type*} [MeasurableSpace X]
    {a : X × T → ℝ} (ha : Measurable a)
    (hint : ∀ x, Integrable (fun t => a (x, t)) μ) :
    ∃ c : X → Code, Measurable c ∧
      ∀ x, realDecode μ (c x) =ᵐ[μ] (fun t => a (x, t)) := by
  classical
  have hex (x : X) (n : ℕ) : ∃ j, approxError μ a x j < (2⁻¹ : ℝ≥0∞) ^ n :=
    exists_approxError_lt μ x (hint x) n
  let c : X → Code := fun x n => Nat.find (hex x n)
  refine ⟨c, measurable_pi_lambda _ (fun n => ?_), fun x => ?_⟩
  · exact measurable_find (fun x => hex x n) (fun j =>
      measurableSet_lt (measurable_approxError μ ha j) measurable_const)
  · apply realDecode_eq_ae_of_summable μ
      (ha.comp (measurable_const.prodMk measurable_id))
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      (∑' n, ∫⁻ t, edist (centers μ (c x n) t) (a (x, t)) ∂μ) ≤
          ∑' n, (2⁻¹ : ℝ≥0∞) ^ n :=
        ENNReal.tsum_le_tsum (fun n => (Nat.find_spec (hex x n)).le)
      _ = 2 := ENNReal.tsum_geometric_two

end RealCodes

end ModNullUniversality.AEPower
