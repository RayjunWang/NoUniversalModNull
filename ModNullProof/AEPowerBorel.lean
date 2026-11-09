import ModNullProof.AEPowerRealCodes
import Definitions.Def_ModNullCore20261109
import Mathlib.MeasureTheory.Measure.Prod

/-!
An almost-everywhere power of a Borel equivalence relation, realized on Baire
space by explicit real-function codes.  The construction includes the Borel
parameter coding theorem, with no selection or representation assumptions.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ModNullUniversality.AEPower

section Target

variable (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y]

/-- A bounded real Borel embedding of any standard Borel space. -/
noncomputable def boundedEmbedding (y : Y) : ℝ :=
  Real.arctan (embeddingReal Y y)

theorem measurableEmbedding_boundedEmbedding : MeasurableEmbedding (boundedEmbedding Y) :=
  (Real.continuous_arctan.measurableEmbedding Real.arctan_injective).comp
    (measurableEmbedding_embeddingReal Y)

theorem norm_boundedEmbedding_le (y : Y) : ‖boundedEmbedding Y y‖ ≤ Real.pi / 2 := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

variable [Nonempty Y]

/-- A total Borel inverse, assigned an arbitrary value outside the embedded range. -/
noncomputable def boundedInverse : ℝ → Y :=
  (measurableEmbedding_boundedEmbedding Y).invFun

theorem measurable_boundedInverse : Measurable (boundedInverse Y) :=
  (measurableEmbedding_boundedEmbedding Y).measurable_invFun

@[simp] theorem boundedInverse_boundedEmbedding (y : Y) :
    boundedInverse Y (boundedEmbedding Y y) = y :=
  (measurableEmbedding_boundedEmbedding Y).leftInverse_invFun y

variable {T : Type*} [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T]
variable (μ : Measure T) [IsFiniteMeasure μ]

/-- The jointly Borel interpretation of Baire codes in the target space. -/
noncomputable def decode (s : Code) (t : T) : Y :=
  boundedInverse Y (realDecode μ s t)

theorem measurable_decode : Measurable (fun p : Code × T => decode Y μ p.1 p.2) :=
  (measurable_boundedInverse Y).comp (measurable_realDecode μ)

/-- Every jointly Borel family has measurable codes recovering all its sections a.e. -/
theorem exists_measurable_code {X : Type*} [MeasurableSpace X]
    {a : X × T → Y} (ha : Measurable a) :
    ∃ c : X → Code, Measurable c ∧
      ∀ x, decode Y μ (c x) =ᵐ[μ] (fun t => a (x, t)) := by
  have hb : Measurable (fun p => boundedEmbedding Y (a p)) :=
    (measurableEmbedding_boundedEmbedding Y).measurable.comp ha
  have hint (x : X) : Integrable (fun t => boundedEmbedding Y (a (x, t))) μ := by
    exact (integrable_const (Real.pi / 2)).mono'
      ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun t => norm_boundedEmbedding_le Y _)
  obtain ⟨c, hc, hcx⟩ := exists_measurable_realCode μ hb hint
  refine ⟨c, hc, fun x => ?_⟩
  filter_upwards [hcx x] with t ht
  simp only [decode, ht, boundedInverse_boundedEmbedding]

end Target

section Relation

variable {T : Type} [MeasurableSpace T] [MeasurableSpace.CountablyGenerated T]
variable (μ : Measure T) [IsFiniteMeasure μ]
variable (F : StandardBorelEquivalence) [Nonempty F.Carrier]

/-- Almost-everywhere pointwise equivalence, on the fixed Baire coding space. -/
noncomputable def powerRelation (s r : Code) : Prop :=
  ∀ᵐ t ∂μ, F.rel (decode F.Carrier μ s t) (decode F.Carrier μ r t)

theorem powerRelation_equivalence : Equivalence (powerRelation μ F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact Eventually.of_forall fun t => F.equivalence.refl _
  · intro s r h
    exact h.mono fun t ht => F.equivalence.symm ht
  · intro s r u hsr hru
    filter_upwards [hsr, hru] with t hsr hru
    exact F.equivalence.trans hsr hru

theorem measurableSet_powerRelation :
    MeasurableSet {p : Code × Code | powerRelation μ F p.1 p.2} := by
  have hp₁ : Measurable (fun p : (Code × Code) × T => (p.1.1, p.2)) :=
    ((measurable_fst : Measurable (Prod.fst : Code × Code → Code)).comp
      measurable_fst).prodMk measurable_snd
  have hp₂ : Measurable (fun p : (Code × Code) × T => (p.1.2, p.2)) :=
    ((measurable_snd : Measurable (Prod.snd : Code × Code → Code)).comp
      measurable_fst).prodMk measurable_snd
  have hm₁ : Measurable (fun p : (Code × Code) × T => decode F.Carrier μ p.1.1 p.2) := by
    simpa only [Function.comp_def] using (measurable_decode F.Carrier μ).comp hp₁
  have hm₂ : Measurable (fun p : (Code × Code) × T => decode F.Carrier μ p.1.2 p.2) := by
    simpa only [Function.comp_def] using (measurable_decode F.Carrier μ).comp hp₂
  have hs : MeasurableSet {p : (Code × Code) × T |
      ¬F.rel (decode F.Carrier μ p.1.1 p.2) (decode F.Carrier μ p.1.2 p.2)} :=
    (F.measurable_graph.preimage (hm₁.prodMk hm₂)).compl
  have hμ := measurable_measure_prodMk_left (ν := μ) hs
  simpa only [powerRelation, ae_iff] using measurableSet_eq_fun hμ measurable_const

/-- The fixed standard Borel target for the almost-everywhere power. -/
noncomputable def power : StandardBorelEquivalence where
  Carrier := Code
  rel := powerRelation μ F
  equivalence := powerRelation_equivalence μ F
  measurable_graph := measurableSet_powerRelation μ F

end Relation

end ModNullUniversality.AEPower
