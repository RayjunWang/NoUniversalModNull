import NoBorelUpperBound.BaireContinuity
import NoBorelUpperBound.BorelEvaluator
import Definitions.Def_NoUniversalFSigma261031052

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.BorelCodes
universe u v

variable {G : Type u} [TopologicalSpace G] [SecondCountableTopology G]

/-- Encode an array of open tests by all basis sets contained in each test. -/
def codeOfOpenTests (U : ℕ → ℕ → Set G) : Code G :=
  fun q => decide ((q.2.2 : Set G) ⊆ U q.1 q.2.1)

theorem eligible_codeOfOpenTests_iff (U : ℕ → ℕ → Set G)
    (hU : ∀ n j, IsOpen (U n j)) (g : G) (n j : ℕ) :
    eligible (codeOfOpenTests U) g n j ↔ g ∈ U n j := by
  classical
  constructor
  · rintro ⟨b,hb,hg⟩
    have hbU : (b : Set G) ⊆ U n j := by
      simpa only [codeOfOpenTests,decide_eq_true_eq] using hb
    exact hbU hg
  · intro hg
    obtain ⟨b,hb,hgb,hbU⟩ :=
      (isBasis_countableBasis G).exists_subset_of_mem_open hg (hU n j)
    exact ⟨⟨b,hb⟩,by simpa only [codeOfOpenTests,decide_eq_true_eq] using hbU,hgb⟩

/-- The fixed Borel evaluator represents every Borel map outside a meager
set. This concerns agreement modulo category, so Borel ranks need not be
bounded by a common ordinal. -/
theorem exists_code_residual_eq
    [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : G → Y) (hf : Measurable f) :
    ∃ c : Code G, ∀ᶠ g in residual G, eval c g = f g := by
  letI := upgradeIsCompletelyMetrizable Y
  obtain ⟨U,hU,hag⟩ := NoBorelUpperBoundFSigma.exists_open_generic_approximation
    f hf (denseSeq Y) (denseRange_denseSeq Y)
    (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    (fun n => div_pos zero_lt_one (by positivity))
  refine ⟨codeOfOpenTests U, hag.mono ?_⟩
  intro g hg
  change limUnder atTop (fun n : ℕ => (approximation (codeOfOpenTests U) g n : Y)) = f g
  apply Filter.Tendsto.limUnder_eq
  apply NoBorelUpperBoundFSigma.tendsto_of_dist_lt_approximation _ _
    (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  apply (hg n).2
  apply (eligible_codeOfOpenTests_iff U hU g n _).mp
  apply eligible_selected
  obtain ⟨j,hj⟩ := (hg n).1
  exact ⟨j,(eligible_codeOfOpenTests_iff U hU g n j).mpr hj⟩

/-- Topological Borel-measurability version used by the mission definitions. -/
theorem exists_code_of_isBorelMeasurable
    [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : G → Y) (hf : NoUniversalFSigma.IsBorelMeasurable f) :
    ∃ c : Code G, ∀ᶠ g in residual G, eval c g = f g := by
  apply exists_code_residual_eq f
  unfold NoUniversalFSigma.IsBorelMeasurable at hf
  rwa [← BorelSpace.measurable_eq,← BorelSpace.measurable_eq] at hf

end NoBorelUpperBoundFSigma.BorelCodes
