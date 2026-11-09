import NoBorelUpperBound.CategoryProduct
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

/-- A Borel map admits a countable array of open dense-point tests which are
correct simultaneously outside a meager set. No uniform bound on Borel ranks
is required. -/
theorem exists_open_generic_approximation
    {G : Type u} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : G → Y) (hf : Measurable f) (y : ℕ → Y) (hy : DenseRange y)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ U : ℕ → ℕ → Set G, (∀ n j, IsOpen (U n j)) ∧
      ∀ᶠ g in residual G, ∀ n,
        (∃ j, g ∈ U n j) ∧ (∀ j, g ∈ U n j → dist (y j) (f g) < ε n) := by
  classical
  have htest (n j : ℕ) :
      ∃ U : Set G, IsOpen U ∧ {g | dist (y j) (f g) < ε n} =ᵇ U := by
    have hB : MeasurableSet {g | dist (y j) (f g) < ε n} := by
      have hO : IsOpen {q : Y | dist (y j) q < ε n} :=
        isOpen_lt (continuous_const.dist continuous_id) continuous_const
      exact hO.measurableSet.preimage hf
    exact hB.residualEq_isOpen
  choose U hU heq using htest
  refine ⟨U,hU,?_⟩
  have hag : ∀ᶠ g in residual G, ∀ n j,
      dist (y j) (f g) < ε n ↔ g ∈ U n j := by
    apply eventually_countable_forall.mpr
    intro n
    apply eventually_countable_forall.mpr
    intro j
    exact eventuallyEq_set.mp (heq n j)
  filter_upwards [hag] with g hg
  intro n
  refine ⟨?_,fun j hj => (hg n j).mpr hj⟩
  obtain ⟨j,hj⟩ := hy.exists_dist_lt (f g) (hε n)
  exact ⟨j,(hg n j).mp (by simpa only [dist_comm] using hj)⟩

/-- Distances bounded by a sequence tending to zero imply convergence. -/
theorem tendsto_of_dist_lt_approximation
    {Y : Type v} [PseudoMetricSpace Y] (s : ℕ → Y) (y : Y)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hs : ∀ n, dist (s n) y < ε n) : Tendsto s atTop (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he : ∀ᶠ n in atTop, ε n < δ := (tendsto_order.1 hε).2 δ hδ
  exact he.mono (fun n hn => lt_trans (hs n) hn)

end NoBorelUpperBoundFSigma
