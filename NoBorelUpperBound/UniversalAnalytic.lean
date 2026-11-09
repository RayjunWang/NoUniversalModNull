import NoBorelUpperBound.TreeSpace

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.Trees

def codeIndex (s t : Node) : ℕ := Encodable.encode (s, t)

/-- A universal projection of a closed relation, with a Baire-space code. -/
def Universal (c x : Baire) : Prop :=
  ∃ y : Baire, ∀ n, c (codeIndex (branchPrefix x n) (branchPrefix y n)) = 0

def graphCode (f : Baire → Baire) (k : ℕ) : ℕ :=
  match Encodable.decode (α := Node × Node) k with
  | none => 1
  | some (s, t) =>
    if ∃ a : Baire, branchPrefix (f a) s.length = s ∧ branchPrefix a t.length = t then 0 else 1

@[simp] theorem graphCode_index_eq_zero (f : Baire → Baire) (s t : Node) :
    graphCode f (codeIndex s t) = 0 ↔
      ∃ a : Baire, branchPrefix (f a) s.length = s ∧ branchPrefix a t.length = t := by
  simp [graphCode, codeIndex]

theorem tendsto_of_prefix_agreement (u : ℕ → Baire) (x : Baire)
    (h : ∀ n, branchPrefix (u n) n = branchPrefix x n) : Tendsto u atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have heq : ∀ᶠ n in atTop, u n i = x i := by
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    exact congrFun (List.ofFn_injective (h n)) ⟨i, by omega⟩
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

theorem universal_graphCode_iff (f : Baire → Baire) (hf : Continuous f) (x : Baire) :
    Universal (graphCode f) x ↔ x ∈ range f := by
  constructor
  · rintro ⟨y, hy⟩
    have hex (n : ℕ) : ∃ a : Baire,
        branchPrefix (f a) n = branchPrefix x n ∧ branchPrefix a n = branchPrefix y n := by
      simpa only [graphCode_index_eq_zero, length_branchPrefix] using hy n
    choose a ha hb using hex
    have h₁ := tendsto_of_prefix_agreement a y hb
    have h₂ := tendsto_of_prefix_agreement (fun n => f (a n)) x ha
    exact ⟨y, tendsto_nhds_unique (hf.tendsto y |>.comp h₁) h₂⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y, fun n => ?_⟩
    apply (graphCode_index_eq_zero _ _ _).mpr
    simpa only [length_branchPrefix] using (show ∃ a : Baire,
      branchPrefix (f a) n = branchPrefix (f y) n ∧ branchPrefix a n = branchPrefix y n from
        ⟨y, rfl, rfl⟩)

theorem exists_universal_code {s : Set Baire} (hs : AnalyticSet s) :
    ∃ c : Baire, ∀ x, Universal c x ↔ x ∈ s := by
  rw [AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, heq⟩
  · refine ⟨fun _ => 1, fun x => ?_⟩
    constructor
    · rintro ⟨y, hy⟩
      have h := hy 0
      norm_num at h
    · exact False.elim
  · exact ⟨graphCode f, fun x => by rw [universal_graphCode_iff f hf x, heq]⟩

/-- The universal analytic relation cannot itself be Borel, by diagonalization. -/
theorem not_borel_universal :
    ¬ @MeasurableSet (Baire × Baire) (borel (Baire × Baire))
      {p | Universal p.1 p.2} := by
  letI : MeasurableSpace Baire := borel Baire
  letI : BorelSpace Baire := ⟨rfl⟩
  intro h
  have hu : MeasurableSet {p : Baire × Baire | Universal p.1 p.2} := by
    have heq : (inferInstance : MeasurableSpace (Baire × Baire)) = borel (Baire × Baire) :=
      BorelSpace.measurable_eq
    rwa [← heq] at h
  have hd : MeasurableSet {x : Baire | ¬ Universal x x} :=
    hu.compl.preimage ((continuous_id.prodMk continuous_id).measurable)
  obtain ⟨c, hc⟩ := exists_universal_code hd.analyticSet
  have hcc := hc c
  change Universal c c ↔ ¬ Universal c c at hcc
  exact iff_not_self hcc

end NoBorelUpperBoundFSigma.Trees
