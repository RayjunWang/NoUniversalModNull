import NoBorelUpperBound.UniversalAnalytic

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.Trees

@[simp] theorem take_branchPrefix (x : Baire) (n k : ℕ) :
    (branchPrefix x n).take k = branchPrefix x (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [branchPrefix]

def codeTree (c x : Baire) : TreeSpace :=
  ⟨fun s => decide (∀ k : Fin (s.length + 1),
      c (codeIndex (branchPrefix x k) (s.take k)) = 0), by
    intro s a hs
    apply decide_eq_true
    intro k
    have hprop : ∀ k : Fin ((s ++ [a]).length + 1),
        c (codeIndex (branchPrefix x k) ((s ++ [a]).take k)) = 0 := of_decide_eq_true hs
    have hk : (k : ℕ) ≤ s.length := by omega
    have h := hprop ⟨k, by simpa using Nat.lt.step k.isLt⟩
    simpa only [List.take_append_of_le_length hk] using h⟩

theorem codeTree_mem_iff (c x : Baire) (s : Node) :
    codeTree c x s = true ↔ ∀ k : Fin (s.length + 1),
      c (codeIndex (branchPrefix x k) (s.take k)) = 0 := by
  simp only [codeTree, decide_eq_true_eq]

theorem codeTree_hasBranch_iff (c x : Baire) : HasBranch (codeTree c x) ↔ Universal c x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => ?_⟩
    have h := (codeTree_mem_iff c x (branchPrefix y n)).mp (hy n)
      ⟨n, by simp⟩
    simpa using h
  · rintro ⟨y, hy⟩
    refine ⟨y, fun n => (codeTree_mem_iff c x (branchPrefix y n)).mpr ?_⟩
    intro k
    have hk : (k : ℕ) ≤ n := by
      have h := k.isLt
      simp only [length_branchPrefix] at h
      omega
    simpa only [take_branchPrefix, Nat.min_eq_left hk] using hy k

theorem continuous_variable_evaluation : Continuous (fun p : Baire × ℕ => p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have heq : ∀ᶠ q : Baire × ℕ in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have h : ContinuousAt (fun q : Baire × ℕ => q.1 p.2) p :=
    ((continuous_apply p.2).comp continuous_fst).continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [heq] with q hq
  rw [hq]

theorem continuous_codeTree : Continuous (fun p : Baire × Baire => codeTree p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro s
  apply (continuous_bool_rng true).mpr
  have heq : (fun p : Baire × Baire => decide (∀ k : Fin (s.length + 1),
      p.1 (codeIndex (branchPrefix p.2 k) (s.take k)) = 0)) ⁻¹' {true} =
      ⋂ k : Fin (s.length + 1),
        {p : Baire × Baire | p.1 (codeIndex (branchPrefix p.2 k) (s.take k)) = 0} := by
    ext p
    simp
  rw [heq]
  apply isClopen_iInter_of_finite
  intro k
  apply (isClopen_discrete {(0 : ℕ)}).preimage
  have hindex : Continuous (fun p : Baire × Baire => codeIndex (branchPrefix p.2 k) (s.take k)) :=
    (continuous_of_discreteTopology : Continuous (fun s' : Node => codeIndex s' (s.take k))).comp
      ((continuous_branchPrefix k).comp continuous_snd)
  simpa only [Function.comp_def] using
    continuous_variable_evaluation.comp (continuous_fst.prodMk hindex)

/-- Ill-founded trees, with the compact topology on their membership bits,
form a non-Borel set. This proof includes the universal analytic diagonal. -/
theorem not_borel_IF : ¬ @MeasurableSet TreeSpace (borel TreeSpace) IF := by
  intro h
  apply not_borel_universal
  have hm : @Measurable (Baire × Baire) TreeSpace (borel (Baire × Baire)) (borel TreeSpace)
      (fun p => codeTree p.1 p.2) := continuous_codeTree.borel_measurable
  have hpre := hm h
  convert hpre using 1
  ext p
  exact (codeTree_hasBranch_iff p.1 p.2).symm

end NoBorelUpperBoundFSigma.Trees
