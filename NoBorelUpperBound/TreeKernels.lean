import NoBorelUpperBound.TreeSpace
import NoBorelUpperBound.TreeShift
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.TreeOperators
open L1Coordinates Trees

def branchSummand (b : Baire) (n : ℕ) : Space :=
  lp.single 1 (branchPrefix b n) ((1/2 : ℝ)^n)

theorem norm_branchSummand (b : Baire) (n : ℕ) : ‖branchSummand b n‖ = (1/2 : ℝ)^n := by
  rw [branchSummand,lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1/2 : ℝ)^n)]

theorem summable_branchSummand (b : Baire) : Summable (branchSummand b) := by
  apply Summable.of_norm
  simpa only [norm_branchSummand] using
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))

def branchVector (b : Baire) : Space := ∑' n, branchSummand b n

theorem branchVector_root (b : Baire) : branchVector b [] = 1 := by
  let ev : Space →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : Node => ℝ) 1 []
  change ev (∑' n, branchSummand b n) = _
  rw [ev.map_tsum (summable_branchSummand b),tsum_eq_single 0]
  · change (lp.single 1 (branchPrefix b 0) ((1/2 : ℝ)^0) : Space) [] = 1
    simp only [branchPrefix_zero,pow_zero,lp.single_apply_self]
  · intro n hn
    have hne : ([] : Node) ≠ branchPrefix b n := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_nil,length_branchPrefix] at hh
      exact hn hh.symm
    change (lp.single 1 (branchPrefix b n) ((1/2 : ℝ)^n) : Space) [] = 0
    exact lp.single_apply_ne _ _ _ hne

theorem shift_branchVector (T : TreeSpace) (b : Baire)
    (hb : ∀ n, T (branchPrefix b n) = true) :
    shift T (branchVector b) = (1/2 : ℝ) • branchVector b := by
  change shiftCLM T (∑' n, branchSummand b n) = _
  rw [(shiftCLM T).map_tsum (summable_branchSummand b)]
  have hm : Summable (fun n => shiftCLM T (branchSummand b n)) :=
    (summable_branchSummand b).map (shiftCLM T) (shiftCLM T).continuous
  rw [hm.tsum_eq_zero_add]
  have hz : shiftCLM T (branchSummand b 0) = 0 := by
    simp only [branchSummand,branchPrefix_zero,shiftCLM_apply,shift_single_nil]
  rw [hz,zero_add]
  have hs (n : ℕ) : shiftCLM T (branchSummand b (n+1)) = (1/2 : ℝ) • branchSummand b n := by
    rw [shiftCLM_apply,branchSummand,branchPrefix_succ,shift_single_concat]
    rw [← branchPrefix_succ,hb,if_pos rfl]
    rw [branchSummand,pow_succ,mul_comm,← smul_eq_mul,lp.single_smul]
  simp_rw [hs]
  exact Summable.tsum_const_smul _ (summable_branchSummand b)

theorem operator_branchVector (T : TreeSpace) (b : Baire)
    (hb : ∀ n, T (branchPrefix b n) = true) : operator T (branchVector b) = 0 := by
  change branchVector b - (2 : ℝ) • shift T (branchVector b) = 0
  rw [shift_branchVector T b hb,smul_smul]
  norm_num

theorem exists_nonzero_child (t : Code) (x : Space) (hx : operator t x = 0)
    (s : Node) (hs : x s ≠ 0) : ∃ n, t (s++[n]) = true ∧ x (s++[n]) ≠ 0 := by
  classical
  by_contra! h
  have heq (n : ℕ) : (if t (s++[n]) = true then x (s++[n]) else 0) = 0 := by
    split_ifs with hn
    · exact h n hn
    · rfl
  have hr := (operator_eq_zero_iff t x).mp hx s
  simp only [heq,tsum_zero,mul_zero] at hr
  exact hs hr

def nextDigit (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) : ℕ :=
  if hs : x s ≠ 0 then Classical.choose (exists_nonzero_child t x hx s hs) else 0

theorem nextDigit_good (t : Code) (x : Space) (hx : operator t x = 0)
    (s : Node) (hs : x s ≠ 0) :
    t (s++[nextDigit t x hx s]) = true ∧ x (s++[nextDigit t x hx s]) ≠ 0 := by
  simpa only [nextDigit,dif_pos hs] using Classical.choose_spec (exists_nonzero_child t x hx s hs)

def nodeChain (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) : ℕ → Node
  | 0 => s
  | n+1 => nodeChain t x hx s n ++ [nextDigit t x hx (nodeChain t x hx s n)]

theorem nodeChain_nonzero (t : Code) (x : Space) (hx : operator t x = 0)
    (s : Node) (hs : x s ≠ 0) (n : ℕ) : x (nodeChain t x hx s n) ≠ 0 := by
  induction n with
  | zero => exact hs
  | succ n IH => exact (nextDigit_good t x hx _ IH).2

def tailDigits (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) : Baire :=
  fun n => nextDigit t x hx (nodeChain t x hx s n)

theorem nodeChain_eq (t : Code) (x : Space) (hx : operator t x = 0) (s : Node) (n : ℕ) :
    nodeChain t x hx s n = s ++ branchPrefix (tailDigits t x hx s) n := by
  induction n with
  | zero => simp [nodeChain]
  | succ n IH =>
    rw [nodeChain,IH,branchPrefix_succ,List.append_assoc]
    simp only [tailDigits,IH]

def extendDigits (s : Node) (b : Baire) : Baire :=
  fun n => if h : n < s.length then s[n] else b (n-s.length)

theorem branchPrefix_extendDigits (s : Node) (b : Baire) (n : ℕ) :
    branchPrefix (extendDigits s b) (s.length+n) = s ++ branchPrefix b n := by
  induction n with
  | zero =>
    simp only [Nat.add_zero,branchPrefix_zero,List.append_nil]
    change List.ofFn (fun i : Fin s.length => extendDigits s b i) = s
    simpa [extendDigits] using List.ofFn_get s
  | succ n IH =>
    rw [Nat.add_succ,branchPrefix_succ,IH,branchPrefix_succ,List.append_assoc]
    congr 2
    simp [extendDigits]

theorem branchPrefix_add (b : Baire) (n m : ℕ) :
    branchPrefix b (n+m) = branchPrefix b n ++ branchPrefix (fun k => b (n+k)) m := by
  simpa [branchPrefix] using (List.ofFn_add (f := fun i : Fin (n+m) => b i))

theorem hasBranch_of_kernel_nonzero (T : TreeSpace) (x : Space)
    (hx : operator T x = 0) (hne : x ≠ 0) : HasBranch T := by
  classical
  have hex : ∃ s, x s ≠ 0 := by
    by_contra! h
    exact hne (by ext s; exact h s)
  obtain ⟨s,hs⟩ := hex
  let b := extendDigits s (tailDigits T x hx s)
  have hchain (n : ℕ) : T (nodeChain T x hx s n) = true :=
    mem_parent T _ _ (nextDigit_good T x hx _ (nodeChain_nonzero T x hx s hs n)).1
  refine ⟨b,fun n => ?_⟩
  have heq : nodeChain T x hx s n = branchPrefix b (n+s.length) := by
    rw [Nat.add_comm,branchPrefix_extendDigits,nodeChain_eq]
  have hc := hchain n
  rw [heq,branchPrefix_add] at hc
  exact mem_of_append T _ _ hc

theorem hasBranch_iff_exists_kernel_root (T : TreeSpace) :
    HasBranch T ↔ ∃ x : Space, operator T x = 0 ∧ x [] = 1 := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨branchVector b,operator_branchVector T b hb,branchVector_root b⟩
  · rintro ⟨x,hx,hr⟩
    apply hasBranch_of_kernel_nonzero T x hx
    intro hzero
    rw [hzero] at hr
    change (0 : ℝ) = 1 at hr
    norm_num at hr

theorem operator_injective_of_not_hasBranch (T : TreeSpace) (hT : ¬ HasBranch T) :
    Function.Injective (operator T) := by
  intro x y hxy
  by_contra hne
  have hz : operator T (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  exact hT (hasBranch_of_kernel_nonzero T (x-y) hz (sub_ne_zero.mpr hne))

end NoBorelUpperBoundFSigma.TreeOperators
