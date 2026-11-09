import NoBorelUpperBound.L1Coordinates
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace NoBorelUpperBoundFSigma.TreeOperators
open L1Coordinates

abbrev Node := List ℕ
abbrev Space := L1 Node
abbrev Code := Node → Bool

def child (p : Node × ℕ) : Node := p.1 ++ [p.2]

theorem child_injective : Function.Injective child := by
  rintro ⟨s,n⟩ ⟨t,m⟩ h
  have hs : s = t := by simpa [child] using congrArg List.dropLast h
  subst t
  have hn : n = m := by simpa [child] using (List.append_cancel_left h)
  exact Prod.ext rfl hn

def summand (t : Code) (x : Space) (p : Node × ℕ) : Space :=
  lp.single 1 p.1 (if t (child p) = true then x (child p) else 0)

theorem norm_summand_le (t : Code) (x : Space) (p : Node × ℕ) :
    ‖summand t x p‖ ≤ ‖x (child p)‖ := by
  rw [summand, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  split_ifs <;> simp

theorem summable_envelope (x : Space) : Summable (fun p : Node × ℕ => ‖x (child p)‖) :=
  (summable_norm x).comp_injective child_injective

theorem summable_norm_summand (t : Code) (x : Space) :
    Summable (fun p => ‖summand t x p‖) :=
  (summable_envelope x).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_summand_le t x)

theorem summable_summand (t : Code) (x : Space) : Summable (summand t x) :=
  (summable_norm_summand t x).of_norm

def shift (t : Code) (x : Space) : Space := ∑' p, summand t x p

theorem norm_shift_le (t : Code) (x : Space) : ‖shift t x‖ ≤ ‖x‖ := by
  calc
    ‖shift t x‖ ≤ ∑' p, ‖summand t x p‖ := norm_tsum_le_tsum_norm (summable_norm_summand t x)
    _ ≤ ∑' p : Node × ℕ, ‖x (child p)‖ :=
      (summable_norm_summand t x).tsum_le_tsum (norm_summand_le t x) (summable_envelope x)
    _ ≤ ∑' s, ‖x s‖ :=
      tsum_comp_le_tsum_of_inj (summable_norm x) (fun _ => norm_nonneg _) child_injective
    _ = ‖x‖ := (norm_eq_tsum x).symm

theorem summand_add (t : Code) (x y : Space) (p : Node × ℕ) :
    summand t (x+y) p = summand t x p + summand t y p := by
  unfold summand
  split_ifs
  · change (lp.single 1 p.1 (x (child p) + y (child p)) : Space) = _
    exact lp.single_add _ _ _ _
  · simp

theorem summand_smul (t : Code) (a : ℝ) (x : Space) (p : Node × ℕ) :
    summand t (a • x) p = a • summand t x p := by
  unfold summand
  split_ifs
  · change (lp.single 1 p.1 (a • x (child p)) : Space) = _
    exact lp.single_smul _ _ _ _
  · simp

def shiftCLM (t : Code) : Space →L[ℝ] Space :=
  ({toFun:=shift t
    map_add':=by
      intro x y
      simp only [shift,summand_add]
      exact (summable_summand t x).tsum_add (summable_summand t y)
    map_smul':=by
      intro a x
      simp only [shift,summand_smul,RingHom.id_apply]
      exact Summable.tsum_const_smul a (summable_summand t x)} : Space →ₗ[ℝ] Space).mkContinuous 1
    (fun x => by simpa using norm_shift_le t x)

@[simp] theorem shiftCLM_apply (t : Code) (x : Space) : shiftCLM t x = shift t x := rfl

theorem shift_apply (t : Code) (x : Space) (s : Node) :
    shift t x s = ∑' n, if t (s ++ [n]) = true then x (s ++ [n]) else 0 := by
  let ev : Space →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : Node => ℝ) 1 s
  have heval : Summable (fun p => ev (summand t x p)) :=
    (summable_summand t x).map ev.toAddMonoidHom ev.continuous
  change ev (∑' p, summand t x p) = _
  rw [ev.map_tsum (summable_summand t x), heval.tsum_prod, tsum_eq_single s]
  · apply tsum_congr
    intro n
    change (lp.single 1 s (if t (s ++ [n]) = true then x (s ++ [n]) else 0) : Space) s = _
    exact lp.single_apply_self _ _ _
  · intro u hu
    have heq (n : ℕ) : ev (summand t x (u,n)) = 0 := by
      change (lp.single 1 u _ : Space) s = (0 : ℝ)
      exact lp.single_apply_ne _ _ _ hu.symm
    simp only [heq,tsum_zero]

theorem continuous_summand (x : Space) (p : Node × ℕ) :
    Continuous (fun t : Code => summand t x p) := by
  have hb : Continuous (fun b : Bool => if b = true then x (child p) else 0) :=
    continuous_of_discreteTopology
  exact (lp.singleContinuousLinearMap ℝ (fun _ : Node => ℝ) 1 p.1).continuous.comp
    (hb.comp (continuous_apply (child p)))

theorem continuous_shift_fixed (x : Space) : Continuous (fun t : Code => shift t x) :=
  continuous_tsum (continuous_summand x) (summable_envelope x) (fun p t => norm_summand_le t x p)

theorem continuous_shift : Continuous (fun p : Code × Space => shift p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hnorm : Tendsto (fun q : Code × Space => ‖q.2-p.2‖) (𝓝 p) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (((continuous_snd.tendsto p).sub
        (tendsto_const_nhds : Tendsto (fun _ : Code × Space => p.2) (𝓝 p) (𝓝 p.2))).norm)
  have hzero : Tendsto (fun q : Code × Space => shift q.1 (q.2-p.2)) (𝓝 p) (𝓝 0) :=
    squeeze_zero_norm (fun q => norm_shift_le q.1 (q.2-p.2)) hnorm
  have hfixed : Tendsto (fun q : Code × Space => shift q.1 p.2) (𝓝 p) (𝓝 (shift p.1 p.2)) :=
    ((continuous_shift_fixed p.2).tendsto p.1).comp (continuous_fst.tendsto p)
  have heq (q : Code × Space) : shift q.1 (q.2-p.2) + shift q.1 p.2 = shift q.1 q.2 := by
    change shiftCLM q.1 (q.2-p.2) + shiftCLM q.1 p.2 = _
    rw [← map_add,sub_add_cancel,shiftCLM_apply]
  simpa only [zero_add] using (hzero.add hfixed).congr' (Eventually.of_forall heq)

def operator (t : Code) : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space - (2 : ℝ) • shiftCLM t

theorem continuous_operator : Continuous (fun p : Code × Space => operator p.1 p.2) := by
  exact continuous_snd.sub (continuous_shift.const_smul (2 : ℝ))

theorem norm_operator_le (t : Code) (x : Space) : ‖operator t x‖ ≤ 3 * ‖x‖ := by
  change ‖x - (2 : ℝ) • shift t x‖ ≤ _
  calc
    ‖x - (2 : ℝ) • shift t x‖ ≤ ‖x‖ + ‖(2 : ℝ) • shift t x‖ := norm_sub_le _ _
    _ = ‖x‖ + 2 * ‖shift t x‖ := by rw [norm_smul]; norm_num
    _ ≤ 3 * ‖x‖ := by nlinarith [norm_shift_le t x]

theorem shift_single_nil (t : Code) (a : ℝ) :
    shift t (lp.single 1 ([] : Node) a) = 0 := by
  have heq (p : Node × ℕ) : summand t (lp.single 1 ([] : Node) a) p = 0 := by
    have hp : child p ≠ [] := by simp [child]
    simp only [summand,lp.single_apply_ne _ _ _ hp]
    split_ifs <;> simp
  simp only [shift,heq,tsum_zero]

theorem shift_single_concat (t : Code) (s : Node) (n : ℕ) (a : ℝ) :
    shift t (lp.single 1 (s++[n]) a) =
      if t (s++[n]) = true then lp.single 1 s a else 0 := by
  rw [shift,tsum_eq_single (s,n)]
  · simp only [summand,child,lp.single_apply_self]
    split_ifs <;> simp
  · intro p hp
    have hn : child p ≠ s++[n] := fun h => hp (child_injective h)
    simp only [summand,lp.single_apply_ne _ _ _ hn]
    split_ifs <;> simp

@[simp] theorem operator_apply (t : Code) (x : Space) (s : Node) :
    operator t x s = x s - 2 * ∑' n, if t (s ++ [n]) = true then x (s ++ [n]) else 0 := by
  change x s - 2 * shift t x s = _
  rw [shift_apply]

theorem operator_eq_zero_iff (t : Code) (x : Space) :
    operator t x = 0 ↔ ∀ s, x s = 2 * ∑' n, if t (s ++ [n]) = true then x (s ++ [n]) else 0 := by
  constructor
  · intro h s
    have h' := congrArg (fun y : Space => y s) h
    simpa only [operator_apply,lp.coeFn_zero,Pi.zero_apply,sub_eq_zero] using h'
  · intro h
    ext s
    simpa only [operator_apply,lp.coeFn_zero,Pi.zero_apply,sub_eq_zero] using h s

end NoBorelUpperBoundFSigma.TreeOperators
