import Definitions.Def_NoBorelUpperBound20261101
import Mathlib.Topology.List
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

noncomputable section
open Set TopologicalSpace Topology

namespace NoBorelUpperBoundFSigma.Trees

abbrev Node := List ℕ
abbrev Baire := ℕ → ℕ

def TreeProperty (t : Node → Bool) : Prop :=
  ∀ s n, t (s ++ [n]) = true → t s = true

abbrev TreeSpace := {t : Node → Bool // TreeProperty t}

instance : CoeFun TreeSpace (fun _ => Node → Bool) := ⟨fun t => t.val⟩

theorem isClosed_treeProperty : IsClosed {t : Node → Bool | TreeProperty t} := by
  unfold TreeProperty
  simp only [setOf_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro n
  have heq : {t : Node → Bool | t (s ++ [n]) = true → t s = true} =
      {t | t (s ++ [n]) = false} ∪ {t | t s = true} := by
    ext t
    cases h : t (s ++ [n]) <;> simp [h]
  rw [heq]
  exact (isClosed_eq (continuous_apply (s ++ [n])) continuous_const).union
    (isClosed_eq (continuous_apply s) continuous_const)

instance : PolishSpace TreeSpace := by
  letI : PolishSpace (Node → Bool) :=
    { toSecondCountableTopology := inferInstance
      toIsCompletelyMetrizableSpace := inferInstance }
  exact isClosed_treeProperty.polishSpace
instance : CompactSpace TreeSpace := isCompact_iff_compactSpace.mp isClosed_treeProperty.isCompact

def mem (T : TreeSpace) (s : Node) : Prop := T s = true

theorem mem_parent (T : TreeSpace) (s : Node) (n : ℕ) (h : T (s ++ [n]) = true) :
    T s = true := T.property s n h

theorem mem_of_append (T : TreeSpace) (s t : Node) (h : T (s ++ t) = true) : T s = true := by
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t n ih =>
    exact ih (mem_parent T (s ++ t) n (by simpa only [List.append_assoc] using h))

def branchPrefix (x : Baire) (n : ℕ) : Node := List.ofFn (fun i : Fin n => x i)

@[simp] theorem length_branchPrefix (x : Baire) (n : ℕ) : (branchPrefix x n).length = n := by
  simp [branchPrefix]

@[simp] theorem branchPrefix_zero (x : Baire) : branchPrefix x 0 = [] := rfl

theorem branchPrefix_succ (x : Baire) (n : ℕ) : branchPrefix x (n + 1) = branchPrefix x n ++ [x n] := by
  simpa [branchPrefix, List.concat_eq_append] using List.ofFn_succ' (fun i : Fin (n + 1) => x i)

theorem continuous_branchPrefix (n : ℕ) : Continuous (fun x : Baire => branchPrefix x n) := by
  exact (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → ℕ) → Node)).comp
    (continuous_pi (fun i => continuous_apply (i : ℕ)))

theorem continuous_eval (s : Node) : Continuous (fun T : TreeSpace => T s) :=
  (continuous_apply s).comp continuous_subtype_val

def HasBranch (T : TreeSpace) : Prop := ∃ x : Baire, ∀ n, T (branchPrefix x n) = true
def IF : Set TreeSpace := {T | HasBranch T}

def fullTree : TreeSpace := ⟨fun _ => true, fun _ _ _ => rfl⟩
def emptyTree : TreeSpace := ⟨fun _ => false, by simp [TreeProperty]⟩

theorem fullTree_mem_IF : fullTree ∈ IF := ⟨fun _ => 0, fun _ => rfl⟩
theorem emptyTree_not_mem_IF : emptyTree ∉ IF := by
  rintro ⟨x, hx⟩
  have h := hx 0
  cases h

end NoBorelUpperBoundFSigma.Trees
