import Definitions.Def_NoBorelUpperBoundTransfer20261101
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.List.Basic

noncomputable section
open Set MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w

namespace FiniteGeneratorWord

/-- A finite sequence of parameters, with the generator index fixed in advance. -/
def Domain (A : ℕ → Type w) : List ℕ → Type w
  | [] => PUnit
  | n :: l => A n × Domain A l

instance domainMeasurableSpace {A : ℕ → Type w} [∀ n, MeasurableSpace (A n)] :
    (l : List ℕ) → MeasurableSpace (Domain A l)
  | [] => inferInstanceAs (MeasurableSpace PUnit)
  | n :: l => @Prod.instMeasurableSpace (A n) (Domain A l) inferInstance
      (domainMeasurableSpace l)

instance domainStandardBorelSpace {A : ℕ → Type w} [∀ n, MeasurableSpace (A n)]
    [∀ n, StandardBorelSpace (A n)] : (l : List ℕ) → StandardBorelSpace (Domain A l)
  | [] => inferInstanceAs (StandardBorelSpace PUnit)
  | n :: l => by
      letI := domainStandardBorelSpace (A := A) l
      exact inferInstanceAs (StandardBorelSpace (A n × Domain A l))

def value {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) :
    (l : List ℕ) → P → Domain A l → G
  | [], _, _ => 1
  | n :: l, p, a => h n p a.1 * value h l p a.2

theorem measurable_value {P : Type u} [MeasurableSpace P]
    {G : Type v} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, MeasurableSpace (A n)]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2)) :
    ∀ l : List ℕ, Measurable (fun pa : P × Domain A l => value h l pa.1 pa.2) := by
  intro l
  induction l with
  | nil => exact measurable_const
  | cons n l IH =>
      exact ((hh n).comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (IH.comp (measurable_fst.prodMk measurable_snd.snd))

theorem value_mem {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) :
    ∀ (l : List ℕ) (a : Domain A l), value h l p a ∈ GeneratedSubgroup h p := by
  intro l
  induction l with
  | nil => intro a; exact (GeneratedSubgroup h p).one_mem
  | cons n l IH =>
      intro a
      exact (GeneratedSubgroup h p).mul_mem
        (Subgroup.subset_closure (mem_iUnion.mpr ⟨n,mem_range_self a.1⟩)) (IH a.2)

theorem list_representation {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P)
    (L : List (Σ n, A n)) :
    ∃ (l : List ℕ) (a : Domain A l),
      value h l p a = (L.map (fun x => h x.1 p x.2)).prod := by
  induction L with
  | nil => exact ⟨[],PUnit.unit,rfl⟩
  | cons x L IH =>
      obtain ⟨l,a,ha⟩ := IH
      exact ⟨x.1 :: l,(x.2,a),by simpa only [value,List.map_cons,List.prod_cons,ha]⟩

def listSubgroup {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) : Subgroup G where
  carrier := {g | ∃ L : List (Σ n, A n), (L.map (fun x => h x.1 p x.2)).prod = g}
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro x y ⟨L,rfl⟩ ⟨M,rfl⟩
    exact ⟨L ++ M,by simp⟩
  inv_mem' := by
    rintro x ⟨L,rfl⟩
    refine ⟨(L.map (fun x => (⟨x.1,x.2⁻¹⟩ : Σ n, A n))).reverse,?_⟩
    simp only [List.map_reverse,List.map_map,Function.comp_def,map_inv]
    simpa only [List.map_map,Function.comp_def] using
      (List.prod_inv_reverse (L.map (fun x => h x.1 p x.2))).symm

theorem mem_iff_exists_value {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) (g : G) :
    g ∈ GeneratedSubgroup h p ↔ ∃ (l : List ℕ) (a : Domain A l), value h l p a = g := by
  constructor
  · intro hg
    have hle : GeneratedSubgroup h p ≤ listSubgroup h p := by
      apply (Subgroup.closure_le _).2
      intro x hx
      obtain ⟨n,a,rfl⟩ := mem_iUnion.mp hx
      exact ⟨[⟨n,a⟩],by simp⟩
    obtain ⟨L,hL⟩ := hle hg
    obtain ⟨l,a,ha⟩ := list_representation h p L
    exact ⟨l,a,ha.trans hL⟩
  · rintro ⟨l,a,rfl⟩
    exact value_mem h p l a

end FiniteGeneratorWord

/-- Membership in an algebraically generated countable Borel family of
continuous-homomorphism images is analytic. Algebraic membership uses finite
words, with no topological closure involved. -/
theorem analyticSet_membershipSet
    {P : Type u} [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, MeasurableSpace (A n)]
    [∀ n, StandardBorelSpace (A n)]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (z₀ : P → G) (hz : Measurable z₀) : AnalyticSet (MembershipSet h z₀) := by
  classical
  have heq : MembershipSet h z₀ = ⋃ l : List ℕ,
      Prod.fst '' {pa : P × FiniteGeneratorWord.Domain A l |
        FiniteGeneratorWord.value h l pa.1 pa.2 = z₀ pa.1} := by
    ext p
    simp only [MembershipSet,mem_setOf_eq,mem_iUnion,mem_image,Prod.exists]
    rw [FiniteGeneratorWord.mem_iff_exists_value]
    constructor
    · rintro ⟨l,a,ha⟩
      exact ⟨l,p,a,ha,rfl⟩
    · rintro ⟨l,q,a,ha,rfl⟩
      exact ⟨l,a,ha⟩
  rw [heq]
  apply AnalyticSet.iUnion
  intro l
  have hS : MeasurableSet {pa : P × FiniteGeneratorWord.Domain A l |
      FiniteGeneratorWord.value h l pa.1 pa.2 = z₀ pa.1} :=
    measurableSet_eq_fun (FiniteGeneratorWord.measurable_value h hh l) (hz.comp measurable_fst)
  exact hS.analyticSet_image measurable_fst

end NoBorelUpperBoundFSigma
