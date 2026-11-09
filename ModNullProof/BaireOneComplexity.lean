import ModNullProof.BorelComplexity
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section

open Set Filter TopologicalSpace
open scoped Topology BigOperators

namespace ModNullUniversality

/-- A real function obtained as the pointwise limit of a sequence of continuous functions. -/
def BaireOne {X : Type*} [TopologicalSpace X] (f : X → ℝ) : Prop :=
  ∃ g : ℕ → X → ℝ, (∀ n, Continuous (g n)) ∧
    ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))

namespace BaireOne

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : X → ℝ}

theorem of_continuous (hf : Continuous f) : BaireOne f :=
  ⟨fun _ => f,fun _ => hf,fun _ => tendsto_const_nhds⟩

theorem const (c : ℝ) : BaireOne (fun _ : X => c) :=
  of_continuous continuous_const

theorem add (hf : BaireOne f) (hg : BaireOne g) : BaireOne (fun x => f x + g x) := by
  obtain ⟨a,ha,ha'⟩ := hf
  obtain ⟨b,hb,hb'⟩ := hg
  exact ⟨fun n x => a n x + b n x,fun n => (ha n).add (hb n),
    fun x => (ha' x).add (hb' x)⟩

theorem neg (hf : BaireOne f) : BaireOne (fun x => -f x) := by
  obtain ⟨a,ha,ha'⟩ := hf
  exact ⟨fun n x => -a n x,fun n => (ha n).neg,fun x => (ha' x).neg⟩

theorem sub (hf : BaireOne f) (hg : BaireOne g) : BaireOne (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : BaireOne f) (hg : BaireOne g) : BaireOne (fun x => f x * g x) := by
  obtain ⟨a,ha,ha'⟩ := hf
  obtain ⟨b,hb,hb'⟩ := hg
  exact ⟨fun n x => a n x * b n x,fun n => (ha n).mul (hb n),
    fun x => (ha' x).mul (hb' x)⟩

theorem smul (hf : BaireOne f) (c : ℝ) : BaireOne (fun x => c * f x) :=
  (const c).mul hf

theorem comp_continuous (hf : BaireOne f) (h : Y → X) (hh : Continuous h) :
    BaireOne (fun y => f (h y)) := by
  obtain ⟨a,ha,ha'⟩ := hf
  exact ⟨fun n y => a n (h y),fun n => (ha n).comp hh,fun y => ha' (h y)⟩

/-- Continuous operations on any family of real Baire-one functions remain Baire one. -/
theorem continuous_operation {ι : Type*} {a : X → ι → ℝ}
    (ha : ∀ i, BaireOne (fun x => a x i)) {p : (ι → ℝ) → ℝ} (hp : Continuous p) :
    BaireOne (fun x => p (a x)) := by
  classical
  choose b hb hb' using ha
  refine ⟨fun n x => p (fun i => b i n x),fun n => ?_,fun x => ?_⟩
  · exact hp.comp (continuous_pi (fun i => hb i n))
  · exact hp.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun i => hb' i x))

theorem sum {ι : Type*} (s : Finset ι) {a : ι → X → ℝ}
    (ha : ∀ i ∈ s, BaireOne (a i)) : BaireOne (fun x => ∑ i ∈ s, a i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (X := X) 0)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (ha i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem prod {ι : Type*} (s : Finset ι) {a : ι → X → ℝ}
    (ha : ∀ i ∈ s, BaireOne (a i)) : BaireOne (fun x => ∏ i ∈ s, a i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (X := X) 1)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (ha i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem matrix_det {n : Type*} [Fintype n] [DecidableEq n] {a : X → Matrix n n ℝ}
    (ha : ∀ i j, BaireOne (fun x => a x i j)) : BaireOne (fun x => (a x).det) := by
  exact continuous_operation (a := fun x (ij : n × n) => a x ij.1 ij.2)
    (fun ij => ha ij.1 ij.2)
    ((continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i,j)))).matrix_det)

theorem matrix_adjugate {n : Type*} [Fintype n] [DecidableEq n] {a : X → Matrix n n ℝ}
    (ha : ∀ i j, BaireOne (fun x => a x i j)) (i j : n) :
    BaireOne (fun x => (a x).adjugate i j) := by
  have hc : Continuous (fun v : n × n → ℝ => fun i j => v (i,j)) :=
    continuous_pi (fun i => continuous_pi (fun j => continuous_apply (i,j)))
  exact continuous_operation (a := fun x (ij : n × n) => a x ij.1 ij.2)
    (fun ij => ha ij.1 ij.2) (hc.matrix_adjugate.matrix_elem i j)

theorem isFSigma_lt (hf : BaireOne f) (a : ℝ) : IsFSigma {x | f x < a} := by
  obtain ⟨u,hu,hlim⟩ := hf
  let C : ℕ → ℕ → Set X := fun k N => ⋂ n ≥ N, {x | u n x ≤ a - 1 / (k + 1 : ℝ)}
  have hC : ∀ k N, IsClosed (C k N) := by
    intro k N
    exact isClosed_iInter (fun n => isClosed_iInter (fun _ =>
      isClosed_le (hu n) continuous_const))
  have hseq : {x | f x < a} = ⋃ k : ℕ, ⋃ N : ℕ, C k N := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      have hsmall : f x < a - 1 / (k + 1 : ℝ) := by linarith
      obtain ⟨N,hN⟩ := eventually_atTop.mp
        ((tendsto_order.mp (hlim x)).2 _ hsmall)
      exact ⟨k,N,by simpa only [C,mem_iInter,mem_setOf_eq] using
        (fun n hn => (hN n hn).le)⟩
    · rintro ⟨k,N,hx⟩
      have hN : ∀ n ≥ N, u n x ≤ a - 1 / (k + 1 : ℝ) := by
        simpa only [C,mem_iInter,mem_setOf_eq] using hx
      have hle := le_of_tendsto (hlim x) (eventually_atTop.mpr ⟨N,hN⟩)
      have hpos : 0 < 1 / (k + 1 : ℝ) := by positivity
      linarith
  rw [hseq]
  exact isFSigma_iUnion_nat (fun k => ⟨C k,hC k,rfl⟩)

theorem isFSigma_gt (hf : BaireOne f) (a : ℝ) : IsFSigma {x | a < f x} := by
  simpa only [neg_lt_neg_iff] using hf.neg.isFSigma_lt (-a)

theorem isFSigma_Ioo (hf : BaireOne f) (a b : ℝ) : IsFSigma (f ⁻¹' Ioo a b) := by
  exact isFSigma_inter (hf.isFSigma_gt a) (hf.isFSigma_lt b)

/-- The defining preimage characterization of real Baire-one functions. -/
theorem isFSigma_preimage_open (hf : BaireOne f) {U : Set ℝ} (hU : IsOpen U) :
    IsFSigma (f ⁻¹' U) := by
  let I := {p : ℚ × ℚ // Ioo (p.1 : ℝ) (p.2 : ℝ) ⊆ U}
  have heq : f ⁻¹' U = ⋃ p : I, f ⁻¹' Ioo (p.val.1 : ℝ) (p.val.2 : ℝ) := by
    ext x
    simp only [mem_preimage,mem_iUnion]
    constructor
    · intro hx
      obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
      obtain ⟨a,hla,hax⟩ := exists_rat_btwn hlr.1
      obtain ⟨b,hxb,hbr⟩ := exists_rat_btwn hlr.2
      refine ⟨⟨(a,b),?_⟩,hax,hxb⟩
      exact fun y hy => hsub ⟨hla.trans hy.1,hy.2.trans hbr⟩
    · rintro ⟨p,hp⟩
      exact p.property hp
  rw [heq]
  exact isFSigma_iUnion (fun p => hf.isFSigma_Ioo _ _)

theorem isGdelta_zero (hf : BaireOne f) : IsGδ {x | f x = 0} := by
  have h := isGdelta_compl_of_isFSigma
    (hf.isFSigma_preimage_open (isClosed_singleton.isOpen_compl : IsOpen ({0} : Set ℝ)ᶜ))
  simpa only [preimage_compl,compl_compl] using h

theorem isGdelta_eq (hf : BaireOne f) (hg : BaireOne g) : IsGδ {x | f x = g x} := by
  simpa only [sub_eq_zero] using (hf.sub hg).isGdelta_zero

theorem isFSigma_ne_zero (hf : BaireOne f) : IsFSigma {x | f x ≠ 0} := by
  exact isFSigma_compl_of_isGdelta hf.isGdelta_zero

theorem isFSigma_ne (hf : BaireOne f) (hg : BaireOne g) : IsFSigma {x | f x ≠ g x} := by
  exact isFSigma_compl_of_isGdelta (hf.isGdelta_eq hg)

end BaireOne
end ModNullUniversality
