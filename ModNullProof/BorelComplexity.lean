import Definitions.Def_ModNullCore20261109
import Mathlib.Topology.GDelta.MetrizableSpace

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace

namespace ModNullUniversality

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isFSigma_compl_of_isGdelta {s : Set X} (hs : IsGδ s) : IsFSigma sᶜ := by
  obtain ⟨U,hU,hseq⟩ := hs.eq_iInter_nat
  refine ⟨fun n => (U n)ᶜ,fun n => (hU n).isClosed_compl,?_⟩
  rw [hseq,compl_iInter]

theorem isGdelta_compl_of_isFSigma {s : Set X} (hs : IsFSigma s) : IsGδ sᶜ := by
  obtain ⟨C,hC,rfl⟩ := hs
  rw [compl_iUnion]
  exact IsGδ.iInter_of_isOpen (fun n => (hC n).isOpen_compl)

theorem differenceFSigma_isDelta3 [PseudoMetrizableSpace X] {s : Set X}
    (hs : DifferenceFSigma s) : IsDelta3 s := by
  obtain ⟨A,B,hA,hB,rfl⟩ := hs
  obtain ⟨C,hC,hseqA⟩ := hA
  obtain ⟨D,hD,hseqB⟩ := hB
  have hAc : IsGδ Aᶜ := isGdelta_compl_of_isFSigma ⟨C,hC,hseqA⟩
  have hBc : IsGδ Bᶜ := isGdelta_compl_of_isFSigma ⟨D,hD,hseqB⟩
  constructor
  · refine ⟨fun n => C n ∩ Bᶜ,fun n => (hC n).isGδ.inter hBc,?_⟩
    rw [hseqA]
    ext x
    simp only [mem_diff,mem_iUnion,mem_inter_iff,mem_compl_iff]
    aesop
  · refine ⟨fun n => (D n ∪ Aᶜ)ᶜ,
      fun n => isFSigma_compl_of_isGdelta ((hD n).isGδ.union hAc),?_⟩
    rw [hseqB]
    ext x
    simp only [mem_diff,mem_iUnion,mem_iInter,mem_compl_iff,mem_union,not_or,not_not]
    exact ⟨fun h i => ⟨fun hi => h.2 ⟨i,hi⟩,h.1⟩,
      fun h => ⟨(h 0).2,fun ⟨i,hi⟩ => (h i).1 hi⟩⟩

theorem isKSigma_image {s : Set X} (hs : IsKSigma s) (f : X → Y)
    (hf : Continuous f) : IsKSigma (f '' s) := by
  obtain ⟨C,hC,rfl⟩ := hs
  exact ⟨fun n => f '' C n,fun n => (hC n).image hf,by rw [image_iUnion]⟩

theorem isFSigma_of_isKSigma [T2Space X] {s : Set X} (hs : IsKSigma s) : IsFSigma s := by
  obtain ⟨C,hC,hseq⟩ := hs
  exact ⟨C,fun n => (hC n).isClosed,hseq⟩

theorem isKSigma_of_isFSigma [CompactSpace X] {s : Set X} (hs : IsFSigma s) : IsKSigma s := by
  obtain ⟨C,hC,hseq⟩ := hs
  exact ⟨C,fun n => (hC n).isCompact,hseq⟩

theorem isKSigma_subtype_image_of_isFSigma {K : Set X} (hK : IsCompact K)
    {s : Set K} (hs : IsFSigma s) : IsKSigma (Subtype.val '' s : Set X) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isKSigma_image (isKSigma_of_isFSigma hs) Subtype.val continuous_subtype_val

theorem isFSigma_iUnion_nat {s : ℕ → Set X} (hs : ∀ n, IsFSigma (s n)) :
    IsFSigma (⋃ n, s n) := by
  classical
  choose C hC hseq using hs
  refine ⟨fun k => C k.unpair.1 k.unpair.2,fun k => hC _ _,?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n,hn⟩
    rw [hseq n] at hn
    obtain ⟨m,hm⟩ := mem_iUnion.mp hn
    exact ⟨Nat.pair n m,by simpa using hm⟩
  · rintro ⟨k,hk⟩
    refine ⟨k.unpair.1,?_⟩
    rw [hseq]
    exact mem_iUnion.mpr ⟨k.unpair.2,hk⟩

theorem isFSigma_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, IsFSigma (s i)) : IsFSigma (⋃ i, s i) := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    obtain ⟨e,he⟩ := exists_surjective_nat ι
    have hseq : (⋃ i, s i) = ⋃ n : ℕ, s (e n) := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        obtain ⟨n,rfl⟩ := he i
        exact ⟨n,hi⟩
      · rintro ⟨n,hn⟩
        exact ⟨e n,hn⟩
    rw [hseq]
    exact isFSigma_iUnion_nat (fun n => hs (e n))
  · letI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
    exact ⟨fun _ => ∅,fun _ => isClosed_empty,by ext x; simp⟩

theorem isFSigma_inter {s t : Set X} (hs : IsFSigma s) (ht : IsFSigma t) :
    IsFSigma (s ∩ t) := by
  obtain ⟨C,hC,rfl⟩ := hs
  obtain ⟨D,hD,rfl⟩ := ht
  refine ⟨fun k => C k.unpair.1 ∩ D k.unpair.2,
    fun k => (hC _).inter (hD _),?_⟩
  ext x
  simp only [mem_inter_iff,mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    exact ⟨Nat.pair i j,by simpa using And.intro hi hj⟩
  · rintro ⟨k,hk⟩
    exact ⟨⟨k.unpair.1,hk.1⟩,⟨k.unpair.2,hk.2⟩⟩

theorem differenceFSigma_image_of_ksigma [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (A B : Set X) (hA : IsKSigma A) (hB : IsKSigma B) :
    DifferenceFSigma (f '' (A \ B)) := by
  refine ⟨f '' A,f '' B,isFSigma_of_isKSigma (isKSigma_image hA f hf),
    isFSigma_of_isKSigma (isKSigma_image hB f hf),?_⟩
  ext y
  constructor
  · rintro ⟨x,⟨hxA,hxB⟩,rfl⟩
    refine ⟨mem_image_of_mem f hxA,?_⟩
    rintro ⟨z,hz,hzx⟩
    exact hxB ((hinj hzx) ▸ hz)
  · rintro ⟨⟨x,hx,hxy⟩,hnot⟩
    refine ⟨x,⟨hx,?_⟩,hxy⟩
    intro hxB
    exact hnot ⟨x,hxB,hxy⟩

theorem isFSigma_preimage {s : Set Y} (hs : IsFSigma s) (f : X → Y)
    (hf : Continuous f) : IsFSigma (f ⁻¹' s) := by
  obtain ⟨C,hC,rfl⟩ := hs
  exact ⟨fun n => f ⁻¹' C n,fun n => (hC n).preimage hf,by rw [preimage_iUnion]⟩

theorem differenceFSigma_preimage {s : Set Y} (hs : DifferenceFSigma s) (f : X → Y)
    (hf : Continuous f) : DifferenceFSigma (f ⁻¹' s) := by
  obtain ⟨A,B,hA,hB,rfl⟩ := hs
  exact ⟨f ⁻¹' A,f ⁻¹' B,isFSigma_preimage hA f hf,isFSigma_preimage hB f hf,rfl⟩

theorem isFSigma_measurableSet [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : IsFSigma s) : MeasurableSet s := by
  obtain ⟨C,hC,rfl⟩ := hs
  exact MeasurableSet.iUnion (fun n => (hC n).measurableSet)

theorem differenceFSigma_measurableSet [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : DifferenceFSigma s) : MeasurableSet s := by
  obtain ⟨A,B,hA,hB,rfl⟩ := hs
  exact (isFSigma_measurableSet hA).diff (isFSigma_measurableSet hB)

end ModNullUniversality
