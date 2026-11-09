import ModNullProof.AEPowerBorel
import Definitions.Def_ModNullCompact20261109
import Mathlib.MeasureTheory.Group.Prod

/-!
The Haar amplification lemma.  A reduction defined on a conull set is encoded
by the whole family of its left translates.  Right translations quasi-preserve
Haar measure, so for each pair of points the coded functions compare exactly
as the original coset relation, almost everywhere.
-/

open MeasureTheory Filter Topology Set

namespace ModNullUniversality

theorem haar_amplification_proved
    (K : CompactMetrizableHaarGroup) (F : StandardBorelEquivalence)
    (hF : Nonempty F.Carrier) :
    ∃ Q : StandardBorelEquivalence,
      ∀ H : Subgroup K.Carrier, MeasurableSet (H : Set K.Carrier) →
        ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
          BorelReducible
            (fun x y : C => CosetRelation K H x.val y.val) F.rel →
          BorelReducible (CosetRelation K H) Q.rel := by
  letI : MetricSpace K.Carrier := TopologicalSpace.metrizableSpaceMetric K.Carrier
  letI : SecondCountableTopology K.Carrier := inferInstance
  letI : Nonempty F.Carrier := hF
  refine ⟨AEPower.power K.haar F, ?_⟩
  intro H _ C hCm hC hred
  obtain ⟨f, hf, hfred⟩ := hred
  obtain ⟨g, hg, hgf⟩ := (MeasurableEmbedding.subtype_coe hCm).exists_measurable_extend
    hf (fun _ => hF)
  have hext (z : K.Carrier) (hz : z ∈ C) : g z = f ⟨z, hz⟩ :=
    congrFun hgf ⟨z, hz⟩
  let a : K.Carrier × K.Carrier → F.Carrier := fun p => g (p.2 * p.1)
  have ha : Measurable a := hg.comp (measurable_snd.mul measurable_fst)
  obtain ⟨c, hc, hcode⟩ := AEPower.exists_measurable_code F.Carrier K.haar ha
  refine ⟨c, hc, fun x y => ?_⟩
  change CosetRelation K H x y ↔
    ∀ᵐ t ∂K.haar, F.rel (AEPower.decode F.Carrier K.haar (c x) t)
      (AEPower.decode F.Carrier K.haar (c y) t)
  have hmem : ∀ᵐ t ∂K.haar, t ∈ C :=
    (ae_mem_iff_measure_eq hCm.nullMeasurableSet).mpr (by simpa using hC)
  have hxmem : ∀ᵐ t ∂K.haar, t * x ∈ C :=
    (quasiMeasurePreserving_mul_right K.haar x).ae hmem
  have hymem : ∀ᵐ t ∂K.haar, t * y ∈ C :=
    (quasiMeasurePreserving_mul_right K.haar y).ae hmem
  have hcompare : ∀ᵐ t ∂K.haar,
      F.rel (AEPower.decode F.Carrier K.haar (c x) t)
        (AEPower.decode F.Carrier K.haar (c y) t) ↔ CosetRelation K H x y := by
    filter_upwards [hcode x, hcode y, hxmem, hymem] with t hx hy htx hty
    rw [hx, hy]
    change F.rel (g (t * x)) (g (t * y)) ↔ CosetRelation K H x y
    rw [hext (t * x) htx, hext (t * y) hty]
    have hcos : CosetRelation K H (t * x) (t * y) ↔ CosetRelation K H x y := by
      simp [CosetRelation, mul_inv_rev, mul_assoc]
    exact (hfred ⟨t * x, htx⟩ ⟨t * y, hty⟩).symm.trans hcos
  constructor
  · intro hxy
    exact hcompare.mono fun t ht => ht.mpr hxy
  · intro hxy
    have hconst : ∀ᵐ _t ∂K.haar, CosetRelation K H x y := by
      filter_upwards [hxy, hcompare] with t ht hc
      exact hc.mp ht
    exact hconst.exists.choose_spec

end ModNullUniversality
