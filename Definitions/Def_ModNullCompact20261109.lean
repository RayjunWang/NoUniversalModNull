import Definitions.Def_ModNullCore20261109
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Polish

set_option autoImplicit false

namespace ModNullUniversality

structure CompactMetrizableHaarGroup where
  Carrier : Type
  [group : Group Carrier]
  [topology : TopologicalSpace Carrier]
  [compact : CompactSpace Carrier]
  [metrizable : TopologicalSpace.MetrizableSpace Carrier]
  [topologicalGroup : IsTopologicalGroup Carrier]
  [measurable : MeasurableSpace Carrier]
  [borelSpace : BorelSpace Carrier]
  haar : MeasureTheory.Measure Carrier
  [probability : MeasureTheory.IsProbabilityMeasure haar]
  [haarMeasure : MeasureTheory.Measure.IsHaarMeasure haar]

attribute [instance] CompactMetrizableHaarGroup.group CompactMetrizableHaarGroup.topology
  CompactMetrizableHaarGroup.compact CompactMetrizableHaarGroup.metrizable
  CompactMetrizableHaarGroup.topologicalGroup CompactMetrizableHaarGroup.measurable
  CompactMetrizableHaarGroup.borelSpace CompactMetrizableHaarGroup.probability
  CompactMetrizableHaarGroup.haarMeasure

def IsAbelian (K : CompactMetrizableHaarGroup) : Prop :=
  ∀ x y : K.Carrier, x * y = y * x

def CosetRelation (K : CompactMetrizableHaarGroup) (H : Subgroup K.Carrier)
    (x y : K.Carrier) : Prop := x⁻¹ * y ∈ H

def LowComplexityFamily (K : CompactMetrizableHaarGroup)
    (H : WF → Subgroup K.Carrier) : Prop :=
  (∀ T, IsDelta3 (H T : Set K.Carrier)) ∧
  (∀ T, IsDelta3 {p : K.Carrier × K.Carrier | CosetRelation K (H T) p.1 p.2}) ∧
  (∀ T, DifferenceFSigma {p : K.Carrier × K.Carrier | CosetRelation K (H T) p.1 p.2})

end ModNullUniversality
