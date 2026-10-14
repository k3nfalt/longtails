import LongTails.Algorithms.StochasticGeneralizedAccelerated
import LongTails.Proofs.DampedGeneralizedDynamics
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

open MeasureTheory

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling energy)

variable {E : Type*} [MeasurableSpace E]

instance measurableSpaceIterate : MeasurableSpace (Iterate E) :=
  MeasurableSpace.comap (fun s => (s.A, s.x, s.z, s.guess)) inferInstance

instance measurableSpacePending : MeasurableSpace (Pending E) :=
  MeasurableSpace.comap (fun p => (p.previous, p.weight, p.y, p.curvature, p.point)) inferInstance

@[fun_prop] lemma measurable_iterate_A : Measurable (fun s : Iterate E => s.A) :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop] lemma measurable_iterate_x : Measurable (fun s : Iterate E => s.x) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable _))

@[fun_prop] lemma measurable_iterate_z : Measurable (fun s : Iterate E => s.z) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))

@[fun_prop] lemma measurable_iterate_guess : Measurable (fun s : Iterate E => s.guess) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))

@[fun_prop] lemma measurable_iterate_mk {α : Type*} [MeasurableSpace α]
    {A G : α → ℝ} {x z : α → E} (hA : Measurable A) (hx : Measurable x)
    (hz : Measurable z) (hG : Measurable G) :
    Measurable (fun a => (⟨A a, x a, z a, G a⟩ : Iterate E)) := by
  apply measurable_comap_iff.mpr
  exact hA.prodMk (hx.prodMk (hz.prodMk hG))

@[fun_prop] lemma measurable_pending_previous : Measurable (fun p : Pending E => p.previous) :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop] lemma measurable_pending_weight : Measurable (fun p : Pending E => p.weight) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable _))

@[fun_prop] lemma measurable_pending_y : Measurable (fun p : Pending E => p.y) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))

@[fun_prop] lemma measurable_pending_curvature : Measurable (fun p : Pending E => p.curvature) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _))))

@[fun_prop] lemma measurable_pending_point : Measurable (fun p : Pending E => p.point) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (comap_measurable _))))

@[fun_prop] lemma measurable_pending_mk {α : Type*} [MeasurableSpace α]
    {s : α → Iterate E} {a M : α → ℝ} {y w : α → E}
    (hs : Measurable s) (ha : Measurable a) (hy : Measurable y)
    (hM : Measurable M) (hw : Measurable w) :
    Measurable (fun t => (⟨s t, a t, y t, M t, w t⟩ : Pending E)) := by
  apply measurable_comap_iff.mpr
  exact hs.prodMk (ha.prodMk (hy.prodMk (hM.prodMk hw)))

@[fun_prop] lemma measurable_tentativeWeight : Measurable (tentativeWeight (E := E)) := by
  unfold tentativeWeight
  fun_prop

@[fun_prop] lemma measurable_batchSize (σ ε δ : ℝ) : Measurable (batchSize (E := E) σ ε δ) := by
  unfold batchSize
  fun_prop

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
@[fun_prop] lemma measurable_coupling : Measurable (coupling (E := E)) := by
  unfold coupling
  fun_prop

omit [CompleteSpace E] in
@[fun_prop] lemma measurable_prepare (L0 L1 : ℝ) :
    Measurable (fun z : Iterate E × E => prepare L0 L1 z.1 z.2) := by
  unfold prepare
  fun_prop

omit [CompleteSpace E] in
@[fun_prop] lemma measurable_finish : Measurable (fun z : Pending E × E => finish z.1 z.2) := by
  unfold finish
  dsimp only
  apply measurable_iterate_mk
  · fun_prop
  · fun_prop
  · fun_prop
  · apply Measurable.ite
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    · fun_prop
    · fun_prop

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
@[fun_prop] lemma measurable_energy {f : E → ℝ} (hf : Measurable f) (u : E) :
    Measurable (energy f u) := by
  unfold energy
  fun_prop

end OracleTemplate.StochasticGeneralized
