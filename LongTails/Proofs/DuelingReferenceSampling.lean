import LongTails.Proofs.DuelingReferenceField
import LongTails.Proofs.ZerothOrderGridEstimator

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceDrift
open LongTails.Proofs.DuelingReferenceSmoothing
open LongTails.Proofs.DuelingReferenceField
open OracleTemplate.ZerothOrder (sphereLaw uniform_integral_explicit)

namespace LongTails.Proofs.DuelingReferenceSampling

lemma measurable_retract {d : ℕ} : Measurable (retract (d := d)) :=
  (OracleTemplate.measurable_clip (E := Point d) 1).subtype_mk

lemma measurable_query (p : Params) : Measurable (Function.uncurry (query p)) := by
  apply Measurable.prodMk
  · apply measurable_retract.comp
    fun_prop
  · apply measurable_retract.comp
    unfold anchor
    apply Measurable.ite (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const)
    · fun_prop
    · apply Measurable.ite (measurableSet_eq_fun (measurable_snd.comp measurable_snd) measurable_const) <;> fun_prop

lemma norm_estimate (p : Params) (hp : spec.valid p) (a : Draw p.d) (b : Bool) :
    ‖estimate p a b‖ = p.d / radius p := by
  have ha := Metric.mem_sphere.mp a.1.property
  rw [dist_zero_right] at ha
  have hr := (tuning hp).2.1
  cases b <;> simp [estimate, score, norm_smul, Real.norm_eq_abs, ha, abs_of_pos hr]

lemma measurable_estimate (p : Params) : Measurable (Function.uncurry (estimate p)) := by
  unfold Function.uncurry estimate
  have hb : Measurable score := Measurable.of_discrete
  fun_prop

set_option maxHeartbeats 1200000 in
lemma estimate_mean {Ω : Type} [MeasurableSpace Ω] {p : Params}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hp : spec.valid p)
    {f : Point p.d → ℝ} {ρ : ℝ → ℝ}
    {g : (Ball p.d × Ball p.d) → Ω → Bool} (hg : Measurable (Function.uncurry g))
    (hmean : ∀ x, (∫ z, score (g x z) ∂ν) = ρ (f x.1.val - f x.2.val))
    (s : State p.d) :
    (∫ z : Draw p.d × Ω, estimate p z.1 (g (query p s z.1) z.2)
      ∂(drawLaw p : Measure _).prod ν) =
    ∫ v : Direction p.d, ((p.d / radius p) *
      value (p := p) f ρ s.2.1 ((1-radius p) • (s.2.1 : Point p.d)+radius p • (v : Point p.d))) •
      (v : Point p.d) ∂(sphereLaw (Point p.d) : Measure _) := by
  have hq : Measurable (query p s) := (measurable_query p).of_uncurry_left (x := s)
  have hbit : Measurable (fun z : Draw p.d × Ω => g (query p s z.1) z.2) :=
    hg.comp ((hq.comp measurable_fst).prodMk measurable_snd)
  have hme := (measurable_estimate p).comp (measurable_fst.prodMk hbit)
  have hi : Integrable (fun z : Draw p.d × Ω => estimate p z.1 (g (query p s z.1) z.2))
      ((drawLaw p : Measure _).prod ν) :=
    Integrable.of_bound hme.aestronglyMeasurable (p.d / radius p)
      (Filter.Eventually.of_forall fun z => (norm_estimate p hp _ _).le)
  rw [integral_prod _ hi]
  let z : Point p.d := (1-radius p) • (s.2.1 : Point p.d)
  let val := fun (a : Draw p.d) => ρ (f (z+radius p • (a.1 : Point p.d)) - f (anchor p s.2.1 a.2))
  have hs := spacing_bounds hp.2.2.2.1
  obtain ⟨_, hh, hrad, _⟩ := tuning hp
  have he (a : Draw p.d) : (∫ ω, estimate p a (g (query p s a) ω) ∂ν) =
      ((p.d / radius p) * val a) • (a.1 : Point p.d) := by
    unfold estimate
    rw [integral_smul_const,integral_const_mul,hmean]
    congr 3
    dsimp only [query, val]
    rw [retract_eq (convex_ball s.2.1.property
      (mem_ball (mem_sphere_zero_iff_norm.mp a.1.property).le) hh.le (hrad.trans hs.2.1)),
      retract_eq (anchor_bounds s.2.1.property hs.1 hs.2.1 a.2).1]
  simp_rw [he]
  let V := fun a : Draw p.d => ((p.d / radius p) * val a) • (a.1 : Point p.d)
  have hV : Integrable V (drawLaw p : Measure _) := by
    have h := hi.integral_prod_left
    simpa only [he,V] using h
  change (∫ a : Direction p.d × Fin 3, V a ∂(sphereLaw (Point p.d) : Measure (Direction p.d)).prod (PMF.uniformOfFintype (Fin 3)).toMeasure) = _
  rw [integral_prod _ hV]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [uniform_integral_explicit]
  simp [V, val, value, mean3, z, Fin.sum_univ_succ, ← add_smul, smul_smul]
  congr 1
  ring

end LongTails.Proofs.DuelingReferenceSampling
