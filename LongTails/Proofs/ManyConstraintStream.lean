import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.ManyConstraintStream

open OracleTemplate.StochasticGeneralized

variable {Ξ : Type*} [MeasurableSpace Ξ] (law : Measure Ξ) [IsProbabilityMeasure law]

lemma integral_block (b : ℕ) (G : (Fin b → Ξ) × (ℕ → Ξ) → ℝ) (hG : Measurable G) {C : ℝ}
    (hC : ∀ p, |G p| ≤ C) :
    ∫ ξ, G ((fun i => ξ i), (fun t => ξ (b + 2 + t))) ∂(Measure.infinitePi fun _ : ℕ => law) =
      ∫ w, ∫ t, G (w, t) ∂(Measure.infinitePi fun _ : ℕ => law)
        ∂(Measure.pi fun _ : Fin b => law) := by
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hb := splitStream_preserving law b
  have h2 := splitStream_preserving law 2
  set g : (Fin b → Ξ) × (ℕ → Ξ) → ℝ := fun p => G (p.1, fun t => p.2 (2 + t)) with hg
  have hgm : Measurable g := hG.comp (measurable_fst.prodMk (by fun_prop))
  have hfun : (fun ξ : ℕ → Ξ => G ((fun i => ξ i), (fun t => ξ (b + 2 + t)))) =
      fun ξ => g (splitStream b ξ) := by
    funext ξ
    simp only [hg, splitStream]
    congr 2
    funext t
    congr 1
    omega
  rw [hfun, hb.integral_comp' g]
  have hgi : Integrable g ((Measure.pi fun _ : Fin b => law).prod inf) :=
    Integrable.of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_prod g hgi]
  congr 1
  funext w
  set g2 : (Fin 2 → Ξ) × (ℕ → Ξ) → ℝ := fun q => G (w, q.2) with hg2
  have hg2m : Measurable g2 := hG.comp (measurable_const.prodMk measurable_snd)
  have hfun2 : (fun t1 : ℕ → Ξ => g (w, t1)) = fun t1 => g2 (splitStream 2 t1) := by
    funext t1; simp [hg, hg2, splitStream]
  change ∫ t1, g (w, t1) ∂inf = _
  rw [hfun2, h2.integral_comp' g2]
  have hg2i : Integrable g2 ((Measure.pi fun _ : Fin 2 => law).prod inf) :=
    Integrable.of_bound hg2m.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_prod g2 hg2i]
  simp [hg2]

lemma integral_skip (c : ℕ) (G : (ℕ → Ξ) → ℝ) (hG : Measurable G) {C : ℝ}
    (hC : ∀ p, |G p| ≤ C) :
    ∫ ξ, G (fun t => ξ (c + t)) ∂(Measure.infinitePi fun _ : ℕ => law) =
      ∫ t, G t ∂(Measure.infinitePi fun _ : ℕ => law) := by
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hc := splitStream_preserving law c
  set g : (Fin c → Ξ) × (ℕ → Ξ) → ℝ := fun p => G p.2 with hg
  have hgm : Measurable g := hG.comp measurable_snd
  have hfun : (fun ξ : ℕ → Ξ => G (fun t => ξ (c + t))) = fun ξ => g (splitStream c ξ) := by
    funext ξ; simp [hg, splitStream]
  rw [hfun, hc.integral_comp' g]
  have hgi : Integrable g ((Measure.pi fun _ : Fin c => law).prod inf) :=
    Integrable.of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  rw [integral_prod g hgi]
  simp [hg]

lemma integral_prefix (n : ℕ) (G : (Fin n → Ξ) × (ℕ → Ξ) → ℝ) (hG : Measurable G) {C : ℝ}
    (hC : ∀ p, |G p| ≤ C) :
    ∫ ξ, G ((fun i => ξ i), (fun t => ξ (n + t))) ∂(Measure.infinitePi fun _ : ℕ => law) =
      ∫ w, ∫ t, G (w, t) ∂(Measure.infinitePi fun _ : ℕ => law)
        ∂(Measure.pi fun _ : Fin n => law) := by
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hn := splitStream_preserving law n
  have hfun : (fun ξ : ℕ → Ξ => G ((fun i => ξ i), (fun t => ξ (n + t)))) =
      fun ξ => G (splitStream n ξ) := by
    funext ξ; simp [splitStream]
  rw [hfun, hn.integral_comp' G]
  have hgi : Integrable G ((Measure.pi fun _ : Fin n => law).prod inf) :=
    Integrable.of_bound hG.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  exact integral_prod G hgi

lemma integral_prefix_only (n : ℕ) (H : (Fin n → Ξ) → ℝ) (hH : Measurable H) :
    ∫ w, H w ∂(Measure.pi fun _ : Fin n => law) =
      ∫ ξ, H (fun i => ξ i) ∂(Measure.infinitePi fun _ : ℕ => law) := by
  have hp := prefix_preserving law n
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable hH.aestronglyMeasurable]

end LongTails.Proofs.ManyConstraintStream
