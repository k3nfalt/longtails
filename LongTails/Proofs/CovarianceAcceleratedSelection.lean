import LongTails.Proofs.CovarianceAcceleratedVariational
import Mathlib.Topology.Maps.Proper.Basic

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedVariational

namespace LongTails.Proofs.CovarianceAcceleratedSelection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} (z : Fin n → E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mean_continuous : Continuous (mean z) := by
  unfold mean
  fun_prop

lemma linearLoss_continuous :
    Continuous (fun q : (Fin n → ℝ) × StdSimplex ℝ (Fin n) => linearLoss q.1 q.2) := by
  unfold linearLoss
  fun_prop

lemma potential_continuous (a β γ : ℝ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Continuous (fun q : StdSimplex ℝ (Fin n) × StdSimplex ℝ (Fin n) =>
      potential z a β γ q.1 q.2) := by
  have hd := divergence_continuous z hM hz
  have hm := mean_continuous z
  unfold potential
  fun_prop

lemma objective_continuous (a β γ : ℝ) {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Continuous (fun q : ((Fin n → ℝ) × StdSimplex ℝ (Fin n)) × StdSimplex ℝ (Fin n) =>
      linearLoss q.1.1 q.2 + potential z a β γ q.2 q.1.2) := by
  exact (linearLoss_continuous.comp (continuous_fst.fst.prodMk continuous_snd)).add
    ((potential_continuous z a β γ hM hz).comp (continuous_snd.prodMk continuous_fst.snd))

lemma exists_minimizer (a β γ : ℝ) (c : Fin n → ℝ) (p : StdSimplex ℝ (Fin n))
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    ∃ w, ∀ u, linearLoss c w + potential z a β γ w p ≤
      linearLoss c u + potential z a β γ u p := by
  have hf := (objective_continuous z a β γ hM hz).comp
    ((continuous_const : Continuous (fun _ : StdSimplex ℝ (Fin n) => (c, p))).prodMk continuous_id)
  obtain ⟨w, _, hw⟩ := isCompact_univ.exists_isMinOn ⟨p, Set.mem_univ _⟩
    (show ContinuousOn (fun w => linearLoss c w + potential z a β γ w p) Set.univ from
      hf.continuousOn)
  exact ⟨w, fun u => hw (Set.mem_univ u)⟩

lemma update_minimizes (a β γ : ℝ) (c : Fin n → ℝ) (p : StdSimplex ℝ (Fin n))
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    ∀ u, linearLoss c (update z a β γ c p) + potential z a β γ (update z a β γ c p) p ≤
      linearLoss c u + potential z a β γ u p := by
  exact Classical.epsilon_spec (exists_minimizer z a β γ c p hM hz)

lemma update_continuous (a β γ : ℝ) (hβ : 0 ≤ β) (hγ : 0 < γ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Continuous (fun q : (Fin n → ℝ) × StdSimplex ℝ (Fin n) => update z a β γ q.1 q.2) := by
  apply continuous_of_isClosed_graph
  have he : (fun q : (Fin n → ℝ) × StdSimplex ℝ (Fin n) => update z a β γ q.1 q.2).graph =
      {q | ∀ u, linearLoss q.1.1 q.2 + potential z a β γ q.2 q.1.2 ≤
        linearLoss q.1.1 u + potential z a β γ u q.1.2} := by
    ext ⟨⟨c, p⟩, w⟩
    change update z a β γ c p = w ↔ ∀ u, linearLoss c w + potential z a β γ w p ≤
      linearLoss c u + potential z a β γ u p
    constructor
    · intro h
      rw [← h]
      exact update_minimizes z a β γ c p hM hz
    · intro h
      exact minimizer_unique z (update z a β γ c p) w p c a β γ hβ hγ hM hz
        (update_minimizes z a β γ c p hM hz) h
  rw [he, Set.ofPred_forall]
  apply isClosed_iInter
  intro u
  apply isClosed_le (objective_continuous z a β γ hM hz)
  exact (objective_continuous z a β γ hM hz).comp
    (continuous_fst.prodMk continuous_const)

lemma clipped_integrand_integrable (x0 : E) (a α : ℝ) (b h g : E) (i : Fin n) :
    Integrable (fun u => density (z i) u *
      max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))) (stdGaussian E) := by
  apply (CovarianceAcceleratedTilt.gaussian_density_integrable (z i)).mono' ?_
    (Filter.Eventually.of_forall fun u => ?_)
  · have hm : Measurable (fun u => density (z i) u *
        max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))) := by
      unfold density
      fun_prop
    exact hm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    unfold density
    rw [abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (CovarianceAcceleratedClipping.clip_abs_le _)
      (Real.exp_pos _).le).trans_eq (mul_one _)

lemma coefficients_continuous (x0 : E) (a α : ℝ) :
    Continuous (fun q : E × E × E => coefficients z x0 a α q.1 q.2.1 q.2.2) := by
  apply continuous_pi
  intro i
  unfold coefficients
  apply Continuous.add (by fun_prop)
  apply continuous_of_dominated (bound := density (z i))
  · intro q
    exact (clipped_integrand_integrable z x0 a α q.1 q.2.1 q.2.2 i).aestronglyMeasurable
  · intro q
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_mul]
    unfold density
    rw [abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (CovarianceAcceleratedClipping.clip_abs_le _)
      (Real.exp_pos _).le).trans_eq (mul_one _)
  · exact CovarianceAcceleratedTilt.gaussian_density_integrable _
  · filter_upwards [] with u
    fun_prop

lemma step_continuous (x0 : E) (a α β γ : ℝ) (hβ : 0 ≤ β) (hγ : 0 < γ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    Continuous (fun q : StdSimplex ℝ (Fin n) × E × E => step z x0 a α β γ q.1 q.2.1 q.2.2) := by
  have hm := mean_continuous z
  have hb : Continuous (fun q : StdSimplex ℝ (Fin n) × E × E =>
      x0 + a • mean z q.1) := by fun_prop
  have hc := (coefficients_continuous z x0 a α).comp
    (hb.prodMk (continuous_snd.fst.prodMk continuous_snd.snd))
  exact (update_continuous z a β γ hβ hγ hM hz).comp (hc.prodMk continuous_fst)

end LongTails.Proofs.CovarianceAcceleratedSelection
