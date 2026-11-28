import LongTails.Proofs.HighProbabilityPhaseOne
import LongTails.Proofs.HeavyTailedHighProbabilityStep

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedHighProbabilityPhaseOne

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient
open LongTails.Proofs.HighProbabilityAdapted LongTails.Proofs.HighProbabilityExecution
open LongTails.Proofs.HighProbabilityEstimator LongTails.Proofs.HighProbabilityStep
open LongTails.Proofs.HighProbabilityPhaseOne LongTails.Proofs.HeavyTailedHighProbabilityStep
open LongTails.Proofs.HighProbabilityDescent

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
lemma ok_tail_heavy {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {G : E → E}
    (hG : Measurable G) (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = G x)
    {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ α) p)
    (hpm : ∀ x, (∫ ω, ‖g x ω - G x‖ ^ α ∂p) ≤ s ^ α) (hs : 0 ≤ s) {σ : ℝ} (hσ : 0 ≤ σ)
    {B η : ℝ} (hlink : 2 * s ^ α * B ^ (2 - α) ≤ σ ^ 2) (hB : 0 < B) {K mp mc : ℕ}
    (hmc : 0 < mc) (x0 : E) (T : ℕ) (r : ℝ) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (mp + mc) => p).real
      {b | r ≤ ∑ t ∈ Finset.range T, okError B K mp mc (g (traj (stepMap B η K mp mc g) x0 b t))
        (G (traj (stepMap B η K mp mc g) x0 b t)) (b t)} ≤
      Real.exp (T * (Real.log 5 + (clipRadius σ B mc 0 / mc + 12 * B / mc) / (2 * (12 * B / mc)))
        - 1 / (2 * (12 * B / mc)) * r) := by
  have ha1 : 0 < 12 * B / mc := by positivity
  have hθ : 0 ≤ 1 / (2 * (12 * B / mc)) := by positivity
  have hfun (x : E) : (fun z => Real.exp (1 / (2 * (12 * B / mc)) * okError B K mp mc (g x) (G x) z)) =
      fun z => Real.exp (okError B K mp mc (g x) (G x) z / (2 * (12 * B / mc))) := by
    funext z; congr 1; ring
  refine adapted_tail (measurable_stepMap B η K mp mc hg) x0
    (measurable_okError_joint B K mp mc hg hG) hθ (fun x => ?_) (fun x => ?_) T r
  · have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
    have h := (block_ok_mgf_heavy (K := K) (mp := mp) hgx (hgi x) (hmean x) hα1 hα2 (hpi x)
      (hpm x) hs hσ hlink hB hmc).1
    rw [hfun x]
    exact h
  · have hgx : Measurable (g x) := hg.comp measurable_prodMk_left
    have h := (block_ok_mgf_heavy (K := K) (mp := mp) hgx (hgi x) (hmean x) hα1 hα2 (hpi x)
      (hpm x) hs hσ hlink hB hmc).2
    rw [hfun x, Real.exp_add, Real.exp_log (by norm_num)]
    exact h

lemma phase_one_prob_heavy {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {f : E → ℝ}
    {L η Δ fstar B Gcap ra σ : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hB : 0 < B) (hσ : 0 ≤ σ)
    {K mp mc J T : ℕ} (hmc : 0 < mc)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlow : ∀ y, fstar ≤ f y)
    (hgm : Measurable (gradient f)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ α) p)
    (hpm : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ α ∂p) ≤ s ^ α) (hs : 0 ≤ s)
    (hlink : 2 * s ^ α * B ^ (2 - α) ≤ σ ^ 2)
    (hJ : Gcap ≤ 4 * (2 ^ J * B)) (hG : 0 ≤ Gcap) (m : ℕ → ℝ) (n : ℕ → ℕ)
    (hρ : ∀ j ∈ Finset.range (J + 1), ∀ x, (Measure.pi fun _ : Fin (mp + mc) => p)
      {z | 2 ^ j * B / 2 < ‖pilotOf B K mp mc (g x) z - gradient f x‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * n j)))
    (x0 : E) (hgap : f x0 - fstar ≤ Δ)
    (hroom : 2 * L * (Δ + η * (2 * ra + ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j) +
      T * (L / 2 * η ^ 2)) ≤ Gcap ^ 2) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (mp + mc) => p).real
      {b | Δ + η * (2 * ra + ∑ j ∈ Finset.range (J + 1), 8 * (2 ^ j * B) * m j) +
        T * (L / 2 * η ^ 2) <
        η * ∑ t ∈ Finset.range T, ‖gradient f (traj (stepMap B η K mp mc g) x0 b t)‖} ≤
      Real.exp (T * (Real.log 5 + (clipRadius σ B mc 0 / mc + 12 * B / mc) / (2 * (12 * B / mc)))
        - 1 / (2 * (12 * B / mc)) * ra) +
      ∑ j ∈ Finset.range (J + 1), Real.exp (T * (1 / 2 : ℝ) ^ n j - n j * Real.log 2 * m j) := by
  refine (measureReal_mono (bad_subset (K := K) hL hη hB hmc hgrad hlip hlow hJ hG m x0 hgap
    hroom)).trans ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
  · exact ok_tail_heavy hg hgm hgi hmean hα1 hα2 hpi hpm hs hσ hlink hB hmc x0 T ra
  · refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    exact scale_tail hg hgm (n j) (hρ j hj) x0 T (m j)

end LongTails.Proofs.HeavyTailedHighProbabilityPhaseOne
