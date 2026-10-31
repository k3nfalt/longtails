import LongTails.Proofs.FairTrackingBounds
import LongTails.Proofs.FairOracleModel
import LongTails.Proofs.FairDescent

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma trajectory_distance (cfg : Config) (hη : 0 ≤ cfg.η) (g : E → Ω → E) (x0 : E)
    (ξ : ℕ → Fin cfg.m → Ω) (t : ℕ) :
    ‖(trajectory cfg g x0 ξ t).1 - (trajectory cfg g x0 ξ t).2.1‖ ≤ cfg.η := by
  cases t with
  | zero => simpa only [trajectory, sub_self, norm_zero] using hη
  | succ t => exact NormalizedStorm.stormStep_dist hη _ _

lemma trajectory_gradient_bound (cfg : Config) (hη : 0 ≤ cfg.η)
    {f : E → ℝ} {F : E → E} {L Δ : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ)
    (hF : ∀ x, HasGradientAt f (F x) x)
    (hLip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (g : E → Ω → E) (x0 : E) (hgap : ∀ x, f x0 - f x ≤ Δ)
    (hG : Real.sqrt (2 * L * Δ) + L * cfg.T * cfg.η ≤ cfg.G)
    (ξ : ℕ → Fin cfg.m → Ω) {t : ℕ} (ht : t ≤ cfg.T) :
    ‖F (trajectory cfg g x0 ξ t).1‖ ≤ cfg.G := by
  have he := path_gradient_bound hL hΔ hη hF hLip
    (fun j => (trajectory cfg g x0 ξ j).1) (direction cfg g x0 ξ)
    (T := cfg.T) (fun j _ => trajectory_step cfg g x0 ξ j) hgap ht
  apply he.trans (le_trans ?_ hG)
  gcongr

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma local_refresh_bounds (cfg : Config) {k : ℕ} (hk : 0 < k) (hm : cfg.m = 4 * k)
    (hR : 0 < cfg.R) (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B)
    {p : Measure Ω} [IsProbabilityMeasure p] {g : E → Ω → E} {F : E → E} {r : ℝ}
    (hg : Measurable (Function.uncurry g)) (hrR : r ≤ cfg.R) (t : ℕ)
    (href : cfg.isRefresh t = true) (x y : E) (hx : ‖F x‖ ≤ cfg.G)
    (hs : p.map (fun ω => g x ω - F x) = p.map (fun ω => -(g x ω - F x)))
    (hp : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64) :
    ‖localBias cfg (Measure.pi fun _ : Fin cfg.m => p) g F t x y‖ ≤
      (2 * cfg.G + 3 * cfg.R) * (1 / 4 : ℝ) ^ k ∧
    observationVariance cfg (Measure.pi fun _ : Fin cfg.m => p) g t x y ≤
      9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * (1 / 4 : ℝ) ^ k := by
  have hb := oracle_refresh_bias hg hR hrR hk x hx hs hp
  have hv := oracle_refresh_second_moment hg hR hrR hk x hx hp
  rw [← hm] at hb hv
  have hv' : (∫ ξ, ‖blockObservation cfg g t x y ξ - F x‖ ^ 2
      ∂(Measure.pi fun _ : Fin cfg.m => p)) ≤
      9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * (1 / 4 : ℝ) ^ k := by
    simpa only [blockObservation, href, ite_true] using hv.2
  constructor
  · simpa only [localBias, observationMean, blockObservation, href, ite_true] using hb
  · have hvi : Integrable (fun ξ => ‖blockObservation cfg g t x y ξ - F x‖ ^ 2)
        (Measure.pi fun _ : Fin cfg.m => p) := by
      simpa only [blockObservation, href, ite_true] using hv.1
    exact (centered_moment_le (integrable_blockObservation cfg (by omega) hR hG hB
      (Measure.pi fun _ : Fin cfg.m => p) hg t x y) (F x) hvi).2.trans hv'

lemma local_increment_bounds (cfg : Config) {k : ℕ} (hk : 0 < k) (hm : cfg.m = 4 * k)
    (hR : 0 < cfg.R) (hG : 0 ≤ cfg.G) (hB : 0 < cfg.B)
    {p : Measure Ω} [IsProbabilityMeasure p] {g : E → Ω → E} {F : E → E} {r κ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hr : 0 ≤ r) (hrR : r ≤ cfg.R) (t : ℕ)
    (href : cfg.isRefresh t ≠ true) (x y : E) (hxy : ‖F x - F y‖ ≤ cfg.B / 2)
    (hd : ‖x - y‖ ≤ cfg.η)
    (hsX : p.map (fun ω => g x ω - F x) = p.map (fun ω => -(g x ω - F x)))
    (hsY : p.map (fun ω => g y ω - F y) = p.map (fun ω => -(g y ω - F y)))
    (hpX : p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64)
    (hpY : p.real {ω | r < ‖g y ω - F y‖} ≤ 1 / 64)
    (hrel : (∫ ω, (‖(g x ω - F x) - (g y ω - F y)‖ /
      (r + ‖g x ω - F x‖ + ‖g y ω - F y‖)) ^ 2 ∂p) ≤ κ ^ 2 * ‖x - y‖ ^ 2) :
    ‖localBias cfg (Measure.pi fun _ : Fin cfg.m => p) g F t x y‖ ≤
      2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + (1 / 4 : ℝ) ^ k)) +
        4 * cfg.B * (1 / 4 : ℝ) ^ k ∧
    observationVariance cfg (Measure.pi fun _ : Fin cfg.m => p) g t x y ≤
      (2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + (1 / 4 : ℝ) ^ k) +
        8 * cfg.B ^ 2 * (1 / 4 : ℝ) ^ k := by
  have hv := oracle_increment_bounds hg hr hR hrR hk x y hB hxy hsX hsY hpX hpY hrel
  rw [← hm] at hv
  have hdi : ‖x - y‖ ^ 2 ≤ cfg.η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have henergy : (2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * ‖x - y‖ ^ 2 + (1 / 4 : ℝ) ^ k) ≤
      (2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + (1 / 4 : ℝ) ^ k) := by gcongr
  have hvi : Integrable (fun ξ => ‖blockObservation cfg g t x y ξ - (F x - F y)‖ ^ 2)
      (Measure.pi fun _ : Fin cfg.m => p) := by
    simpa only [blockObservation, href, Bool.false_eq_true, ite_false] using hv.1
  have hvar := centered_moment_le (integrable_blockObservation cfg (by omega) hR hG hB.le
    (Measure.pi fun _ : Fin cfg.m => p) hg t x y) (F x - F y) hvi
  constructor
  · have hb' := hv.2.1.trans (add_le_add
      (mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 2 / cfg.B)) le_rfl)
    simpa only [localBias, observationMean, blockObservation, href, Bool.false_eq_true, ite_false] using hb'
  · have hv' : (∫ ξ, ‖blockObservation cfg g t x y ξ - (F x - F y)‖ ^ 2
        ∂(Measure.pi fun _ : Fin cfg.m => p)) ≤
        (2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + (1 / 4 : ℝ) ^ k) +
          8 * cfg.B ^ 2 * (1 / 4 : ℝ) ^ k := by
      simpa only [blockObservation, href, Bool.false_eq_true, ite_false] using
        hv.2.2.trans (add_le_add henergy le_rfl)
    exact hvar.2.trans hv'

lemma trajectory_oracle_bounds (cfg : Config) {k : ℕ} (hk : 0 < k) (hm : cfg.m = 4 * k)
    (hR : 0 < cfg.R) (hB : 0 < cfg.B) (hη : 0 ≤ cfg.η)
    {p : Measure Ω} [IsProbabilityMeasure p] {g : E → Ω → E} {F : E → E}
    {f : E → ℝ} {r κ L Δ : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hr : 0 ≤ r)
    (hg : Measurable (Function.uncurry g)) (hrR : r ≤ cfg.R)
    (hF : ∀ x, HasGradientAt f (F x) x)
    (hLip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (x0 : E) (hgap : ∀ x, f x0 - f x ≤ Δ)
    (hG : Real.sqrt (2 * L * Δ) + L * cfg.T * cfg.η ≤ cfg.G)
    (hstep : L * cfg.η ≤ cfg.B / 2)
    (hs : ∀ x, p.map (fun ω => g x ω - F x) = p.map (fun ω => -(g x ω - F x)))
    (hp : ∀ x, p.real {ω | r < ‖g x ω - F x‖} ≤ 1 / 64)
    (hrel : ∀ x y, (∫ ω, (‖(g x ω - F x) - (g y ω - F y)‖ /
      (r + ‖g x ω - F x‖ + ‖g y ω - F y‖)) ^ 2 ∂p) ≤ κ ^ 2 * ‖x - y‖ ^ 2)
    (ξ : ℕ → Fin cfg.m → Ω) {t : ℕ} (ht : t < cfg.T) :
    ‖localBias cfg (Measure.pi fun _ : Fin cfg.m => p) g F t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1‖ ≤
      (if cfg.isRefresh t then (2 * cfg.G + 3 * cfg.R) * (1 / 4 : ℝ) ^ k
      else 2 / cfg.B * ((2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + (1 / 4 : ℝ) ^ k)) +
        4 * cfg.B * (1 / 4 : ℝ) ^ k) ∧
    observationVariance cfg (Measure.pi fun _ : Fin cfg.m => p) g t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 ≤
      (if cfg.isRefresh t then 9 * cfg.R ^ 2 + (2 * cfg.G + 3 * cfg.R) ^ 2 * (1 / 4 : ℝ) ^ k
      else (2 : ℝ) ^ 23 * cfg.R ^ 2 * (κ ^ 2 * cfg.η ^ 2 + (1 / 4 : ℝ) ^ k) +
        8 * cfg.B ^ 2 * (1 / 4 : ℝ) ^ k) := by
  have hG0 : 0 ≤ cfg.G := le_trans (by positivity) hG
  by_cases href : cfg.isRefresh t = true
  · simp only [href, ite_true]
    exact local_refresh_bounds cfg hk hm hR hG0 hB.le hg hrR t href _ _
      (trajectory_gradient_bound cfg hη hL hΔ hF hLip g x0 hgap hG ξ ht.le) (hs _) (hp _)
  · simp only [href, Bool.false_eq_true, ite_false]
    have hd := trajectory_distance cfg hη g x0 ξ t
    have hgrad := (hLip (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1).trans
      ((mul_le_mul_of_nonneg_left hd hL.le).trans hstep)
    exact local_increment_bounds cfg hk hm hR hG0 hB hg hr hrR t href _ _ hgrad hd
      (hs _) (hs _) (hp _) (hp _) (hrel _ _)

end OracleTemplate.FairVarianceReduction
