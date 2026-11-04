import LongTails.Proofs.QuarticTraceExtension
import LongTails.Proofs.QuarticTrialGuarantee
import LongTails.Proofs.QuarticAccelerationRate

namespace LongTails.Proofs.AcceleratedQuarticExecution

open LongTails.Algorithms.AcceleratedQuarticNewton
open LongTails.Algorithms.QuarticProximalTrial LongTails.Algorithms.QuarticAcceleration
open LongTails.Proofs.QuarticAccelerationTrace LongTails.Proofs.QuarticTraceExtension
open LongTails.Proofs.QuarticTrialExecution
open scoped RealInnerProductSpace Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def GoodAt (f : E → ℝ) (ε γ : ℝ) (x0 xstar : E) (k : ℕ) : Status E → Prop
  | .initial => k = 0
  | .running μ s => ∃ t : Trace E, Valid t f γ x0 k ∧ 0 < k ∧ t.state k = s ∧ t.guess k = μ
  | .finished y => f y - f xstar ≤ ε
  | .failed => False

lemma proximal_support {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε γ : ℝ} {c xstar y g : E} (hv : ValidAt f ε γ c xstar (.proximal y g)) :
    (∀ x, f y + ⟪g, x - y⟫ ≤ f x) ∧
      ‖g + (parameter E γ c y) • (y - c)‖ ≤ γ * ‖y - c‖ ^ 3 / 32 := by
  constructor
  · intro x
    rw [hv.1]
    have hh := OracleTemplate.Gradient.convex_support hc (fun x => (hf x).hasGradientAt) y x
    linarith only [hh]
  · simpa only [LongTails.Algorithms.QuarticProximal.grad, smul_smul, parameter] using hv.2

lemma zero_accurate {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε γ : ℝ} (hε : 0 ≤ ε) (hγ : 0 < γ) {c xstar y g : E}
    (hv : ValidAt f ε γ c xstar (.proximal y g)) (hz : parameter E γ c y = 0) : f y - f xstar ≤ ε := by
  have hh := proximal_support hf hc hv
  have hmin := LongTails.Proofs.QuarticAcceleration.zero_residual_min hγ c y g hh.1 hz hh.2
  linarith [hmin xstar]

lemma receive_initial_good {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε γ : ℝ} (hε : 0 ≤ ε) (hγ : 0 < γ) (x0 xstar : E) (result : TrialResult E)
    (hv : ValidAt f ε γ x0 xstar result) :
    GoodAt f ε γ x0 xstar 1 (receive E γ x0 .initial result) := by
  classical
  cases result with
  | accurate y => exact hv
  | failed => exact False.elim hv
  | proximal y g =>
    have hh := proximal_support hf hc hv
    by_cases hz : parameter E γ x0 y = 0
    · simp only [receive, queryCenter]
      erw [ite_eq_left hz]
      exact zero_accurate hf hc hε hγ hv hz
    · have hlam : 0 < parameter E γ x0 y := by
        have hn : 0 ≤ parameter E γ x0 y := mul_nonneg hγ.le (sq_nonneg _)
        exact lt_of_le_of_ne hn (Ne.symm hz)
      simp only [receive, queryCenter]
      erw [ite_eq_right hz]
      refine ⟨startTrace γ x0 y g, start_valid x0 y g hlam hh.1 hh.2, by norm_num, ?_, ?_⟩
      · exact (start_end x0 y g hlam).1
      · exact (start_end x0 y g hlam).2

lemma receive_running_good {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε γ : ℝ} (hε : 0 ≤ ε) (hγ : 0 < γ) (x0 xstar : E) {k : ℕ}
    (μ : ℝ) (s : LongTails.Algorithms.CompositeCubicAcceleration.State E)
    (hgood : GoodAt f ε γ x0 xstar k (.running μ s)) (result : TrialResult E)
    (hv : ValidAt f ε γ (LongTails.Algorithms.CompositeCubicAcceleration.center E μ s) xstar result) :
    GoodAt f ε γ x0 xstar (k + 1) (receive E γ x0 (.running μ s) result) := by
  classical
  obtain ⟨t, ht, hk, hs, hμ⟩ := hgood
  have hloc : location t k = LongTails.Algorithms.CompositeCubicAcceleration.center E μ s := by
    simp only [location, hs, hμ]
  cases result with
  | accurate y => exact hv
  | failed => exact False.elim hv
  | proximal y g =>
    have hh := proximal_support hf hc hv
    by_cases hz : parameter E γ (LongTails.Algorithms.CompositeCubicAcceleration.center E μ s) y = 0
    · simp only [receive, queryCenter]
      erw [ite_eq_left hz]
      exact zero_accurate hf hc hε hγ hv hz
    · have hlam : 0 < parameter E γ (location t k) y := by
        rw [hloc]
        exact lt_of_le_of_ne (mul_nonneg hγ.le (sq_nonneg _)) (Ne.symm hz)
      simp only [receive, queryCenter]
      erw [ite_eq_right hz]
      refine ⟨append t k γ y g, ?_, by omega, ?_, ?_⟩
      · apply append_valid ht y g hlam (by intro he; omega) hh.1
        simpa only [hloc] using hh.2
      · simpa only [hs, hμ] using (append_next t k γ y g).1
      · simpa only [hμ, hloc] using (append_next t k γ y g).2

omit [FiniteDimensional ℝ E] in
lemma good_center {f : E → ℝ} (hc : ConvexOn ℝ Set.univ f) {ε γ R : ℝ} (hγ : 0 < γ)
    (x0 xstar : E) (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x)
    {k : ℕ} (status : Status E) (hgood : GoodAt f ε γ x0 xstar k status) :
    ‖queryCenter E x0 status - xstar‖ ≤ (1 + 3 * (k : ℝ)) * R := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hx0
  have hscale : R ≤ (1 + 3 * (k : ℝ)) * R := by nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hR]
  cases status with
  | initial => exact hx0.trans hscale
  | finished y => exact hx0.trans hscale
  | failed => exact False.elim hgood
  | running μ s =>
    obtain ⟨t, ht, _, hs, hμ⟩ := hgood
    have hh := (QuarticAccelerationRadius.point_center_radius ht hc hγ hx0 hmin k le_rfl).2
    simpa only [location, hs, hμ, queryCenter] using hh

omit [FiniteDimensional ℝ E] in
lemma good_output_accuracy {f : E → ℝ} (hc : ConvexOn ℝ Set.univ f)
    {ε γ R : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hR : 0 < R)
    (x0 xstar : E) (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x)
    {N : ℕ} (hbudget : 64 * (1 + (γ * R ^ 4 / ε) ^ (1 / 5 : ℝ)) ≤ (N : ℝ))
    (status : Status E) (hgood : GoodAt f ε γ x0 xstar N status) :
    f (output x0 status) - f xstar ≤ ε := by
  cases status with
  | initial =>
    change N = 0 at hgood
    rw [hgood] at hbudget
    have hp : 0 < 64 * (1 + (γ * R ^ 4 / ε) ^ (1 / 5 : ℝ)) := by positivity
    norm_num at hbudget
    linarith
  | finished y => exact hgood
  | failed => exact False.elim hgood
  | running μ s =>
    obtain ⟨t, ht, _, hs, _⟩ := hgood
    have hh := QuarticAccelerationRate.objective_accuracy ht hc hγ hR hε hx0 hmin hbudget
    simpa only [hs, output] using hh

lemma center_scale {Q : ℝ} (hQ : 3 ≤ Q) {N k : ℕ} (hk : k ≤ N) (hN : (N : ℝ) ≤ 256 * Q) :
    1 + 3 * (k : ℝ) ≤ Q ^ 8 := by
  have h7 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 7
  have hcast : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hh := mul_le_mul_of_nonneg_right h7 (by linarith : 0 ≤ Q)
  norm_num at hh
  have he : Q ^ 7 * Q = Q ^ 8 := by ring
  rw [he] at hh
  nlinarith only [hN, hcast, hh, hQ]


lemma round_preserves {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε R Q L γ : ℝ} (hε : 0 ≤ ε) (hγ : 0 < γ) (x0 xstar : E) {n k : ℕ} [NeZero n]
    (oracle : Fin n × E → LongTails.Algorithms.TaylorCorrectedNewton.Reply E)
    (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q))
    (status : Status E) (hgood : GoodAt f ε γ x0 xstar k status)
    (hcert : ValidAt f ε γ (queryCenter E x0 status) xstar
      (OracleTemplate.QueryPlan.eval oracle (trial ε R Q L γ x0 (queryCenter E x0 status) seed))) :
    GoodAt f ε γ x0 xstar (k + 1) (OracleTemplate.QueryPlan.eval oracle (round ε R Q L γ x0 seed status)) := by
  cases status with
  | initial =>
    change k = 0 at hgood
    subst k
    simp only [LongTails.Algorithms.AcceleratedQuarticNewton.round, OracleTemplate.QueryPlan.eval_map]
    exact receive_initial_good hf hc hε hγ x0 xstar _ hcert
  | running μ s =>
    simp only [LongTails.Algorithms.AcceleratedQuarticNewton.round, OracleTemplate.QueryPlan.eval_map]
    exact receive_running_good hf hc hε hγ x0 xstar μ s hgood _ hcert
  | finished y =>
    rw [LongTails.Algorithms.AcceleratedQuarticNewton.round, eval_padResult]
    exact hgood
  | failed => exact False.elim hgood

lemma round_bad_le {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ Set.univ f)
    {ε R Q L γ : ℝ} (hε : 0 ≤ ε) (hγ : 0 < γ) (x0 xstar : E) {n k : ℕ} [NeZero n]
    (oracle : Fin n × E → LongTails.Algorithms.TaylorCorrectedNewton.Reply E)
    (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q))
    (status : Status E) (hgood : GoodAt f ε γ x0 xstar k status)
    (hcert : OracleTemplate.QueryPlan.eval oracle (trial ε R Q L γ x0 (queryCenter E x0 status) seed) ≠ .failed →
      ValidAt f ε γ (queryCenter E x0 status) xstar
        (OracleTemplate.QueryPlan.eval oracle (trial ε R Q L γ x0 (queryCenter E x0 status) seed))) :
    (if ¬GoodAt f ε γ x0 xstar (k + 1) (OracleTemplate.QueryPlan.eval oracle (round ε R Q L γ x0 seed status))
      then (1 : ℝ) else 0) ≤
    (if OracleTemplate.QueryPlan.eval oracle (trial ε R Q L γ x0 (queryCenter E x0 status) seed) = .failed
      then (1 : ℝ) else 0) := by
  classical
  by_cases hh : OracleTemplate.QueryPlan.eval oracle (trial ε R Q L γ x0 (queryCenter E x0 status) seed) = .failed
  · simp only [hh, ↓reduceIte]
    split_ifs <;> norm_num
  · have hg := round_preserves hf hc hε hγ x0 xstar oracle seed status hgood (hcert hh)
    simp only [hg, hh, not_true_eq_false, ↓reduceIte, le_refl]


end LongTails.Proofs.AcceleratedQuarticExecution
