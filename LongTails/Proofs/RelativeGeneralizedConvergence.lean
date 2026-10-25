import LongTails.Proofs.RelativeGeneralizedStep
import LongTails.Proofs.RelativeGeneralizedGrowth
import LongTails.Proofs.RelativeGeneralizedBudget
import LongTails.Proofs.ExecutionHistory

open Set

namespace OracleTemplate.RelativeGeneralized

open LongTails.Setups.RelativeGeneralizedSmoothConvex

lemma sequence_invariant (p : Public) (N : ℕ) (I : Instance p) {u : p.E}
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (hα : 0 ≤ p.α) (hαmax : p.α ≤ 1 / 100)
    (hf : ConvexOn ℝ univ I.f) (hg : ∀ w, HasGradientAt I.f (I.grad w) w)
    (hcont : Continuous I.grad)
    (hs : CompositeGeneralized.SymmetricSmooth I.grad p.L0 p.L1)
    (hm : IsMinOn I.f univ u) (hu : ‖u - p.x0‖ ≤ p.R)
    (hinit : I.f p.x0 - I.f u ≤ p.Δ)
    (s : ℕ → State p.E) (reply : ℕ → p.E) (hs0 : s 0 = initialState p)
    (hstep : ∀ k, s (k + 1) = advance p N (s k) (reply k))
    (herr : ∀ k, ‖reply k - I.grad (queryPoint p N (s k))‖ ≤
      p.α * ‖I.grad (queryPoint p N (s k))‖) :
    ∀ k, k ≤ N → 0 < (s k).A ∧ ‖(s k).x - p.x0‖ ≤ 2 * p.R ∧
      ‖(s k).z - p.x0‖ ≤ 2 * p.R ∧
      (s k).A * (I.f (s k).x - I.f u) + 1 / 2 * ‖(s k).z - u‖ ^ 2 ≤
        (3 / 2 + p.α ^ 2 * k) * p.R ^ 2 := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [hs0]
      change 0 < p.R ^ 2 / p.Δ ∧ ‖p.x0 - p.x0‖ ≤ 2 * p.R ∧
        ‖p.x0 - p.x0‖ ≤ 2 * p.R ∧
        p.R ^ 2 / p.Δ * (I.f p.x0 - I.f u) + 1 / 2 * ‖p.x0 - u‖ ^ 2 ≤ _
      refine ⟨by positivity, by simp; positivity, by simp; positivity, ?_⟩
      have hg0 := mul_le_mul_of_nonneg_left hinit (show 0 ≤ p.R ^ 2 / p.Δ by positivity)
      have heq : p.R ^ 2 / p.Δ * p.Δ = p.R ^ 2 := div_mul_cancel₀ _ hΔ.ne'
      rw [heq] at hg0
      rw [norm_sub_rev p.x0 u]
      have hu2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      simp only [Nat.cast_zero, mul_zero, add_zero]
      nlinarith
  | succ k ih =>
      intro hk
      obtain ⟨hA, hx, hz, hpot⟩ := ih (by omega)
      have hgap : I.f (s k).x - I.f u ≤ noiseBudget p N * p.R ^ 2 / (s k).A := by
        apply (le_div_iff₀ hA).mpr
        have hkn : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
        have hh := mul_le_mul_of_nonneg_left hkn (sq_nonneg p.α)
        have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg p.R)
        unfold noiseBudget
        nlinarith [sq_nonneg ‖(s k).z - u‖, sq_nonneg p.R]
      have hnext := advance_potential p N I h0 h1 hR hα hαmax hf hg hcont hs hm hu
        (s k) hA hx hz hgap (reply k) (herr k)
      rw [hstep]
      have hB : 1 ≤ noiseBudget p N := by
        unfold noiseBudget
        nlinarith [mul_nonneg (sq_nonneg p.α) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have ha := (tuning_bounds hA hB hR h0 h1).1
      change 0 < weight p N (s k) at ha
      refine ⟨by dsimp [advance]; positivity,
        projection_feasible p hR.le _, projection_feasible p hR.le _, ?_⟩
      push_cast
      nlinarith

lemma sequence_growth (p : Public) (N : ℕ) (s : ℕ → State p.E) (reply : ℕ → p.E)
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (hR : 0 ≤ p.R)
    (hA : ∀ k, k ≤ N → 0 < (s k).A)
    (hstep : ∀ k, s (k + 1) = advance p N (s k) (reply k)) :
    let Q := 1 + p.L1 * p.R * Real.sqrt (noiseBudget p N)
    let r := fun k => Real.sqrt (p.L0 * (s k).A)
    (N : ℝ) / 12288 ≤ (r N + 2 * Q * Real.log (r N)) -
      (r 0 + 2 * Q * Real.log (r 0)) := by
  dsimp only
  let Q := 1 + p.L1 * p.R * Real.sqrt (noiseBudget p N)
  let r := fun k => Real.sqrt (p.L0 * (s k).A)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_nonneg (mul_nonneg h1 hR) (Real.sqrt_nonneg (noiseBudget p N))]
  have hincr (k : ℕ) (hk : k < N) :
      1 / 12288 ≤ (r (k + 1) + 2 * Q * Real.log (r (k + 1))) -
        (r k + 2 * Q * Real.log (r k)) := by
    have hh := weight_growth (hA k (by omega)) hQ h0
    simpa only [r, hstep, advance, weight, Q] using hh
  have hsum : ∀ k, k ≤ N → (k : ℝ) / 12288 ≤
      (r k + 2 * Q * Real.log (r k)) - (r 0 + 2 * Q * Real.log (r 0)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hi := ih (by omega)
        have hn := hincr k (by omega)
        push_cast
        linarith
  exact hsum N le_rfl

lemma execution_accuracy (p : Public) (hp : spec.valid p) (I : Instance p)
    (oracle : Oracle p.E p.E) (hadm : spec.admissible p I oracle) :
    let T := p.L0 * p.R ^ 2 / p.ε
    let q := p.L1 * p.R
    let H := 1 + Real.log (2 + T + q + p.Δ / (p.L0 * p.R ^ 2))
    let N := ⌈(2 : ℝ) ^ 60 * (Real.sqrt T + p.α ^ 2 * T + (1 + q) * H + p.α ^ 2 * q ^ 2 * H ^ 2)⌉₊
    ∃ u, IsMinOn I.f univ u ∧ ∀ seed : (k : ℕ) → oracle.Seed k,
      I.f (output p N oracle seed) - I.f u ≤ p.ε := by
  dsimp only
  let T := p.L0 * p.R ^ 2 / p.ε
  let q := p.L1 * p.R
  let d := p.Δ / (p.L0 * p.R ^ 2)
  let U := 2 + T + q + d
  let H := 1 + Real.log U
  let S := Real.sqrt T + p.α ^ 2 * T + (1 + q) * H + p.α ^ 2 * q ^ 2 * H ^ 2
  let N := ⌈(2 : ℝ) ^ 60 * S⌉₊
  change ∃ u, IsMinOn I.f univ u ∧ ∀ seed : (k : ℕ) → oracle.Seed k,
    I.f (output p N oracle seed) - I.f u ≤ p.ε
  rcases hp with ⟨h0, h1, hR, hΔ, hα, hαmax, hε⟩
  rcases hadm with ⟨herr, hf, hg, hcont, hs, u, hm, hu, hinit⟩
  have hu' : ‖u - p.x0‖ ≤ p.R := by rwa [norm_sub_rev]
  refine ⟨u, hm, ?_⟩
  intro seed
  let s := fun k => (executeIndexedState oracle (acceleration p N) () seed k).1
  let reply := fun k => executeAnswerAt oracle (acceleration p N) () seed k
    ((acceleration p N).query (s k))
  have hs0 : s 0 = initialState p := rfl
  have hstep (k : ℕ) : s (k + 1) = advance p N (s k) (reply k) := rfl
  have herr' (k : ℕ) : ‖reply k - I.grad (queryPoint p N (s k))‖ ≤
      p.α * ‖I.grad (queryPoint p N (s k))‖ := herr _ _ _
  have hinv := sequence_invariant p N I h0 h1 hR hΔ hα hαmax hf hg hcont hs hm hu'
    hinit s reply hs0 hstep herr'
  have hA (k : ℕ) (hk : k ≤ N) := (hinv k hk).1
  have hNinv := hinv N le_rfl
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have henv := budget_envelope hT hq hd.le hα (show p.α ≤ 1 by linarith)
  change 2 ≤ U ∧ 1 ≤ H ∧ H ≤ U ∧ 1 ≤ S ∧ S ≤ 4 * U ^ 4 at henv
  have hcounts := ceiling_budget_bounds henv.2.2.2.1 henv.1 henv.2.2.2.2
  change 0 < N ∧ (2 : ℝ) ^ 60 * S ≤ N ∧ (N : ℝ) ≤ 8 * (2 : ℝ) ^ 60 * U ^ 4 at hcounts
  let r := fun k => Real.sqrt (p.L0 * (s k).A)
  have hr (k : ℕ) (hk : k ≤ N) : 0 < r k := by
    dsimp [r]
    exact Real.sqrt_pos.2 (mul_pos h0 (hA k hk))
  have hinitSquare : (r 0) ^ 2 * d = 1 := by
    dsimp [r]
    rw [Real.sq_sqrt (mul_nonneg h0.le (hA 0 (Nat.zero_le N)).le), hs0]
    dsimp [initialState, d]
    field_simp
  have hprogress := sequence_growth p N s reply h0 h1 hR.le hA hstep
  have hnum := numeric_accuracy hT hq hd hα (show p.α ≤ 1 by linarith)
    (show (0 : ℝ) < N by exact_mod_cast hcounts.1) (hr 0 (Nat.zero_le N))
    (hr N le_rfl) hinitSquare hcounts.2.1 hcounts.2.2 hprogress
  change noiseBudget p N * T ≤ (r N) ^ 2 at hnum
  change noiseBudget p N * T ≤ (Real.sqrt (p.L0 * (s N).A)) ^ 2 at hnum
  rw [Real.sq_sqrt (mul_nonneg h0.le (hA N le_rfl).le)] at hnum
  have hscaled := mul_le_mul_of_nonneg_right hnum hε.le
  have heq : noiseBudget p N * T * p.ε = p.L0 * (noiseBudget p N * p.R ^ 2) := by
    dsimp [T]
    field_simp
  rw [heq] at hscaled
  have hb : noiseBudget p N * p.R ^ 2 ≤ p.ε * (s N).A := by nlinarith only [hscaled, h0]
  have hpot := hNinv.2.2.2
  have hgap : I.f (s N).x - I.f u ≤ p.ε := by
    unfold noiseBudget at hb
    have hpos := hA N le_rfl
    nlinarith [sq_nonneg ‖(s N).z - u‖, sq_nonneg p.R]
  have hout : output p N oracle seed = (s N).x := by
    unfold output execute
    exact congrArg Prod.fst (executeWithTrace_eq_executeIndexedState
      oracle (acceleration p N) N () seed)
  rwa [hout]

end OracleTemplate.RelativeGeneralized
