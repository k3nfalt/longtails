import LongTails.Proofs.ExecutionHistory
import LongTails.Setups.UncalibratedSharp
import LongTails.Algorithms.RobustPolyak
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Proofs.GdPL

open scoped RealInnerProductSpace
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient

namespace OracleTemplate.UncalibratedSharp

open LongTails.Setups.UncalibratedSharp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma scale_invariance (c r γ : ℝ) (w : E) (hγ : 0 < γ) :
    (c * (γ * r) / ‖γ • w‖ ^ 2) • (γ • w) = (c * r / ‖w‖ ^ 2) • w := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ, mul_pow, smul_smul]
  congr 1
  by_cases hw : ‖w‖ = 0
  · simp [hw]
  · field_simp

lemma interval_progress (t α β z r : ℝ) (ht : 0 < t) (hα : 0 < α) (hαβ : α ≤ β)
    (_hz : 0 ≤ z) (hr : α * z ≤ r) (hr' : r ≤ β * z) :
    let c := 2 * t / (α + β)
    c ^ 2 * α * β * z ^ 2 ≤ 2 * c * r * t * z - c ^ 2 * r ^ 2 := by
  let c := 2 * t / (α + β)
  have hsum : 0 < α + β := by linarith
  have hc : c * (α + β) = 2 * t := by dsimp [c]; field_simp
  have hh := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr')
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
  have he := congrArg (fun a => a * c * r * z) hc
  change c ^ 2 * α * β * z ^ 2 ≤ _
  nlinarith only [hh', he]

lemma normalized_step (d w : E) (z r t α β μ M : ℝ)
    (ht : 0 < t) (hα : 0 < α) (hαβ : α ≤ β) (hμ : 0 < μ) (hM : 0 < M)
    (hz : 0 ≤ z) (hra : α * z ≤ r) (hrb : r ≤ β * z)
    (hsupport : t * z ≤ ⟪w, d⟫) (hsharp : μ * ‖d‖ ≤ z) (hw : ‖w‖ ≤ M) :
    let c := 2 * t / (α + β)
    ‖d - (c * r / ‖w‖ ^ 2) • w‖ ^ 2 ≤
      (1 - c ^ 2 * α * β * μ ^ 2 / M ^ 2) * ‖d‖ ^ 2 := by
  let c := 2 * t / (α + β)
  have hβ : 0 < β := hα.trans_le hαβ
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 ≤ r := (mul_nonneg hα.le hz).trans hra
  by_cases hw0 : w = 0
  · subst w
    simp only [inner_zero_left] at hsupport
    have hz0 : z = 0 := by nlinarith
    have hd0 : d = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d])
    simp [hd0]
  have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  have he : ‖d - (c * r / ‖w‖ ^ 2) • w‖ ^ 2 =
      ‖d‖ ^ 2 - (2 * c * r * ⟪w, d⟫ - c ^ 2 * r ^ 2) / ‖w‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      ← real_inner_comm d w]
    field_simp
    ring
  have hs := mul_le_mul_of_nonneg_left hsupport (show 0 ≤ 2 * c * r by positivity)
  have hi := interval_progress t α β z r ht hα hαβ hz hra hrb
  change c ^ 2 * α * β * z ^ 2 ≤ _ at hi
  have hnum : c ^ 2 * α * β * z ^ 2 ≤ 2 * c * r * ⟪w, d⟫ - c ^ 2 * r ^ 2 := by
    nlinarith only [hi, hs]
  have hdist := pow_le_pow_left₀ (show 0 ≤ μ * ‖d‖ by positivity) hsharp 2
  have hm := pow_le_pow_left₀ (norm_nonneg w) hw 2
  have hcoef : 0 ≤ c ^ 2 * α * β := by positivity
  have hbound : (c ^ 2 * α * β * μ ^ 2 / M ^ 2) * ‖d‖ ^ 2 ≤
      (2 * c * r * ⟪w, d⟫ - c ^ 2 * r ^ 2) / ‖w‖ ^ 2 := by
    calc
      _ = (c ^ 2 * α * β * (μ * ‖d‖) ^ 2) / M ^ 2 := by ring
      _ ≤ (c ^ 2 * α * β * z ^ 2) / M ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hM)).mpr (mul_le_mul_of_nonneg_left hdist hcoef)
      _ ≤ (c ^ 2 * α * β * z ^ 2) / ‖w‖ ^ 2 := div_le_div_of_nonneg_left (by positivity) hn hm
      _ ≤ _ := (div_le_div_iff_of_pos_right hn).mpr hnum
  change ‖d - (c * r / ‖w‖ ^ 2) • w‖ ^ 2 ≤ _
  rw [he]
  nlinarith only [hbound]

lemma contraction_parameters (p : Params) (hp : spec.valid p) :
    let κ := 4 * (p.μ - p.ρ) ^ 2 * p.α * p.β / ((p.G + p.ρ) ^ 2 * (p.α + p.β) ^ 2)
    let c := 2 * (1 - p.ρ / p.μ) / (p.α + p.β)
    0 < κ ∧ κ ≤ 1 ∧ c ^ 2 * p.α * p.β * p.μ ^ 2 / (p.G + p.ρ) ^ 2 = κ := by
  rcases hp with ⟨hρ, hρμ, hμG, hα, hαβ, hR, hε⟩
  have hμ : 0 < p.μ := hρ.trans_lt hρμ
  have hG : 0 < p.G := hμ.trans_le hμG
  have hβ : 0 < p.β := hα.trans_le hαβ
  have hM : 0 < p.G + p.ρ := by positivity
  have hsum : 0 < p.α + p.β := by positivity
  dsimp only
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one (show 0 < (p.G + p.ρ) ^ 2 * (p.α + p.β) ^ 2 by positivity)).mpr
    have h1 : (p.μ - p.ρ) ^ 2 ≤ (p.G + p.ρ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : 4 * p.α * p.β ≤ (p.α + p.β) ^ 2 := by nlinarith [sq_nonneg (p.α - p.β)]
    have hh := mul_le_mul h1 h2 (show 0 ≤ 4 * p.α * p.β by positivity) (sq_nonneg _)
    nlinarith only [hh]
  · field_simp
    ring

lemma oracle_step (p : Params) (hp : spec.valid p) (f : p.E → ℝ) (x u : p.E)
    (hmin : IsMinOn f Set.univ u) (hsharp : p.μ * ‖x - u‖ ≤ f x - f u)
    (γ r : ℝ) (g e : p.E) (hγ : 0 < γ) (hg : ‖g‖ ≤ p.G) (he : ‖e‖ ≤ p.ρ)
    (hsub : ∀ y, f x + ⟪g, y - x⟫ ≤ f y)
    (hra : p.α * (f x - f u) ≤ r) (hrb : r ≤ p.β * (f x - f u)) :
    let c := 2 * (1 - p.ρ / p.μ) / (p.α + p.β)
    let κ := 4 * (p.μ - p.ρ) ^ 2 * p.α * p.β / ((p.G + p.ρ) ^ 2 * (p.α + p.β) ^ 2)
    ‖x - (c * (γ * r) / ‖γ • (g + e)‖ ^ 2) • (γ • (g + e)) - u‖ ^ 2 ≤
      (1 - κ) * ‖x - u‖ ^ 2 := by
  have hparam := contraction_parameters p hp
  rcases hp with ⟨hρ, hρμ, hμG, hα, hαβ, hR, hε⟩
  have hμ : 0 < p.μ := hρ.trans_lt hρμ
  have hG : 0 < p.G := hμ.trans_le hμG
  have ht : 0 < 1 - p.ρ / p.μ := sub_pos.mpr ((div_lt_one hμ).mpr hρμ)
  have hz : 0 ≤ f x - f u := sub_nonneg.mpr (hmin (Set.mem_univ x))
  have hs : f x - f u ≤ ⟪g, x - u⟫ := by
    have hh := hsub u
    rw [show u - x = -(x - u) by module, inner_neg_right] at hh
    linarith
  have heinner : -p.ρ * ‖x - u‖ ≤ ⟪e, x - u⟫ := by
    have hh := real_inner_le_norm (-e) (x - u)
    simp only [inner_neg_left, norm_neg] at hh
    have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (x - u))
    nlinarith only [hh, hm]
  have hsupport : (1 - p.ρ / p.μ) * (f x - f u) ≤ ⟪g + e, x - u⟫ := by
    rw [inner_add_left]
    have hh := mul_le_mul_of_nonneg_left (add_le_add hs heinner) hμ.le
    have hh' := mul_le_mul_of_nonneg_left hsharp hρ
    have hid : p.μ * ((1 - p.ρ / p.μ) * (f x - f u)) = (p.μ - p.ρ) * (f x - f u) := by
      field_simp
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [hh, hh', hid]
  have hw : ‖g + e‖ ≤ p.G + p.ρ := (norm_add_le _ _).trans (add_le_add hg he)
  have hn := normalized_step (x - u) (g + e) (f x - f u) r (1 - p.ρ / p.μ)
    p.α p.β p.μ (p.G + p.ρ) ht hα hαβ hμ (by positivity) hz hra hrb hsupport hsharp hw
  dsimp only at hn ⊢
  rw [scale_invariance _ _ _ _ hγ, show x -
      (2 * (1 - p.ρ / p.μ) / (p.α + p.β) * r / ‖g + e‖ ^ 2) • (g + e) - u =
      (x - u) - (2 * (1 - p.ρ / p.μ) / (p.α + p.β) * r / ‖g + e‖ ^ 2) • (g + e) by module]
  rw [hparam.2.2] at hn
  exact hn

lemma execute_accuracy (p : Params) (f : p.E → ℝ) (O : Oracle p.E (ℝ × p.E))
    (hp : spec.valid p) (ho : spec.admissible p f O) (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hbudget : ⌈(1 / (4 * (p.μ - p.ρ) ^ 2 * p.α * p.β / ((p.G + p.ρ) ^ 2 * (p.α + p.β) ^ 2))) * Real.log (1 + p.G ^ 2 * p.R ^ 2 / p.ε ^ 2)⌉₊ ≤ K) :
    let c := 2 * (1 - p.ρ / p.μ) / (p.α + p.β)
    let output := execute O (robustPolyak c p.x0) (fun _ => K) () ξ
    ∃ u, IsMinOn f Set.univ u ∧ f output - f u ≤ p.ε := by
  have hparam := contraction_parameters p hp
  have hvalid := hp
  rcases hp with ⟨hρ, hρμ, hμG, hα, hαβ, hR, hε⟩
  rcases ho with ⟨hlip, u, hmin, hdist, hsharp, hans⟩
  let κ := 4 * (p.μ - p.ρ) ^ 2 * p.α * p.β / ((p.G + p.ρ) ^ 2 * (p.α + p.β) ^ 2)
  let c := 2 * (1 - p.ρ / p.μ) / (p.α + p.β)
  let A := robustPolyak c p.x0
  let step : ℕ → p.E → p.E := fun k x => A.update x (executeAnswerAt O A () ξ k (A.query x))
  let x : ℕ → p.E := fun k => advance step k 0 p.x0
  have hx (k : ℕ) : x (k + 1) = step k (x k) := by
    dsimp [x]
    rw [advance_add, Nat.zero_add]
    rfl
  have hq : 0 ≤ 1 - κ := sub_nonneg.mpr hparam.2.1
  have hrate : ∀ k, ‖x k - u‖ ^ 2 ≤ (1 - κ) ^ k * p.R ^ 2 := by
    intro k
    induction k with
    | zero => simpa [x, advance] using pow_le_pow_left₀ (norm_nonneg _) hdist 2
    | succ k ih =>
      obtain ⟨γ, r, g, e, hγ, hg, he, hsub, hra, hrb, ha⟩ := hans (executeIndexedState O A () ξ k).2 (x k) (ξ _)
      have hs := oracle_step p hvalid f (x k) u hmin (hsharp _) γ r g e hγ hg he hsub hra hrb
      rw [hx]
      dsimp only [step, executeAnswerAt, A, robustPolyak]
      erw [ha]
      have hi := mul_le_mul_of_nonneg_left ih hq
      rw [pow_succ]
      change ‖x k - (c * (γ * r) / ‖γ • (g + e)‖ ^ 2) • (γ • (g + e)) - u‖ ^ 2 ≤ _
      change ‖x k - (c * (γ * r) / ‖γ • (g + e)‖ ^ 2) • (γ • (g + e)) - u‖ ^ 2 ≤
        (1 - κ) * ‖x k - u‖ ^ 2 at hs
      exact hs.trans (by convert hi using 1; ring)
  have hμ : 0 < p.μ := hρ.trans_lt hρμ
  have hG : 0 < p.G := hμ.trans_le hμG
  have hgap : f (x K) - f u ≤ p.G * ‖x K - u‖ := (le_abs_self _).trans (hlip _ _)
  have hgap0 : 0 ≤ f (x K) - f u := sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hsq := pow_le_pow_left₀ hgap0 hgap 2
  have hnorm := mul_le_mul_of_nonneg_left (hrate K) (sq_nonneg p.G)
  have hb := PLGradient.geometric_budget 1 κ (p.G ^ 2 * p.R ^ 2) (p.ε ^ 2)
    hparam.1 hparam.2.1 (by positivity) (by positivity) K (by simpa only [div_one] using hbudget)
  change (1 - κ / 1) ^ K * (p.G ^ 2 * p.R ^ 2) ≤ p.ε ^ 2 at hb
  rw [div_one] at hb
  have hacc : f (x K) - f u ≤ p.ε := by nlinarith only [hsq, hnorm, hb, hgap0, hε]
  dsimp only
  erw [execute_advance_history]
  exact ⟨u, hmin, hacc⟩

end OracleTemplate.UncalibratedSharp
