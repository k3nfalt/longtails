import LongTails.Setups.QuasarAmortizedLMO
import LongTails.Algorithms.TwoCallFrankWolfe
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient

namespace OracleTemplate.QuasarAmortizedLMO

open LongTails.Setups.QuasarAmortizedLMO

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma shifted_support (f : E → ℝ) (x y v u : E) (L D τ δ : ℝ)
    (hlip : ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖)
    (hdu : ‖y - u‖ ≤ D)
    (hs : τ * (f y - f u) ≤ ⟪gradient f y, y - u⟫)
    (hlmo : ⟪gradient f x, v⟫ ≤ ⟪gradient f x, u⟫ + δ) :
    τ * (f y - f u) ≤ ⟪gradient f x, y - v⟫ + δ + L * ‖y - x‖ * D := by
  have he := real_inner_le_norm (gradient f y - gradient f x) (y - u)
  have hm := mul_le_mul hlip hdu (norm_nonneg _) ((norm_nonneg _).trans hlip)
  have hi : ⟪gradient f y, y - u⟫ =
      ⟪gradient f x, y - v⟫ + (⟪gradient f x, v⟫ - ⟪gradient f x, u⟫) +
      ⟪gradient f y - gradient f x, y - u⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [hi] at hs
  linarith

lemma weighted_step (f : E → ℝ) (x v u : E) (L D τ δ : ℝ) (k : ℕ)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hdv : ‖v - x‖ ≤ D)
    (hlmo : ⟪gradient f x, v⟫ ≤ ⟪gradient f x, u⟫ + δ)
    (hdu : ‖(1 - 2 / (τ * k + 2)) • x + (2 / (τ * k + 2)) • v - u‖ ≤ D)
    (hs : τ * (f ((1 - 2 / (τ * k + 2)) • x + (2 / (τ * k + 2)) • v) - f u) ≤
      ⟪gradient f ((1 - 2 / (τ * k + 2)) • x + (2 / (τ * k + 2)) • v),
        (1 - 2 / (τ * k + 2)) • x + (2 / (τ * k + 2)) • v - u⟫) :
    ((k : ℝ) + 1) * (k + 2) *
      (f ((1 - 2 / (τ * k + 2)) • x + (2 / (τ * k + 2)) • v) - f u) ≤
      (k : ℝ) * (k + 1) * (f x - f u) + 6 * L * D ^ 2 / τ ^ 2 +
        (2 * (k + 1) / τ) * δ := by
  let η := 2 / (τ * (k : ℝ) + 2)
  let y := (1 - η) • x + η • v
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have ht : 0 < τ * (k : ℝ) + 2 := by positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hyx : y - x = η • (v - x) := by dsimp [y]; module
  have hyv : y - v = (1 - η) • (x - v) := by dsimp [y]; module
  have hnorm : ‖y - x‖ ≤ η * D := by
    rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hdv hη
  have hs' := shifted_support f x y v u L D τ δ (hlip y x) hdu hs hlmo
  rw [hyv, inner_smul_right] at hs'
  have hn1 := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hL hD)
  have hn2 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (show 0 ≤ L / 2 by positivity)
  have hd := Gradient.smooth_upper_bound hg hlip x y
  rw [show ⟪gradient f x, y - x⟫ = -η * ⟪gradient f x, x - v⟫ by
    rw [hyx, inner_smul_right, show v - x = -(x - v) by module, inner_neg_right]; ring] at hd
  have hw1 := mul_le_mul_of_nonneg_left hd (show 0 ≤ (k : ℝ) * (k + 1) by positivity)
  have hw2 := mul_le_mul_of_nonneg_left hs' (show 0 ≤ 2 * ((k : ℝ) + 1) / τ by positivity)
  have hc : (k : ℝ) * (k + 1) * η = (2 * (k + 1) / τ) * (1 - η) := by
    dsimp [η]
    field_simp
    ring
  have hτcancel : 2 * ((k : ℝ) + 1) / τ * τ = 2 * (k + 1) := by field_simp
  have hcore : ((k : ℝ) + 1) * (k + 2) * (f y - f u) ≤
      (k : ℝ) * (k + 1) * (f x - f u) +
        ((k : ℝ) * (k + 1) * η ^ 2 / 2 + (2 * (k + 1) / τ) * η) * L * D ^ 2 +
        (2 * (k + 1) / τ) * δ := by
    have h1 := mul_le_mul_of_nonneg_left hn2 (show 0 ≤ (k : ℝ) * (k + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hn1 (show 0 ≤ 2 * ((k : ℝ) + 1) / τ by positivity)
    have hc' := congrArg (fun a => a * ⟪gradient f x, x - v⟫) hc
    have hτ' := congrArg (fun a => a * (f y - f u)) hτcancel
    nlinarith only [hw1, hw2, h1, h2, hc', hτ']
  have htlow : τ * ((k : ℝ) + 1) ≤ τ * k + 2 := by nlinarith
  have htlow2 : τ * (k : ℝ) ≤ τ * k + 2 := by linarith
  have hcoef1 : (k : ℝ) * (k + 1) * η ^ 2 / 2 ≤ 2 / τ ^ 2 := by
    dsimp [η]
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    have hh := mul_le_mul htlow2 htlow (show 0 ≤ τ * ((k : ℝ) + 1) by positivity) ht.le
    field_simp
    nlinarith
  have hcoef2 : (2 * ((k : ℝ) + 1) / τ) * η ≤ 4 / τ ^ 2 := by
    dsimp [η]
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    field_simp
    nlinarith
  have hh := mul_le_mul_of_nonneg_right (add_le_add hcoef1 hcoef2) (show 0 ≤ L * D ^ 2 by positivity)
  rw [show (2 / τ ^ 2 + 4 / τ ^ 2) * (L * D ^ 2) = 6 * L * D ^ 2 / τ ^ 2 by ring] at hh
  rw [← mul_assoc] at hh
  change ((k : ℝ) + 1) * (k + 2) * (f y - f u) ≤ _
  linarith only [hcore, hh]

lemma execute_accuracy (p : Params) (f : p.E → ℝ) (O : Oracle (p.E ⊕ p.E) p.E)
    (hp : spec.valid p) (ho : spec.admissible p f O)
    (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hiterations : max 1 ⌈(6 * p.L * p.D ^ 2 / p.τ ^ 2 + 2 * p.Γ / p.τ) / p.ε⌉₊ ≤ K) :
    let output := execute O (twoCallFrankWolfe p.τ p.x0) (fun _ => (2 * K)) () ξ
    ∃ u ∈ p.C, IsMinOn f p.C u ∧ output ∈ p.C ∧ f output - f u ≤ p.ε := by
  rcases hp with ⟨hL, hτ, hτ1, hD, hΓ, hε, hconv, hx0, hdiam⟩
  rcases ho with ⟨hg, hlip, hans, ⟨δ, hδ, hsumδ, hlmo⟩, u, hu, hmin, hquasar⟩
  let η := fun k : ℕ => 2 / (p.τ * (k : ℝ) + 2)
  let step := fun k x => (1 - η k) • x + η k •
    O.answer (2 * k + 1) (0, (Sum.inr (gradient f x))) (ξ (2 * k + 1))
  let x := fun k => advance step k 0 p.x0
  let v := fun k => O.answer (2 * k + 1) (0, (Sum.inr (gradient f (x k)))) (ξ (2 * k + 1))
  have hx (k : ℕ) : x (k + 1) = (1 - η k) • x k + η k • v k := by
    dsimp only [x]
    rw [advance_add, Nat.zero_add]
    rfl
  have hη (k : ℕ) : 0 ≤ η k ∧ η k ≤ 1 := by
    have ht : 0 < p.τ * (k : ℝ) + 2 := by positivity
    exact ⟨by dsimp [η]; positivity, (div_le_one ht).mpr (by linarith [mul_nonneg hτ.le (Nat.cast_nonneg k)])⟩
  have hfeas : ∀ k, x k ∈ p.C := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih =>
      rw [hx]
      exact hconv ih (hlmo k _ _).1 (sub_nonneg.mpr (hη k).2) (hη k).1 (by ring)
  have hrate (k : ℕ) : ((k : ℝ) + 1) * (k + 2) * (f (x (k + 1)) - f u) ≤
      (k : ℝ) * (k + 1) * (f (x k) - f u) + 6 * p.L * p.D ^ 2 / p.τ ^ 2 +
        (2 * (k + 1) / p.τ) * δ k := by
    rw [hx]
    apply weighted_step f (x k) (v k) u p.L p.D p.τ (δ k) k hL hD hτ hτ1 hg hlip
    · exact hdiam _ (hlmo k _ _).1 _ (hfeas k)
    · exact (hlmo k _ _).2 u hu
    · rw [← hx]
      exact hdiam _ (hfeas (k + 1)) _ hu
    · rw [← hx]
      exact hquasar _ (hfeas (k + 1))
  have henergy : ∀ k : ℕ, (k : ℝ) * (k + 1) * (f (x k) - f u) ≤
      (k : ℝ) * (6 * p.L * p.D ^ 2 / p.τ ^ 2) +
        ∑ j ∈ Finset.range k, (2 * ((j : ℝ) + 1) / p.τ) * δ j := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := hrate k
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      nlinarith only [ih, hh]
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hiterations)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have herrors : (∑ j ∈ Finset.range K, (2 * ((j : ℝ) + 1) / p.τ) * δ j) ≤
      (2 * (K : ℝ) / p.τ) * p.Γ := by
    calc
      _ ≤ ∑ j ∈ Finset.range K, (2 * (K : ℝ) / p.τ) * δ j := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (hδ j)
        apply (div_le_div_iff_of_pos_right hτ).mpr
        have hj' : (j : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hj
        linarith
      _ = (2 * (K : ℝ) / p.τ) * ∑ j ∈ Finset.range K, δ j := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsumδ K) (by positivity)
  have hceil : (6 * p.L * p.D ^ 2 / p.τ ^ 2 + 2 * p.Γ / p.τ) / p.ε ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right 1 _).trans hiterations))
  have hbudget := (div_le_iff₀ hε).mp hceil
  have hbudget' := mul_le_mul_of_nonneg_left hbudget hKr.le
  have hacc : f (x K) - f u ≤ p.ε := by
    have he := henergy K
    have hscale : (K : ℝ) * (K + 1) * (f (x K) - f u) ≤ (K : ℝ) * (K + 1) * p.ε := by
      calc
        _ ≤ (K : ℝ) * (6 * p.L * p.D ^ 2 / p.τ ^ 2) + (2 * (K : ℝ) / p.τ) * p.Γ :=
          he.trans (by linarith only [herrors])
        _ = (K : ℝ) * (6 * p.L * p.D ^ 2 / p.τ ^ 2 + 2 * p.Γ / p.τ) := by ring
        _ ≤ (K : ℝ) * ((K : ℝ) * p.ε) := hbudget'
        _ ≤ _ := by nlinarith only [mul_pos hKr hε]
    exact (mul_le_mul_iff_right₀ (show 0 < (K : ℝ) * (K + 1) by positivity)).mp hscale
  let A := twoCallFrankWolfe p.τ p.x0
  let rawStep := fun k s => A.update s (O.answer k (A.query s) (ξ k))
  have hstate : ∀ k, advance rawStep (2 * k) 0 (A.initial ()) = (false, k, x k, 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, advance_add, Nat.zero_add, ih]
      simp only [advance, rawStep, A, twoCallFrankWolfe, Bool.false_eq_true,
        ite_false, ite_true, hans]
      rw [hx]
  dsimp only
  erw [execute_advance]
  erw [hstate K]
  exact ⟨u, hu, hmin, hfeas K, hacc⟩

end OracleTemplate.QuasarAmortizedLMO
