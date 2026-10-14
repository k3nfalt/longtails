import LongTails.Proofs.FrankWolfeGeometry
import LongTails.Proofs.FrankWolfePowerBounds

namespace OracleTemplate.FrankWolfe

open LongTails.Setups.UniformlyConvexHolder

lemma holder_geometry_distance {h gap d gradient a c r : ℝ}
    (hh : 0 < h) (hd : 0 ≤ d) (ha : 0 < a) (hc : 0 < c)
    (hgrowth : h ≤ gradient * c * h ^ (1 / r))
    (hgeom : a / 2 * gradient * d ≤ gap) :
    d ≤ (2 * c / a) * gap * h ^ (1 / r - 1) := by
  have hp : 0 ≤ c * h ^ (1 / r) := mul_nonneg hc.le (Real.rpow_nonneg hh.le _)
  have hprod : (a / 2 * h) * d ≤ gap * (c * h ^ (1 / r)) := by
    calc
      _ ≤ (a / 2 * (gradient * c * h ^ (1 / r))) * d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrowth (by positivity)) hd
      _ = (a / 2 * gradient * d) * (c * h ^ (1 / r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeom hp
  calc
    d ≤ (gap * (c * h ^ (1 / r))) / (a / 2 * h) :=
      (le_div_iff₀ (mul_pos (div_pos ha (by norm_num)) hh)).mpr (by nlinarith)
    _ = _ := by
      rw [Real.rpow_sub hh, Real.rpow_one]
      field_simp

lemma holder_quadratic_decrease {h gap d L b q r : ℝ}
    (hh : 0 < h) (hgap : h ≤ gap) (hd : 0 < d) (hL : 0 < L) (hb : 0 < b)
    (hq : 3 < q) (hr : 2 < r)
    (hdistance : d ^ q ≤ b * gap * h ^ (1 / r - 1)) :
    h ^ (2 - 2 / (q * r)) / (2 * L * b ^ (2 / q)) ≤ gap ^ 2 / (2 * L * d ^ 2) := by
  have hqpos : 0 < q := by linarith
  have hrpos : 0 < r := by linarith
  have hgpos : 0 < gap := hh.trans_le hgap
  have hα : 0 ≤ 2 / q := div_nonneg (by norm_num) hqpos.le
  have hα2 : 0 ≤ 2 - 2 / q := by
    have := (div_lt_one hqpos).mpr (by linarith : (2 : ℝ) < q)
    linarith
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hd.le _) hdistance hα
  rw [← Real.rpow_mul hd.le, show q * (2 / q) = 2 by field_simp, Real.rpow_two,
    Real.mul_rpow (mul_nonneg hb.le hgpos.le) (Real.rpow_nonneg hh.le _),
    Real.mul_rpow hb.le hgpos.le, ← Real.rpow_mul hh.le] at hpow
  have hexp : (2 - 2 / (q * r)) + (1 / r - 1) * (2 / q) = 2 - 2 / q := by
    field_simp
    ring
  have hg := mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hh.le hgap hα2) (Real.rpow_nonneg hgpos.le (2 / q))
  rw [← Real.rpow_add hgpos, show 2 - 2 / q + 2 / q = 2 by ring, Real.rpow_two] at hg
  have hprod : h ^ (2 - 2 / (q * r)) * d ^ 2 ≤ b ^ (2 / q) * gap ^ 2 := by
    calc
      _ ≤ h ^ (2 - 2 / (q * r)) *
          (b ^ (2 / q) * gap ^ (2 / q) * h ^ ((1 / r - 1) * (2 / q))) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hh.le _)
      _ = b ^ (2 / q) * (h ^ (2 - 2 / q) * gap ^ (2 / q)) := by
        calc
          _ = b ^ (2 / q) * ((h ^ (2 - 2 / (q * r)) * h ^ ((1 / r - 1) * (2 / q))) * gap ^ (2 / q)) := by ring
          _ = _ := by rw [← Real.rpow_add hh, hexp]
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hb.le _)
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * L * b ^ (2 / q))
    (by positivity : 0 < 2 * L * d ^ 2)).mpr
  have hscaled := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 * L)
  nlinarith

lemma minimum_power_decrease {h H p B : ℝ} (hh : 0 ≤ h) (hH : 0 < H)
    (hhH : h ≤ H) (hp : 0 < p) (hB : 0 < B) :
    h ^ (1 + p) / (2 * H ^ p + B) ≤ min (h / 2) (h ^ (1 + p) / B) := by
  have hden : 0 < 2 * H ^ p + B := by positivity
  have hpow : 0 ≤ h ^ (1 + p) := Real.rpow_nonneg hh _
  apply le_min
  · apply (div_le_iff₀ hden).mpr
    rcases hh.eq_or_lt with hzero | hpos
    · subst h
      simp [Real.zero_rpow (by linarith : 1 + p ≠ 0)]
    have heq : h ^ (1 + p) = h * h ^ p := by rw [Real.rpow_add hpos, Real.rpow_one]
    rw [heq]
    have hpower := Real.rpow_le_rpow hpos.le hhH hp.le
    have hmul := mul_le_mul_of_nonneg_left hpower hpos.le
    nlinarith [mul_nonneg hpos.le hB.le]
  · exact div_le_div_of_nonneg_left hpow hB (by have := Real.rpow_nonneg hH.le p; linarith)

lemma reciprocal_descent_sum {h : ℕ → ℝ} {p κ : ℝ} (hp : 0 ≤ p) (hκ : 0 ≤ κ)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hstep : ∀ n, h (n + 1) ≤ h n - κ * h n ^ (1 + p)) (N : ℕ) (hN : 0 < h N) :
    h 0 ^ (-p) + p * κ * N ≤ h N ^ (-p) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hm := mul_nonneg hκ (Real.rpow_nonneg (hnonneg n) (1 + p))
    have hprev : 0 < h n := by have := hstep n; linarith
    have hi := ih hprev
    have hs := reciprocal_descent_step hprev hN hp hκ (hstep n)
    push_cast
    nlinarith

lemma accuracy_of_power_descent {h : ℕ → ℝ} {p den ε : ℝ} (hp : 1 / 2 < p)
    (hden : 0 < den) (hε : 0 < ε) (hnonneg : ∀ n, 0 ≤ h n)
    (hstep : ∀ n, h (n + 1) ≤ h n - h n ^ (1 + p) / den)
    (N : ℕ) (hbudget : 2 * den * ε ^ (-p) ≤ N) : h N ≤ ε := by
  by_contra hfail
  have hlarge : ε < h N := lt_of_not_ge hfail
  have hp0 : 0 < p := by linarith
  have hrec := reciprocal_descent_sum (p := p) (κ := 1 / den) hp0.le (by positivity)
    hnonneg (fun n => by simpa [div_eq_mul_inv, mul_comm] using hstep n) N (hε.trans hlarge)
  have hinverse : h N ^ (-p) ≤ ε ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hε hlarge.le (by linarith)
  have hbudget' := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ p * (1 / den))
  have heq : p * (1 / den) * (2 * den * ε ^ (-p)) = 2 * p * ε ^ (-p) := by field_simp
  rw [heq] at hbudget'
  have hpositive := Real.rpow_pos_of_pos hε (-p)
  have hzero := Real.rpow_nonneg (hnonneg 0) (-p)
  nlinarith [mul_pos (by linarith : 0 < 2 * p - 1) hpositive]

open Set InnerProductSpace
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma primal_le_gap {C : Set E} {f : E → ℝ} {g x atom y : E}
    (hc : ConvexOn ℝ C f) (hx : x ∈ C) (hy : y ∈ C)
    (hg : HasGradientAt f g x) (hlmo : ⟪g, atom⟫ ≤ ⟪g, y⟫) :
    f x - f y ≤ ⟪g, x - atom⟫ := by
  have h := convex_support_on hc hx hy hg
  simp only [inner_sub_right] at h ⊢
  linarith

lemma short_step_holder_decrease {C : Set E} {f : E → ℝ} {g : E → E}
    {L a c q r : ℝ} (hL : 0 < L) (ha : 0 < a) (hc : 0 < c)
    (hq : 3 < q) (hr : 2 < r) (hC : UniformlyConvexSet C a q)
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x atom y : E} (hx : x ∈ C) (hatom : atom ∈ C) (hy : y ∈ C)
    (hmin : IsMinOn f C y) (hlmo : ∀ z ∈ C, ⟪g x, atom⟫ ≤ ⟪g x, z⟫)
    (hdist : ‖x - y‖ ≤ c * (f x - f y) ^ (1 / r)) :
    f (shortStep L x (g x) atom) - f y ≤ f x - f y -
      min ((f x - f y) / 2)
        ((f x - f y) ^ (2 - 2 / (q * r)) / (2 * L * (2 * c / a) ^ (2 / q))) := by
  have hgap := primal_le_gap hf hx hy (hg x hx) (hlmo y hy)
  have hnonneg : 0 ≤ f x - f y := sub_nonneg.mpr (hmin hx)
  have hs := short_step_objective_descent hC.convex hL hg hlip hx hatom (hlmo x hx)
  by_cases hzero : f x - f y = 0
  · have he : 0 < 2 - 2 / (q * r) := by
      have hp : 2 < q * r := by nlinarith
      have := (div_lt_one (by positivity : 0 < q * r)).mpr hp
      linarith
    rw [hzero, Real.zero_rpow he.ne', zero_div, zero_div, min_self, sub_zero]
    have hm : 0 ≤ min (⟪g x, x - atom⟫ / 2)
        (⟪g x, x - atom⟫ ^ 2 / (2 * (L * ‖atom - x‖ ^ 2))) := by
      exact le_min (by linarith) (div_nonneg (sq_nonneg _) (by positivity))
    linarith
  have hh : 0 < f x - f y := lt_of_le_of_ne hnonneg (Ne.symm hzero)
  have hne : x ≠ atom := by intro heq; simp [heq] at hgap; rw [heq] at hh; linarith
  have hd : 0 < ‖x - atom‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hgeom := uniformly_convex_gap hC hx hatom hlmo
  have hgrowth := gradient_growth hf hx hy (hg x hx) rfl hdist
  have hdistance := holder_geometry_distance hh (Real.rpow_nonneg hd.le q) ha hc hgrowth hgeom
  have hquad := holder_quadratic_decrease hh hgap hd hL (by positivity : 0 < 2 * c / a) hq hr hdistance
  rw [norm_sub_rev x atom] at hquad
  have hminle := min_le_min (show (f x - f y) / 2 ≤ ⟪g x, x - atom⟫ / 2 by linarith)
    (show (f x - f y) ^ (2 - 2 / (q * r)) / (2 * L * (2 * c / a) ^ (2 / q)) ≤
      ⟪g x, x - atom⟫ ^ 2 / (2 * (L * ‖atom - x‖ ^ 2)) by simpa [mul_assoc] using hquad)
  linarith

lemma short_step_first_gap {C : Set E} {f : E → ℝ} {g : E → E} {L D : ℝ}
    (hC : Convex ℝ C) (hL : 0 < L)
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x atom y : E} (hx : x ∈ C) (hatom : atom ∈ C) (hy : y ∈ C)
    (hlmo : ∀ z ∈ C, ⟪g x, atom⟫ ≤ ⟪g x, z⟫) (hd : ‖atom - x‖ ≤ D) :
    f (shortStep L x (g x) atom) - f y ≤ L * D ^ 2 := by
  have hgap := primal_le_gap hf hx hy (hg x hx) (hlmo y hy)
  by_cases heq : atom = x
  · simp [heq, shortStep] at hgap ⊢
    nlinarith [mul_nonneg hL.le (sq_nonneg D)]
  have hcurv : 0 < L * ‖atom - x‖ ^ 2 :=
    mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr heq)))
  have hmodel := short_step_smooth_model hC hL hg hlip hx hatom (hlmo x hx)
  dsimp only at hmodel
  have hbound := short_step_initial_bound hcurv hgap (by linarith :
    f (shortStep L x (g x) atom) - f y ≤ f x - f y -
      min 1 (⟪g x, x - atom⟫ / (L * ‖atom - x‖ ^ 2)) * ⟪g x, x - atom⟫ +
      (L * ‖atom - x‖ ^ 2) / 2 * (min 1 (⟪g x, x - atom⟫ / (L * ‖atom - x‖ ^ 2))) ^ 2)
  have hsq := mul_self_le_mul_self (norm_nonneg (atom - x)) hd
  have hmul := mul_le_mul_of_nonneg_left hsq hL.le
  nlinarith [sq_nonneg D]

end OracleTemplate.FrankWolfe
