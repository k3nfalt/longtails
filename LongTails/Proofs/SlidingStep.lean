import LongTails.Proofs.SlidingInner
import LongTails.Proofs.CompositeGeneralizedStep

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

open CompositeGeneralized (mixPoint SymmetricSmooth mix_sub_left mix_sub_mix mix_dist mix_mem
  ball_lipschitz ball_upper shifted_cocoercive optimality scaled_gap_bound le_two_mul_of_sq)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma slideWeight_spec {L1 R A M : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A) (hM : 0 < M) :
    0 < slideWeight L1 R A M ∧ slideWeight L1 R A M ≤ A / (1 + 80 * L1 * R) ∧
      16 * M * slideWeight L1 R A M ^ 2 ≤ A + slideWeight L1 R A M := by
  set s := Real.sqrt (1 + 64 * M * A)
  have hs2 : s ^ 2 = 1 + 64 * M * A := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hr : 0 < (1 + s) / (32 * M) := by positivity
  have hcap : 0 < A / (1 + 80 * L1 * R) := by positivity
  have har : slideWeight L1 R A M ≤ (1 + s) / (32 * M) := min_le_left _ _
  have hapos : 0 < slideWeight L1 R A M := lt_min hr hcap
  refine ⟨hapos, min_le_right _ _, ?_⟩
  set a := slideWeight L1 R A M
  rw [le_div_iff₀ (by positivity)] at har
  have hsq : (32 * M * a - 1) ^ 2 ≤ s ^ 2 := by
    have h1 : -s ≤ 32 * M * a - 1 := by nlinarith
    have h2 : 32 * M * a - 1 ≤ s := by nlinarith
    nlinarith
  nlinarith

lemma slide_cap {L1 R A a : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A) (ha : 0 < a)
    (hcap : a ≤ A / (1 + 80 * L1 * R)) :
    a ≤ A ∧ 80 * (L1 * R) * (a / (A + a)) ≤ 1 ∧ 80 * (a * L1 * R) ≤ A := by
  have hden : 0 < 1 + 80 * L1 * R := by positivity
  rw [le_div_iff₀ hden] at hcap
  have hLR : 0 ≤ L1 * R := by positivity
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  rw [mul_div_assoc', div_le_one (by positivity)]
  nlinarith

omit [CompleteSpace E] in
lemma convexOn_of_subgradient {h : E → ℝ} {sub : E → E} {Q : Set E} {M : ℝ} (hQ : Convex ℝ Q)
    (hS : SubgradientOracle h sub Q M) : ConvexOn ℝ Q h := by
  refine ⟨hQ, fun x hx y hy c d hc hd hcd => ?_⟩
  simpa [smul_eq_mul] using sub_convex_mix hQ hS hx hy hc hd hcd

structure Hyp (f h : E → ℝ) (g : E → E) (Q : Set E) (L0 L1 : ℝ) : Prop where
  hL0 : 0 < L0
  hL1 : 0 ≤ L1
  convex : ConvexOn ℝ univ f
  grad : ∀ x, HasGradientAt f (g x) x
  cont : Continuous g
  smooth : SymmetricSmooth g L0 L1
  setConvex : Convex ℝ Q
  regConvex : ConvexOn ℝ Q h

lemma slide_combine {f h : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hh : ConvexOn ℝ Q h)
    {A a M e : ℝ} (hA : 0 < A) (ha : 0 < a) (hstep : 3 * M * a ^ 2 ≤ A + a)
    {x z ub up xs : E} (hx : x ∈ Q) (hub : ub ∈ Q)
    (hps : a * (⟪g (mixPoint A a x z), ub - xs⟫ + h ub - h xs) + 1 / 3 * ‖ub - z‖ ^ 2 +
      ‖up - xs‖ ^ 2 / 2 ≤ ‖z - xs‖ ^ 2 / 2 + e)
    (hdesc : f (mixPoint A a x ub) ≤ f (mixPoint A a x z) +
      ⟪g (mixPoint A a x z), mixPoint A a x ub - mixPoint A a x z⟫ +
        M * ‖mixPoint A a x ub - mixPoint A a x z‖ ^ 2) :
    (A + a) * (f (mixPoint A a x ub) + h (mixPoint A a x ub) - (f xs + h xs)) +
        ‖up - xs‖ ^ 2 / 2 ≤
      A * (f x + h x - (f xs + h xs)) + ‖z - xs‖ ^ 2 / 2 + e := by
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z
  set x' := mixPoint A a x ub
  set gy := g y
  set l := A / (A + a)
  set m := a / (A + a)
  have hlm : l + m = 1 := by simp only [l, m]; field_simp
  have hl0 : 0 ≤ l := by positivity
  have hm0 : 0 ≤ m := by positivity
  have e1 : x' - y = m • (ub - z) := mix_sub_mix A a x z ub
  have e2 : x' - y = l • (x - y) + m • (ub - y) := by
    have hh2 : l • (x - y) + m • (ub - y) = (l • x + m • ub) - (l + m) • y := by module
    rw [hh2, hlm, one_smul]
    rfl
  have i1 : ⟪gy, x' - y⟫ = l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, ub - xs⟫) := by
    rw [e2, inner_add_right, inner_smul_right, inner_smul_right,
      show ub - y = (xs - y) + (ub - xs) by abel, inner_add_right]
  have n1 : ‖x' - y‖ ^ 2 = m ^ 2 * ‖ub - z‖ ^ 2 := by
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have c1 := Gradient.convex_support hc hf y x
  have c2 := Gradient.convex_support hc hf y xs
  have hhx' : h x' ≤ l * h x + m * h ub := by
    have hh3 := hh.2 hx hub hl0 hm0 hlm
    simp only [smul_eq_mul] at hh3
    exact hh3
  have hq : (A + a) * (M * (m ^ 2 * ‖ub - z‖ ^ 2)) ≤ 1 / 3 * ‖ub - z‖ ^ 2 := by
    have e : (A + a) * (M * (m ^ 2 * ‖ub - z‖ ^ 2)) =
        (3 * M * a ^ 2) / (A + a) * (1 / 3 * ‖ub - z‖ ^ 2) := by
      simp only [m]; field_simp
    rw [e]
    have hfrac : (3 * M * a ^ 2) / (A + a) ≤ 1 := (div_le_one hS).mpr hstep
    have hn : 0 ≤ 1 / 3 * ‖ub - z‖ ^ 2 := by positivity
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hdesc hS.le
  rw [i1, n1] at hd
  have ex1 : (A + a) * (f y + (l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, ub - xs⟫)) +
      M * (m ^ 2 * ‖ub - z‖ ^ 2)) =
      (A + a) * f y + A * ⟪gy, x - y⟫ + a * ⟪gy, xs - y⟫ + a * ⟪gy, ub - xs⟫ +
        (A + a) * (M * (m ^ 2 * ‖ub - z‖ ^ 2)) := by
    simp only [l, m]; field_simp; ring
  rw [ex1] at hd
  have hh' := mul_le_mul_of_nonneg_left hhx' hS.le
  have ex2 : (A + a) * (l * h x + m * h ub) = A * h x + a * h ub := by
    simp only [l, m]; field_simp
  rw [ex2] at hh'
  have k1 := mul_le_mul_of_nonneg_left c1 hA.le
  have k2 := mul_le_mul_of_nonneg_left c2 ha.le
  nlinarith

set_option maxHeartbeats 1000000 in
lemma slide_step {f h : E → ℝ} {g : E → E} {Q : Set E} {L0 L1 : ℝ} (hy : Hyp f h g Q L0 L1)
    {R P e : ℝ} (hR : 0 < R) {xs : E} (hxs : xs ∈ Q) (hmin : IsMinOn (fun x => f x + h x) Q xs)
    {A : ℝ} {x z : E} (hA : 0 < A) (hx : x ∈ Q)
    (hΦ : A * (f x + h x - (f xs + h xs)) + ‖z - xs‖ ^ 2 / 2 ≤ P) (hPe : P + e ≤ R ^ 2)
    (he : 0 ≤ e) (hxd : ‖x - xs‖ ≤ 20 * R) {ub up : E} (hub : ub ∈ Q)
    (hps : slideWeight L1 R A (L0 + L1 * ‖g x‖) *
        (⟪g (mixPoint A (slideWeight L1 R A (L0 + L1 * ‖g x‖)) x z), ub - xs⟫ + h ub - h xs) +
        1 / 3 * ‖ub - z‖ ^ 2 + ‖up - xs‖ ^ 2 / 2 ≤ ‖z - xs‖ ^ 2 / 2 + e) :
    (A + slideWeight L1 R A (L0 + L1 * ‖g x‖)) *
        (f (mixPoint A (slideWeight L1 R A (L0 + L1 * ‖g x‖)) x ub) +
          h (mixPoint A (slideWeight L1 R A (L0 + L1 * ‖g x‖)) x ub) - (f xs + h xs)) +
        ‖up - xs‖ ^ 2 / 2 ≤ P + e ∧
      mixPoint A (slideWeight L1 R A (L0 + L1 * ‖g x‖)) x ub ∈ Q ∧
      ‖mixPoint A (slideWeight L1 R A (L0 + L1 * ‖g x‖)) x ub - xs‖ ≤ 20 * R := by
  have hL0 := hy.hL0
  have hL1 := hy.hL1
  set M := L0 + L1 * ‖g x‖ with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨ha, hcap, hroot⟩ := slideWeight_spec hL1 hR hA hM
  set a := slideWeight L1 R A M with hadef
  obtain ⟨haA, hratio, haL⟩ := slide_cap hL1 hR hA ha hcap
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z with hydef
  set gy := g y with hgydef
  set x' := mixPoint A a x ub with hx'def
  set t := a / (A + a) with htdef
  have ht0 : 0 ≤ t := by positivity
  have hgap0 : 0 ≤ f x + h x - (f xs + h xs) := by
    have := hmin hx
    simp only [mem_ofPred_eq] at this
    linarith
  have hzsq : ‖z - xs‖ ^ 2 / 2 + e ≤ R ^ 2 := by linarith [mul_nonneg hA.le hgap0]
  have hzR : ‖z - xs‖ ≤ 2 * R := by
    apply le_two_mul_of_sq hR.le
    linarith
  have hzx : ‖z - x‖ ≤ 22 * R := by
    calc ‖z - x‖ = ‖(z - xs) - (x - xs)‖ := by congr 1; abel
      _ ≤ ‖z - xs‖ + ‖x - xs‖ := norm_sub_le _ _
      _ ≤ 22 * R := by linarith
  have hyx : ‖y - x‖ ≤ 22 * R * t := by
    rw [hydef, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hzx ht0
    linarith
  set gs := g xs with hgsdef
  have hoptx := optimality hy.convex hy.grad hy.cont hy.setConvex hy.regConvex hxs hmin hx
  have hH0 : 0 ≤ f x - f xs - ⟪gs, x - xs⟫ := by
    have := Gradient.convex_support hy.convex hy.grad xs x
    linarith
  have hAH : A * (f x - f xs - ⟪gs, x - xs⟫) ≤ R ^ 2 := by
    have h1 : f x - f xs - ⟪gs, x - xs⟫ ≤ f x + h x - (f xs + h xs) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hA.le
    linarith [sq_nonneg ‖z - xs‖, mul_nonneg hA.le hgap0]
  have hcoc := shifted_cocoercive hL0 hL1 hy.convex hy.grad hy.cont hy.smooth xs x
  have hroot4 : 4 * M * a ^ 2 ≤ A + a := by linarith [mul_nonneg hM.le (sq_nonneg a)]
  have haγ : a * ‖g x - gs‖ ≤ 9 / 4 * R :=
    scaled_gap_bound ha (norm_nonneg _) hH0 hR hcoc hAH hroot4 haA (by linarith)
  have hLyx : L1 * ‖y - x‖ ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hyx hL1
    have h2 : L1 * (22 * R * t) = 22 / 80 * (80 * (L1 * R) * t) := by ring
    linarith
  have hgyx : ‖gy - g x‖ ≤ 2 * M * ‖y - x‖ :=
    ball_lipschitz hL0.le hL1 hy.cont hy.smooth (x := x) (u := y) (v := x) hLyx le_rfl
      (by simp)
  have hagy : a * ‖gy - g x‖ ≤ 11 / 4 * R := by
    have h1 : a * ‖gy - g x‖ ≤ a * (2 * M * (22 * R * t)) :=
      mul_le_mul_of_nonneg_left (hgyx.trans (mul_le_mul_of_nonneg_left hyx (by positivity)))
        ha.le
    have h2 : a * (2 * M * (22 * R * t)) = 11 / 4 * R * (16 * M * a ^ 2 / (A + a)) := by
      simp only [t]; field_simp; ring
    have h3 : 16 * M * a ^ 2 / (A + a) ≤ 1 := (div_le_one hS).mpr hroot
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 11 / 4 * R by positivity)
    linarith
  have hgygs : ‖gy - gs‖ ≤ ‖gy - g x‖ + ‖g x - gs‖ := by
    calc ‖gy - gs‖ = ‖(gy - g x) + (g x - gs)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hB : a * ‖gy - gs‖ ≤ 5 * R := by
    have := mul_le_mul_of_nonneg_left hgygs ha.le
    linarith
  have hoptu := optimality hy.convex hy.grad hy.cont hy.setConvex hy.regConvex hxs hmin hub
  have hcs : -⟪gy - gs, ub - xs⟫ ≤ ‖gy - gs‖ * ‖ub - xs‖ := by
    have := real_inner_le_norm (-(gy - gs)) (ub - xs)
    rwa [inner_neg_left, norm_neg] at this
  have hlow : -(a * ‖gy - gs‖ * ‖ub - xs‖) ≤ a * (⟪gy, ub - xs⟫ + h ub - h xs) := by
    have hi : ⟪gy, ub - xs⟫ = ⟪gy - gs, ub - xs⟫ + ⟪gs, ub - xs⟫ := by
      rw [inner_sub_left]; ring
    rw [hi]
    have k1 := mul_le_mul_of_nonneg_left hcs ha.le
    have h2 : 0 ≤ ⟪gs, ub - xs⟫ + h ub - h xs := by linarith
    have k2 := mul_nonneg ha.le h2
    linear_combination k1 + k2
  set d := ‖ub - z‖ with hddef
  have hubxs_le : ‖ub - xs‖ ≤ d + 2 * R := by
    calc ‖ub - xs‖ = ‖(ub - z) + (z - xs)‖ := by congr 1; abel
      _ ≤ d + ‖z - xs‖ := norm_add_le _ _
      _ ≤ d + 2 * R := by linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdq : d ^ 2 ≤ 33 * R ^ 2 + 15 * R * d := by
    have h1 : a * ‖gy - gs‖ * ‖ub - xs‖ ≤ 5 * R * (d + 2 * R) :=
      mul_le_mul hB hubxs_le (norm_nonneg _) (by positivity)
    have hU := sq_nonneg ‖up - xs‖
    linear_combination 3 * hps + 3 * hlow + 3 * h1 + 3 * hzsq + (3 / 2) * hU
  have hd17 : d ≤ 17 * R := by
    by_contra hcon
    push Not at hcon
    have hp := mul_pos (sub_pos.2 hcon) (show 0 < d + 2 * R by positivity)
    nlinarith
  have hubxs : ‖ub - xs‖ ≤ 19 * R := by linarith
  have hubx : ‖ub - x‖ ≤ 39 * R := by
    calc ‖ub - x‖ = ‖(ub - xs) - (x - xs)‖ := by congr 1; abel
      _ ≤ ‖ub - xs‖ + ‖x - xs‖ := norm_sub_le _ _
      _ ≤ 39 * R := by linarith
  have hx'x : ‖x' - x‖ ≤ 39 * R * t := by
    rw [hx'def, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hubx ht0
    linarith
  have hr : L1 * (39 * R * t) ≤ 1 / 2 := by
    have h2 : L1 * (39 * R * t) = 39 / 80 * (80 * (L1 * R) * t) := by ring
    linarith
  have hdesc : f x' ≤ f y + ⟪gy, x' - y⟫ + M * ‖x' - y‖ ^ 2 :=
    ball_upper hL0.le hL1 hy.grad hy.cont hy.smooth (x := x) (u := y) (v := x') hr
      (hyx.trans (by linarith [mul_nonneg hR.le ht0])) hx'x
  have hstep3 : 3 * M * a ^ 2 ≤ A + a := by linarith [mul_nonneg hM.le (sq_nonneg a)]
  have hmain := slide_combine hy.convex hy.grad hy.regConvex hA ha hstep3 hx hub hps hdesc
  refine ⟨by linarith, mix_mem hy.setConvex hA.le ha.le hS hx hub,
    mix_dist hA.le ha.le hS x ub xs hxd (by linarith)⟩

end OracleTemplate.GeneralizedSliding
