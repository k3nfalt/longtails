import LongTails.Proofs.CompositeGeneralizedStep

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inexact_stm_step {f ψ : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {A a M : ℝ} (hA : 0 < A) (ha : 0 < a) (hstep : 4 * M * a ^ 2 ≤ A + a)
    {x z p xs e : E} (hx : x ∈ Q) (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪g (mixPoint A a x z) + e, u - z⟫ + ψ u)
      Q p)
    (hdesc : f (mixPoint A a x p) ≤ f (mixPoint A a x z) +
      ⟪g (mixPoint A a x z), mixPoint A a x p - mixPoint A a x z⟫ +
        M * ‖mixPoint A a x p - mixPoint A a x z‖ ^ 2) :
    (A + a) * (f (mixPoint A a x p) + ψ (mixPoint A a x p) - (f xs + ψ xs)) +
        ‖p - xs‖ ^ 2 / 2 ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 -
        ‖p - z‖ ^ 2 / 4 - a * ⟪e, p - xs⟫ := by
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z
  set x' := mixPoint A a x p
  set gy := g y
  set l := A / (A + a)
  set m := a / (A + a)
  have hlm : l + m = 1 := by simp only [l, m]; field_simp
  have hl0 : 0 ≤ l := by positivity
  have hm0 : 0 ≤ m := by positivity
  have e1 : x' - y = m • (p - z) := mix_sub_mix A a x z p
  have e2 : x' - y = l • (x - y) + m • (p - y) := by
    have h : l • (x - y) + m • (p - y) = (l • x + m • p) - (l + m) • y := by module
    rw [h, hlm, one_smul]
    rfl
  have i1 : ⟪gy, x' - y⟫ = l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, p - xs⟫) := by
    rw [e2, inner_add_right, inner_smul_right, inner_smul_right,
      show p - y = (xs - y) + (p - xs) by abel, inner_add_right]
  have n1 : ‖x' - y‖ ^ 2 = m ^ 2 * ‖p - z‖ ^ 2 := by
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have c1 := Gradient.convex_support hc hf y x
  have c2 := Gradient.convex_support hc hf y xs
  have hψx' : ψ x' ≤ l * ψ x + m * ψ p := by
    have h := hψ.2 hx hp hl0 hm0 hlm
    simp only [smul_eq_mul] at h
    exact h
  have tp := prox_three_point hQ hψ ha hp hmin hxs
  simp only [inner_add_left] at tp
  have hq : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) ≤ ‖p - z‖ ^ 2 / 4 := by
    have e : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) =
        (4 * M * a ^ 2) / (A + a) * (‖p - z‖ ^ 2 / 4) := by
      simp only [m]; field_simp
    rw [e]
    have hfrac : (4 * M * a ^ 2) / (A + a) ≤ 1 := (div_le_one hS).mpr hstep
    have hn : 0 ≤ ‖p - z‖ ^ 2 / 4 := by positivity
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hdesc hS.le
  rw [i1, n1] at hd
  have ex1 : (A + a) * (f y + (l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, p - xs⟫)) +
      M * (m ^ 2 * ‖p - z‖ ^ 2)) =
      (A + a) * f y + A * ⟪gy, x - y⟫ + a * ⟪gy, xs - y⟫ + a * ⟪gy, p - xs⟫ +
        (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) := by
    simp only [l, m]; field_simp; ring
  rw [ex1] at hd
  have hψ' := mul_le_mul_of_nonneg_left hψx' hS.le
  have ex2 : (A + a) * (l * ψ x + m * ψ p) = A * ψ x + a * ψ p := by
    simp only [l, m]; field_simp
  rw [ex2] at hψ'
  have k1 := mul_le_mul_of_nonneg_left c1 hA.le
  have k2 := mul_le_mul_of_nonneg_left c2 ha.le
  nlinarith

omit [CompleteSpace E] in
lemma inexact_error_split {a : ℝ} (ha : 0 ≤ a) (e p z xs : E) :
    -(‖p - z‖ ^ 2 / 4) - a * ⟪e, p - xs⟫ ≤
      a * ⟪e, xs - z⟫ + a ^ 2 * ‖e‖ ^ 2 := by
  have he : ⟪e, p - xs⟫ = ⟪e, p - z⟫ - ⟪e, xs - z⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hn := abs_real_inner_le_norm e (p - z)
  have hlo : -‖e‖ * ‖p - z‖ ≤ ⟪e, p - z⟫ := by
    have := neg_abs_le ⟪e, p - z⟫
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hlo ha
  have hs := sq_nonneg (a * ‖e‖ - ‖p - z‖ / 2)
  rw [he]
  nlinarith

lemma inexact_stm_potential {f ψ : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {A a M : ℝ} (hA : 0 < A) (ha : 0 < a) (hstep : 4 * M * a ^ 2 ≤ A + a)
    {x z p xs e : E} (hx : x ∈ Q) (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪g (mixPoint A a x z) + e, u - z⟫ + ψ u)
      Q p)
    (hdesc : f (mixPoint A a x p) ≤ f (mixPoint A a x z) +
      ⟪g (mixPoint A a x z), mixPoint A a x p - mixPoint A a x z⟫ +
        M * ‖mixPoint A a x p - mixPoint A a x z‖ ^ 2) :
    (A + a) * (f (mixPoint A a x p) + ψ (mixPoint A a x p) - (f xs + ψ xs)) +
        ‖p - xs‖ ^ 2 / 2 ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 +
        a * ⟪e, xs - z⟫ + a ^ 2 * ‖e‖ ^ 2 := by
  have h := inexact_stm_step hc hf hQ hψ hA ha hstep hx hp hxs hmin hdesc
  have he := inexact_error_split ha.le e p z xs
  linarith

lemma inexact_local_descent {f ψ : E → ℝ} {g : E → E} {Q : Set E}
    {prox : ℝ → E → E → E} {L0 L1 R A a M : ℝ}
    (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs x z e : E}
    (hxs : xs ∈ Q) (hmin : IsMinOn (fun u => f u + ψ u) Q xs)
    (hs : Inv f ψ Q xs R (A, x, z)) (ha : 0 < a)
    (hcap : a ≤ A / (1 + 32 * L1 * R)) (hroot : 4 * M * a ^ 2 ≤ A + a)
    (hMupper : L0 + L1 * ‖g x‖ ≤ M) (herror : a * ‖e‖ ≤ R) :
    let y := mixPoint A a x z
    let p := prox a z (g y + e)
    let x' := mixPoint A a x p
    f x' ≤ f y + ⟪g y, x' - y⟫ + M * ‖x' - y‖ ^ 2 := by
  obtain ⟨hA, hx, hz, hΦ, hxd, hzd⟩ := hs
  simp only at hA hx hz hΦ hxd hzd
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hMupper
  obtain ⟨haA, hratio, haL⟩ := cap_ratio hL1 hR hA ha hcap
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z with hydef
  set gy := g y with hgydef
  obtain ⟨hp, hpmin⟩ := h.proxSpec a ha z (gy + e)
  set p := prox a z (gy + e) with hpdef
  set x' := mixPoint A a x p with hx'def
  set t := a / (A + a) with htdef
  have ht0 : 0 ≤ t := by positivity
  have hRt : 0 ≤ R * t := by positivity
  have hzx : ‖z - x‖ ≤ 4 * R := by
    calc ‖z - x‖ = ‖(z - xs) - (x - xs)‖ := by congr 1; abel
      _ ≤ ‖z - xs‖ + ‖x - xs‖ := norm_sub_le _ _
      _ ≤ 4 * R := by linarith
  have hyx : ‖y - x‖ ≤ 4 * R * t := by
    rw [hydef, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hzx ht0
    linarith
  set gs := g xs with hgsdef
  have hoptx := optimality h.convex h.grad h.cont h.setConvex h.regConvex hxs hmin hx
  have hH0 : 0 ≤ f x - f xs - ⟪gs, x - xs⟫ := by
    have := Gradient.convex_support h.convex h.grad xs x
    linarith
  have hAH : A * (f x - f xs - ⟪gs, x - xs⟫) ≤ R ^ 2 := by
    have h1 : f x - f xs - ⟪gs, x - xs⟫ ≤ f x + ψ x - (f xs + ψ xs) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hA.le
    have h3 := sq_nonneg ‖z - xs‖
    linarith
  have hcoc := shifted_cocoercive hL0 hL1 h.convex h.grad h.cont h.smooth xs x
  have haγ : a * ‖g x - gs‖ ≤ 9 / 4 * R :=
    scaled_gap_bound ha (norm_nonneg _) hH0 hR hcoc hAH
      (by nlinarith [mul_le_mul_of_nonneg_right hMupper (sq_nonneg a)]) haA (by linarith)
  have hLyx : L1 * ‖y - x‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hyx hL1
    linarith
  have hgyx : ‖gy - g x‖ ≤ 2 * M * ‖y - x‖ :=
    (ball_lipschitz hL0.le hL1 h.cont h.smooth (x := x) (u := y) (v := x) hLyx le_rfl
      (by simp)).trans (by gcongr)
  have hagy : a * ‖gy - g x‖ ≤ 2 * R := by
    have h1 : a * ‖gy - g x‖ ≤ a * (2 * M * (4 * R * t)) :=
      mul_le_mul_of_nonneg_left (hgyx.trans (mul_le_mul_of_nonneg_left hyx (by positivity)))
        ha.le
    have h2 : a * (2 * M * (4 * R * t)) = 2 * R * (4 * M * a ^ 2 / (A + a)) := by
      simp only [t]; field_simp
    have h3 : 4 * M * a ^ 2 / (A + a) ≤ 1 := (div_le_one hS).mpr hroot
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * R by positivity)
    linarith
  have hoptp := optimality h.convex h.grad h.cont h.setConvex h.regConvex hxs hmin hp
  have hpd := prox_distance h.setConvex h.regConvex ha hp hxs hpmin hoptp
  have hgygs : ‖gy - gs‖ ≤ ‖gy - g x‖ + ‖g x - gs‖ := by
    calc ‖gy - gs‖ = ‖(gy - g x) + (g x - gs)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hpxs : ‖p - xs‖ ≤ 25 / 2 * R := by
    have hnoise : ‖gy + e - gs‖ ≤ ‖gy - gs‖ + ‖e‖ := by
      rw [show gy + e - gs = (gy - gs) + e by abel]
      exact norm_add_le _ _
    have h1 := mul_le_mul_of_nonneg_left hgygs ha.le
    have h2 := mul_le_mul_of_nonneg_left hnoise ha.le
    linarith
  have hpx : ‖p - x‖ ≤ 29 / 2 * R := by
    calc ‖p - x‖ = ‖(p - xs) - (x - xs)‖ := by congr 1; abel
      _ ≤ ‖p - xs‖ + ‖x - xs‖ := norm_sub_le _ _
      _ ≤ 29 / 2 * R := by linarith
  have hx'x : ‖x' - x‖ ≤ 29 / 2 * R * t := by
    rw [hx'def, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hpx ht0
    linarith
  have hr : L1 * (29 / 2 * R * t) ≤ 1 / 2 := by linarith
  have hdesc : f x' ≤ f y + ⟪gy, x' - y⟫ + M * ‖x' - y‖ ^ 2 :=
    (ball_upper hL0.le hL1 h.grad h.cont h.smooth (x := x) (u := y) (v := x') hr
      (hyx.trans (by linarith)) hx'x).trans (by gcongr)
  exact hdesc

lemma inexact_controlled_step {f ψ : E → ℝ} {g : E → E} {Q : Set E}
    {prox : ℝ → E → E → E} {L0 L1 R A a M : ℝ}
    (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs x z e : E}
    (hxs : xs ∈ Q) (hmin : IsMinOn (fun u => f u + ψ u) Q xs)
    (hs : Inv f ψ Q xs R (A, x, z)) (ha : 0 < a)
    (hcap : a ≤ A / (1 + 32 * L1 * R)) (hroot : 4 * M * a ^ 2 ≤ A + a)
    (hMupper : L0 + L1 * ‖g x‖ ≤ M) (herror : a * ‖e‖ ≤ R) :
    let p := prox a z (g (mixPoint A a x z) + e)
    let x' := mixPoint A a x p
    p ∈ Q ∧ x' ∈ Q ∧
      (A + a) * (f x' + ψ x' - (f xs + ψ xs)) + ‖p - xs‖ ^ 2 / 2 ≤
        A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 +
          a * ⟪e, xs - z⟫ + a ^ 2 * ‖e‖ ^ 2 := by
  have hd := inexact_local_descent h hR hxs hmin hs ha hcap hroot hMupper herror
  obtain ⟨hp, hpmin⟩ := h.proxSpec a ha z (g (mixPoint A a x z) + e)
  refine ⟨hp, mix_mem h.setConvex hs.1.le ha.le (by linarith [hs.1]) hs.2.1 hp, ?_⟩
  exact inexact_stm_potential h.convex h.grad h.setConvex h.regConvex hs.1 ha hroot
    hs.2.1 hp hxs hpmin hd

omit [CompleteSpace E] in
lemma inexact_step_invariant {f ψ : E → ℝ} {Q : Set E} {xs x z p : E}
    {R A a : ℝ} (hQ : Convex ℝ Q) (hR : 0 < R)
    (hmin : IsMinOn (fun u => f u + ψ u) Q xs)
    (hs : Inv f ψ Q xs R (A, x, z)) (ha : 0 < a) (hp : p ∈ Q)
    (henergy : (A + a) * (f (mixPoint A a x p) + ψ (mixPoint A a x p) -
      (f xs + ψ xs)) + ‖p - xs‖ ^ 2 / 2 ≤ R ^ 2) :
    Inv f ψ Q xs R (A + a, mixPoint A a x p, p) := by
  have hS : 0 < A + a := by linarith [hs.1]
  have hx' := mix_mem hQ hs.1.le ha.le hS hs.2.1 hp
  have hgap : 0 ≤ f (mixPoint A a x p) + ψ (mixPoint A a x p) - (f xs + ψ xs) :=
    sub_nonneg.mpr (hmin hx')
  have hpd : ‖p - xs‖ ≤ 2 * R := by
    apply le_two_mul_of_sq hR.le
    have := mul_nonneg hS.le hgap
    linarith
  exact ⟨hS, hx', hp, henergy,
    mix_dist hs.1.le ha.le hS x p xs hs.2.2.2.2.1 hpd, hpd⟩

lemma shifted_curvature_bound {γ L H L1 : ℝ} (hL : 0 ≤ L)
    (hH : 0 ≤ H)
    (h : γ ^ 2 ≤ 8 * (L + 2 * L1 * γ) * H) :
    L1 * γ ≤ L + 18 * L1 ^ 2 * H := by
  have hscaled := mul_le_mul_of_nonneg_left h (sq_nonneg L1)
  by_contra hn
  have hgt : L + 18 * L1 ^ 2 * H < L1 * γ := lt_of_not_ge hn
  have hpos : 0 < L1 * γ + L + 2 * L1 ^ 2 * H := by nlinarith
  have hp := mul_pos (sub_pos.mpr hgt) hpos
  nlinarith [mul_nonneg hL (mul_nonneg (sq_nonneg L1) hH)]

end OracleTemplate.CompositeGeneralized
