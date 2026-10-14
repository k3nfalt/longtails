import LongTails.Algorithms.CompositeGeneralizedAccelerated
import LongTails.Proofs.CompositeGeneralizedLocal

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeGeneralized

open LongTails.Setups.CompositeGeneralizedSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma weight_spec {L1 R A M : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A) (hM : 0 < M) :
    0 < weight L1 R A M ∧ weight L1 R A M ≤ A / (1 + 32 * L1 * R) ∧
      4 * M * weight L1 R A M ^ 2 ≤ A + weight L1 R A M := by
  set s := Real.sqrt (1 + 16 * M * A)
  have hs2 : s ^ 2 = 1 + 16 * M * A := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hr : 0 < (1 + s) / (8 * M) := by positivity
  have hcap : 0 < A / (1 + 32 * L1 * R) := by positivity
  have har : weight L1 R A M ≤ (1 + s) / (8 * M) := min_le_left _ _
  have hapos : 0 < weight L1 R A M := lt_min hr hcap
  refine ⟨hapos, min_le_right _ _, ?_⟩
  set a := weight L1 R A M
  rw [le_div_iff₀ (by positivity)] at har
  have hsq : (8 * M * a - 1) ^ 2 ≤ s ^ 2 := by
    have h1 : -s ≤ 8 * M * a - 1 := by nlinarith
    have h2 : 8 * M * a - 1 ≤ s := by nlinarith
    nlinarith
  nlinarith

omit [CompleteSpace E] in
lemma mix_sub_left {A a : ℝ} (hS : 0 < A + a) (x z : E) :
    mixPoint A a x z - x = (a / (A + a)) • (z - x) := by
  unfold mixPoint
  have h : A / (A + a) = 1 - a / (A + a) := by field_simp; ring
  rw [h]
  module

omit [CompleteSpace E] in
lemma mix_sub_mix (A a : ℝ) (x z p : E) :
    mixPoint A a x p - mixPoint A a x z = (a / (A + a)) • (p - z) := by
  unfold mixPoint
  module

omit [CompleteSpace E] in
lemma mix_dist {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hS : 0 < A + a) (x z c : E) {D : ℝ}
    (hx : ‖x - c‖ ≤ D) (hz : ‖z - c‖ ≤ D) : ‖mixPoint A a x z - c‖ ≤ D := by
  have he : mixPoint A a x z - c = (A / (A + a)) • (x - c) + (a / (A + a)) • (z - c) := by
    unfold mixPoint
    have h : A / (A + a) + a / (A + a) = 1 := by field_simp
    calc (A / (A + a)) • x + (a / (A + a)) • z - c
        = (A / (A + a)) • x + (a / (A + a)) • z - (A / (A + a) + a / (A + a)) • c := by
          rw [h, one_smul]
      _ = _ := by module
  rw [he]
  have h1 : 0 ≤ A / (A + a) := by positivity
  have h2 : 0 ≤ a / (A + a) := by positivity
  calc ‖(A / (A + a)) • (x - c) + (a / (A + a)) • (z - c)‖
      ≤ (A / (A + a)) * ‖x - c‖ + (a / (A + a)) * ‖z - c‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
          abs_of_nonneg h2]
    _ ≤ (A / (A + a)) * D + (a / (A + a)) * D := by gcongr
    _ = D := by field_simp

omit [CompleteSpace E] in
lemma mix_mem {Q : Set E} (hQ : Convex ℝ Q) {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hS : 0 < A + a) {x z : E} (hx : x ∈ Q) (hz : z ∈ Q) : mixPoint A a x z ∈ Q :=
  hQ hx hz (by positivity) (by positivity) (by field_simp)

lemma stm_step {f ψ : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {A a M : ℝ} (hA : 0 < A) (ha : 0 < a) (hstep : 2 * M * a ^ 2 ≤ A + a)
    {x z p xs : E} (hx : x ∈ Q) (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪g (mixPoint A a x z), u - z⟫ + ψ u)
      Q p)
    (hdesc : f (mixPoint A a x p) ≤ f (mixPoint A a x z) +
      ⟪g (mixPoint A a x z), mixPoint A a x p - mixPoint A a x z⟫ +
        M * ‖mixPoint A a x p - mixPoint A a x z‖ ^ 2) :
    (A + a) * (f (mixPoint A a x p) + ψ (mixPoint A a x p) - (f xs + ψ xs)) +
        ‖p - xs‖ ^ 2 / 2 ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 := by
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
  have hq : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) ≤ ‖p - z‖ ^ 2 / 2 := by
    have e : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) =
        (2 * M * a ^ 2) / (A + a) * (‖p - z‖ ^ 2 / 2) := by
      simp only [m]; field_simp
    rw [e]
    have hfrac : (2 * M * a ^ 2) / (A + a) ≤ 1 := (div_le_one hS).mpr hstep
    have hn : 0 ≤ ‖p - z‖ ^ 2 / 2 := by positivity
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

structure Hyp (f ψ : E → ℝ) (g : E → E) (Q : Set E) (prox : ℝ → E → E → E)
    (L0 L1 : ℝ) : Prop where
  hL0 : 0 < L0
  hL1 : 0 ≤ L1
  convex : ConvexOn ℝ univ f
  grad : ∀ x, HasGradientAt f (g x) x
  cont : Continuous g
  smooth : SymmetricSmooth g L0 L1
  setConvex : Convex ℝ Q
  regConvex : ConvexOn ℝ Q ψ
  proxSpec : ∀ a, 0 < a → ∀ z v, prox a z v ∈ Q ∧
    IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪v, u - z⟫ + ψ u) Q (prox a z v)

noncomputable def step (L0 L1 R : ℝ) (g : E → E) (prox : ℝ → E → E → E)
    (s : ℝ × E × E) : ℝ × E × E :=
  (s.1 + weight L1 R s.1 (L0 + L1 * ‖g s.2.1‖),
    mixPoint s.1 (weight L1 R s.1 (L0 + L1 * ‖g s.2.1‖)) s.2.1
      (prox (weight L1 R s.1 (L0 + L1 * ‖g s.2.1‖)) s.2.2
        (g (mixPoint s.1 (weight L1 R s.1 (L0 + L1 * ‖g s.2.1‖)) s.2.1 s.2.2))),
    prox (weight L1 R s.1 (L0 + L1 * ‖g s.2.1‖)) s.2.2
      (g (mixPoint s.1 (weight L1 R s.1 (L0 + L1 * ‖g s.2.1‖)) s.2.1 s.2.2)))

def Inv (f ψ : E → ℝ) (Q : Set E) (xs : E) (R : ℝ) (s : ℝ × E × E) : Prop :=
  0 < s.1 ∧ s.2.1 ∈ Q ∧ s.2.2 ∈ Q ∧
    s.1 * (f s.2.1 + ψ s.2.1 - (f xs + ψ xs)) + ‖s.2.2 - xs‖ ^ 2 / 2 ≤ R ^ 2 ∧
    ‖s.2.1 - xs‖ ≤ 2 * R ∧ ‖s.2.2 - xs‖ ≤ 2 * R

lemma cap_ratio {L1 R A a : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R) (hA : 0 < A) (ha : 0 < a)
    (hcap : a ≤ A / (1 + 32 * L1 * R)) :
    a ≤ A ∧ 32 * (L1 * R) * (a / (A + a)) ≤ 1 ∧ 32 * (a * L1 * R) ≤ A := by
  have hden : 0 < 1 + 32 * L1 * R := by positivity
  rw [le_div_iff₀ hden] at hcap
  have hLR : 0 ≤ L1 * R := by positivity
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  rw [mul_div_assoc', div_le_one (by positivity)]
  nlinarith

lemma le_two_mul_of_sq {u R : ℝ} (hR : 0 ≤ R) (h : u ^ 2 ≤ 2 * R ^ 2) : u ≤ 2 * R := by
  nlinarith

lemma scaled_gap_bound {a γ M H A R L1 : ℝ} (ha : 0 < a) (hγ : 0 ≤ γ)
    (hH : 0 ≤ H) (hR : 0 < R)
    (hcoc : γ ^ 2 ≤ 8 * (M + L1 * γ) * H) (hAH : A * H ≤ R ^ 2)
    (hroot : 4 * M * a ^ 2 ≤ A + a) (haA : a ≤ A) (haL : 32 * (a * L1 * R) ≤ A) :
    a * γ ≤ 9 / 4 * R := by
  set T := a * γ
  have hT0 : 0 ≤ T := by positivity
  have h1 : T ^ 2 ≤ 8 * (a ^ 2 * M) * H + 8 * (a * L1) * T * H := by
    have h := mul_le_mul_of_nonneg_left hcoc (sq_nonneg a)
    have e : a ^ 2 * (8 * (M + L1 * γ) * H) = 8 * (a ^ 2 * M) * H + 8 * (a * L1) * T * H := by
      simp only [T]; ring
    have e2 : a ^ 2 * γ ^ 2 = T ^ 2 := by simp only [T]; ring
    rw [e, e2] at h
    exact h
  have haM : a ^ 2 * M ≤ A / 2 := by linarith
  have h2 : 8 * (a ^ 2 * M) * H ≤ 4 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right haM hH
    linarith
  have h3 : 8 * (a * L1) * T * H ≤ T * R / 4 := by
    have h5 : 32 * (a * L1 * R) * (T * H) ≤ A * (T * H) :=
      mul_le_mul_of_nonneg_right haL (by positivity)
    have h6 : A * H * T ≤ R ^ 2 * T := mul_le_mul_of_nonneg_right hAH hT0
    have h7 : 32 * R * (8 * (a * L1) * T * H) ≤ 32 * R * (T * R / 4) := by
      have e1 : 32 * R * (8 * (a * L1) * T * H) = 8 * (32 * (a * L1 * R) * (T * H)) := by ring
      have e2 : 32 * R * (T * R / 4) = 8 * (R ^ 2 * T) := by ring
      have e3 : A * (T * H) = A * H * T := by ring
      rw [e1, e2]
      linarith
    exact le_of_mul_le_mul_left h7 (by positivity)
  have hq : T ^ 2 ≤ 4 * R ^ 2 + T * R / 4 := by linarith
  nlinarith

set_option maxHeartbeats 1000000 in
lemma inv_step {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R : ℝ} (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) {s : ℝ × E × E}
    (hs : Inv f ψ Q xs R s) : Inv f ψ Q xs R (step L0 L1 R g prox s) := by
  obtain ⟨A, x, z⟩ := s
  obtain ⟨hA, hx, hz, hΦ, hxd, hzd⟩ := hs
  simp only at hA hx hz hΦ hxd hzd
  have hL0 := h.hL0
  have hL1 := h.hL1
  set M := L0 + L1 * ‖g x‖ with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨ha, hcap, hroot⟩ := weight_spec hL1 hR hA hM
  set a := weight L1 R A M with hadef
  obtain ⟨haA, hratio, haL⟩ := cap_ratio hL1 hR hA ha hcap
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z with hydef
  set gy := g y with hgydef
  obtain ⟨hp, hpmin⟩ := h.proxSpec a ha z gy
  set p := prox a z gy with hpdef
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
    scaled_gap_bound ha (norm_nonneg _) hH0 hR hcoc hAH hroot haA (by linarith)
  have hLyx : L1 * ‖y - x‖ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hyx hL1
    linarith
  have hgyx : ‖gy - g x‖ ≤ 2 * M * ‖y - x‖ :=
    ball_lipschitz hL0.le hL1 h.cont h.smooth (x := x) (u := y) (v := x) hLyx le_rfl
      (by simp)
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
  have hpxs : ‖p - xs‖ ≤ 21 / 2 * R := by
    have := mul_le_mul_of_nonneg_left hgygs ha.le
    linarith
  have hpx : ‖p - x‖ ≤ 25 / 2 * R := by
    calc ‖p - x‖ = ‖(p - xs) - (x - xs)‖ := by congr 1; abel
      _ ≤ ‖p - xs‖ + ‖x - xs‖ := norm_sub_le _ _
      _ ≤ 25 / 2 * R := by linarith
  have hx'x : ‖x' - x‖ ≤ 25 / 2 * R * t := by
    rw [hx'def, mix_sub_left hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_left hpx ht0
    linarith
  have hr : L1 * (25 / 2 * R * t) ≤ 1 / 2 := by linarith
  have hdesc : f x' ≤ f y + ⟪gy, x' - y⟫ + M * ‖x' - y‖ ^ 2 :=
    ball_upper hL0.le hL1 h.grad h.cont h.smooth (x := x) (u := y) (v := x') hr
      (hyx.trans (by linarith)) hx'x
  have hstep : 2 * M * a ^ 2 ≤ A + a := by
    have := mul_nonneg hM.le (sq_nonneg a)
    linarith
  have hmain := stm_step h.convex h.grad h.setConvex h.regConvex hA ha hstep hx hp hxs
    hpmin hdesc
  have hx'Q : x' ∈ Q := mix_mem h.setConvex hA.le ha.le hS hx hp
  have hgap' : 0 ≤ f x' + ψ x' - (f xs + ψ xs) := by
    have := hmin hx'Q
    simp only [mem_ofPred_eq] at this
    linarith
  have hΦ' : (A + a) * (f x' + ψ x' - (f xs + ψ xs)) + ‖p - xs‖ ^ 2 / 2 ≤ R ^ 2 := by
    linarith
  have hp2 : ‖p - xs‖ ≤ 2 * R := by
    apply le_two_mul_of_sq hR.le
    have := mul_nonneg hS.le hgap'
    linarith
  change Inv f ψ Q xs R (A + a, x', p)
  exact ⟨hS, hx'Q, hp, hΦ', mix_dist hA.le ha.le hS x p xs hxd hp2, hp2⟩

end OracleTemplate.CompositeGeneralized
