import LongTails.Proofs.CompositeGeneralizedLocal
import LongTails.Algorithms.GeneralizedGradientSliding

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def SubgradientOracle (h : E → ℝ) (sub : E → E) (Q : Set E) (M : ℝ) : Prop :=
  ∀ u ∈ Q, ‖sub u‖ ≤ M ∧ ∀ v ∈ Q, h u + ⟪sub u, v - u⟫ ≤ h v

def ProjectionOracle (proj : E → E) (Q : Set E) : Prop :=
  ∀ w, proj w ∈ Q ∧ ∀ u ∈ Q, ‖w - proj w‖ ≤ ‖w - u‖

omit [CompleteSpace E] in
lemma proj_variational {proj : E → E} {Q : Set E} (hQ : Convex ℝ Q)
    (hP : ProjectionOracle proj Q) (w : E) {u : E} (hu : u ∈ Q) :
    ⟪w - proj w, u - proj w⟫ ≤ 0 := by
  obtain ⟨hp, hnear⟩ := hP w
  have hmin : IsMinOn (fun v => ‖v - w‖ ^ 2 / (2 * 1) + ⟪(0 : E), v - w⟫ + (0 : ℝ)) Q
      (proj w) := by
    intro v hv
    simp only [mem_ofPred_eq, inner_zero_left, add_zero]
    have h := hnear v hv
    rw [norm_sub_rev w (proj w), norm_sub_rev w v] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    linarith
  have h3 := CompositeGeneralized.prox_three_point (ψ := fun _ => (0 : ℝ)) hQ
    (convexOn_const 0 hQ) one_pos hp hmin hu
  simp only [inner_zero_left, sub_self, add_zero, mul_zero] at h3
  have e : ‖w - u‖ ^ 2 = ‖w - proj w‖ ^ 2 + ‖u - proj w‖ ^ 2 -
      2 * ⟪w - proj w, u - proj w⟫ := by
    rw [show w - u = (w - proj w) - (u - proj w) by abel, norm_sub_sq_real]; ring
  rw [norm_sub_rev (proj w) u, norm_sub_rev (proj w) w] at h3
  nlinarith

omit [CompleteSpace E] in
lemma polar (a b c : E) : 2 * ⟪a - c, b - c⟫ = ‖a - c‖ ^ 2 + ‖b - c‖ ^ 2 - ‖b - a‖ ^ 2 := by
  have h1 := norm_sub_sq_real (b - c) (a - c)
  have h2 : ⟪b - c, a - c⟫ = ⟪a - c, b - c⟫ := real_inner_comm _ _
  rw [show b - a = (b - c) - (a - c) by abel, h1, h2]
  ring


omit [CompleteSpace E] in
lemma inner_three_point {proj : E → E} {Q : Set E} (hQ : Convex ℝ Q)
    (hP : ProjectionOracle proj Q) {β p : ℝ} (hβ : 0 < β) (hp : 0 ≤ p) (z u' v : E)
    {u : E} (hu : u ∈ Q) :
    ⟪v, proj (innerTarget β p z u' v) - u⟫ + β / 2 * ‖proj (innerTarget β p z u' v) - z‖ ^ 2 +
        β * p / 2 * ‖proj (innerTarget β p z u' v) - u'‖ ^ 2 ≤
      β / 2 * ‖u - z‖ ^ 2 + β * p / 2 * ‖u - u'‖ ^ 2 -
        β * (1 + p) / 2 * ‖proj (innerTarget β p z u' v) - u‖ ^ 2 := by
  set w := innerTarget β p z u' v
  set q := proj w
  have hvi := proj_variational hQ hP w hu
  have h1p : 0 < 1 + p := by linarith
  have hw : (1 + p) • w = z + p • u' - (1 / β) • v := by
    simp only [w, innerTarget, smul_smul]
    rw [mul_one_div_cancel h1p.ne', one_smul]
  have key : (1 + p) • (w - q) = (z - q) + p • (u' - q) - (1 / β) • v := by
    rw [smul_sub, hw]
    module
  have hvi2 : ⟪(z - q) + p • (u' - q) - (1 / β) • v, u - q⟫ ≤ 0 := by
    rw [← key, inner_smul_left]
    simp only [conj_trivial]
    exact mul_nonpos_of_nonneg_of_nonpos h1p.le hvi
  rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left] at hvi2
  simp only [conj_trivial] at hvi2
  have pz := polar z u q
  have pu := polar u' u q
  have hv : ⟪v, u - q⟫ = -⟪v, q - u⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hv] at hvi2
  have e1 : ‖z - q‖ = ‖q - z‖ := norm_sub_rev _ _
  have e2 : ‖u' - q‖ = ‖q - u'‖ := norm_sub_rev _ _
  have e3 : ‖u - q‖ = ‖q - u‖ := norm_sub_rev _ _
  rw [e1, e3] at pz
  rw [e2, e3] at pu
  have hm := mul_le_mul_of_nonneg_left hvi2 hβ.le
  have e : β * (⟪z - q, u - q⟫ + p * ⟪u' - q, u - q⟫ - 1 / β * -⟪v, q - u⟫) =
      β * ⟪z - q, u - q⟫ + β * p * ⟪u' - q, u - q⟫ + ⟪v, q - u⟫ := by
    field_simp; ring
  have k1 : β * ⟪z - q, u - q⟫ = β / 2 * (‖q - z‖ ^ 2 + ‖q - u‖ ^ 2 - ‖u - z‖ ^ 2) := by
    linear_combination (β / 2) * pz
  have k2 : β * p * ⟪u' - q, u - q⟫ =
      β * p / 2 * (‖q - u'‖ ^ 2 + ‖q - u‖ ^ 2 - ‖u - u'‖ ^ 2) := by
    linear_combination (β * p / 2) * pu
  rw [e, mul_zero] at hm
  linarith

omit [CompleteSpace E] in
lemma inner_step {proj : E → E} {Q : Set E} (hQ : Convex ℝ Q) (hP : ProjectionOracle proj Q)
    {h : E → ℝ} {sub : E → E} {M : ℝ} (hS : SubgradientOracle h sub Q M)
    {β p : ℝ} (hβ : 0 < β) (hp : 0 < p) (g z u' : E) (hu' : u' ∈ Q) {u : E} (hu : u ∈ Q) :
    ⟪g, proj (innerTarget β p z u' (g + sub u')) - u⟫ +
        h (proj (innerTarget β p z u' (g + sub u'))) - h u +
        β / 2 * ‖proj (innerTarget β p z u' (g + sub u')) - z‖ ^ 2 ≤
      β / 2 * ‖u - z‖ ^ 2 + β * p / 2 * ‖u - u'‖ ^ 2 -
        β * (1 + p) / 2 * ‖proj (innerTarget β p z u' (g + sub u')) - u‖ ^ 2 +
        2 * M ^ 2 / (β * p) := by
  set q := proj (innerTarget β p z u' (g + sub u'))
  have hq : q ∈ Q := (hP _).1
  have h3 := inner_three_point hQ hP hβ hp.le z u' (g + sub u') hu
  obtain ⟨hs', hsub'⟩ := hS u' hu'
  obtain ⟨hsq, hsubq⟩ := hS q hq
  have l1 := hsub' u hu
  have l2 := hsubq u' hu'
  have hcs1 : ⟪sub q, u' - q⟫ ≥ -(M * ‖q - u'‖) := by
    have := real_inner_le_norm (sub q) (q - u')
    have e : ⟪sub q, u' - q⟫ = -⟪sub q, q - u'⟫ := by rw [← inner_neg_right, neg_sub]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hsq (norm_nonneg (q - u'))]
  have hcs2 : ⟪sub u', q - u'⟫ ≥ -(M * ‖q - u'‖) := by
    have := real_inner_le_norm (sub u') (-(q - u'))
    rw [inner_neg_right, norm_neg] at this
    nlinarith [mul_le_mul_of_nonneg_right hs' (norm_nonneg (q - u'))]
  have hi : ⟪g + sub u', q - u⟫ = ⟪g, q - u⟫ + ⟪sub u', q - u'⟫ - ⟪sub u', u - u'⟫ := by
    have e : ⟪sub u', q - u⟫ = ⟪sub u', q - u'⟫ - ⟪sub u', u - u'⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    rw [inner_add_left, e]; ring
  rw [hi] at h3
  set r := ‖q - u'‖
  have young : 2 * M * r - β * p / 2 * r ^ 2 ≤ 2 * M ^ 2 / (β * p) := by
    have hbp : 0 < β * p := by positivity
    rw [le_div_iff₀ hbp]
    nlinarith [sq_nonneg (β * p * r - 2 * M)]
  nlinarith


lemma wsum_succ (t : ℕ) : wsum (t + 1) = wsum t + (t + 2) := by
  simp only [wsum]; push_cast; ring

lemma wsum_nonneg (t : ℕ) : 0 ≤ wsum t := by
  simp only [wsum]; positivity

noncomputable def innerSeq (proj sub : ℕ → E → E) (β : ℝ) (g z : E) : ℕ → E × E
  | 0 => (z, z)
  | t + 1 =>
      let s := innerSeq proj sub β g z t
      let u := proj t (innerTarget β ((t + 1 : ℝ) / 2) z s.1 (g + sub t s.1))
      (u, (wsum t / wsum (t + 1)) • s.2 + ((t + 2 : ℝ) / wsum (t + 1)) • u)

noncomputable def innerObj (h : E → ℝ) (β : ℝ) (g z : E) (v : E) : ℝ :=
  ⟪g, v⟫ + h v + β / 2 * ‖v - z‖ ^ 2

omit [CompleteSpace E] in
lemma sub_convex_mix {h : E → ℝ} {sub : E → E} {Q : Set E} {M : ℝ} (hQ : Convex ℝ Q)
    (hS : SubgradientOracle h sub Q M) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c + d = 1) :
    h (c • x + d • y) ≤ c * h x + d * h y := by
  have hm : c • x + d • y ∈ Q := hQ hx hy hc hd hcd
  obtain ⟨_, hsm⟩ := hS _ hm
  have l1 := hsm x hx
  have l2 := hsm y hy
  have e : c • (x - (c • x + d • y)) + d • (y - (c • x + d • y)) = 0 := by
    have : c • x + d • y - (c + d) • (c • x + d • y) = 0 := by rw [hcd, one_smul, sub_self]
    rw [← this]; module
  have hz : c * ⟪sub (c • x + d • y), x - (c • x + d • y)⟫ +
      d * ⟪sub (c • x + d • y), y - (c • x + d • y)⟫ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, e, inner_zero_right]
  have k1 := mul_le_mul_of_nonneg_left l1 hc
  have k2 := mul_le_mul_of_nonneg_left l2 hd
  have hm1 : h (c • x + d • y) = c * h (c • x + d • y) + d * h (c • x + d • y) := by
    rw [← add_mul, hcd, one_mul]
  linarith

omit [CompleteSpace E] in
lemma obj_convex_mix {h : E → ℝ} {sub : E → E} {Q : Set E} {M : ℝ} (hQ : Convex ℝ Q)
    (hS : SubgradientOracle h sub Q M) {β : ℝ} (hβ : 0 ≤ β) (g z : E) {x y : E}
    (hx : x ∈ Q) (hy : y ∈ Q) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c + d = 1) :
    innerObj h β g z (c • x + d • y) ≤ c * innerObj h β g z x + d * innerObj h β g z y := by
  have hh := sub_convex_mix hQ hS hx hy hc hd hcd
  have hc' : c = 1 - d := by linarith
  have hn : ‖c • x + d • y - z‖ ^ 2 ≤ c * ‖x - z‖ ^ 2 + d * ‖y - z‖ ^ 2 := by
    have e : c • x + d • y - z = (1 - d) • (x - z) + d • (y - z) := by
      rw [← hc']
      have : c • x + d • y - (c + d) • z = c • (x - z) + d • (y - z) := by module
      rw [hcd, one_smul] at this
      exact this
    rw [e, CompositeGeneralized.norm_mix_sq, ← hc']
    nlinarith [mul_nonneg (mul_nonneg hd hc) (sq_nonneg ‖x - z - (y - z)‖)]
  have hi : ⟪g, c • x + d • y⟫ = c * ⟪g, x⟫ + d * ⟪g, y⟫ := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  simp only [innerObj]
  rw [hi]
  nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ β / 2 by positivity)]

omit [CompleteSpace E] in
lemma innerSeq_spec {proj : ℕ → E → E} {Q : Set E} (hQ : Convex ℝ Q)
    (hP : ∀ t, ProjectionOracle (proj t) Q) {h : E → ℝ} {sub : ℕ → E → E} {M : ℝ}
    (hS : ∀ t, SubgradientOracle h (sub t) Q M) {β : ℝ} (hβ : 0 < β) (g : E) {z : E} (hz : z ∈ Q)
    {u : E} (hu : u ∈ Q) (t : ℕ) :
    (innerSeq proj sub β g z t).1 ∈ Q ∧ (innerSeq proj sub β g z t).2 ∈ Q ∧
      wsum t * (innerObj h β g z (innerSeq proj sub β g z t).2 - innerObj h β g z u) +
          β / 4 * ((t + 1) * (t + 2)) * ‖(innerSeq proj sub β g z t).1 - u‖ ^ 2 ≤
        β / 2 * ‖z - u‖ ^ 2 + 8 * M ^ 2 * t / β := by
  induction t with
  | zero =>
    simp only [innerSeq, wsum, CharP.cast_eq_zero, zero_mul, zero_div, mul_zero, zero_add]
    refine ⟨hz, hz, ?_⟩
    have : 0 ≤ ‖z - u‖ ^ 2 := sq_nonneg _
    nlinarith
  | succ t ih =>
    obtain ⟨hu1, hu2, hrec⟩ := ih
    set s := innerSeq proj sub β g z t with hsdef
    have hp : (0 : ℝ) < (t + 1 : ℝ) / 2 := by positivity
    set q := proj t (innerTarget β ((t + 1 : ℝ) / 2) z s.1 (g + sub t s.1)) with hqdef
    have hq : q ∈ Q := (hP t _).1
    have hW1 : 0 < wsum (t + 1) := by
      rw [wsum_succ]; have := wsum_nonneg t; positivity
    have hc : 0 ≤ wsum t / wsum (t + 1) := div_nonneg (wsum_nonneg t) hW1.le
    have hd : 0 ≤ ((t : ℝ) + 2) / wsum (t + 1) := by positivity
    have hcd : wsum t / wsum (t + 1) + ((t : ℝ) + 2) / wsum (t + 1) = 1 := by
      rw [← add_div, ← wsum_succ, div_self hW1.ne']
    have hnext : innerSeq proj sub β g z (t + 1) =
        (q, (wsum t / wsum (t + 1)) • s.2 + (((t : ℝ) + 2) / wsum (t + 1)) • q) := by
      simp only [innerSeq, hsdef, hqdef]
    rw [hnext]
    simp only
    refine ⟨hq, hQ hu2 hq hc hd hcd, ?_⟩
    have hmix := obj_convex_mix hQ (hS 0) hβ.le g z hu2 hq hc hd hcd
    have hstep := inner_step hQ (hP t) (hS t) hβ hp g z s.1 hu1 hu
    have hmixW := mul_le_mul_of_nonneg_left hmix hW1.le
    have e1 : wsum (t + 1) * (wsum t / wsum (t + 1) * innerObj h β g z s.2 +
        ((t : ℝ) + 2) / wsum (t + 1) * innerObj h β g z q) =
        wsum t * innerObj h β g z s.2 + ((t : ℝ) + 2) * innerObj h β g z q := by
      field_simp
    rw [e1] at hmixW
    have hstep' : innerObj h β g z q - innerObj h β g z u ≤
        β * ((t + 1 : ℝ) / 2) / 2 * ‖u - s.1‖ ^ 2 -
          β * (1 + (t + 1 : ℝ) / 2) / 2 * ‖q - u‖ ^ 2 +
          2 * M ^ 2 / (β * ((t + 1 : ℝ) / 2)) := by
      simp only [innerObj]
      have := hstep
      rw [← hqdef, inner_sub_right] at this
      linarith
    have hyoung : ((t : ℝ) + 2) * (2 * M ^ 2 / (β * ((t + 1 : ℝ) / 2))) ≤ 8 * M ^ 2 / β := by
      rw [show ((t : ℝ) + 2) * (2 * M ^ 2 / (β * ((t + 1 : ℝ) / 2))) =
          (4 * M ^ 2 / β) * (((t : ℝ) + 2) / (t + 1)) by field_simp; ring]
      have hr : ((t : ℝ) + 2) / (t + 1) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have h4 : 0 ≤ 4 * M ^ 2 / β := by positivity
      have := mul_le_mul_of_nonneg_left hr h4
      linarith [this, show 4 * M ^ 2 / β * 2 = 8 * M ^ 2 / β by ring]
    have hstepW := mul_le_mul_of_nonneg_left hstep' (show (0 : ℝ) ≤ (t : ℝ) + 2 by positivity)
    rw [wsum_succ] at hmixW ⊢
    rw [norm_sub_rev u s.1] at hstepW
    push_cast
    linear_combination hmixW + hrec + hstepW + hyoung

lemma wsum_pos {T : ℕ} (hT : 1 ≤ T) : 0 < wsum T := by
  simp only [wsum]
  have : (1 : ℝ) ≤ T := by exact_mod_cast hT
  positivity

lemma inner_error_bound {T : ℕ} (hT : 1 ≤ T) :
    8 * (T : ℝ) * (wsum T + 1) / wsum T ^ 2 ≤ 24 / (T + 3) := by
  have hW := wsum_pos hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [wsum]
  nlinarith [sq_nonneg ((T : ℝ) - 1), mul_pos (by linarith : (0 : ℝ) < T) (by linarith : (0 : ℝ) < T)]

omit [CompleteSpace E] in
lemma sliding_three_point {proj : ℕ → E → E} {Q : Set E} (hQ : Convex ℝ Q)
    (hP : ∀ t, ProjectionOracle (proj t) Q) {h : E → ℝ} {sub : ℕ → E → E} {M : ℝ}
    (hS : ∀ t, SubgradientOracle h (sub t) Q M) {a : ℝ} (ha : 0 < a) {T : ℕ} (hT : 1 ≤ T)
    (g : E) {z : E} (hz : z ∈ Q) {u : E} (hu : u ∈ Q) :
    (innerSeq proj sub (wsum T / (a * (wsum T + 1))) g z T).1 ∈ Q ∧
      (innerSeq proj sub (wsum T / (a * (wsum T + 1))) g z T).2 ∈ Q ∧
      a * (⟪g, (innerSeq proj sub (wsum T / (a * (wsum T + 1))) g z T).2 - u⟫ +
          h (innerSeq proj sub (wsum T / (a * (wsum T + 1))) g z T).2 - h u) +
        1 / 3 * ‖(innerSeq proj sub (wsum T / (a * (wsum T + 1))) g z T).2 - z‖ ^ 2 +
        ‖(innerSeq proj sub (wsum T / (a * (wsum T + 1))) g z T).1 - u‖ ^ 2 / 2 ≤
      ‖z - u‖ ^ 2 / 2 + 24 * M ^ 2 * a ^ 2 / (T + 3) := by
  have hW := wsum_pos hT
  set W := wsum T with hWdef
  set β := W / (a * (W + 1)) with hβdef
  have hβ : 0 < β := by positivity
  obtain ⟨h1, h2, hspec⟩ := innerSeq_spec hQ hP hS hβ g hz hu T
  refine ⟨h1, h2, ?_⟩
  set s := innerSeq proj sub β g z T
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTT : ((T : ℝ) + 1) * (T + 2) = 2 * (W + 1) := by
    simp only [hWdef, wsum]; ring
  rw [hTT] at hspec
  simp only [innerObj] at hspec
  set X := ⟪g, s.2 - u⟫ + h s.2 - h u
  have hX : ⟪g, s.2⟫ + h s.2 + β / 2 * ‖s.2 - z‖ ^ 2 - (⟪g, u⟫ + h u + β / 2 * ‖u - z‖ ^ 2) =
      X + β / 2 * ‖s.2 - z‖ ^ 2 - β / 2 * ‖u - z‖ ^ 2 := by
    simp only [X, inner_sub_right]; ring
  rw [hX] at hspec
  have hβW : β * (W + 1) = W / a := by
    simp only [hβdef]; field_simp
  have key : W * X + β * W / 2 * ‖s.2 - z‖ ^ 2 + W / a / 2 * ‖s.1 - u‖ ^ 2 ≤
      W / a / 2 * ‖z - u‖ ^ 2 + 8 * M ^ 2 * T / β := by
    rw [norm_sub_rev u z] at hspec
    have e1 : β / 4 * (2 * (W + 1)) = W / a / 2 := by rw [← hβW]; ring
    rw [e1] at hspec
    have e2 : W / a / 2 * ‖z - u‖ ^ 2 = β / 2 * ‖z - u‖ ^ 2 + W * (β / 2 * ‖z - u‖ ^ 2) := by
      rw [← hβW]; ring
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left key (show 0 ≤ a / W by positivity)
  have e3 : a / W * (W * X + β * W / 2 * ‖s.2 - z‖ ^ 2 + W / a / 2 * ‖s.1 - u‖ ^ 2) =
      a * X + a * β / 2 * ‖s.2 - z‖ ^ 2 + ‖s.1 - u‖ ^ 2 / 2 := by
    field_simp
  have e4 : a / W * (W / a / 2 * ‖z - u‖ ^ 2 + 8 * M ^ 2 * T / β) =
      ‖z - u‖ ^ 2 / 2 + M ^ 2 * a ^ 2 * (8 * T * (W + 1) / W ^ 2) := by
    simp only [hβdef]; field_simp
  rw [e3, e4] at hmul
  have herr := inner_error_bound hT
  rw [← hWdef] at herr
  have herr2 : M ^ 2 * a ^ 2 * (8 * T * (W + 1) / W ^ 2) ≤ 24 * M ^ 2 * a ^ 2 / (T + 3) := by
    have := mul_le_mul_of_nonneg_left herr (show 0 ≤ M ^ 2 * a ^ 2 by positivity)
    calc _ ≤ M ^ 2 * a ^ 2 * (24 / ((T : ℝ) + 3)) := this
      _ = 24 * M ^ 2 * a ^ 2 / (T + 3) := by ring
  have hcoef : 1 / 3 ≤ a * β / 2 := by
    have : a * β = W / (W + 1) := by simp only [hβdef]; field_simp
    rw [this]
    have hW2 : 2 ≤ W := by simp only [hWdef, wsum]; nlinarith
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
    linarith
  nlinarith [sq_nonneg ‖s.2 - z‖]

end OracleTemplate.GeneralizedSliding
