import LongTails.Proofs.ChiSquarePerspective
import LongTails.Proofs.ChiSquareDuality

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ChiSquareDro

structure Cfg where
  c : ℝ
  gx : ℝ
  ge : ℝ
  gs : ℝ
  elo : ℝ
  ehi : ℝ
  slo : ℝ
  shi : ℝ

noncomputable def clampTo (a b t : ℝ) : ℝ := max a (min b t)

lemma clampTo_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clampTo a b t ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma clampTo_dist {a b v : ℝ} (hv : v ∈ Icc a b) (t : ℝ) :
    (clampTo a b t - v) ^ 2 ≤ (t - v) ^ 2 := by
  unfold clampTo
  rcases le_total t b with h | h
  · rw [min_eq_right h]
    rcases le_total a t with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h']
      nlinarith [hv.1, hv.2]
  · rw [min_eq_left h, max_eq_right (le_trans hv.1 hv.2)]
    nlinarith [hv.1, hv.2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ξ : Type*}

lemma proj_dist {D : Set E} {proj : E → E}
    (hvi : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) (y : E) {u : E} (hu : u ∈ D) :
    ‖proj y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  have h := hvi y u hu
  have e : y - u = (y - proj y) + (proj y - u) := by abel
  rw [e, norm_add_sq_real]
  have : ⟪y - proj y, proj y - u⟫ = -⟪y - proj y, u - proj y⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [this]
  nlinarith [sq_nonneg ‖y - proj y‖]

lemma proj_fix {D : Set E} {proj : E → E}
    (hvi : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) {x : E} (hx : x ∈ D) : proj x = x := by
  have h := hvi x x hx
  rw [real_inner_self_eq_norm_sq] at h
  have : ‖x - proj x‖ = 0 := by nlinarith [norm_nonneg (x - proj x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

noncomputable def tailAt (loss : E → Ξ → ℝ) (x : E) (η : ℝ) (ω : Ξ) : ℝ := tail (loss x) η ω

noncomputable def gradX (k : Cfg) (loss : E → Ξ → ℝ) (sub : E → Ξ → E) (x : E) (η s : ℝ)
    (ω : Ξ) : E := (k.c * tailAt loss x η ω / s) • sub x ω

noncomputable def gradE (k : Cfg) (loss : E → Ξ → ℝ) (x : E) (η s : ℝ) (ω : Ξ) : ℝ :=
  1 - k.c * tailAt loss x η ω / s

noncomputable def gradS (k : Cfg) (loss : E → Ξ → ℝ) (x : E) (η s : ℝ) (ω : Ξ) : ℝ :=
  k.c / 2 - k.c * tailAt loss x η ω ^ 2 / (2 * s ^ 2)

noncomputable def stepState (k : Cfg) (proj : E → E) (loss : E → Ξ → ℝ) (sub : E → Ξ → E)
    (z : E × ℝ × ℝ) (ω : Ξ) : E × ℝ × ℝ :=
  (proj z.1 - k.gx • gradX k loss sub (proj z.1) z.2.1 z.2.2 ω,
   clampTo k.elo k.ehi (z.2.1 - k.ge * gradE k loss (proj z.1) z.2.1 z.2.2 ω),
   clampTo k.slo k.shi (z.2.2 - k.gs * gradS k loss (proj z.1) z.2.1 z.2.2 ω))

noncomputable def potential (k : Cfg) (proj : E → E) (xs : E) (es ss : ℝ) (z : E × ℝ × ℝ) : ℝ :=
  ‖proj z.1 - xs‖ ^ 2 / k.gx + (z.2.1 - es) ^ 2 / k.ge + (z.2.2 - ss) ^ 2 / k.gs

noncomputable def phiAt (k : Cfg) (loss : E → Ξ → ℝ) (x : E) (η s : ℝ) (ω : Ξ) : ℝ :=
  phi k.c (tailAt loss x η ω) η s

noncomputable def noiseAt (k : Cfg) (loss : E → Ξ → ℝ) (sub : E → Ξ → E) (x : E) (η s : ℝ)
    (ω : Ξ) : ℝ :=
  k.gx * ‖gradX k loss sub x η s ω‖ ^ 2 + k.ge * gradE k loss x η s ω ^ 2 +
    k.gs * gradS k loss x η s ω ^ 2

lemma one_step {k : Cfg} (hc : 0 ≤ k.c) (hgx : 0 < k.gx) (hge : 0 < k.ge) (hgs : 0 < k.gs)
    (hslo : 0 < k.slo) {D : Set E} {proj : E → E} (hin : ∀ y, proj y ∈ D)
    (hvi : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0)
    {loss : E → Ξ → ℝ} {sub : E → Ξ → E}
    (hsub : ∀ ω, ∀ x ∈ D, ∀ y ∈ D, loss x ω + ⟪sub x ω, y - x⟫ ≤ loss y ω)
    {xs : E} (hxs : xs ∈ D) {es ss : ℝ} (hes : es ∈ Icc k.elo k.ehi) (hss : ss ∈ Icc k.slo k.shi)
    {z : E × ℝ × ℝ} (hs : z.2.2 ∈ Icc k.slo k.shi) (ω : Ξ) :
    potential k proj xs es ss (stepState k proj loss sub z ω) ≤
      potential k proj xs es ss z -
        2 * (phiAt k loss (proj z.1) z.2.1 z.2.2 ω - phiAt k loss xs es ss ω) +
        noiseAt k loss sub (proj z.1) z.2.1 z.2.2 ω := by
  set x := proj z.1
  set η := z.2.1
  set s := z.2.2
  have hs0 : 0 < s := lt_of_lt_of_le hslo hs.1
  have hss0 : 0 < ss := lt_of_lt_of_le hslo hss.1
  have hx : x ∈ D := hin _
  set gX := gradX k loss sub x η s ω
  set gE := gradE k loss x η s ω
  set gS := gradS k loss x η s ω
  have hx' : ‖proj (x - k.gx • gX) - xs‖ ^ 2 ≤
      ‖x - xs‖ ^ 2 - 2 * k.gx * ⟪gX, x - xs⟫ + k.gx ^ 2 * ‖gX‖ ^ 2 := by
    have h1 := proj_dist hvi (x - k.gx • gX) hxs
    have e2 : ‖x - k.gx • gX - xs‖ ^ 2 =
        ‖x - xs‖ ^ 2 - 2 * k.gx * ⟪gX, x - xs⟫ + k.gx ^ 2 * ‖gX‖ ^ 2 := by
      rw [show x - k.gx • gX - xs = (x - xs) - k.gx • gX by abel, norm_sub_sq_real,
        inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
      ring
    linarith
  have he' := clampTo_dist hes (η - k.ge * gE)
  have hs' := clampTo_dist hss (s - k.gs * gS)
  set u := tailAt loss x η ω with hu
  set u' := tailAt loss xs es ω with hu'
  have hsample : phi k.c u η s + k.c * u / s * ⟪sub x ω, xs - x⟫ + (1 - k.c * u / s) * (es - η) +
      (k.c / 2 - k.c * u ^ 2 / (2 * s ^ 2)) * (ss - s) ≤ phi k.c u' es ss :=
    sample_ineq (g := sub x ω) (dx := xs - x) (l := loss x ω) (l' := loss xs ω)
      (η := η) (η' := es) (s := s) (s' := ss) hc hs0 hss0 (hsub ω x hx xs hxs)
  unfold potential phiAt noiseAt
  change ‖proj (x - k.gx • gX) - xs‖ ^ 2 / k.gx +
      (clampTo k.elo k.ehi (η - k.ge * gE) - es) ^ 2 / k.ge +
      (clampTo k.slo k.shi (s - k.gs * gS) - ss) ^ 2 / k.gs ≤
    ‖x - xs‖ ^ 2 / k.gx + (η - es) ^ 2 / k.ge + (s - ss) ^ 2 / k.gs -
      2 * (phi k.c u η s - phi k.c u' es ss) +
      (k.gx * ‖gX‖ ^ 2 + k.ge * gE ^ 2 + k.gs * gS ^ 2)
  have hinner : ⟪gX, x - xs⟫ = -(k.c * u / s * ⟪sub x ω, xs - x⟫) := by
    simp only [gX, gradX, inner_smul_left, RCLike.conj_to_real]
    rw [show x - xs = -(xs - x) by abel, inner_neg_right]
    ring
  have t1 : ‖proj (x - k.gx • gX) - xs‖ ^ 2 / k.gx ≤
      ‖x - xs‖ ^ 2 / k.gx - 2 * ⟪gX, x - xs⟫ + k.gx * ‖gX‖ ^ 2 := by
    have := div_le_div_of_nonneg_right hx' hgx.le
    have e : (‖x - xs‖ ^ 2 - 2 * k.gx * ⟪gX, x - xs⟫ + k.gx ^ 2 * ‖gX‖ ^ 2) / k.gx =
        ‖x - xs‖ ^ 2 / k.gx - 2 * ⟪gX, x - xs⟫ + k.gx * ‖gX‖ ^ 2 := by
      field_simp
    linarith
  have t2 : (clampTo k.elo k.ehi (η - k.ge * gE) - es) ^ 2 / k.ge ≤
      (η - es) ^ 2 / k.ge - 2 * gE * (η - es) + k.ge * gE ^ 2 := by
    have := div_le_div_of_nonneg_right he' hge.le
    have e : (η - k.ge * gE - es) ^ 2 / k.ge = (η - es) ^ 2 / k.ge - 2 * gE * (η - es) +
        k.ge * gE ^ 2 := by field_simp; ring
    linarith
  have t3 : (clampTo k.slo k.shi (s - k.gs * gS) - ss) ^ 2 / k.gs ≤
      (s - ss) ^ 2 / k.gs - 2 * gS * (s - ss) + k.gs * gS ^ 2 := by
    have := div_le_div_of_nonneg_right hs' hgs.le
    have e : (s - k.gs * gS - ss) ^ 2 / k.gs = (s - ss) ^ 2 / k.gs - 2 * gS * (s - ss) +
        k.gs * gS ^ 2 := by field_simp; ring
    linarith
  have key : 2 * (k.c * u / s * ⟪sub x ω, xs - x⟫) - 2 * gE * (η - es) - 2 * gS * (s - ss) ≤
      -2 * (phi k.c u η s - phi k.c u' es ss) := by
    have hgE : gE = 1 - k.c * u / s := rfl
    have hgS : gS = k.c / 2 - k.c * u ^ 2 / (2 * s ^ 2) := rfl
    rw [hgE, hgS]
    linear_combination 2 * hsample
  rw [hinner] at t1
  linarith

end OracleTemplate.ChiSquareDro
