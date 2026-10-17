import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Metric Filter Topology
open InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.PLHessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {L μ ρ : ℝ}

lemma grad_zero_of_min (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) : gradient f u = 0 := by
  have hd := Gradient.descent hL hg hlip u
  have hh : f u ≤ f (u - (1 / L) • gradient f u) := hm (mem_univ _)
  have hsq : ‖gradient f u‖ ^ 2 / (2 * L) ≤ 0 := by linarith
  have hz := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hsq
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient f u)])

lemma grad_sq_le (hL : 0 < L) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) (x : E) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - f u) := by
  have hd := Gradient.descent hL hg hlip x
  have hl : f u ≤ f (x - (1 / L) • gradient f x) := hm (mem_univ _)
  have h2 : ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - f u := by linarith
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

noncomputable def gdSeq (f : E → ℝ) (L : ℝ) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => gdSeq f L x n - (1 / L) • gradient f (gdSeq f L x n)

lemma gd_step_len (hL : 0 < L) (hμ : 0 < μ) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2)
    (y : E) :
    Real.sqrt μ * ‖(1 / L) • gradient f y‖ ≤
      4 * (Real.sqrt (f y - f u) - Real.sqrt (f (y - (1 / L) • gradient f y) - f u)) := by
  set G := ‖gradient f y‖
  set y' := y - (1 / L) • gradient f y
  have hd : f y' ≤ f y - G ^ 2 / (2 * L) := Gradient.descent hL hg hlip y
  have h0 : 0 ≤ f y' - f u := sub_nonneg.mpr (hm (mem_univ _))
  have h1 : 0 ≤ f y - f u := sub_nonneg.mpr (hm (mem_univ _))
  set s := Real.sqrt (f y - f u)
  set s' := Real.sqrt (f y' - f u)
  have hs2 : s ^ 2 = f y - f u := Real.sq_sqrt h1
  have hs'2 : s' ^ 2 = f y' - f u := Real.sq_sqrt h0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs'0 : 0 ≤ s' := Real.sqrt_nonneg _
  have hm2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hm0 : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hlen : ‖(1 / L) • gradient f y‖ = G / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
  rw [hlen]
  have hG0 : 0 ≤ G := norm_nonneg _
  have hpl' : 2 * μ * s ^ 2 ≤ G ^ 2 := by rw [hs2]; exact hpl y
  have hsG : Real.sqrt μ * s * Real.sqrt 2 ≤ G := by
    have h : (Real.sqrt μ * s * Real.sqrt 2) ^ 2 ≤ G ^ 2 := by
      rw [mul_pow, mul_pow, hm2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; nlinarith
    have hp : 0 ≤ Real.sqrt μ * s * Real.sqrt 2 := by positivity
    nlinarith [sq_nonneg (Real.sqrt μ * s * Real.sqrt 2 - G),
      sq_nonneg (Real.sqrt μ * s * Real.sqrt 2 + G)]
  have hdiff : s' ^ 2 ≤ s ^ 2 - G ^ 2 / (2 * L) := by rw [hs2, hs'2]; linarith
  have hss : s' ≤ s := by nlinarith [div_nonneg (sq_nonneg G) (by positivity : (0 : ℝ) ≤ 2 * L)]
  have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  rw [div_eq_mul_inv, ← mul_assoc, mul_comm (Real.sqrt μ) G]
  have key : G ^ 2 / (2 * L) ≤ (s - s') * (2 * s) := by nlinarith
  by_cases hG : G = 0
  · rw [hG]; nlinarith
  have hGp : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hG)
  have hk2 : G ^ 2 ≤ 2 * L * ((s - s') * (2 * s)) := by
    rw [div_le_iff₀ (by positivity)] at key; linarith
  have hds : 0 ≤ s - s' := by linarith
  have hc : 0 ≤ Real.sqrt μ * Real.sqrt 2 := by positivity
  have hA : G ^ 2 * (Real.sqrt μ * Real.sqrt 2) ≤ 4 * L * (s - s') * G := by
    calc G ^ 2 * (Real.sqrt μ * Real.sqrt 2)
        ≤ 4 * L * (s - s') * s * (Real.sqrt μ * Real.sqrt 2) := by
          apply mul_le_mul_of_nonneg_right _ hc; nlinarith
      _ = 4 * L * (s - s') * (Real.sqrt μ * s * Real.sqrt 2) := by ring
      _ ≤ 4 * L * (s - s') * G := by
          apply mul_le_mul_of_nonneg_left hsG; positivity
  have hB : G * (Real.sqrt μ * Real.sqrt 2) ≤ 4 * L * (s - s') := by
    have : G * (G * (Real.sqrt μ * Real.sqrt 2)) ≤ G * (4 * L * (s - s')) := by nlinarith
    exact le_of_mul_le_mul_left this hGp
  have hk4 : G * Real.sqrt μ ≤ 4 * L * (s - s') := by
    nlinarith [mul_nonneg hG0 hm0.le]
  rw [show G * Real.sqrt μ * L⁻¹ = (G * Real.sqrt μ) / L by ring, div_le_iff₀ hL]
  linarith

lemma gd_path (hL : 0 < L) (hμ : 0 < μ) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2)
    (x : E) : ∀ n, Real.sqrt μ * ‖gdSeq f L x n - x‖ ≤
      4 * (Real.sqrt (f x - f u) - Real.sqrt (f (gdSeq f L x n) - f u))
  | 0 => by simp [gdSeq]
  | n + 1 => by
      have ih := gd_path hL hμ hg hlip hm hpl x n
      have hs := gd_step_len hL hμ hg hlip hm hpl (gdSeq f L x n)
      have htri : ‖gdSeq f L x (n + 1) - x‖ ≤
          ‖gdSeq f L x n - x‖ + ‖(1 / L) • gradient f (gdSeq f L x n)‖ := by
        have : gdSeq f L x (n + 1) - x =
            (gdSeq f L x n - x) - (1 / L) • gradient f (gdSeq f L x n) := by
          simp only [gdSeq]; abel
        rw [this]; exact norm_sub_le _ _
      have hm0 : 0 ≤ Real.sqrt μ := Real.sqrt_nonneg _
      have := mul_le_mul_of_nonneg_left htri hm0
      simp only [gdSeq] at this ⊢
      linarith

lemma gd_gap (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2)
    (x : E) : ∀ n, f (gdSeq f L x n) - f u ≤ (1 - μ / L) ^ n * (f x - f u)
  | 0 => by simp [gdSeq]
  | n + 1 => by
      have ih := gd_gap hL hμ hμL hg hlip hm hpl x n
      have hd := Gradient.descent hL hg hlip (gdSeq f L x n)
      have hp := hpl (gdSeq f L x n)
      have hr : 0 ≤ 1 - μ / L := by rw [sub_nonneg, div_le_one hL]; exact hμL
      simp only [gdSeq]
      have h1 : ‖gradient f (gdSeq f L x n)‖ ^ 2 / (2 * L) ≥
          μ / L * (f (gdSeq f L x n) - f u) := by
        rw [ge_iff_le, le_div_iff₀ (by positivity)]
        have : μ / L * (f (gdSeq f L x n) - f u) * (2 * L) =
            2 * μ * (f (gdSeq f L x n) - f u) := by field_simp
        linarith
      calc f (gdSeq f L x n - (1 / L) • gradient f (gdSeq f L x n)) - f u
          ≤ (1 - μ / L) * (f (gdSeq f L x n) - f u) := by nlinarith
        _ ≤ (1 - μ / L) * ((1 - μ / L) ^ n * (f x - f u)) := mul_le_mul_of_nonneg_left ih hr
        _ = (1 - μ / L) ^ (n + 1) * (f x - f u) := by ring

lemma quad_growth [FiniteDimensional ℝ E] (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f univ u) (hpl : ∀ x, 2 * μ * (f x - f u) ≤ ‖gradient f x‖ ^ 2)
    (x : E) : ∃ p, IsMinOn f univ p ∧ μ * ‖x - p‖ ^ 2 ≤ 16 * (f x - f u) := by
  set R := 4 * Real.sqrt (f x - f u) / Real.sqrt μ
  have hm0 : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hball : ∀ n, gdSeq f L x n ∈ closedBall x R := by
    intro n
    rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hm0]
    have h := gd_path hL hμ hg hlip hm hpl x n
    have : 0 ≤ Real.sqrt (f (gdSeq f L x n) - f u) := Real.sqrt_nonneg _
    nlinarith
  obtain ⟨p, hp, φ, hφ, hlim⟩ := (isCompact_closedBall x R).tendsto_subseq hball
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt
  have hr0 : 0 ≤ 1 - μ / L := by rw [sub_nonneg, div_le_one hL]; exact hμL
  have hμL0 : 0 < μ / L := by positivity
  have hr1 : 1 - μ / L < 1 := by linarith
  have hgap0 : Tendsto (fun n => f (gdSeq f L x n)) atTop (𝓝 (f u)) := by
    have hupper : Tendsto (fun n => f u + (1 - μ / L) ^ n * (f x - f u)) atTop (𝓝 (f u)) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (f x - f u)
      simpa using this.const_add (f u)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => hm (mem_univ _)) (fun n => ?_)
    have := gd_gap hL hμ hμL hg hlip hm hpl x n
    simp only; linarith
  have h1 : Tendsto (fun n => f (gdSeq f L x (φ n))) atTop (𝓝 (f p)) :=
    (hcont.tendsto p).comp hlim
  have h2 : Tendsto (fun n => f (gdSeq f L x (φ n))) atTop (𝓝 (f u)) :=
    hgap0.comp hφ.tendsto_atTop
  have hfp : f p = f u := tendsto_nhds_unique h1 h2
  refine ⟨p, fun z _ => by rw [hfp]; exact hm (mem_univ z), ?_⟩
  rw [mem_closedBall, dist_comm, dist_eq_norm] at hp
  have hR : Real.sqrt μ * ‖x - p‖ ≤ 4 * Real.sqrt (f x - f u) := by
    rw [le_div_iff₀ hm0] at hp; linarith
  have h0 : 0 ≤ f x - f u := sub_nonneg.mpr (hm (mem_univ _))
  have hsq : (Real.sqrt μ * ‖x - p‖) ^ 2 ≤ (4 * Real.sqrt (f x - f u)) ^ 2 := by
    have : 0 ≤ Real.sqrt μ * ‖x - p‖ := by positivity
    nlinarith
  rw [mul_pow, mul_pow, Real.sq_sqrt hμ.le, Real.sq_sqrt h0] at hsq
  linarith

lemma aiming (hρ : 0 ≤ ρ) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hdiff : Differentiable ℝ (gradient f))
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    {p : E} (hp0 : gradient f p = 0) (x : E) :
    2 * (f x - f p) - 3 * ρ * ‖x - p‖ ^ 3 ≤ ⟪gradient f x, x - p⟫ := by
  set d := x - p
  set H := fderiv ℝ (gradient f)
  let θ : ℝ → ℝ := fun t => ⟪gradient f (p + t • d), d⟫
  let θ' : ℝ → ℝ := fun t => ⟪H (p + t • d) d, d⟫
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => p + t • d) d t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const d).const_add p
  have hθ : ∀ t, HasDerivAt θ (θ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => gradient f (p + t • d)) (H (p + t • d) d) t :=
      (hdiff _).hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 := HasDerivAt.inner ℝ h1 (hasDerivAt_const t d)
    simpa [θ, θ'] using h2
  have hθ'b : ∀ t ∈ Icc (0 : ℝ) 1, |θ' t - θ' 0| ≤ ρ * ‖d‖ ^ 3 := by
    intro t ht
    have e : θ' t - θ' 0 = ⟪(H (p + t • d) - H p) d, d⟫ := by
      simp [θ', inner_sub_left]
    rw [e]
    have h1 := abs_real_inner_le_norm ((H (p + t • d) - H p) d) d
    have h2 := (H (p + t • d) - H p).le_opNorm d
    have h3 : ‖H (p + t • d) - H p‖ ≤ ρ * ‖d‖ := by
      have := hH (p + t • d) p
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
      have : ρ * (t * ‖d‖) ≤ ρ * ‖d‖ := by
        apply mul_le_mul_of_nonneg_left _ hρ; nlinarith [norm_nonneg d, ht.2]
      linarith
    have hd0 := norm_nonneg d
    calc |⟪(H (p + t • d) - H p) d, d⟫| ≤ ‖(H (p + t • d) - H p) d‖ * ‖d‖ := h1
      _ ≤ (‖H (p + t • d) - H p‖ * ‖d‖) * ‖d‖ := mul_le_mul_of_nonneg_right h2 hd0
      _ ≤ (ρ * ‖d‖ * ‖d‖) * ‖d‖ := by gcongr
      _ = ρ * ‖d‖ ^ 3 := by ring
  let φ : ℝ → ℝ := fun t => θ t - t * θ' 0
  have hφ : ∀ t, HasDerivAt φ (θ' t - θ' 0) t := by
    intro t
    have := (hθ t).sub ((hasDerivAt_id t).mul_const (θ' 0))
    simp only [id_eq, one_mul] at this
    exact this
  have hφ0 : φ 0 = 0 := by
    show ⟪gradient f (p + (0 : ℝ) • d), d⟫ - 0 * θ' 0 = 0
    simp [hp0]
  have hφb : ∀ t ∈ Icc (0 : ℝ) 1, |φ t| ≤ ρ * ‖d‖ ^ 3 * t := by
    intro t ht
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := φ) (f' := fun t => θ' t - θ' 0) (C := ρ * ‖d‖ ^ 3)
      (fun t _ => (hφ t).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hθ'b t ⟨ht.1, ht.2.le⟩) t ht
    rw [hφ0, sub_zero, Real.norm_eq_abs, sub_zero] at h
    exact h
  let k : ℝ → ℝ := fun t => f (p + t • d) - t ^ 2 / 2 * θ' 0
  have hk : ∀ t, HasDerivAt k (φ t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f (p + t • d)) (θ t) t := by
      have h := (hg (p + t • d)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const d |>.const_add p)
      simp only [id_eq, one_smul, toDual_apply_apply] at h
      exact h
    have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * θ' 0) (t * θ' 0) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).mul_const (θ' 0)
      convert this using 1
      push_cast; ring
    exact h1.sub h3
  have hkb := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := k) (f' := φ) (C := ρ * ‖d‖ ^ 3)
    (fun t _ => (hk t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      have := hφb t ⟨ht.1, ht.2.le⟩
      have : ρ * ‖d‖ ^ 3 * t ≤ ρ * ‖d‖ ^ 3 := by
        have : 0 ≤ ρ * ‖d‖ ^ 3 := by positivity
        nlinarith [ht.2]
      linarith) 1 ⟨zero_le_one, le_rfl⟩
  have hp1 : p + (1 : ℝ) • d = x := by simp [d]
  have hk1 : k 1 - k 0 = f x - f p - θ' 0 / 2 := by
    simp only [k, hp1, zero_smul, add_zero]; ring
  rw [hk1, Real.norm_eq_abs] at hkb
  have hφ1 := hφb 1 ⟨zero_le_one, le_rfl⟩
  have hθ1 : θ 1 = ⟪gradient f x, d⟫ := by simp only [θ, hp1]
  simp only [φ, hθ1, one_mul, mul_one] at hφ1
  have := (abs_le.mp hkb).2
  have := (abs_le.mp hφ1).1
  linarith

end OracleTemplate.PLHessian
