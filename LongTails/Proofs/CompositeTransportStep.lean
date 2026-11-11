import LongTails.Proofs.ProximalLinearDecayStep

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeTransport

open OracleTemplate.SampledComposite OracleTemplate.Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma mapping_antitone {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {x g p q : E}
    (hp : p ∈ Q) (hpm : IsMinOn (proxObj ψ a x g) Q p)
    (hq : q ∈ Q) (hqm : IsMinOn (proxObj ψ b x g) Q q) :
    ‖(1 / b) • (x - q)‖ ≤ ‖(1 / a) • (x - p)‖ := by
  have hb : 0 < b := ha.trans_le hab
  have h1 := prox_three_point hQ hψ ha hp hpm hq
  have h2 := prox_three_point hQ hψ hb hq hqm hp
  have gen : ∀ u w : E, ‖w‖ ^ 2 - ‖u - w‖ ^ 2 - ‖u‖ ^ 2 = 2 * ⟪u, w - u⟫ := by
    intro u w
    rw [norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
    ring
  have e1 : ‖q - x‖ ^ 2 - ‖q - p‖ ^ 2 - ‖p - x‖ ^ 2 = 2 * ⟪x - p, (x - q) - (x - p)⟫ := by
    rw [norm_sub_rev q x, norm_sub_rev p x, show q - p = (x - p) - (x - q) by abel]
    exact gen _ _
  have e2 : ‖p - x‖ ^ 2 - ‖p - q‖ ^ 2 - ‖q - x‖ ^ 2 = 2 * ⟪x - q, (x - p) - (x - q)⟫ := by
    rw [norm_sub_rev q x, norm_sub_rev p x, show p - q = (x - q) - (x - p) by abel]
    exact gen _ _
  set d₁ := x - p
  set d₂ := x - q
  rw [e1] at h1
  rw [e2] at h2
  have hg : ⟪g, p - q⟫ + ⟪g, q - p⟫ = 0 := by
    rw [← inner_add_right]; simp
  have hsum : 0 ≤ ⟪d₁, d₂ - d₁⟫ / a + ⟪d₂, d₁ - d₂⟫ / b := by
    have : 2 * ⟪d₁, d₂ - d₁⟫ / (2 * a) = ⟪d₁, d₂ - d₁⟫ / a := by field_simp
    have : 2 * ⟪d₂, d₁ - d₂⟫ / (2 * b) = ⟪d₂, d₁ - d₂⟫ / b := by field_simp
    linarith
  set X := ‖(1 / a) • d₁‖
  set Y := ‖(1 / b) • d₂‖
  have hX : ‖d₁‖ = a * X := by
    simp only [X, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ha)]; field_simp
  have hY : ‖d₂‖ = b * Y := by
    simp only [Y, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hb)]; field_simp
  have hcs : ⟪d₁, d₂⟫ ≤ ‖d₁‖ * ‖d₂‖ := real_inner_le_norm _ _
  have hkey : a * X ^ 2 + b * Y ^ 2 ≤ (a + b) * (X * Y) := by
    have i1 : ⟪d₁, d₂ - d₁⟫ = ⟪d₁, d₂⟫ - ‖d₁‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have i2 : ⟪d₂, d₁ - d₂⟫ = ⟪d₁, d₂⟫ - ‖d₂‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
    rw [i1, i2] at hsum
    have hmul : 0 ≤ a * b * ((⟪d₁, d₂⟫ - ‖d₁‖ ^ 2) / a + (⟪d₁, d₂⟫ - ‖d₂‖ ^ 2) / b) :=
      mul_nonneg (mul_nonneg ha.le hb.le) hsum
    have e : a * b * ((⟪d₁, d₂⟫ - ‖d₁‖ ^ 2) / a + (⟪d₁, d₂⟫ - ‖d₂‖ ^ 2) / b) =
        (a + b) * ⟪d₁, d₂⟫ - b * ‖d₁‖ ^ 2 - a * ‖d₂‖ ^ 2 := by
      field_simp; ring
    rw [e, hX, hY] at hmul
    have hcs' : ⟪d₁, d₂⟫ ≤ a * X * (b * Y) := by rw [← hX, ← hY]; exact hcs
    have hab0 : 0 < a + b := by linarith
    have : (a + b) * ⟪d₁, d₂⟫ ≤ (a + b) * (a * X * (b * Y)) := mul_le_mul_of_nonneg_left hcs' hab0.le
    have hfac : a * b * (a * X ^ 2 + b * Y ^ 2) ≤ a * b * ((a + b) * (X * Y)) := by nlinarith
    exact le_of_mul_le_mul_left hfac (mul_pos ha hb)
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  by_contra hlt
  push Not at hlt
  have h3 : 0 < (b * Y - a * X) * (Y - X) := by
    apply mul_pos _ (by linarith)
    nlinarith
  nlinarith

section Smooth

variable [CompleteSpace E]

lemma composite_descent {f : E → ℝ} {grad : E → E} {ψ : E → ℝ} {Q : Set E} {L γ lam : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) (hγ : 0 < γ) (hγL : γ * L ≤ 1)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {x m p : E} (hx : x ∈ Q) (hp : p ∈ Q)
    (hpm : IsMinOn (proxObj ψ γ x m) Q p) :
    f (x + lam • (p - x)) + ψ (x + lam • (p - x)) ≤ f x + ψ x - lam / (2 * γ) * ‖p - x‖ ^ 2 +
      lam * (‖grad x - m‖ * ‖p - x‖) := by
  have h3 := prox_three_point hQ hψ hγ hp hpm hx
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub] at h3
  have hpx : ‖x - p‖ = ‖p - x‖ := norm_sub_rev _ _
  rw [hpx] at h3
  have hψc : ψ (x + lam • (p - x)) ≤ (1 - lam) * ψ x + lam * ψ p := by
    have e : x + lam • (p - x) = (1 - lam) • x + lam • p := by module
    rw [e]
    have := hψ.2 hx hp (by linarith : (0 : ℝ) ≤ 1 - lam) hl0 (by ring)
    simpa using this
  have hfu := smooth_upper_bound hf hlip x (x + lam • (p - x))
  have hd : x + lam • (p - x) - x = lam • (p - x) := by abel
  rw [hd, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0] at hfu
  have hinner : ⟪grad x, p - x⟫ = ⟪grad x - m, p - x⟫ + ⟪m, p - x⟫ := by
    rw [inner_sub_left]; ring
  have hcs : ⟪grad x - m, p - x⟫ ≤ ‖grad x - m‖ * ‖p - x‖ := real_inner_le_norm _ _
  have hmv : ⟪m, p - x⟫ = -⟪m, x - p⟫ := by rw [← inner_neg_right, neg_sub]
  have h3' : ψ p + ⟪m, p - x⟫ ≤ ψ x - ‖p - x‖ ^ 2 / γ := by
    have e : (-‖p - x‖ ^ 2 - ‖p - x‖ ^ 2) / (2 * γ) = -(‖p - x‖ ^ 2 / γ) := by field_simp; ring
    have : ⟪m, p - x⟫ = -⟪m, x - p⟫ := hmv
    linarith [h3, e]
  have hquad : L / 2 * (lam * ‖p - x‖) ^ 2 ≤ lam / (2 * γ) * ‖p - x‖ ^ 2 := by
    have hlam2 : lam ^ 2 ≤ lam := by nlinarith
    have hLγ : L ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
    have : L / 2 * (lam * ‖p - x‖) ^ 2 = (L * lam ^ 2) / 2 * ‖p - x‖ ^ 2 := by ring
    rw [this]
    have h1 : L * lam ^ 2 ≤ (1 / γ) * lam := mul_le_mul hLγ hlam2 (sq_nonneg _) (by positivity)
    have e2 : lam / (2 * γ) = (1 / γ) * lam / 2 := by field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hlin : lam * ⟪grad x - m, p - x⟫ ≤ lam * (‖grad x - m‖ * ‖p - x‖) :=
    mul_le_mul_of_nonneg_left hcs hl0
  have e3 : lam / (2 * γ) * ‖p - x‖ ^ 2 = lam * (‖p - x‖ ^ 2 / γ) - lam / (2 * γ) * ‖p - x‖ ^ 2 := by
    field_simp; ring
  nlinarith [hψc, hfu, h3', hquad, hlin, hinner]

lemma capped_progress {f : E → ℝ} {grad : E → E} {ψ : E → ℝ} {Q : Set E} {L γ ε : ℝ}
    (hf : ∀ x, HasGradientAt f (grad x) x) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) (hγ : 0 < γ) (hγL : γ * L ≤ 1) (hε : 0 < ε)
    {x m p : E} (hx : x ∈ Q) (hp : p ∈ Q) (hpm : IsMinOn (proxObj ψ γ x m) Q p) :
    let lam := min 1 (2 * γ * ε / ‖p - x‖)
    ε * ‖p - x‖ ≤ f x + ψ x - (f (x + lam • (p - x)) + ψ (x + lam • (p - x))) +
      γ * (9 * ‖grad x - m‖ ^ 2 + 9 / 8 * ε ^ 2) := by
  intro lam
  set s := ‖p - x‖ with hs
  set e := ‖grad x - m‖ with he
  have hs0 : 0 ≤ s := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  have hl0 : 0 ≤ lam := le_min zero_le_one (by positivity)
  have hl1 : lam ≤ 1 := min_le_left _ _
  have hd := composite_descent hf hlip hQ hψ hγ hγL hl0 hl1 hx hp hpm
  rw [← hs, ← he] at hd
  by_cases hsD : s ≤ 2 * γ * ε
  · have hlam : lam * s = s := by
      rcases hs0.eq_or_lt with h0 | hpos
      · rw [← h0]; ring
      · have : 1 ≤ 2 * γ * ε / s := by rw [le_div_iff₀ hpos]; linarith
        have : lam = 1 := min_eq_left this
        rw [this, one_mul]
    have hdesc : f x + ψ x - (f (x + lam • (p - x)) + ψ (x + lam • (p - x))) ≥
        s ^ 2 / (2 * γ) - e * s := by
      have e1 : lam / (2 * γ) * s ^ 2 = (lam * s) * s / (2 * γ) := by ring
      have e2 : lam * (e * s) = (lam * s) * e := by ring
      rw [e1, e2, hlam] at hd
      have e3 : s * s / (2 * γ) = s ^ 2 / (2 * γ) := by ring
      linarith
    have am1 : ε * s ≤ s ^ 2 / (4 * γ) + γ * ε ^ 2 := by
      have : 0 ≤ (s / (2 * γ) - ε) ^ 2 * γ := mul_nonneg (sq_nonneg _) hγ.le
      have e1 : (s / (2 * γ) - ε) ^ 2 * γ = s ^ 2 / (4 * γ) + γ * ε ^ 2 - ε * s := by
        field_simp; ring
      linarith
    have am2 : e * s ≤ s ^ 2 / (4 * γ) + γ * e ^ 2 := by
      have : 0 ≤ (s / (2 * γ) - e) ^ 2 * γ := mul_nonneg (sq_nonneg _) hγ.le
      have e1 : (s / (2 * γ) - e) ^ 2 * γ = s ^ 2 / (4 * γ) + γ * e ^ 2 - e * s := by
        field_simp; ring
      linarith
    have e4 : s ^ 2 / (2 * γ) = s ^ 2 / (4 * γ) + s ^ 2 / (4 * γ) := by field_simp; ring
    nlinarith [sq_nonneg e, sq_nonneg ε, hγ]
  · push Not at hsD
    have hspos : 0 < s := lt_of_le_of_lt (by positivity) hsD
    have hlam : lam = 2 * γ * ε / s := by
      apply min_eq_right
      rw [div_le_one hspos]; exact hsD.le
    have hls : lam * s = 2 * γ * ε := by rw [hlam]; field_simp
    have hdesc : f x + ψ x - (f (x + lam • (p - x)) + ψ (x + lam • (p - x))) ≥
        ε * s - 2 * γ * ε * e := by
      have e1 : lam / (2 * γ) * s ^ 2 = (lam * s) * s / (2 * γ) := by ring
      have e2 : lam * (e * s) = (lam * s) * e := by ring
      rw [e1, e2, hls] at hd
      have e3 : 2 * γ * ε * s / (2 * γ) = ε * s := by field_simp
      linarith
    have : 2 * ε * e ≤ 9 * e ^ 2 + 9 / 8 * ε ^ 2 := by nlinarith [sq_nonneg (3 * e - ε / 3)]
    nlinarith

end Smooth

lemma capped_move_le {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (x p : E) :
    ‖min 1 (2 * γ * ε / ‖p - x‖) • (p - x)‖ ≤ 2 * γ * ε := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
  rcases (norm_nonneg (p - x)).eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  · calc min 1 (2 * γ * ε / ‖p - x‖) * ‖p - x‖ ≤ 2 * γ * ε / ‖p - x‖ * ‖p - x‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
      _ = 2 * γ * ε := by field_simp

lemma hessian_remainder {grad : E → E} {hess : E → E →L[ℝ] E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hd : ∀ x, HasFDerivAt grad (hess x) x) (hl : ∀ x y, ‖hess x - hess y‖ ≤ ρ * ‖x - y‖)
    (v d : E) : ‖grad (v + d) - grad v - hess v d‖ ≤ ρ * ‖d‖ ^ 2 := by
  have hconv : Convex ℝ (Metric.closedBall v ‖d‖) := convex_closedBall v ‖d‖
  have hderiv : ∀ z ∈ Metric.closedBall v ‖d‖,
      HasFDerivWithinAt (fun z => grad z - hess v z) (hess z - hess v) (Metric.closedBall v ‖d‖) z :=
    fun z _ => ((hd z).sub (hess v).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall v ‖d‖, ‖hess z - hess v‖ ≤ ρ * ‖d‖ := by
    intro z hz
    have hz' : ‖z - v‖ ≤ ‖d‖ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    exact (hl z v).trans (mul_le_mul_of_nonneg_left hz' hρ)
  have hv : v ∈ Metric.closedBall v ‖d‖ := Metric.mem_closedBall_self (norm_nonneg d)
  have hvd : v + d ∈ Metric.closedBall v ‖d‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have key := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hv hvd
  have e : grad (v + d) - hess v (v + d) - (grad v - hess v v) = grad (v + d) - grad v - hess v d := by
    rw [map_add]; abel
  rw [e, add_sub_cancel_left] at key
  calc ‖grad (v + d) - grad v - hess v d‖ ≤ ρ * ‖d‖ * ‖d‖ := key
    _ = ρ * ‖d‖ ^ 2 := by ring

lemma transport_bias {grad : E → E} {hess : E → E →L[ℝ] E} {ρ α : ℝ} (hρ : 0 ≤ ρ)
    (hd : ∀ x, HasFDerivAt grad (hess x) x) (hl : ∀ x y, ‖hess x - hess y‖ ≤ ρ * ‖x - y‖)
    (hα : 0 < α) (hα1 : α ≤ 1) (x x' : E) :
    ‖(1 - α) • (grad x - grad x') + α • (grad (x' + ((1 - α) / α) • (x' - x)) - grad x')‖ ≤
      ρ / α * ‖x' - x‖ ^ 2 := by
  set c := (1 - α) / α
  set Δ := x' - x
  have r1 := hessian_remainder hρ hd hl x' (-Δ)
  have r2 := hessian_remainder hρ hd hl x' (c • Δ)
  have hx : x' + -Δ = x := by simp [Δ]
  rw [hx] at r1
  have hlin : (1 - α) • hess x' (-Δ) + α • hess x' (c • Δ) = 0 := by
    rw [map_neg, map_smul, smul_neg, smul_smul]
    have : α * c = 1 - α := by simp only [c]; field_simp
    rw [this]; abel
  have e : (1 - α) • (grad x - grad x') + α • (grad (x' + c • Δ) - grad x') =
      (1 - α) • (grad x - grad x' - hess x' (-Δ)) + α • (grad (x' + c • Δ) - grad x' - hess x' (c • Δ)) := by
    have h : (1 - α) • (grad x - grad x' - hess x' (-Δ)) + α • (grad (x' + c • Δ) - grad x' - hess x' (c • Δ)) =
        ((1 - α) • (grad x - grad x') + α • (grad (x' + c • Δ) - grad x')) -
          ((1 - α) • hess x' (-Δ) + α • hess x' (c • Δ)) := by module
    rw [h, hlin, sub_zero]
  rw [e]
  have h1α : 0 ≤ 1 - α := by linarith
  have hc0 : 0 ≤ c := div_nonneg h1α hα.le
  calc ‖(1 - α) • (grad x - grad x' - hess x' (-Δ)) + α • (grad (x' + c • Δ) - grad x' - hess x' (c • Δ))‖
      ≤ (1 - α) * ‖grad x - grad x' - hess x' (-Δ)‖ + α * ‖grad (x' + c • Δ) - grad x' - hess x' (c • Δ)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1α, abs_of_pos hα]
    _ ≤ (1 - α) * (ρ * ‖-Δ‖ ^ 2) + α * (ρ * ‖c • Δ‖ ^ 2) := by gcongr
    _ = ρ * ‖Δ‖ ^ 2 * ((1 - α) + α * c ^ 2) := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]; ring
    _ ≤ ρ / α * ‖Δ‖ ^ 2 := by
        have hb : (1 - α) + α * c ^ 2 ≤ 1 / α := by
          simp only [c]
          rw [div_pow]
          have : (1 - α) + α * ((1 - α) ^ 2 / α ^ 2) = (1 - α) / α := by field_simp; ring
          rw [this]
          exact div_le_div_of_nonneg_right (by linarith) hα.le
        have : ρ / α * ‖Δ‖ ^ 2 = ρ * ‖Δ‖ ^ 2 * (1 / α) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hb (by positivity)

end OracleTemplate.CompositeTransport
