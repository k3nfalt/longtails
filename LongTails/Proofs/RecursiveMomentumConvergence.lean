import LongTails.Proofs.RecursiveMomentumDescent
import LongTails.Proofs.NormalizedStormConvergence
import LongTails.Setups.AffineVarianceMeanSquaredSmooth

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.RecursiveMomentum

open OracleTemplate.NormalizedStorm

noncomputable def mR (Γ Λ ε : ℝ) : ℝ := 1 + 3 * Γ + 6 * Λ / ε

noncomputable def mInvA (Γ Λ ε : ℝ) : ℝ := 1 + 8 * Γ ^ 2 + 32 * Λ ^ 2 / ε ^ 2

noncomputable def mGamma (L Lbar Γ Λ ε : ℝ) : ℝ := 1 / (4 * (L + Lbar) * mR Γ Λ ε)

noncomputable def mB (Γ Λ ε : ℝ) : ℕ := ⌈Γ ^ 2 * mR Γ Λ ε + Λ ^ 2 / ε ^ 2⌉₊ + 1

noncomputable def mT (L Lbar Γ Λ Δ ε : ℝ) : ℕ :=
  ⌈64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 + 16 * mInvA Γ Λ ε⌉₊

section Tuning

variable {L Lbar Γ Λ Δ ε : ℝ}

structure MTune (L Lbar Γ Λ Δ ε : ℝ) : Prop where
  L_pos : 0 < L
  Lbar_nn : 0 ≤ Lbar
  Γ_nn : 0 ≤ Γ
  Λ_nn : 0 ≤ Λ
  Δ_nn : 0 ≤ Δ
  ε_pos : 0 < ε

lemma MTune.r_ge (h : MTune L Lbar Γ Λ Δ ε) : 1 ≤ mR Γ Λ ε := by
  have := h.Γ_nn; have := h.Λ_nn; have := h.ε_pos
  have : 0 ≤ 6 * Λ / ε := by positivity
  unfold mR; linarith

lemma MTune.ia_ge (h : MTune L Lbar Γ Λ Δ ε) : 1 ≤ mInvA Γ Λ ε := by
  have := h.ε_pos
  have : 0 ≤ 32 * Λ ^ 2 / ε ^ 2 := by positivity
  unfold mInvA; nlinarith [sq_nonneg Γ]

lemma MTune.ia_le (h : MTune L Lbar Γ Λ Δ ε) : mInvA Γ Λ ε ≤ mR Γ Λ ε ^ 2 := by
  have hε := h.ε_pos; have hΓ := h.Γ_nn; have hΛ := h.Λ_nn
  set t := Λ / ε
  have ht : 0 ≤ t := by positivity
  have e1 : 32 * Λ ^ 2 / ε ^ 2 = 32 * t ^ 2 := by simp only [t]; field_simp
  have e2 : 6 * Λ / ε = 6 * t := by simp only [t]; ring
  unfold mInvA mR
  rw [e1, e2]
  nlinarith [mul_nonneg hΓ ht]

lemma MTune.a_Γ (h : MTune L Lbar Γ Λ Δ ε) : 1 / mInvA Γ Λ ε * Γ ^ 2 ≤ 1 / 8 := by
  have hia := h.ia_ge
  have : 0 ≤ 32 * Λ ^ 2 / ε ^ 2 := by have := h.ε_pos; positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by linarith) (by norm_num)]
  unfold mInvA at *
  nlinarith

lemma MTune.a_Λ (h : MTune L Lbar Γ Λ Δ ε) : 32 * Λ ^ 2 ≤ mInvA Γ Λ ε * ε ^ 2 := by
  have hε := h.ε_pos
  unfold mInvA
  have e : 32 * Λ ^ 2 / ε ^ 2 * ε ^ 2 = 32 * Λ ^ 2 := by field_simp
  nlinarith [sq_nonneg Γ, sq_nonneg ε]

lemma MTune.K_pos (h : MTune L Lbar Γ Λ Δ ε) : 0 < L + Lbar := by
  have := h.L_pos; have := h.Lbar_nn; linarith

lemma MTune.gamma_pos (h : MTune L Lbar Γ Λ Δ ε) : 0 < mGamma L Lbar Γ Λ ε := by
  have := h.K_pos; have := h.r_ge
  unfold mGamma; positivity

lemma MTune.gamma_L (h : MTune L Lbar Γ Λ Δ ε) : mGamma L Lbar Γ Λ ε * L ≤ 1 / 2 := by
  have hK := h.K_pos; have hr := h.r_ge; have hL := h.L_pos; have := h.Lbar_nn
  unfold mGamma
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma MTune.gamma_c (h : MTune L Lbar Γ Λ Δ ε) :
    4 * (Lbar ^ 2 + L ^ 2) * mGamma L Lbar Γ Λ ε ^ 2 ≤ 1 / mInvA Γ Λ ε / 4 := by
  have hK := h.K_pos; have hr := h.r_ge; have hL := h.L_pos; have hLb := h.Lbar_nn
  have hia := h.ia_ge; have hial := h.ia_le
  unfold mGamma
  rw [div_pow, one_pow, div_div, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have h1 : Lbar ^ 2 + L ^ 2 ≤ (L + Lbar) ^ 2 := by nlinarith
  have h2 : 4 * (Lbar ^ 2 + L ^ 2) * (mInvA Γ Λ ε * 4) ≤
      4 * (L + Lbar) ^ 2 * (mR Γ Λ ε ^ 2 * 4) := by
    have := mul_le_mul h1 hial (by linarith) (by positivity)
    nlinarith
  nlinarith

lemma acc_core {K r ia B N L Δ ε Λ Γ φ0 u0 : ℝ} (hK : L ≤ K) (hL : 0 ≤ L) (hr : 1 ≤ r)
    (hia : 1 ≤ ia) (hial : ia ≤ r ^ 2) (hBpos : 0 < B) (hB1 : Γ ^ 2 * r ≤ B)
    (hB2 : Λ ^ 2 ≤ B * ε ^ 2) (hNε : 64 * K * r * Δ ≤ N * ε ^ 2) (hNa : 16 * ia ≤ N)
    (hΛ : 32 * Λ ^ 2 ≤ ia * ε ^ 2) (hφ0 : 0 ≤ φ0) (hφΔ : φ0 ≤ Δ)
    (hu0 : B * u0 ≤ Γ ^ 2 * (2 * L * φ0) + Λ ^ 2) :
    16 * K * r * φ0 + 4 * ia * u0 + 8 * Λ ^ 2 * N / ia ≤ N * ε ^ 2 := by
  have hK0 : 0 ≤ K := le_trans hL hK
  have hr0 : 0 ≤ r := by linarith
  have hia0 : 0 < ia := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hKr : K * r * φ0 ≤ K * r * Δ := mul_le_mul_of_nonneg_left hφΔ (mul_nonneg hK0 hr0)
  have hLr : L * r * φ0 ≤ K * r * φ0 := by
    have := mul_le_mul_of_nonneg_right hK (mul_nonneg hr0 hφ0)
    linarith [mul_assoc L r φ0, mul_assoc K r φ0]
  have t1 : 16 * K * r * φ0 ≤ N * ε ^ 2 / 4 := by linarith
  have t3 : 8 * Λ ^ 2 * N / ia ≤ N * ε ^ 2 / 4 := by
    rw [div_le_iff₀ hia0]
    have := mul_le_mul_of_nonneg_right hΛ hN0
    linarith
  have a1 : ia * Γ ^ 2 ≤ r * B := by
    have h1 := mul_le_mul_of_nonneg_right hial (sq_nonneg Γ)
    have h2 := mul_le_mul_of_nonneg_left hB1 hr0
    have e : r ^ 2 * Γ ^ 2 = r * (Γ ^ 2 * r) := by ring
    linarith
  have a3 : 8 * L * r * φ0 ≤ N * ε ^ 2 / 8 := by linarith
  have s1 : 4 * ia * (B * u0) ≤ 4 * ia * (Γ ^ 2 * (2 * L * φ0) + Λ ^ 2) :=
    mul_le_mul_of_nonneg_left hu0 (by linarith)
  have s2 : ia * Γ ^ 2 * (8 * L * φ0) ≤ B * (N * ε ^ 2 / 8) := by
    have h1 := mul_le_mul_of_nonneg_right a1 (by positivity : (0 : ℝ) ≤ 8 * L * φ0)
    have h2 := mul_le_mul_of_nonneg_left a3 hBpos.le
    have e : r * B * (8 * L * φ0) = B * (8 * L * r * φ0) := by ring
    linarith
  have s3 : 4 * ia * Λ ^ 2 ≤ B * (N * ε ^ 2 / 4) := by
    have h1 := mul_le_mul_of_nonneg_left hB2 (by linarith : (0 : ℝ) ≤ 4 * ia)
    have h2 := mul_le_mul_of_nonneg_right hNa (mul_nonneg hBpos.le hε2)
    have e1 : 4 * ia * (B * ε ^ 2) = 16 * ia * (B * ε ^ 2) / 4 := by ring
    have e2 : B * (N * ε ^ 2 / 4) = N * (B * ε ^ 2) / 4 := by ring
    linarith
  have t2 : B * (4 * ia * u0) ≤ B * (3 * (N * ε ^ 2) / 8) := by
    have e1 : B * (4 * ia * u0) = 4 * ia * (B * u0) := by ring
    have e2 : 4 * ia * (Γ ^ 2 * (2 * L * φ0) + Λ ^ 2) =
        ia * Γ ^ 2 * (8 * L * φ0) + 4 * ia * Λ ^ 2 := by ring
    have e3 : B * (3 * (N * ε ^ 2) / 8) = B * (N * ε ^ 2 / 8) + B * (N * ε ^ 2 / 4) := by ring
    linarith
  have t2' : 4 * ia * u0 ≤ 3 * (N * ε ^ 2) / 8 := le_of_mul_le_mul_left t2 hBpos
  have : 0 ≤ N * ε ^ 2 := mul_nonneg hN0 hε2
  linarith

lemma MTune.accuracy (h : MTune L Lbar Γ Λ Δ ε) {φ0 u0 : ℝ} (hφ0 : 0 ≤ φ0) (hφΔ : φ0 ≤ Δ)
    (hu0 : (mB Γ Λ ε : ℝ) * u0 ≤ Γ ^ 2 * (2 * L * φ0) + Λ ^ 2) :
    4 / mGamma L Lbar Γ Λ ε * φ0 + 4 / (1 / mInvA Γ Λ ε) * u0 +
        8 * (1 / mInvA Γ Λ ε) * Λ ^ 2 * ((mT L Lbar Γ Λ Δ ε : ℝ) + 1) ≤
      ((mT L Lbar Γ Λ Δ ε : ℝ) + 1) * ε ^ 2 := by
  have hK := h.K_pos; have hr := h.r_ge; have hL := h.L_pos; have hε := h.ε_pos
  have hia := h.ia_ge; have hial := h.ia_le; have hΓ := h.Γ_nn; have hΔ := h.Δ_nn
  have hT : 64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 + 16 * mInvA Γ Λ ε ≤
      (mT L Lbar Γ Λ Δ ε : ℝ) + 1 := by
    have := Nat.le_ceil (64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 + 16 * mInvA Γ Λ ε)
    unfold mT
    linarith
  have hx : 0 ≤ 64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 := by
    have : 0 ≤ mR Γ Λ ε := by linarith
    positivity
  have hNε : 64 * (L + Lbar) * mR Γ Λ ε * Δ ≤ ((mT L Lbar Γ Λ Δ ε : ℝ) + 1) * ε ^ 2 := by
    have e : 64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 * ε ^ 2 =
        64 * (L + Lbar) * mR Γ Λ ε * Δ := by field_simp
    have h16 : 0 ≤ 16 * mInvA Γ Λ ε := by linarith
    have := mul_le_mul_of_nonneg_right hT (sq_nonneg ε)
    nlinarith [sq_nonneg ε]
  have hB0 : Γ ^ 2 * mR Γ Λ ε + Λ ^ 2 / ε ^ 2 + 1 ≤ (mB Γ Λ ε : ℝ) := by
    have := Nat.le_ceil (Γ ^ 2 * mR Γ Λ ε + Λ ^ 2 / ε ^ 2)
    unfold mB
    push_cast
    linarith
  have hq : 0 ≤ Λ ^ 2 / ε ^ 2 := by positivity
  have hp : 0 ≤ Γ ^ 2 * mR Γ Λ ε := mul_nonneg (sq_nonneg Γ) (by linarith)
  have hB2 : Λ ^ 2 ≤ (mB Γ Λ ε : ℝ) * ε ^ 2 := by
    have e : Λ ^ 2 / ε ^ 2 * ε ^ 2 = Λ ^ 2 := by field_simp
    have := mul_le_mul_of_nonneg_right hB0 (sq_nonneg ε)
    nlinarith [sq_nonneg ε]
  have eγ : 4 / mGamma L Lbar Γ Λ ε = 16 * (L + Lbar) * mR Γ Λ ε := by
    unfold mGamma
    rw [div_div_eq_mul_div, div_one]
    ring
  have ea : 4 / (1 / mInvA Γ Λ ε) = 4 * mInvA Γ Λ ε := by
    rw [div_div_eq_mul_div, div_one]
  have ea2 : 8 * (1 / mInvA Γ Λ ε) * Λ ^ 2 * ((mT L Lbar Γ Λ Δ ε : ℝ) + 1) =
      8 * Λ ^ 2 * ((mT L Lbar Γ Λ Δ ε : ℝ) + 1) / mInvA Γ Λ ε := by ring
  rw [eγ, ea, ea2]
  exact acc_core (K := L + Lbar) (by linarith [h.Lbar_nn]) hL.le hr hia hial (by linarith)
    (by linarith) hB2 hNε (by linarith) h.a_Λ hφ0 hφΔ hu0

lemma MTune.calls (h : MTune L Lbar Γ Λ Δ ε) :
    mB Γ Λ ε + mT L Lbar Γ Λ Δ ε ≤
      ⌈16 + 131 * Γ ^ 2 + 5 * Γ ^ 4 + 516 * Λ ^ 2 / ε ^ 2 +
        64 * (L + Lbar) * (1 + 3 * Γ) * Δ / ε ^ 2 + 384 * (L + Lbar) * Λ * Δ / ε ^ 3⌉₊ + 2 := by
  have hK := h.K_pos; have hr := h.r_ge; have hε := h.ε_pos; have hΓ := h.Γ_nn
  have hΛ := h.Λ_nn; have hΔ := h.Δ_nn; have hia := h.ia_ge
  have hx : 0 ≤ Γ ^ 2 * mR Γ Λ ε + Λ ^ 2 / ε ^ 2 := by positivity
  have hy : 0 ≤ 64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 + 16 * mInvA Γ Λ ε := by positivity
  have hsum := ceil_add_ceil_le hx hy
  set t := Λ / ε
  have ht : 0 ≤ t := by positivity
  have hle : Γ ^ 2 * mR Γ Λ ε + Λ ^ 2 / ε ^ 2 +
      (64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 + 16 * mInvA Γ Λ ε) ≤
      16 + 131 * Γ ^ 2 + 5 * Γ ^ 4 + 516 * Λ ^ 2 / ε ^ 2 +
        64 * (L + Lbar) * (1 + 3 * Γ) * Δ / ε ^ 2 + 384 * (L + Lbar) * Λ * Δ / ε ^ 3 := by
    have e1 : Λ ^ 2 / ε ^ 2 = t ^ 2 := by simp only [t]; field_simp
    have e2 : 516 * Λ ^ 2 / ε ^ 2 = 516 * t ^ 2 := by simp only [t]; field_simp
    have e3 : 384 * (L + Lbar) * Λ * Δ / ε ^ 3 = 384 * (L + Lbar) * t * Δ / ε ^ 2 := by
      simp only [t]; field_simp
    have e4 : 64 * (L + Lbar) * mR Γ Λ ε * Δ / ε ^ 2 =
        64 * (L + Lbar) * (1 + 3 * Γ) * Δ / ε ^ 2 + 384 * (L + Lbar) * t * Δ / ε ^ 2 := by
      simp only [mR, t]; field_simp; ring
    have e5 : mInvA Γ Λ ε = 1 + 8 * Γ ^ 2 + 32 * t ^ 2 := by
      simp only [mInvA, t]; field_simp
    have e6 : mR Γ Λ ε = 1 + 3 * Γ + 6 * t := by simp only [mR, t]; ring
    rw [e1, e2, e3, e4, e5, e6]
    nlinarith [sq_nonneg (Γ ^ 2 - t), sq_nonneg (Γ * (Γ - 1)), mul_nonneg hΓ ht]
  have hc := Nat.ceil_mono hle
  unfold mB mT
  omega

end Tuning

section Master

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

omit [CompleteSpace E] in
lemma measurable_momentumOut (hg : Measurable (Function.uncurry g)) (γ a : ℝ) (b0 T : ℕ)
    (x0 : E) :
    Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) => (momentumPair g γ a b0 x0 ω.2 ω.1.val).1) :=
  measurable_from_prod_countable_right fun τ => (measurable_momentumPair hg γ a b0 x0 τ.val).fst

theorem AffineHyp.master_lintegral (H : AffineHyp p F g L Lbar Γ Λ lower) {Δ ε : ℝ}
    (hLb : 0 ≤ Lbar) (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (x0 : E)
    (hgap : F x0 - lower ≤ Δ) :
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (momentumPair g (mGamma L Lbar Γ Λ ε) (1 / mInvA Γ Λ ε)
        (mB Γ Λ ε) x0 ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin (mT L Lbar Γ Λ Δ ε + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  have h : MTune L Lbar Γ Λ Δ ε := ⟨H.L_pos, hLb, hΓ, hΛ, hΔ, hε⟩
  set γ := mGamma L Lbar Γ Λ ε
  set a := 1 / mInvA Γ Λ ε
  set b0 := mB Γ Λ ε
  set T := mT L Lbar Γ Λ Δ ε
  set P := Measure.infinitePi fun _ : ℕ => p
  have hia := h.ia_ge
  have ha0 : 0 < a := by simp only [a]; positivity
  have ha1 : a ≤ 1 := by simp only [a]; rw [div_le_one (by linarith)]; exact hia
  have hγ := h.gamma_pos
  have hsum := H.grad_sq_sum hγ h.gamma_L ha0 ha1 h.a_Γ h.gamma_c b0 x0 (T + 1)
  have hF0 : 0 ≤ F x0 - lower := sub_nonneg.mpr (H.low x0)
  obtain ⟨hb1, hb2⟩ := H.batch_moment (p := p) x0 b0
  have hu0 : (b0 : ℝ) * ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P ≤
      Γ ^ 2 * (2 * L * (F x0 - lower)) + Λ ^ 2 := by
    have := H.grad_sq_le x0
    have := mul_le_mul_of_nonneg_left this (sq_nonneg Γ)
    linarith
  have hacc : 4 / γ * (F x0 - lower) +
      4 / a * ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P + 8 * a * Λ ^ 2 * ((T : ℝ) + 1) ≤ ((T : ℝ) + 1) * ε ^ 2 := h.accuracy hF0 hgap hu0
  have hint : ∀ j, Integrable (fun ξ => ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2) P :=
    fun j => (H.integrable_all hγ.le h.gamma_L ha0.le ha1 b0 x0 j).2.2.1
  have hpt : ∀ (j : ℕ) (ξ : ℕ → Ω), ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ≤
      ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 / (2 * ε) + ε / 2 := by
    intro j ξ
    have := sq_nonneg (‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ - ε)
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have hbd : ∀ j, Integrable (fun ξ =>
      ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 / (2 * ε) + ε / 2) P :=
    fun j => ((hint j).div_const (2 * ε)).add (integrable_const (ε / 2))
  have hgi : ∀ j, Integrable (fun ξ => ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖) P := by
    intro j
    refine Integrable.mono' (hbd j) (H.measurable_gradNorm γ a b0 x0 j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_norm]
    exact hpt j ξ
  have hamgm : ∀ j, ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ∂P ≤
      (∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 ∂P) / (2 * ε) + ε / 2 := by
    intro j
    have hm := integral_mono (hgi j) (hbd j) (hpt j)
    rw [integral_add ((hint j).div_const _) (integrable_const _), integral_div,
      integral_const] at hm
    simpa using hm
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) =>
      ENNReal.ofReal ‖gradient F (momentumPair g γ a b0 x0 ω.2 ω.1.val).1‖) :=
    ENNReal.measurable_ofReal.comp
      (H.grad_continuous.measurable.comp (measurable_momentumOut H.meas γ a b0 T x0)).norm
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (T + 1), (Fintype.card ({τ} : Set (Fin (T + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  have hj : ∀ τ : Fin (T + 1),
      ∫⁻ ξ, ENNReal.ofReal ‖gradient F (momentumPair g γ a b0 x0 ξ τ.val).1‖ ∂P =
      ENNReal.ofReal (∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ τ.val).1‖ ∂P) := by
    intro τ
    rw [ofReal_integral_eq_lintegral_ofReal (hgi τ.val)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
  simp_rw [hj]
  rw [← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ k).1‖ ∂P)]
  have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hbound : ∑ k ∈ Finset.range (T + 1),
      ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ k).1‖ ∂P ≤ ((T : ℝ) + 1) * ε := by
    have h1 : ∑ k ∈ Finset.range (T + 1), ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ k).1‖ ∂P ≤
        ∑ k ∈ Finset.range (T + 1),
          ((∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ k).1‖ ^ 2 ∂P) / (2 * ε) + ε / 2) :=
      Finset.sum_le_sum fun k _ => hamgm k
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at h1
    have h2 : ∑ k ∈ Finset.range (T + 1),
        ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ k).1‖ ^ 2 ∂P ≤ ((T : ℝ) + 1) * ε ^ 2 := by
      have hu0n : 0 ≤ ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P :=
        integral_nonneg fun _ => by positivity
      push_cast at hsum
      linarith
    have h3 : (∑ k ∈ Finset.range (T + 1),
        ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ k).1‖ ^ 2 ∂P) / (2 * ε) ≤
        ((T : ℝ) + 1) * ε / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    push_cast at h1
    linarith
  have hinv : (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((T : ℝ) + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  rw [hinv, ← ENNReal.ofReal_mul
    (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_one_div, div_le_iff₀ hT]
  linarith

end Master

open LongTails.Setups.AffineVarianceMeanSquaredSmooth

theorem convergence : Convergence LongTails.Setups.AffineVarianceMeanSquaredSmooth.spec
    (fun q _ => ⌈16 + 131 * q.Γ ^ 2 + 5 * q.Γ ^ 4 + 516 * q.Λ ^ 2 / q.ε ^ 2 +
      64 * (q.L + q.Lbar) * (1 + 3 * q.Γ) * q.Δ / q.ε ^ 2 +
      384 * (q.L + q.Lbar) * q.Λ * q.Δ / q.ε ^ 3⌉₊ + 2) := by
  apply convergence_of_public_budget (S := spec) (fun q => ⌈16 + 131 * q.Γ ^ 2 + 5 * q.Γ ^ 4 +
    516 * q.Λ ^ 2 / q.ε ^ 2 + 64 * (q.L + q.Lbar) * (1 + 3 * q.Γ) * q.Δ / q.ε ^ 2 +
    384 * (q.L + q.Lbar) * q.Λ * q.Δ / q.ε ^ 3⌉₊ + 2)
  refine ⟨fun q => recursiveMomentum (mGamma q.L q.Lbar q.Γ q.Λ q.ε) (1 / mInvA q.Γ q.Λ q.ε)
    (mB q.Γ q.Λ q.ε) (mT q.L q.Lbar q.Γ q.Λ q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hLb, hΓ, hΛ, hΔ, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgap, hgm, hint, hmean, hvi, hvar, hdi, hmss⟩ :=
    hadm
  have H : AffineHyp (p : Measure q.Ω) f g q.L q.Lbar q.Γ q.Λ (f q.x0 - q.Δ) :=
    ⟨hgrad, hlip, fun x => by linarith [hgap x], hgm, hint, hmean, hvi, hvar, hdi, hmss, hL⟩
  have h : MTune q.L q.Lbar q.Γ q.Λ q.Δ q.ε := ⟨hL, hLb, hΓ, hΛ, hΔ, hε⟩
  set γ := mGamma q.L q.Lbar q.Γ q.Λ q.ε
  set a := 1 / mInvA q.Γ q.Λ q.ε
  set b0 := mB q.Γ q.Λ q.ε
  set T := mT q.L q.Lbar q.Γ q.Λ q.Δ q.ε
  set K := ⌈16 + 131 * q.Γ ^ 2 + 5 * q.Γ ^ 4 + 516 * q.Λ ^ 2 / q.ε ^ 2 +
      64 * (q.L + q.Lbar) * (1 + 3 * q.Γ) * q.Δ / q.ε ^ 2 +
      384 * (q.L + q.Lbar) * q.Λ * q.Δ / q.ε ^ 3⌉₊ + 2
  have hK : b0 + T ≤ K := h.calls
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hexec : ∀ (τ : Fin (T + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (recursiveMomentum γ a b0 T q.x0) (fun _ => K)
        (show (recursiveMomentum γ a b0 T q.x0).Seed from τ) ξ =
      (momentumPair g γ a b0 q.x0 ξ τ.val).1 :=
    fun τ ξ => execute_recursiveMomentum g P γ a b0 T q.x0 K τ ξ hK
  have hout : (fun seed : (recursiveMomentum γ a b0 T q.x0).Seed × ((k : ℕ) → q.Ω) =>
      (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (recursiveMomentum γ a b0 T q.x0) (fun _ => K) seed.1
          seed.2)) =
      fun ω => (momentumPair g γ a b0 q.x0 ω.2 ω.1.val).1 := by
    funext seed; exact hexec seed.1 seed.2
  refine ⟨?_, ?_⟩
  · rw [hout]; exact measurable_momentumOut hgm γ a b0 T q.x0
  have hfun : (fun ω : (recursiveMomentum γ a b0 T q.x0).Seed × (ℕ → q.Ω) =>
      ‖gradient f (execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
          Oracle (q.E × q.E) (q.E × q.E)) (recursiveMomentum γ a b0 T q.x0) (fun _ => K) ω.1
          ω.2)‖) =
      fun ω => ‖gradient f (momentumPair g γ a b0 q.x0 ω.2 ω.1.val).1‖ := by
    funext ω; rw [hexec ω.1 ω.2]
  rw [hfun]
  change Integrable (fun ω : Fin (T + 1) × (ℕ → q.Ω) =>
      ‖gradient f (momentumPair g γ a b0 q.x0 ω.2 ω.1.val).1‖)
      ((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (T + 1) × (ℕ → q.Ω), ‖gradient f (momentumPair g γ a b0 q.x0 ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → q.Ω) =>
      ‖gradient f (momentumPair g γ a b0 q.x0 ω.2 ω.1.val).1‖) :=
    (H.grad_continuous.measurable.comp (measurable_momentumOut hgm γ a b0 T q.x0)).norm
  have hgap' : f q.x0 - (f q.x0 - q.Δ) ≤ q.Δ := by linarith
  have hL' := H.master_lintegral hLb hΓ hΛ hΔ hε q.x0 hgap'
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable
      hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'

end OracleTemplate.RecursiveMomentum
