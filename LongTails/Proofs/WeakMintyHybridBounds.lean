import LongTails.Algorithms.WeakMintyHybrid
import LongTails.Proofs.WeakMintyTaylorStep
import LongTails.Proofs.WeakMintyPicard
import LongTails.Proofs.HessianLipschitzModel

open scoped RealInnerProductSpace

namespace OracleTemplate.WeakMintyHybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Hyp (F : E → E) (J : E → E →L[ℝ] E) (L₁ L₂ ρ : ℝ) (z : E) : Prop where
  deriv : ∀ x, HasFDerivAt F (J x) x
  jlip : ∀ x y, ‖J x - J y‖ ≤ L₂ * ‖x - y‖
  lip : ∀ x y, ‖F x - F y‖ ≤ L₁ * ‖x - y‖
  minty : ∀ x, -(ρ / 2) * ‖F x‖ ^ 2 ≤ ⟪F x, x - z⟫

variable {F : E → E} {J : E → E →L[ℝ] E} {L₁ L₂ ρ : ℝ} {z : E}

lemma Hyp.jnorm (h : Hyp F J L₁ L₂ ρ z) (hL₁ : 0 ≤ L₁) (x : E) : ‖J x‖ ≤ L₁ :=
  (h.deriv x).le_of_lip' hL₁ (Filter.Eventually.of_forall (fun y => h.lip y x))

lemma Hyp.taylor (h : Hyp F J L₁ L₂ ρ z) (hL₂ : 0 ≤ L₂) (x s : E) :
    ‖F (x + s) - F x - J x s‖ ≤ L₂ * ‖s‖ ^ 2 := by
  have hd : ∀ u, fderiv ℝ F u = J u := fun u => (h.deriv u).fderiv
  have hh := NonlinearTemporalDiscrepancy.gradient_linearization_bound hL₂
    (fun u => (h.deriv u).differentiableAt)
    (fun u v => by simpa only [hd] using h.jlip u v) x (x + s)
  simpa only [hd, add_sub_cancel_left] using hh

lemma modelStep_equation [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (g : E) {k : ℝ} (hk : 0 < k) :
    g + J (modelStep J g k) + (k * ‖modelStep J g k‖) • modelStep J g k = 0 := by
  rw [modelStep, dite_eq_left hk]
  exact Classical.choose_spec (RegularizedLinearRoot.exists_root J g hk)

lemma margin_pos {L₁ ρ : ℝ} (h : ρ * L₁ < 2) : 0 < margin L₁ ρ := by
  dsimp [margin]
  linarith

lemma margin_le_one {L₁ ρ : ℝ} (hL₁ : 0 ≤ L₁) (hρ : 0 ≤ ρ) : margin L₁ ρ ≤ 1 := by
  dsimp [margin]
  nlinarith [mul_nonneg hρ hL₁]

lemma margin_relation (L₁ ρ : ℝ) : ρ * L₁ = 2 * (1 - margin L₁ ρ) := by
  dsimp [margin]
  ring

lemma cubic_progress [FiniteDimensional ℝ E] (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (x : E) {ε : ℝ} (hε : 0 < ε) (hg : ε < ‖F x‖)
    (hcap : ‖F x‖ ≤ (margin L₁ ρ) ^ 2 * L₁ ^ 2 / (64 * L₂)) :
    let δ := margin L₁ ρ
    let s := modelStep (J x) (F x) (16 * L₂ / δ)
    let η := 1 / ((16 * L₂ / δ) * ‖s‖)
    ε < ‖F (x + s)‖ →
      ‖x - (δ / 4 * η) • F (x + s) - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 -
        δ ^ 4 * ε / (16384 * L₂) := by
  dsimp only
  intro hv
  let δ := margin L₁ ρ
  let s := modelStep (J x) (F x) (16 * L₂ / δ)
  let η := 1 / ((16 * L₂ / δ) * ‖s‖)
  have hδ : 0 < δ := margin_pos hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hg0 : F x ≠ 0 := by intro hz; rw [hz, norm_zero] at hg; linarith
  have hc := WeakMintyTaylor.cubic_certificate (J x) (F x) s (F (x + s))
    hL₁ hL₂ hρ hδ hδ1 (margin_relation L₁ ρ) (h.jnorm hL₁.le x) hg0 hcap
    (modelStep_equation (J x) (F x) (by positivity)) (h.taylor hL₂.le x s)
  have hp := WeakMintyTaylor.relaxed_progress x z s (F (x + s)) hc.1 hρ hδ hδ1
    hc.2.1 (h.minty (x + s)) hc.2.2.1
  have hb := WeakMintyTaylor.cubic_charge hδ hδ1 hL₂ (hv.le.trans hc.2.2.2)
  exact hp.trans (by dsimp [δ, s, η] at *; linarith)

lemma fallback_progress [CompleteSpace E] (h : Hyp F J L₁ L₂ ρ z)
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hρ : 0 ≤ ρ) (hρL : ρ * L₁ < 2)
    (x : E) {ε : ℝ} (hε : 0 < ε) (hg : ε ≤ ‖F x‖)
    (hcap : (margin L₁ ρ) ^ 2 * L₁ ^ 2 / (64 * L₂) ≤ ‖F x‖) :
    let δ := margin L₁ ρ
    let η := (1 - δ / 4) / L₁
    let y := picardPoint F x η (innerCount δ)
    ‖x - (δ / 4 * η) • F y - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 -
      δ ^ 4 * ε / (16384 * L₂) := by
  dsimp only
  let δ := margin L₁ ρ
  let η := (1 - δ / 4) / L₁
  let T : E → E := fun y => x - η • F y
  let y := picardPoint F x η (innerCount δ)
  let s := y - x
  have hδ : 0 < δ := margin_pos hρL
  have hδ1 : δ ≤ 1 := margin_le_one hL₁.le hρ
  have hη := WeakMintyTaylor.fallback_margin hL₁ hδ hδ1 (margin_relation L₁ ρ)
  have hηL : η * L₁ = 1 - δ / 4 := by dsimp [η]; field_simp
  have hT : ∀ u v, ‖T u - T v‖ ≤ (1 - δ / 4) * ‖u - v‖ := by
    intro u v
    have hid : T u - T v = -(η • (F u - F v)) := by dsimp [T]; module
    rw [hid, norm_neg, norm_smul, Real.norm_of_nonneg hη.1.le]
    have hh := mul_le_mul_of_nonneg_left (h.lip u v) hη.1.le
    change η * ‖F u - F v‖ ≤ η * (L₁ * ‖u - v‖) at hh
    rw [← mul_assoc, hηL] at hh
    exact hh
  have hcert := WeakMintyPicard.iterate_residual T x hδ hδ1 hT
    (show (4 / δ) * Real.log (1024 / δ ^ 2) ≤ (innerCount δ : ℝ) from Nat.le_ceil _)
  have he : ‖s + η • F y‖ ≤ (δ / 16) * ‖s‖ := by
    have hid : s + η • F y = y - T y := by dsimp [s, T]; abel
    rw [hid]
    exact hcert
  have hlip : ‖F x - F y‖ ≤ L₁ * ‖s‖ := by
    simpa only [s, norm_sub_rev x y] using h.lip x y
  have hanchor := WeakMintyTaylor.fallback_anchor_bound s (F x) (F y) hL₁ hη.1
    (show δ / 16 ≤ 1 by linarith) (show η * L₁ ≤ 1 by rw [hηL]; linarith)
    (show 3 / 4 ≤ η * L₁ by rw [hηL]; linarith) he hlip
  have hm : -(ρ / 2) * ‖F y‖ ^ 2 ≤ ⟪F y, x + s - z⟫ := by
    simpa [s] using h.minty y
  have hp := WeakMintyTaylor.relaxed_progress x z s (F y) hη.1 hρ hδ hδ1 hη.2 hm he
  have hb := WeakMintyTaylor.fallback_charge hδ hL₁ hL₂ hε.le hg hcap hanchor
  exact hp.trans (by dsimp [δ, η, y, s] at *; linarith)

end OracleTemplate.WeakMintyHybrid
