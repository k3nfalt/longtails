import LongTails.Proofs.VarianceReducedWeakMintyInner
import LongTails.Proofs.VarianceReducedWeakMintyAlgebra

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.VarianceReducedWeakMinty

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype Ω] [Nonempty Ω]

lemma mean_outer_correction (F : E → E) (z y v xstar : E) (g : Ω → E)
    {η ρ s V : ℝ} (hη : 0 < η) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hrel : ρ = η * (1 - s))
    (hwm : -ρ * ‖F y + v‖ ^ 2 ≤ ⟪F y + v, y - xstar⟫)
    (hm : ∑ ω, (g ω - F y) = 0) (hv : (𝔼 ω, ‖g ω - F y‖ ^ 2) ≤ V) :
    (𝔼 ω, ‖z - (s * η) • (g ω + v) - xstar‖ ^ 2) ≤
      ‖z - xstar‖ ^ 2 - s ^ 2 / 2 * ‖z - y‖ ^ 2 +
        2 * scaledError F η z (y, v) + s ^ 2 * η ^ 2 * V := by
  have hwm' : -(1 - s) * ‖η • (F y + v)‖ ^ 2 ≤
      ⟪η • (F y + v), y - xstar⟫ := by
    have hh := mul_le_mul_of_nonneg_left hwm hη.le
    rw [hrel] at hh
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_left]
    nlinarith
  have hm' : ∑ ω, η • (g ω - F y) = 0 := by rw [← Finset.smul_sum, hm, smul_zero]
  have h := mean_corrected_energy z y xstar (η • (F y + v))
    (fun ω => η • (g ω - F y)) hs hs1 hm' hwm'
  have he (ω : Ω) : z - s • (η • (F y + v) + η • (g ω - F y)) - xstar =
      z - (s * η) • (g ω + v) - xstar := by module
  simp only [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Finset.mul_expect] at h
  have hv' := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ s ^ 2 * η ^ 2)
  dsimp only [scaledError]
  nlinarith

lemma finite_outer_step {I : Type*} [Fintype I] [Nonempty I]
    (F : E → E) (x w xstar : E) (Y : I → E × E) (g : I → Ω → E)
    {η ρ s p : ℝ} (hη : 0 < η) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) (hrel : ρ = η * (1 - s))
    (hwm : ∀ i, -ρ * ‖F (Y i).1 + (Y i).2‖ ^ 2 ≤
      ⟪F (Y i).1 + (Y i).2, (Y i).1 - xstar⟫)
    (hm : ∀ i, ∑ ω, (g i ω - F (Y i).1) = 0)
    (herr : (𝔼 i, scaledError F η ((1 - p) • x + p • w) (Y i)) ≤
      s ^ 2 / 32 * (𝔼 i, ‖(1 - p) • x + p • w - (Y i).1‖ ^ 2) +
        p / 64 * ‖(1 - p) • x + p • w - w‖ ^ 2)
    (hnoise : η ^ 2 * (𝔼 i, 𝔼 ω, ‖g i ω - F (Y i).1‖ ^ 2) ≤
      (𝔼 i, ‖(1 - p) • x + p • w - (Y i).1‖ ^ 2) / 32 +
        p / 32 * ‖(1 - p) • x + p • w - w‖ ^ 2) :
    (𝔼 i, 𝔼 ω, ‖(1 - p) • x + p • w - (s * η) • (g i ω + (Y i).2) - xstar‖ ^ 2) +
      s ^ 2 * η ^ 2 / 16 * (𝔼 i, ‖F (Y i).1 + (Y i).2‖ ^ 2) ≤
        (1 - p) * ‖x - xstar‖ ^ 2 + p * ‖w - xstar‖ ^ 2 := by
  let z := (1 - p) • x + p • w
  have hz : ‖z - w‖ ^ 2 ≤ ‖x - w‖ ^ 2 := by
    have he : z - w = (1 - p) • (x - w) := by dsimp [z]; module
    rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hh : (1 - p) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x - w‖)]
  have henergy := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
    mean_outer_correction F z (Y i).1 (Y i).2 xstar (g i) hη hs hs1 hrel (hwm i) (hm i) le_rfl)
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Fintype.expect_const, Prod.mk.eta] at henergy
  have hres (i : I) : η ^ 2 * ‖F (Y i).1 + (Y i).2‖ ^ 2 ≤
      2 * ‖z - (Y i).1‖ ^ 2 + 2 * scaledError F η z (Y i) := by
    have hh := FiniteSum.norm_sub_sq_le (z - (Y i).1)
      ((z - (Y i).1) - η • (F (Y i).1 + (Y i).2))
    rw [show (z - (Y i).1) - ((z - (Y i).1) - η • (F (Y i).1 + (Y i).2)) =
      η • (F (Y i).1 + (Y i).2) by abel, norm_sub_rev (z - (Y i).1)] at hh
    simpa only [scaledError, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hh
  have hr := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hres i)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hr
  have hid := snapshot_energy x w xstar p
  have hbase : ‖z - xstar‖ ^ 2 = (1 - p) * ‖x - xstar‖ ^ 2 +
      p * ‖w - xstar‖ ^ 2 - p * (1 - p) * ‖x - w‖ ^ 2 := hid
  rw [hbase] at henergy
  have hh := outer_absorption (base := (1 - p) * ‖x - xstar‖ ^ 2 + p * ‖w - xstar‖ ^ 2)
    hs hs1 hp hp2
    (Finset.expect_nonneg (s := Finset.univ) (fun i _ => sq_nonneg ‖z - (Y i).1‖))
    (sq_nonneg ‖x - w‖) (sq_nonneg ‖z - w‖) hz herr hnoise hr (by simpa only [mul_assoc] using henergy)
  dsimp only [z] at hh
  nlinarith only [hh]

open LongTails.Setups.FiniteSumWeakMintyInclusion

omit [Fintype Ω] [Nonempty Ω] in
lemma stepPlan_descent {n b : ℕ} [NeZero n] (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) (x w xstar t : E) {η ρ s p L ν h : ℝ}
    (hη : 0 < η) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hrel : ρ = η * (1 - s)) (hν : 0 ≤ ν) (hh : 0 < h)
    (hhdef : h = 1 - η ^ 2 * L ^ 2) (hsmall : η ^ 2 * ν / h ≤ s ^ 2 * p / 65536)
    (hJ : ∀ a c, ‖J η a - J η c‖ ≤ ‖a - c‖)
    (hJres : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (ht : J η ((1 - p) • x + p • w - η • operator F t) = t)
    (hF : ∀ u v, ‖operator F u - operator F v‖ ≤ L * ‖u - v‖)
    (hwm : ∀ y, ∀ v ∈ A y, -ρ * ‖operator F y + v‖ ^ 2 ≤ ⟪operator F y + v, y - xstar⟫)
    (hm : ∀ y, ∑ ξ : Fin b → Fin n, (estimatorValue exact F w y ξ - operator F y) = 0)
    (hv : ∀ y, (𝔼 ξ : Fin b → Fin n, ‖estimatorValue exact F w y ξ - operator F y‖ ^ 2) ≤
      ν * ‖y - w‖ ^ 2) (k : ℕ) (hpower : (1 - h / 2) ^ k ≤ s ^ 2 / 8192) :
    let S := fun ξ : StepSeed n b (k + 1) =>
      QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)
    (𝔼 ξ, ‖(S ξ).1 - xstar‖ ^ 2) +
      s ^ 2 * η ^ 2 / 16 * (𝔼 ξ, ‖operator F (S ξ).2.1 + (S ξ).2.2‖ ^ 2) ≤
        (1 - p) * ‖x - xstar‖ ^ 2 + p * ‖w - xstar‖ ^ 2 := by
  let z := (1 - p) • x + p • w
  let Y := fun ξ : Fin (k + 1) → Fin b → Fin n =>
    QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) (k + 1) ξ (z, 0))
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hh1 : h ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg L)]
  have hα0 : 0 ≤ η ^ 2 * ν / h := by positivity
  have hθα : η ^ 2 * ν ≤ η ^ 2 * ν / h := by
    have hm' := mul_le_mul_of_nonneg_left hh1 hα0
    rw [div_mul_cancel₀ _ hh.ne'] at hm'
    simpa using hm'
  obtain ⟨hcoef, hθ1, hθp⟩ := noise_relaxation hs hs1 hp hp2 hθα hsmall
  have hs2p := mul_le_mul_of_nonneg_right (show p ≤ 1 by linarith) (sq_nonneg s)
  have hweak : η ^ 2 * ν / h ≤ s ^ 2 / 65536 := by nlinarith
  have hnoise : η ^ 2 * ν ≤ h / 8 := by
    have hb : η ^ 2 * ν / h ≤ 1 / 8 := by nlinarith
    have hm' := (div_le_iff₀ hh).mp hb
    nlinarith
  have herr := picard_relative_error exact F J z w t hη hν hh hhdef hnoise hs hs1 hweak
    hJ ht hF hm hv k hpower
  have herr' : (𝔼 ξ, scaledError (operator F) η z (Y ξ)) ≤
      s ^ 2 / 32 * (𝔼 ξ, ‖z - (Y ξ).1‖ ^ 2) + p / 64 * ‖z - w‖ ^ 2 := by
    have hh' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖z - w‖)
    exact herr.trans (by dsimp only [Y]; nlinarith)
  have hnoise' : η ^ 2 * (𝔼 i, 𝔼 ξ : Fin b → Fin n,
      ‖estimatorValue exact F w (Y i).1 ξ - operator F (Y i).1‖ ^ 2) ≤
      (𝔼 i, ‖z - (Y i).1‖ ^ 2) / 32 + p / 32 * ‖z - w‖ ^ 2 := by
    have ha := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hv (Y i).1)
    have hb (i) : ‖(Y i).1 - w‖ ^ 2 ≤ 2 * ‖z - (Y i).1‖ ^ 2 + 2 * ‖z - w‖ ^ 2 := by
      have hd := FiniteSum.norm_sub_sq_le (z - w) (z - (Y i).1)
      rw [show (z - w) - (z - (Y i).1) = (Y i).1 - w by abel] at hd
      linarith
    have hc := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hb i)
    simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at ha hc
    have h1 := mul_le_mul_of_nonneg_left ha (sq_nonneg η)
    have h2 := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ η ^ 2 * ν)
    have h3 := mul_le_mul_of_nonneg_right hθ1
      (Finset.expect_nonneg (s := Finset.univ) (fun i _ => sq_nonneg ‖z - (Y i).1‖))
    have h4 := mul_le_mul_of_nonneg_right hθp (sq_nonneg ‖z - w‖)
    nlinarith
  have hmY (i : Fin (k + 1) → Fin b → Fin n) := eval_picardPlan_member exact F J A hη hJres z w (k + 1) (by omega) i (z, 0)
  have hout := finite_outer_step (operator F) x w xstar Y
    (fun i => estimatorValue exact F w (Y i).1) hη hs hs1 hp hp2 hrel
    (fun i => hwm _ _ (hmY i)) (fun i => hm (Y i).1) herr' hnoise'
  have he (ξ : StepSeed n b (k + 1)) :
      QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ) =
        (z - (s * η) • (estimatorValue exact F w (Y ξ.1).1 ξ.2 + (Y ξ.1).2), Y ξ.1) := by
    simp only [stepPlan, QueryPlan.eval_bind, QueryPlan.eval_map, eval_estimatorPlan]
    rfl
  dsimp only
  simp only [he]
  simp only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const]
  simpa only [Fintype.expect_const, z] using hout

end OracleTemplate.VarianceReducedWeakMinty
