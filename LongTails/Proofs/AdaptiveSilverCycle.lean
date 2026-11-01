import LongTails.Proofs.AdaptiveSilverModel
import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.HessianLipschitzModel

namespace LongTails.Proofs.AdaptiveSilverCycle

open scoped RealInnerProductSpace
open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.AdaptiveSilverScalar
open LongTails.Proofs.AdaptiveSilverSplit
open LongTails.Proofs.AdaptiveSilverDynamics
open LongTails.Proofs.AdaptiveSilverModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Psi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
  (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)

include hc

noncomputable def uq (g0 d : E) : E := (g0 + H d) - P b eig (g0 + H d)

omit hc in
lemma step_shape (L : ℝ) (gr : E → E) (g0 x0 x : E) (h : ℝ) :
    x - h • ((1 / L) • gr x) - x0 =
      (x - x0) - (h / L) • (g0 + H (x - x0) + (gr x - g0 - H (x - x0))) := by
  module

lemma psi_run_upper (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (L : ℝ) (hL : 0 < L) (gr : E → E)
    (g0 x0 : E) {e : ℝ} :
    ∀ (hs : List ℝ) (x : E), (∀ h ∈ hs, 0 ≤ h) →
      (∀ t < hs.length, ‖gr (run (fun y => (1 / L) • gr y) (hs.take t) x) - g0 -
        H (run (fun y => (1 / L) • gr y) (hs.take t) x - x0)‖ ≤ e) →
      psiPart b eig H g0 (run (fun y => (1 / L) • gr y) hs x - x0) ≤
        psiPart b eig H g0 (x - x0) + hs.sum / (2 * L) * e ^ 2
  | [], x, _, _ => by simp [run]
  | h :: t, x, hpos, herr => by
    have hh := hpos h (by simp)
    have h0 := herr 0 (by simp)
    simp only [List.take_zero, run] at h0
    have ih := psi_run_upper hsym L hL gr g0 x0 t (x - h • ((1 / L) • gr x))
      (fun h' hh' => hpos h' (List.mem_cons_of_mem _ hh'))
      (fun s hs' => by
        have := herr (s + 1) (by simp; omega)
        simpa [List.take_succ_cons, run] using this)
    simp only [run, List.sum_cons]
    have hstep := psi_step b eig H hc hsym g0 (x - x0) (gr x - g0 - H (x - x0))
      (show 0 ≤ h / L by positivity)
    rw [← step_shape H L gr g0 x0 x h] at hstep
    have he2 : ‖gr x - g0 - H (x - x0)‖ ^ 2 ≤ e ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h0 2
    have : h / L / 2 * ‖gr x - g0 - H (x - x0)‖ ^ 2 ≤ h / (2 * L) * e ^ 2 := by
      rw [show h / L / 2 = h / (2 * L) by ring]
      exact mul_le_mul_of_nonneg_left he2 (by positivity)
    have hu : 0 ≤ h / L / 2 * ‖(g0 + H (x - x0)) - P b eig (g0 + H (x - x0))‖ ^ 2 := by
      positivity
    have : (h + t.sum) / (2 * L) * e ^ 2 = h / (2 * L) * e ^ 2 + t.sum / (2 * L) * e ^ 2 := by
      ring
    linarith

lemma psi_run_lower (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (L : ℝ) (hL : 0 < L)
    (hH : ‖H‖ ≤ L) (gr : E → E) (g0 x0 : E) {e : ℝ} (he : 0 ≤ e) :
    ∀ (hs : List ℝ) (x : E) (r : ℝ), (∀ h ∈ hs, 0 ≤ h) →
      (∀ t < hs.length, ‖gr (run (fun y => (1 / L) • gr y) (hs.take t) x) - g0 -
        H (run (fun y => (1 / L) • gr y) (hs.take t) x - x0)‖ ≤ e) →
      r ≤ ‖uq b eig H g0 (x - x0)‖ →
      psiPart b eig H g0 (run (fun y => (1 / L) • gr y) hs x - x0) ≤
        psiPart b eig H g0 (x - x0) - hs.sum / (2 * L) * (max 0 (r - hs.sum * e)) ^ 2 +
          hs.sum / (2 * L) * e ^ 2
  | [], x, r, _, _, _ => by simp [run]
  | h :: t, x, r, hpos, herr, hr => by
    have hh := hpos h (by simp)
    have h0 := herr 0 (by simp)
    simp only [List.take_zero, run] at h0
    set x' := x - h • ((1 / L) • gr x) with hx'
    have hstep := psi_step b eig H hc hsym g0 (x - x0) (gr x - g0 - H (x - x0))
      (show 0 ≤ h / L by positivity)
    have hgrad := grad_step b eig H hc g0 (x - x0) (gr x - g0 - H (x - x0))
      (show 0 ≤ h / L by positivity)
    rw [← step_shape H L gr g0 x0 x h] at hstep hgrad
    have hgr' : r - h * e ≤ ‖uq b eig H g0 (x' - x0)‖ := by
      have : h / L * ‖H‖ * ‖gr x - g0 - H (x - x0)‖ ≤ h * e := by
        have h1 : h / L * ‖H‖ ≤ h := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hL]
          exact mul_le_mul_of_nonneg_left hH hh
        exact mul_le_mul h1 h0 (norm_nonneg _) hh
      unfold uq at hr ⊢
      linarith
    have ih := psi_run_lower hsym L hL hH gr g0 x0 he t x' (r - h * e)
      (fun h' hh' => hpos h' (List.mem_cons_of_mem _ hh'))
      (fun s hs' => by
        have := herr (s + 1) (by simp; omega)
        simpa [List.take_succ_cons, run, hx'] using this) hgr'
    simp only [run, List.sum_cons]
    rw [← hx']
    have he2 : ‖gr x - g0 - H (x - x0)‖ ^ 2 ≤ e ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h0 2
    set T := t.sum
    have hT : 0 ≤ T := List.sum_nonneg (fun h' hh' => hpos h' (List.mem_cons_of_mem _ hh'))
    have hm1 : max 0 (r - (h + T) * e) ^ 2 ≤ ‖uq b eig H g0 (x - x0)‖ ^ 2 := by
      have hm : max 0 (r - (h + T) * e) ≤ ‖uq b eig H g0 (x - x0)‖ := by
        apply max_le (norm_nonneg _)
        nlinarith [mul_nonneg (add_nonneg hh hT) he]
      exact pow_le_pow_left₀ (le_max_left _ _) hm 2
    have hm2 : max 0 (r - (h + T) * e) ^ 2 ≤ max 0 (r - h * e - T * e) ^ 2 := by
      rw [show r - h * e - T * e = r - (h + T) * e by ring]
    have hA : h / L / 2 * ‖uq b eig H g0 (x - x0)‖ ^ 2 ≥
        h / (2 * L) * max 0 (r - (h + T) * e) ^ 2 := by
      rw [show h / L / 2 = h / (2 * L) by ring]
      exact mul_le_mul_of_nonneg_left hm1 (by positivity)
    have hB : T / (2 * L) * max 0 (r - h * e - T * e) ^ 2 ≥
        T / (2 * L) * max 0 (r - (h + T) * e) ^ 2 :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    have hC : h / L / 2 * ‖gr x - g0 - H (x - x0)‖ ^ 2 ≤ h / (2 * L) * e ^ 2 := by
      rw [show h / L / 2 = h / (2 * L) by ring]
      exact mul_le_mul_of_nonneg_left he2 (by positivity)
    unfold uq at hA
    have : (h + T) / (2 * L) = h / (2 * L) + T / (2 * L) := by ring
    rw [this]
    nlinarith

end Psi

end LongTails.Proofs.AdaptiveSilverCycle
