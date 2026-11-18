import LongTails.Proofs.SampleLossMixture
import LongTails.Proofs.PLMinimaxImplicit
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped RealInnerProductSpace
open LongTails.Proofs.SampleLossMixture

namespace LongTails.Proofs.SampleLossCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma mixture_differentiable (a b : ℕ → E → ℝ) (ha : ∀ i, Differentiable ℝ (a i))
    (hb : ∀ i, Differentiable ℝ (b i)) (n : ℕ) :
    Differentiable ℝ (fun x => mixture (fun i => a i x) (fun i => b i x) n) := by
  induction n with
  | zero => exact differentiable_const _
  | succ n ih => exact ((differentiable_const (1 : ℝ) |>.sub (ha n)).mul ih).add ((ha n).mul (hb n))

lemma mixture_line (a b : ℕ → ℝ → ℝ) (da db : ℕ → ℝ) (t : ℝ)
    (ha : ∀ i, HasDerivAt (a i) (da i) t) (hb : ∀ i, HasDerivAt (b i) (db i) t) (n : ℕ) :
    HasDerivAt (fun s => mixture (fun i => a i s) (fun i => b i s) n)
      (tangent (fun i => a i t) (fun i => b i t) da db n) t := by
  induction n with
  | zero => exact hasDerivAt_const _ _
  | succ n ih =>
    have h := (((hasDerivAt_const t (1 : ℝ)).sub (ha n)).mul ih).add ((ha n).mul (hb n))
    convert h using 1 <;> first | rfl | (simp [tangent, variation, blend]; ring)

lemma affine_line (x v : E) : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  convert (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> first | rfl | simp

lemma derivative_line {F : E → ℝ} (x v : E) (hF : DifferentiableAt ℝ F x) :
    HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 := by
  have h : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • v) := by simpa using hF.hasFDerivAt
  exact h.comp_hasDerivAt 0 (affine_line x v)

lemma mixture_fderiv (a b : ℕ → E → ℝ) (ha : ∀ i, Differentiable ℝ (a i))
    (hb : ∀ i, Differentiable ℝ (b i)) (x v : E) (n : ℕ) :
    fderiv ℝ (fun y => mixture (fun i => a i y) (fun i => b i y) n) x v =
      tangent (fun i => a i x) (fun i => b i x)
        (fun i => fderiv ℝ (a i) x v) (fun i => fderiv ℝ (b i) x v) n := by
  have h := mixture_line (fun i t => a i (x + t • v)) (fun i t => b i (x + t • v))
    _ _ 0 (fun i => derivative_line x v (ha i x)) (fun i => derivative_line x v (hb i x)) n
  simp only [zero_smul, add_zero] at h
  exact (derivative_line x v (mixture_differentiable a b ha hb n x)).unique h

lemma grad_lipschitz_of_model {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {F : H → ℝ} {C : ℝ} (hC : 0 ≤ C) (hF : Differentiable ℝ F)
    (hmod : ∀ x v, |F (x + v) - F x - fderiv ℝ F x v| ≤ C * ‖v‖ ^ 2) (x y : H) :
    ‖gradient F x - gradient F y‖ ≤ 6 * C * ‖x - y‖ := by
  have h := OracleTemplate.PLMinimax.derivative_lipschitz_of_quadratic_remainder (G := F) (A := fderiv ℝ F) hC hmod y x
  have he (z : H) : InnerProductSpace.toDual ℝ H (gradient F z) = fderiv ℝ F z :=
    (hF z).hasGradientAt.hasFDerivAt.fderiv.symm
  rw [← he x, ← he y, ← map_sub, LinearIsometryEquiv.norm_map] at h
  exact h

end LongTails.Proofs.SampleLossCalculus
