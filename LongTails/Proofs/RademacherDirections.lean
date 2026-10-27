import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.RademacherDirections

def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

noncomputable def lin {d : ℕ} (a : Fin d → ℝ) (s : Fin d → Bool) : ℝ := ∑ i, a i * sgn (s i)

lemma lin_succ {d : ℕ} (a : Fin (d + 1) → ℝ) (b : Bool) (s : Fin d → Bool) :
    lin a (Fin.cons b s) = a 0 * sgn b + lin (fun i => a i.succ) s := by
  simp [lin, Fin.sum_univ_succ]

lemma sum_cons {d : ℕ} (h : (Fin (d + 1) → Bool) → ℝ) :
    ∑ s, h s = ∑ s : Fin d → Bool, (h (Fin.cons true s) + h (Fin.cons false s)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.univ_bool, Finset.sum_insert (by decide : true ∉ ({false} : Finset Bool)),
    Finset.sum_singleton]
  rw [Finset.sum_add_distrib]
  rfl

lemma sum_lin_mul {d : ℕ} (a b : Fin d → ℝ) :
    ∑ s, lin a s * lin b s = 2 ^ d * ∑ i, a i * b i := by
  induction d with
  | zero => simp [lin]
  | succ d ih =>
      rw [sum_cons]
      simp only [lin_succ, sgn, ite_true, Bool.false_eq_true, ite_false]
      have h := ih (fun i => a i.succ) (fun i => b i.succ)
      have e : ∀ s : Fin d → Bool,
          (a 0 * 1 + lin (fun i => a i.succ) s) * (b 0 * 1 + lin (fun i => b i.succ) s) +
            (a 0 * -1 + lin (fun i => a i.succ) s) * (b 0 * -1 + lin (fun i => b i.succ) s) =
          2 * (a 0 * b 0) + 2 * (lin (fun i => a i.succ) s * lin (fun i => b i.succ) s) := by
        intro s; ring
      simp_rw [e]
      have hc : ∑ s : Fin d → Bool, (2 : ℝ) * (a 0 * b 0) = 2 ^ d * (2 * (a 0 * b 0)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
      have hm : ∑ s : Fin d → Bool, (2 : ℝ) * (lin (fun i => a i.succ) s * lin (fun i => b i.succ) s) =
          2 * (2 ^ d * ∑ i : Fin d, a i.succ * b i.succ) := by
        rw [← Finset.mul_sum, h]
      rw [Finset.sum_add_distrib, hc, hm, Fin.sum_univ_succ]
      ring

lemma sum_lin_sq_mul_sq {d : ℕ} (a b : Fin d → ℝ) :
    ∑ s, lin a s ^ 2 * lin b s ^ 2 ≤
      2 ^ d * ((∑ i, a i ^ 2) * (∑ i, b i ^ 2) + 2 * (∑ i, a i * b i) ^ 2) := by
  induction d with
  | zero => simp [lin]
  | succ d ih =>
      rw [sum_cons]
      simp only [lin_succ, sgn, ite_true, Bool.false_eq_true, ite_false]
      set a' : Fin d → ℝ := fun i => a i.succ
      set b' : Fin d → ℝ := fun i => b i.succ
      have h4 := ih a' b'
      have hab := sum_lin_mul a' b'
      have haa := sum_lin_mul a' a'
      have hbb := sum_lin_mul b' b'
      have e : ∀ s : Fin d → Bool,
          (a 0 * 1 + lin a' s) ^ 2 * (b 0 * 1 + lin b' s) ^ 2 +
            (a 0 * -1 + lin a' s) ^ 2 * (b 0 * -1 + lin b' s) ^ 2 =
          2 * (a 0 ^ 2 * b 0 ^ 2) + 2 * a 0 ^ 2 * (lin b' s * lin b' s) +
            2 * b 0 ^ 2 * (lin a' s * lin a' s) + 2 * (lin a' s ^ 2 * lin b' s ^ 2) +
            8 * (a 0 * b 0) * (lin a' s * lin b' s) := by
        intro s; ring
      simp_rw [e]
      have hpow : (0 : ℝ) < 2 ^ d := by positivity
      set A := ∑ i, a' i ^ 2
      set B := ∑ i, b' i ^ 2
      set C := ∑ i, a' i * b' i
      have hA : ∑ i, a' i * a' i = A := by simp [A, sq]
      have hB : ∑ i, b' i * b' i = B := by simp [B, sq]
      have hc : ∑ s : Fin d → Bool, (2 : ℝ) * (a 0 ^ 2 * b 0 ^ 2) = 2 ^ d * (2 * (a 0 ^ 2 * b 0 ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
      have h1 : ∑ s : Fin d → Bool, 2 * a 0 ^ 2 * (lin b' s * lin b' s) = 2 * a 0 ^ 2 * (2 ^ d * B) := by
        rw [← Finset.mul_sum, hbb, hB]
      have h2 : ∑ s : Fin d → Bool, 2 * b 0 ^ 2 * (lin a' s * lin a' s) = 2 * b 0 ^ 2 * (2 ^ d * A) := by
        rw [← Finset.mul_sum, haa, hA]
      have h3 : ∑ s : Fin d → Bool, 2 * (lin a' s ^ 2 * lin b' s ^ 2) ≤ 2 * (2 ^ d * (A * B + 2 * C ^ 2)) := by
        rw [← Finset.mul_sum]; linarith
      have h5 : ∑ s : Fin d → Bool, 8 * (a 0 * b 0) * (lin a' s * lin b' s) = 8 * (a 0 * b 0) * (2 ^ d * C) := by
        rw [← Finset.mul_sum, hab]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, hc, h1, h2, h5]
      have hsa : ∑ i, a i ^ 2 = a 0 ^ 2 + A := by rw [Fin.sum_univ_succ]
      have hsb : ∑ i, b i ^ 2 = b 0 ^ 2 + B := by rw [Fin.sum_univ_succ]
      have hsc : ∑ i, a i * b i = a 0 * b 0 + C := by rw [Fin.sum_univ_succ]
      rw [hsa, hsb, hsc, show (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d by ring]
      nlinarith [h3, mul_nonneg hpow.le (sq_nonneg (a 0 * b 0))]

lemma sum_lin_sq {d : ℕ} (a : Fin d → ℝ) : ∑ s, lin a s ^ 2 = 2 ^ d * ∑ i, a i ^ 2 := by
  have := sum_lin_mul a a
  simpa [sq] using this

end LongTails.Proofs.RademacherDirections
