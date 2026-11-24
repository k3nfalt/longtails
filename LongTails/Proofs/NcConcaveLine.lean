import LongTails.Proofs.NcConcavePsi
import Mathlib.Analysis.Calculus.Deriv.Inv

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveLine

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi

variable {n : ℕ}

lemma line_coord (x v : ℝ) : HasDerivAt (fun t : ℝ => x + t * v) v 0 := by
  have h := HasDerivAt.const_add x (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) v)
  simpa using h

lemma nu_line (x v : ℝ) : HasDerivAt (fun t : ℝ => nu (x + t * v)) (dnu x * v) 0 := by
  have h : HasDerivAt (fun t : ℝ => nu (x + t * v)) (dnu (x + 0 * v) * v) 0 :=
    hasDerivAt_of_model (C := 3 * v ^ 2) (fun s s' => by
      have := nu_model (x + s * v) (x + s' * v)
      have e1 : x + s' * v - (x + s * v) = (s' - s) * v := by ring
      rw [e1] at this
      have e2 : 3 * ((s' - s) * v) ^ 2 = 3 * v ^ 2 * (s' - s) ^ 2 := by ring
      rw [e2] at this
      have e3 : dnu (x + s * v) * ((s' - s) * v) = dnu (x + s * v) * v * (s' - s) := by ring
      rw [e3] at this
      exact this) 0
  simpa using h

lemma rr_line (x v : ℝ) : HasDerivAt (fun t : ℝ => rr (x + t * v)) (drr x * v) 0 := by
  have h : HasDerivAt (fun t : ℝ => rr (x + t * v)) (drr (x + 0 * v) * v) 0 :=
    hasDerivAt_of_model (C := v ^ 2) (fun s s' => by
      have := rr_model (x + s * v) (x + s' * v)
      have e1 : x + s' * v - (x + s * v) = (s' - s) * v := by ring
      rw [e1] at this
      have e2 : 1 * ((s' - s) * v) ^ 2 = v ^ 2 * (s' - s) ^ 2 := by ring
      rw [e2] at this
      have e3 : drr (x + s * v) * ((s' - s) * v) = drr (x + s * v) * v * (s' - s) := by ring
      rw [e3] at this
      exact this) 0
  simpa using h

lemma q_line (u v : Fin (n + 1) → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => q (fun j => u j + t * v j) i) (dq u v i) 0 := by
  have h1 := nu_line (u i.castSucc) (v i.castSucc)
  have h2 := nu_line (u i.succ) (v i.succ)
  have h := HasDerivAt.mul h1 (HasDerivAt.const_sub 1 h2)
  unfold q dq
  convert h using 1
  simp only [zero_mul, add_zero]
  ring

lemma sq2q_line (u v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => sq2 (q (fun j => u j + t * v j)))
      (∑ i, 2 * q u i * dq u v i) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.pow (q_line u v i) 2)
  unfold sq2
  convert h using 1
  apply Finset.sum_congr rfl; intro i _
  have e : (fun j => u j + 0 * v j) = u := by funext j; simp
  simp only [e, Nat.cast_ofNat]
  ring

lemma nrm_line (u v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => nrm (fun j => u j + t * v j))
      ((∑ i, q u i * dq u v i) / nrm u) 0 := by
  have e : (fun j => u j + 0 * v j) = u := by funext j; simp
  have h0 : 1 + sq2 (q (fun j => u j + 0 * v j)) ≠ 0 := by
    rw [e]; linarith [sq2_nonneg (q u)]
  have h := HasDerivAt.sqrt (HasDerivAt.const_add 1 (sq2q_line u v)) h0
  unfold nrm
  convert h using 1
  rw [e]
  have hp := nrm_pos u
  have h2 : (∑ i, 2 * q u i * dq u v i) = 2 * ∑ i, q u i * dq u v i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  have hs : 0 < Real.sqrt (1 + sq2 (q u)) := hp
  field_simp

lemma rho_line (u v : Fin (n + 1) → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => rho (fun j => u j + t * v j) i) (drho u v i) 0 := by
  have e : (fun j => u j + 0 * v j) = u := by funext j; simp
  have hn : nrm (fun j => u j + 0 * v j) ≠ 0 := (nrm_pos _).ne'
  have h := HasDerivAt.div (q_line u v i) (nrm_line u v) hn
  unfold rho
  convert h using 1
  rw [e]
  unfold drho
  have hp := nrm_pos u
  field_simp

lemma sumsq_line {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ) (f' : ι → ℝ)
    (hf : ∀ i, HasDerivAt (f i) (f' i) 0) :
    HasDerivAt (fun t => ∑ i, f i t ^ 2) (∑ i, 2 * f i 0 * f' i) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.pow (hf i) 2)
  convert h using 1
  apply Finset.sum_congr rfl; intro i _
  simp only [Nat.cast_ofNat]
  ring

lemma hpart_line (u v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => hpart (fun j => u j + t * v j)) (dhpart u v) 0 := by
  have h0 := line_coord (u 0) (v 0)
  have h1 := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun j _ => nu_line (u j.succ) (v j.succ))
  have h2 := sumsq_line (fun j t => rr (u j + t * v j)) (fun j => drr (u j) * v j)
    (fun j => rr_line (u j) (v j))
  have h := ((HasDerivAt.const_mul (-cη) h0).sub (HasDerivAt.const_mul cη h1)).add
    (HasDerivAt.const_mul (cη / 2) h2)
  unfold hpart dhpart
  convert h using 1
  simp only [zero_mul, add_zero]
  have e : cη * ∑ j, rr (u j) * drr (u j) * v j = cη / 2 * ∑ j, 2 * rr (u j) * (drr (u j) * v j) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]

noncomputable def psiTerm (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 / 2) * (a i - rho u i) ^ 2 + (1 / 2) * (b i - rb u i) ^ 2 + (1 / 2) * a i ^ 2 +
    (1 / 2) * b i ^ 2 + (1 / 2) * (a i - b i / 2) ^ 2

lemma psi_sum (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) :
    psi u a b = hpart u + ∑ i, psiTerm u a b i := by
  simp only [psi, psiTerm, Finset.mul_sum, Finset.sum_add_distrib]
  ring

lemma psiTerm_line (u du : Fin (n + 1) → ℝ) (a b da db : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => psiTerm (fun j => u j + t * du j) (fun i => a i + t * da i)
      (fun i => b i + t * db i) i)
      ((a i - rho u i) * (da i - drho u du i) + (b i - rb u i) * (db i - drr (u i.succ) * du i.succ) +
        a i * da i + b i * db i + (a i - b i / 2) * (da i - db i / 2)) 0 := by
  have hA := HasDerivAt.fun_pow (HasDerivAt.fun_sub (line_coord (a i) (da i)) (rho_line u du i)) 2
  have hB := HasDerivAt.fun_pow
    (HasDerivAt.fun_sub (line_coord (b i) (db i)) (rr_line (u i.succ) (du i.succ))) 2
  have ha := HasDerivAt.fun_pow (line_coord (a i) (da i)) 2
  have hb := HasDerivAt.fun_pow (line_coord (b i) (db i)) 2
  have hab := HasDerivAt.fun_pow (HasDerivAt.fun_sub (line_coord (a i) (da i))
    (HasDerivAt.div_const (line_coord (b i) (db i)) 2)) 2
  have h := HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add
    (HasDerivAt.const_mul (1 / 2) hA) (HasDerivAt.const_mul (1 / 2) hB))
    (HasDerivAt.const_mul (1 / 2) ha)) (HasDerivAt.const_mul (1 / 2) hb))
    (HasDerivAt.const_mul (1 / 2) hab)
  have e0 : (fun j => u j + 0 * du j) = u := by funext j; simp
  unfold psiTerm
  convert h using 1
  · funext t; simp only [rb]
  · simp only [zero_mul, add_zero, rb]
    norm_num
    ring

lemma psi_line (u du : Fin (n + 1) → ℝ) (a b da db : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => psi (fun j => u j + t * du j) (fun i => a i + t * da i)
      (fun i => b i + t * db i))
      (dpsiU u a b du + ∑ i, ((gab u a b i).1 * da i + (gab u a b i).2 * db i)) 0 := by
  have hH := hpart_line u du
  have hS := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => psiTerm_line u du a b da db i)
  have h := hH.add hS
  have he : (fun t : ℝ => psi (fun j => u j + t * du j) (fun i => a i + t * da i)
      (fun i => b i + t * db i)) = fun t => hpart (fun j => u j + t * du j) +
        ∑ i, psiTerm (fun j => u j + t * du j) (fun i => a i + t * da i) (fun i => b i + t * db i) i := by
    funext t; rw [psi_sum]
  rw [he]
  convert h using 1
  have e1 : dpsiU u a b du + ∑ i, ((gab u a b i).1 * da i + (gab u a b i).2 * db i) =
      dhpart u du + ∑ i, (-((a i - rho u i) * drho u du i) - (b i - rb u i) * (drr (u i.succ) * du i.succ) +
        ((gab u a b i).1 * da i + (gab u a b i).2 * db i)) := by
    unfold dpsiU
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [e1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gab]
  ring

end LongTails.Proofs.NcConcaveLine
