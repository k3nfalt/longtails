import LongTails.Proofs.MatrixGeneralizedLocal
import LongTails.Algorithms.MatrixGeneralizedZO
import LongTails.Proofs.RecursiveGradientEnergy

open InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth


lemma sgn_sq (b : Bool) : sgnR b ^ 2 = 1 := by cases b <;> simp [sgnR]

lemma expect_bool (F : Bool → ℝ) : (𝔼 x : Bool, F x) = (F true + F false) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp []

noncomputable def lin {d : ℕ} (a : Fin d → ℝ) (s : Fin d → Bool) : ℝ :=
  ∑ i, a i * sgnR (s i)

lemma lin_cons {d : ℕ} (a : Fin (d + 1) → ℝ) (b : Bool) (s : Fin d → Bool) :
    lin a (Fin.cons b s) = a 0 * sgnR b + lin (fun i => a i.succ) s := by
  simp [lin, Fin.sum_univ_succ]

@[simp] lemma sgn_true : sgnR true = 1 := by simp [sgnR]

@[simp] lemma sgn_false : sgnR false = -1 := by simp [sgnR]

lemma expect_lin {d : ℕ} (a : Fin d → ℝ) : (𝔼 s : Fin d → Bool, lin a s) = 0 := by
  induction d with
  | zero => simp [lin]
  | succ d ih =>
    rw [NonconvexFiniteSum.expect_function_succ, Finset.expect_comm]
    simp only [expect_bool, lin_cons, sgn_true, sgn_false]
    trans (𝔼 t : Fin d → Bool, lin (fun i => a i.succ) t)
    · apply Finset.expect_congr rfl; intro t _; ring
    · exact ih _

lemma expect_lin_mul {d : ℕ} (a b : Fin d → ℝ) :
    (𝔼 s : Fin d → Bool, lin a s * lin b s) = ∑ i, a i * b i := by
  induction d with
  | zero => simp [lin]
  | succ d ih =>
    rw [NonconvexFiniteSum.expect_function_succ, Finset.expect_comm]
    simp only [expect_bool, lin_cons, sgn_true, sgn_false]
    trans (𝔼 t : Fin d → Bool,
      (a 0 * b 0 + lin (fun i => a i.succ) t * lin (fun i => b i.succ) t))
    · apply Finset.expect_congr rfl; intro t _; ring
    · rw [Finset.expect_add_distrib, Fintype.expect_const, ih, Fin.sum_univ_succ]

lemma expect_lin_four {d : ℕ} (a b c e : Fin d → ℝ) :
    (𝔼 s : Fin d → Bool, lin a s * lin b s * lin c s * lin e s) =
      (∑ i, a i * b i) * (∑ i, c i * e i) + (∑ i, a i * c i) * (∑ i, b i * e i) +
        (∑ i, a i * e i) * (∑ i, b i * c i) - 2 * ∑ i, a i * b i * c i * e i := by
  induction d with
  | zero => simp [lin]
  | succ d ih =>
    rw [NonconvexFiniteSum.expect_function_succ, Finset.expect_comm]
    simp only [expect_bool, lin_cons, sgn_true, sgn_false]
    set A := fun t : Fin d → Bool => lin (fun i => a i.succ) t
    set B := fun t : Fin d → Bool => lin (fun i => b i.succ) t
    set C := fun t : Fin d → Bool => lin (fun i => c i.succ) t
    set E := fun t : Fin d → Bool => lin (fun i => e i.succ) t
    trans (𝔼 t : Fin d → Bool,
      (a 0 * b 0 * c 0 * e 0 + a 0 * b 0 * (C t * E t) + a 0 * c 0 * (B t * E t) +
        a 0 * e 0 * (B t * C t) + b 0 * c 0 * (A t * E t) + b 0 * e 0 * (A t * C t) +
        c 0 * e 0 * (A t * B t) + A t * B t * C t * E t))
    · apply Finset.expect_congr rfl; intro t _; ring
    · simp only [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect]
      simp only [A, B, C, E, expect_lin_mul, ih, Fin.sum_univ_succ]
      ring


lemma inner_eq_sum {d : ℕ} (g w : Point d) : ⟪g, w⟫ = ∑ i, g i * w i := by
  simp [PiLp.inner_apply, mul_comm]

lemma norm_sq_eq_sum {d : ℕ} (g : Point d) : ‖g‖ ^ 2 = ∑ i, g i * g i := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]

lemma inner_vec {d : ℕ} (g : Point d) (s : Fin d → Bool) : ⟪g, signVec s⟫ = lin (fun i => g i) s := by
  simp [signVec, lin, PiLp.inner_apply, mul_comm]

lemma norm_vec_sq {d : ℕ} (s : Fin d → Bool) : ‖signVec s‖ ^ 2 = d := by
  rw [← real_inner_self_eq_norm_sq, inner_vec]
  simp [lin, signVec, ← sq, sgn_sq]

lemma expect_inner_vec_mul {d : ℕ} (g w : Point d) :
    (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ * ⟪w, signVec s⟫) = ⟪g, w⟫ := by
  simp only [inner_vec, expect_lin_mul]
  simp [PiLp.inner_apply, mul_comm]

lemma expect_inner_vec_sq {d : ℕ} (g : Point d) :
    (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ ^ 2) = ‖g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← expect_inner_vec_mul]
  simp [sq]

lemma expect_inner_vec_four {d : ℕ} (g : Point d) :
    (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ ^ 4) ≤ 3 * (‖g‖ ^ 2) ^ 2 := by
  have h := expect_lin_four (fun i => g i) (fun i => g i) (fun i => g i) (fun i => g i)
  have hn : ‖g‖ ^ 2 = ∑ i, g i * g i := norm_sq_eq_sum g
  have h4 : 0 ≤ ∑ i, g i * g i * g i * g i :=
    Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (g i * g i)]
  simp only [inner_vec]
  have e : ∀ s, lin (fun i => g i) s ^ 4 =
      lin (fun i => g i) s * lin (fun i => g i) s * lin (fun i => g i) s *
        lin (fun i => g i) s := fun s => by ring
  simp only [e, h, hn]
  linarith

section Quadratic

variable {d : ℕ} {H : Point d →L[ℝ] Point d}

noncomputable def ebasis (k : Fin d) : Point d := EuclideanSpace.single k 1

lemma quad_vec (hS : ∀ v w, ⟪H v, w⟫ = ⟪v, H w⟫) (s : Fin d → Bool) :
    ⟪H (signVec s), signVec s⟫ = ∑ k, lin (fun i => H (ebasis k) i) s * sgnR (s k) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (H (signVec s)) k = ⟪H (signVec s), ebasis k⟫ := by
    simp [ebasis, PiLp.inner_apply]
  rw [RCLike.inner_apply, conj_trivial, hk, hS, real_inner_comm, inner_vec]
  simp [signVec, mul_comm]

lemma expect_quad (hS : ∀ v w, ⟪H v, w⟫ = ⟪v, H w⟫) :
    (𝔼 s : Fin d → Bool, ⟪H (signVec s), signVec s⟫) = ∑ k, ⟪H (ebasis k), ebasis k⟫ := by
  simp only [quad_vec hS]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hsk : ∀ s : Fin d → Bool, sgnR (s k) = lin (fun i => (ebasis k : Point d) i) s := by
    intro s
    simp [lin, ebasis]
  simp only [hsk, expect_lin_mul]
  simp [ebasis, PiLp.inner_apply]

lemma expect_inner_sq_quad (hS : ∀ v w, ⟪H v, w⟫ = ⟪v, H w⟫)
    (hdiag : ∀ k, 0 ≤ ⟪H (ebasis k), ebasis k⟫) (g : Point d) :
    (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ ^ 2 * ⟪H (signVec s), signVec s⟫) ≤
      ‖g‖ ^ 2 * (∑ k, ⟪H (ebasis k), ebasis k⟫) + 2 * ⟪H g, g⟫ := by
  have hsk : ∀ (k : Fin d) (s : Fin d → Bool),
      sgnR (s k) = lin (fun i => (ebasis k : Point d) i) s := by
    intro k s
    simp [lin, ebasis]
  have hb : ∀ (k : Fin d) (a : Fin d → ℝ), (∑ i, a i * (ebasis k : Point d) i) = a k := by
    intro k a; simp [ebasis]
  have hdk : ∀ k, H (ebasis k) k = ⟪H (ebasis k), ebasis k⟫ := by
    intro k; rw [inner_eq_sum, hb k (fun i => H (ebasis k) i)]
  have hgk : ∀ k, (∑ i, g i * H (ebasis k) i) = ⟪H g, ebasis k⟫ := by
    intro k
    rw [hS, ← inner_eq_sum]
  have hHg : ∑ k, ⟪H g, ebasis k⟫ * g k = ⟪H g, g⟫ := by
    rw [inner_eq_sum (H g) g]
    apply Finset.sum_congr rfl; intro k _
    rw [inner_eq_sum, hb k (fun i => H g i)]
  have hterm : ∀ k, (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ ^ 2 * (lin (fun i => H (ebasis k) i) s *
      sgnR (s k))) = ‖g‖ ^ 2 * ⟪H (ebasis k), ebasis k⟫ + 2 * (⟪H g, ebasis k⟫ * g k) -
        2 * (g k * g k * ⟪H (ebasis k), ebasis k⟫) := by
    intro k
    trans (𝔼 s : Fin d → Bool, lin (fun i => g i) s * lin (fun i => g i) s *
      lin (fun i => H (ebasis k) i) s * lin (fun i => (ebasis k : Point d) i) s)
    · apply Finset.expect_congr rfl; intro s _
      rw [hsk k s, inner_vec]; ring
    · rw [expect_lin_four]
      simp only [hb]
      rw [← norm_sq_eq_sum, hgk, hdk]
      ring
  have hsplit : (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ ^ 2 * ⟪H (signVec s), signVec s⟫) =
      ∑ k, (𝔼 s : Fin d → Bool, ⟪g, signVec s⟫ ^ 2 * (lin (fun i => H (ebasis k) i) s *
        sgnR (s k))) := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl; intro s _
    rw [quad_vec hS, Finset.mul_sum]
  rw [hsplit]
  simp only [hterm]
  have hneg : 0 ≤ ∑ k, g k * g k * ⟪H (ebasis k), ebasis k⟫ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (mul_self_nonneg (g k)) (hdiag k)
  have h1 : ∑ k, (‖g‖ ^ 2 * ⟪H (ebasis k), ebasis k⟫ + 2 * (⟪H g, ebasis k⟫ * g k) -
      2 * (g k * g k * ⟪H (ebasis k), ebasis k⟫)) =
      ‖g‖ ^ 2 * (∑ k, ⟪H (ebasis k), ebasis k⟫) + 2 * (∑ k, ⟪H g, ebasis k⟫ * g k) -
        2 * ∑ k, g k * g k * ⟪H (ebasis k), ebasis k⟫ := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
  rw [h1, hHg]
  linarith

end Quadratic

end OracleTemplate.MatrixGeneralizedZO
