import LongTails.Proofs.NcConcaveC11
import LongTails.Proofs.NcConcavePhi

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveRhoModel

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars
open LongTails.Proofs.NcConcaveTransitions LongTails.Proofs.NcConcaveTransitionBounds
open LongTails.Proofs.NcConcavePartTwo LongTails.Proofs.NcConcaveGadgets
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveC11 LongTails.Proofs.NcConcavePhi

variable {n : ℕ}

noncomputable def zd (θ : ℝ) (u du : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => dzeta θ (u j) * du j

noncomputable def dRho (θ : ℝ) (u du : Fin (n + 1) → ℝ) : Fin n → ℝ := drho (zu θ u) (zd θ u du)

lemma sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i ∈ s, x i ^ 2 ≤ (∑ i ∈ s, x i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    nlinarith [hx k]

lemma nuz_lip {θ : ℝ} (hθ : 0 < θ) (x y : ℝ) :
    |nu (zeta θ x) - nu (zeta θ y)| ≤ 3 / 2 * |x - y| :=
  (nu_lipschitz _ _).trans (mul_le_mul_of_nonneg_left (zeta_lip hθ x y) (by norm_num))

lemma qz_lip {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    sq2 (fun i => q (zu θ u') i - q (zu θ u) i) ≤ 9 * sq1 (fun j => u' j - u j) := by
  have hpt : ∀ i : Fin n, (q (zu θ u') i - q (zu θ u) i) ^ 2 ≤
      9 / 2 * ((u' i.castSucc - u i.castSucc) ^ 2 + (u' i.succ - u i.succ) ^ 2) := by
    intro i
    simp only [q, zu]
    set A := nu (zeta θ (u i.castSucc))
    set A' := nu (zeta θ (u' i.castSucc))
    set B := nu (zeta θ (u i.succ))
    set B' := nu (zeta θ (u' i.succ))
    have hA := nu_le_one (zeta θ (u' i.castSucc))
    have hA0 := nu_nonneg (zeta θ (u' i.castSucc))
    have hB := nu_le_one (zeta θ (u i.succ))
    have hB0 := nu_nonneg (zeta θ (u i.succ))
    have l1 := nuz_lip hθ (u' i.castSucc) (u i.castSucc)
    have l2 := nuz_lip hθ (u' i.succ) (u i.succ)
    have e : A' * (1 - B') - A * (1 - B) = (A' - A) * (1 - B) - A' * (B' - B) := by ring
    rw [e]
    have hb : |(A' - A) * (1 - B) - A' * (B' - B)| ≤
        3 / 2 * |u' i.castSucc - u i.castSucc| + 3 / 2 * |u' i.succ - u i.succ| := by
      calc _ ≤ |(A' - A) * (1 - B)| + |A' * (B' - B)| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - B), abs_of_nonneg hA0]
          apply add_le_add
          · calc |A' - A| * (1 - B) ≤ |A' - A| * 1 :=
                  mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
              _ ≤ _ := by linarith
          · calc A' * |B' - B| ≤ 1 * |B' - B| := mul_le_mul_of_nonneg_right hA (abs_nonneg _)
              _ ≤ _ := by linarith
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at h2
    have := sq_abs (u' i.castSucc - u i.castSucc)
    have := sq_abs (u' i.succ - u i.succ)
    nlinarith [sq_nonneg (|u' i.castSucc - u i.castSucc| - |u' i.succ - u i.succ|)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hpt i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  have c1 := sum_castSucc_le (fun j => u' j - u j)
  have c2 := sum_succ_le (fun j => u' j - u j)
  unfold sq2
  linarith

lemma qz_model {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    sq2 (fun i => q (zu θ u') i - q (zu θ u) i - dq (zu θ u) (zd θ u (fun j => u' j - u j)) i) ≤
      2116 * sq1 (fun j => u' j - u j) ^ 2 := by
  have hm := nuz_model hθ
  have hpt : ∀ i : Fin n, |q (zu θ u') i - q (zu θ u) i - dq (zu θ u) (zd θ u (fun j => u' j - u j)) i| ≤
      23 * ((u' i.castSucc - u i.castSucc) ^ 2 + (u' i.succ - u i.succ) ^ 2) := by
    intro i
    simp only [q, dq, zu, zd]
    set A := nu (zeta θ (u i.castSucc))
    set A' := nu (zeta θ (u' i.castSucc))
    set B := nu (zeta θ (u i.succ))
    set B' := nu (zeta θ (u' i.succ))
    set dA := dnu (zeta θ (u i.castSucc)) * dzeta θ (u i.castSucc)
    set dB := dnu (zeta θ (u i.succ)) * dzeta θ (u i.succ)
    set x1 := u' i.castSucc - u i.castSucc
    set x2 := u' i.succ - u i.succ
    have e : A' * (1 - B') - A * (1 - B) -
        (dnu (zeta θ (u i.castSucc)) * (dzeta θ (u i.castSucc) * x1) * (1 - B) -
          A * (dnu (zeta θ (u i.succ)) * (dzeta θ (u i.succ) * x2))) =
        (1 - B) * (A' - A - dA * x1) - A * (B' - B - dB * x2) - (A' - A) * (B' - B) := by
      simp only [dA, dB]; ring
    rw [e]
    have m1 := hm (u i.castSucc) (u' i.castSucc)
    have m2 := hm (u i.succ) (u' i.succ)
    have hB := nu_le_one (zeta θ (u i.succ))
    have hB0 := nu_nonneg (zeta θ (u i.succ))
    have hA := nu_le_one (zeta θ (u i.castSucc))
    have hA0 := nu_nonneg (zeta θ (u i.castSucc))
    have l1 := nuz_lip hθ (u' i.castSucc) (u i.castSucc)
    have l2 := nuz_lip hθ (u' i.succ) (u i.succ)
    have p1 : |(1 - B) * (A' - A - dA * x1)| ≤ 21 * x1 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - B)]
      calc _ ≤ 1 * (21 * x1 ^ 2) := mul_le_mul (by linarith) m1 (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have p2 : |A * (B' - B - dB * x2)| ≤ 21 * x2 ^ 2 := by
      rw [abs_mul, abs_of_nonneg hA0]
      calc _ ≤ 1 * (21 * x2 ^ 2) := mul_le_mul hA m2 (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    have p3 : |(A' - A) * (B' - B)| ≤ 3 / 2 * |x1| * (3 / 2 * |x2|) := by
      rw [abs_mul]; exact mul_le_mul l1 l2 (abs_nonneg _) (by positivity)
    have hc : |x1| * |x2| ≤ (x1 ^ 2 + x2 ^ 2) / 2 := by
      rw [← sq_abs x1, ← sq_abs x2]; nlinarith [sq_nonneg (|x1| - |x2|)]
    calc _ ≤ |(1 - B) * (A' - A - dA * x1) - A * (B' - B - dB * x2)| + |(A' - A) * (B' - B)| :=
          abs_sub _ _
      _ ≤ |(1 - B) * (A' - A - dA * x1)| + |A * (B' - B - dB * x2)| + |(A' - A) * (B' - B)| := by
          linarith [abs_sub ((1 - B) * (A' - A - dA * x1)) (A * (B' - B - dB * x2))]
      _ ≤ 21 * x1 ^ 2 + 21 * x2 ^ 2 + 3 / 2 * |x1| * (3 / 2 * |x2|) := by linarith
      _ ≤ _ := by nlinarith [abs_nonneg x1, abs_nonneg x2]
  set E : Fin n → ℝ := fun i =>
    q (zu θ u') i - q (zu θ u) i - dq (zu θ u) (zd θ u (fun j => u' j - u j)) i
  have h1 : sq2 E ≤ ∑ i : Fin n, (23 * ((u' i.castSucc - u i.castSucc) ^ 2 +
      (u' i.succ - u i.succ) ^ 2)) ^ 2 := by
    unfold sq2
    apply Finset.sum_le_sum; intro i _
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpt i) 2
  have h2 := sum_sq_le_sq_sum Finset.univ (fun i : Fin n => 23 * ((u' i.castSucc - u i.castSucc) ^ 2 +
      (u' i.succ - u i.succ) ^ 2)) (fun i => by positivity)
  have h3 : ∑ i : Fin n, 23 * ((u' i.castSucc - u i.castSucc) ^ 2 + (u' i.succ - u i.succ) ^ 2) ≤
      46 * sq1 (fun j => u' j - u j) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have c1 := sum_castSucc_le (fun j => u' j - u j)
    have c2 := sum_succ_le (fun j => u' j - u j)
    linarith
  have h4 : 0 ≤ ∑ i : Fin n, 23 * ((u' i.castSucc - u i.castSucc) ^ 2 + (u' i.succ - u i.succ) ^ 2) :=
    Finset.sum_nonneg fun i _ => by positivity
  have h5 := pow_le_pow_left₀ h4 h3 2
  calc sq2 E ≤ _ := h1.trans h2
    _ ≤ (46 * sq1 (fun j => u' j - u j)) ^ 2 := h5
    _ = _ := by ring

lemma dphiN_sub (z h h' : Fin n → ℝ) :
    (fun i => dphiN z h i - dphiN z h' i) = dphiN z (fun i => h i - h' i) := by
  funext i
  simp only [dphiN, mul_sub, Finset.sum_sub_distrib]
  ring

theorem rhoz_model {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    sq2 (fun i => rho (zu θ u') i - rho (zu θ u) i - dRho θ u (fun j => u' j - u j) i) ≤
      10816 * sq1 (fun j => u' j - u j) ^ 2 := by
  set z := q (zu θ u)
  set z' := q (zu θ u')
  set h := dq (zu θ u) (zd θ u (fun j => u' j - u j))
  have e : (fun i => rho (zu θ u') i - rho (zu θ u) i - dRho θ u (fun j => u' j - u j) i) =
      fun i => (phiN z' i - phiN z i - dphiN z (fun j => z' j - z j) i) +
        dphiN z (fun j => z' j - z j - h j) i := by
    funext i
    have h1 : dRho θ u (fun j => u' j - u j) i = dphiN z h i := rfl
    have h2 : dphiN z (fun j => z' j - z j) i - dphiN z h i = dphiN z (fun j => z' j - z j - h j) i :=
      congrFun (dphiN_sub z (fun j => z' j - z j) h) i
    have h3 : rho (zu θ u') i = phiN z' i := rfl
    have h4 : rho (zu θ u) i = phiN z i := rfl
    rw [h3, h4, h1, ← h2]
    ring
  rw [e]
  refine (sq2_add_le _ _).trans ?_
  have m1 := phiN_model z z'
  have m2 := sq2_dphiN_le z (fun j => z' j - z j - h j)
  have m3 := qz_model hθ u u'
  have l1 := qz_lip hθ u u'
  have hS := sq1_nonneg (fun j => u' j - u j)
  have hq0 := sq2_nonneg (fun j => z' j - z j)
  have hsq : sq2 (fun j => z' j - z j) ^ 2 ≤ (9 * sq1 (fun j => u' j - u j)) ^ 2 :=
    pow_le_pow_left₀ hq0 l1 2
  have m3' : sq2 (fun j => z' j - z j - h j) ≤ 2116 * sq1 (fun j => u' j - u j) ^ 2 := m3
  nlinarith

theorem rhoz_lip {θ : ℝ} (hθ : 0 < θ) (u u' : Fin (n + 1) → ℝ) :
    sq2 (fun i => rho (zu θ u') i - rho (zu θ u) i) ≤ 36 * sq1 (fun j => u' j - u j) := by
  have h1 := phiN_lip (q (zu θ u')) (q (zu θ u))
  have h2 := qz_lip hθ u u'
  simp only [← rho_eq_phiN] at h1
  linarith

lemma sq2_dRho_le {θ : ℝ} (hθ : 0 < θ) (u du : Fin (n + 1) → ℝ) :
    sq2 (dRho θ u du) ≤ 9 * sq1 du := by
  have h1 := sq2_drho_le_nine (zu θ u) (zd θ u du)
  have h2 : sq1 (zd θ u du) ≤ sq1 du := by
    unfold sq1 zd
    apply Finset.sum_le_sum; intro j _
    rw [mul_pow]
    have := dzeta_abs hθ (u j)
    have h' : dzeta θ (u j) ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) this
    nlinarith [sq_nonneg (du j)]
  unfold dRho; linarith

lemma dRho_add {θ : ℝ} (u v w : Fin (n + 1) → ℝ) (i : Fin n) :
    dRho θ u (v + w) i = dRho θ u v i + dRho θ u w i := by
  have : zd θ u (v + w) = zd θ u v + zd θ u w := by
    funext j; simp only [zd, Pi.add_apply]; ring
  simp only [dRho, this, drho_add]

lemma dRho_smul {θ : ℝ} (u v : Fin (n + 1) → ℝ) (c : ℝ) (i : Fin n) :
    dRho θ u (c • v) i = c * dRho θ u v i := by
  have : zd θ u (c • v) = c • zd θ u v := by
    funext j; simp only [zd, Pi.smul_apply, smul_eq_mul]; ring
  simp only [dRho, this, drho_smul]

end LongTails.Proofs.NcConcaveRhoModel
