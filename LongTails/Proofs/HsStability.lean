import LongTails.Proofs.HsChain
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.HsProfile LongTails.Proofs.HsChain Set

namespace LongTails.Proofs.HsStability

lemma gronwall_unit (φ φd : ℝ → ℝ) (c : ℝ) (hφ : ∀ t, HasDerivAt φ (φd t) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, φd t ≤ c * φ t) : φ 1 ≤ Real.exp c * φ 0 := by
  let ψ := fun t => φ t * Real.exp (-(c * t))
  have hψ : ∀ t, HasDerivAt ψ (φd t * Real.exp (-(c * t)) +
      φ t * (Real.exp (-(c * t)) * (-(c * 1)))) t := by
    intro t
    have h1 := ((hasDerivAt_id t).const_mul c).neg.exp
    exact (hφ t).mul (by simpa using h1)
  have hanti : AntitoneOn ψ (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr fun t => (hψ t).continuousAt).continuousOn
    · exact fun t _ => (hψ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψ t).deriv]
      have hb' := hb t ⟨ht.1.le, ht.2.le⟩
      have he := Real.exp_pos (-(c * t))
      nlinarith
  have h := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [ψ, mul_zero, neg_zero, Real.exp_zero, mul_one, mul_one] at h
  have he : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hec := Real.exp_pos c
  calc φ 1 = Real.exp c * (φ 1 * Real.exp (-c)) := by
        rw [← mul_assoc, mul_comm (Real.exp c), mul_assoc, he, mul_one]
    _ ≤ Real.exp c * φ 0 := mul_le_mul_of_nonneg_left h hec.le

section Algebra

variable {ι : Type*} [Fintype ι]

lemma sum_cauchy (s x y : ι → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (∑ i, s i * (x i * y i)) ^ 2 ≤ (∑ i, s i * x i ^ 2) * (∑ i, s i * y i ^ 2) :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => mul_nonneg (hs i) (sq_nonneg _)) (fun i _ => mul_nonneg (hs i) (sq_nonneg _))
    (fun i _ => le_of_eq (by ring))

lemma abs_two_mul_le (E D X W Q S Hc : ℝ) (hE : 0 ≤ E) (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hS : 0 < S)
    (hHc : Hc ≤ S ^ 2) (hX : X ^ 2 ≤ Hc * W ^ 2 * Q) :
    |2 * E * D * X| ≤ S * W * (E * D ^ 2 + E * Q) := by
  have hX2 : X ^ 2 ≤ S ^ 2 * W ^ 2 * Q := by
    have : Hc * W ^ 2 * Q ≤ S ^ 2 * W ^ 2 * Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHc (sq_nonneg W)) hQ
    linarith
  rcases hW.eq_or_lt with hW0 | hWp
  · have hX0 : X = 0 := by
      rw [← hW0] at hX2
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm (by simpa using hX2)
        (sq_nonneg X))
    rw [hX0, ← hW0]
    simp
  · have hT : 0 < S * W := mul_pos hS hWp
    have hX3 : X ^ 2 ≤ (S * W) ^ 2 * Q := by rw [mul_pow]; exact hX2
    have k1 : 0 ≤ (S * W) * ((S * W) * (E * D ^ 2 + E * Q) + 2 * E * D * X) := by
      nlinarith [mul_nonneg hE (sq_nonneg (S * W * D + X)), mul_nonneg hE (sub_nonneg.mpr hX3)]
    have k2 : 0 ≤ (S * W) * ((S * W) * (E * D ^ 2 + E * Q) - 2 * E * D * X) := by
      nlinarith [mul_nonneg hE (sq_nonneg (S * W * D - X)), mul_nonneg hE (sub_nonneg.mpr hX3)]
    have k1' := (mul_nonneg_iff_of_pos_left hT).mp k1
    have k2' := (mul_nonneg_iff_of_pos_left hT).mp k2
    rw [abs_le]
    constructor <;> linarith

end Algebra

lemma abs_sum_le_sum_abs' {ι : Type*} [Fintype ι] (f : ι → ℝ) : |∑ i, f i| ≤ ∑ i, |f i| :=
  Finset.abs_sum_le_sum_abs _ _

set_option maxHeartbeats 800000 in
lemma phi_deriv_bound {ι : Type*} [Fintype ι]
    (lam κ m1 η1 m2 η2 η2' Γ Hc S Δ W Vn : ℝ) (s2 s3 av bw : ι → ℝ) (P E E3 zd D wv : ℝ)
    (hs2 : ∀ i, 0 ≤ s2 i) (hs3 : ∀ i, |s3 i| ≤ m1 * s2 i + η1) (hbw : ∀ i, |bw i| ≤ 2 * W)
    (hΓ : ∑ i, av i ^ 2 ≤ Γ * Vn ^ 2) (hHcv : ∑ i, s2 i * av i ^ 2 ≤ Hc * Vn ^ 2)
    (hHcw : ∑ i, s2 i * bw i ^ 2 ≤ Hc * W ^ 2)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hE : 0 ≤ E) (hE1 : E ≤ m2 * (1 - P) + η2')
    (hE2 : E ≤ m2 * P + η2') (hE3 : |E3| ≤ m2 * E + η2)
    (hband : E ≠ 0 ∨ E3 ≠ 0 → |zd| ≤ Δ * W ∧ D ^ 2 ≤ Δ ^ 2 * Vn ^ 2)
    (hwv : |wv| ≤ W * Vn) (hW : 0 ≤ W) (hVn : 0 ≤ Vn) (hκ : 0 ≤ κ) (hm1 : 0 ≤ m1)
    (hm2 : 0 ≤ m2) (hη1 : 0 ≤ η1) (hη2 : 0 ≤ η2) (hη2' : 0 ≤ η2') (hS : 0 < S)
    (hSHc : Hc ≤ S ^ 2) (hΔ : 0 ≤ Δ) (hlam : 0 ≤ lam) (hΓ0 : 0 ≤ Γ) (hHc0 : 0 ≤ Hc)
    (hL : 2 * η1 * Γ + Δ * κ * η2' + Δ * η2' * Hc + Δ ^ 3 * η2 + κ ^ 2 * η2' + S * η2' * Hc ≤
      (2 * m1 + Δ * m2 + S * m2 + κ * m2 + 1 + S) * lam) :
    |(1 - P) * (∑ i, s3 i * bw i * av i ^ 2) +
        E * zd * (κ * Vn ^ 2 - ∑ i, s2 i * av i ^ 2) + E3 * zd * D ^ 2 +
        2 * E * D * (κ * wv - ∑ i, s2 i * (bw i * av i))| ≤
      (2 * m1 + Δ * m2 + S * m2 + κ * m2 + 1 + S) * W *
        (lam * Vn ^ 2 + (1 - P) * (∑ i, s2 i * av i ^ 2) + P * κ * Vn ^ 2 + E * D ^ 2) := by
  set qC := ∑ i, s2 i * av i ^ 2 with hqC
  set qCd := ∑ i, s3 i * bw i * av i ^ 2 with hqCd
  set X := ∑ i, s2 i * (bw i * av i) with hX
  set M := 2 * m1 + Δ * m2 + S * m2 + κ * m2 + 1 + S with hM
  have hqC0 : 0 ≤ qC := Finset.sum_nonneg fun i _ => mul_nonneg (hs2 i) (sq_nonneg _)
  have hav0 : 0 ≤ ∑ i, av i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hqCd : |qCd| ≤ 2 * W * (m1 * qC + η1 * (Γ * Vn ^ 2)) := by
    have h1 : |qCd| ≤ ∑ i, (m1 * s2 i + η1) * (2 * W) * av i ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (av i))]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hs3 i) (hbw i) (abs_nonneg _)
        (add_nonneg (mul_nonneg hm1 (hs2 i)) hη1)) (sq_nonneg _)
    have h2 : ∑ i, (m1 * s2 i + η1) * (2 * W) * av i ^ 2 =
        2 * W * (m1 * qC + η1 * ∑ i, av i ^ 2) := by
      rw [hqC, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2] at h1
    have h3 : η1 * ∑ i, av i ^ 2 ≤ η1 * (Γ * Vn ^ 2) := mul_le_mul_of_nonneg_left hΓ hη1
    linarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * W by linarith)]
  have hX2 : X ^ 2 ≤ Hc * W ^ 2 * qC := by
    have h := sum_cauchy s2 bw av hs2
    have h' := mul_le_mul_of_nonneg_right hHcw hqC0
    exact h.trans h'
  have hφ0 : 0 ≤ lam * Vn ^ 2 + (1 - P) * qC + P * κ * Vn ^ 2 + E * D ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hP1) hqC0
    positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hterm1 : |(1 - P) * qCd| ≤ W * (2 * m1 * ((1 - P) * qC) + 2 * η1 * Γ * Vn ^ 2) := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hP1)]
    have h1 := mul_le_mul_of_nonneg_left hqCd (sub_nonneg.mpr hP1)
    have h2 : (1 - P) * (η1 * (Γ * Vn ^ 2)) ≤ η1 * (Γ * Vn ^ 2) := by
      have : 0 ≤ η1 * (Γ * Vn ^ 2) := by positivity
      have := mul_nonneg hP0 this
      linarith
    linarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * W by linarith)]
  by_cases hz : E = 0 ∧ E3 = 0
  · obtain ⟨hE0, hE30⟩ := hz
    rw [hE0, hE30]
    simp only [zero_mul, mul_zero, add_zero]
    have hle : W * (2 * m1 * ((1 - P) * qC) + 2 * η1 * Γ * Vn ^ 2) ≤
        M * W * (lam * Vn ^ 2 + (1 - P) * qC + P * κ * Vn ^ 2) := by
      have hq := mul_nonneg (sub_nonneg.mpr hP1) hqC0
      have hL' : 2 * η1 * Γ ≤ M * lam := by
        have : 0 ≤ Δ * κ * η2' + Δ * η2' * Hc + Δ ^ 3 * η2 + κ ^ 2 * η2' + S * η2' * Hc := by
          positivity
        rw [hM]; linarith
      have hm1M : 2 * m1 ≤ M := by
        rw [hM]
        have : 0 ≤ Δ * m2 + S * m2 + κ * m2 + 1 + S := by positivity
        linarith
      have hPk : 0 ≤ P * κ * Vn ^ 2 := by positivity
      have e1 : W * (2 * m1 * ((1 - P) * qC)) ≤ W * (M * ((1 - P) * qC)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm1M hq) hW
      have e2 : W * (2 * η1 * Γ * Vn ^ 2) ≤ W * (M * lam * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL' (sq_nonneg _)) hW
      have e3 : 0 ≤ M * W * (P * κ * Vn ^ 2) := by positivity
      linarith
    exact hterm1.trans hle
  · have hb := hband (by
      by_contra hc
      push Not at hc
      exact hz hc)
    obtain ⟨hzd, hD⟩ := hb
    have hD0 : |D| ≤ Δ * Vn := by
      rw [← abs_of_nonneg (mul_nonneg hΔ hVn)]
      exact sq_le_sq.mp (by rw [mul_pow]; exact hD)
    have hterm2 : |E * zd * (κ * Vn ^ 2)| ≤ W * (Δ * m2 * (P * κ * Vn ^ 2) +
        Δ * κ * η2' * Vn ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hE, abs_of_nonneg (by positivity : 0 ≤ κ * Vn ^ 2)]
      have h1 : E * |zd| * (κ * Vn ^ 2) ≤ (m2 * P + η2') * (Δ * W) * (κ * Vn ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hE2 hzd (abs_nonneg _) (by positivity))
          (by positivity)
      linarith
    have hterm3 : |E * zd * qC| ≤ W * (Δ * m2 * ((1 - P) * qC) + Δ * η2' * Hc * Vn ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hE, abs_of_nonneg hqC0]
      have h1 : E * |zd| * qC ≤ (m2 * (1 - P) + η2') * (Δ * W) * qC :=
        mul_le_mul_of_nonneg_right (mul_le_mul hE1 hzd (abs_nonneg _)
          (add_nonneg (mul_nonneg hm2 (sub_nonneg.mpr hP1)) hη2')) hqC0
      have h2 : η2' * (Δ * W) * qC ≤ η2' * (Δ * W) * (Hc * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left hHcv (by positivity)
      linarith
    have hterm4 : |E3 * zd * D ^ 2| ≤ W * (Δ * m2 * (E * D ^ 2) + Δ ^ 3 * η2 * Vn ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg D)]
      have h1 : |E3| * |zd| * D ^ 2 ≤ (m2 * E + η2) * (Δ * W) * D ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hE3 hzd (abs_nonneg _) (by positivity))
          (sq_nonneg _)
      have h2 : η2 * (Δ * W) * D ^ 2 ≤ η2 * (Δ * W) * (Δ ^ 2 * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
      linarith
    have hterm5 : |2 * E * D * (κ * wv)| ≤ W * (E * D ^ 2 + κ * m2 * (P * κ * Vn ^ 2) +
        κ ^ 2 * η2' * Vn ^ 2) := by
      have h1 : |2 * E * D * (κ * wv)| ≤ 2 * E * |D| * (κ * (W * Vn)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hE, abs_of_nonneg hκ,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwv hκ) (by positivity)
      have h2 : 2 * E * |D| * (κ * (W * Vn)) ≤ W * (E * D ^ 2 + E * κ ^ 2 * Vn ^ 2) := by
        have e : (|D| - κ * Vn) ^ 2 = D ^ 2 - 2 * |D| * (κ * Vn) + κ ^ 2 * Vn ^ 2 := by
          rw [sub_sq, sq_abs]; ring
        have h3 : 0 ≤ E * W * (D ^ 2 - 2 * |D| * (κ * Vn) + κ ^ 2 * Vn ^ 2) := by
          rw [← e]; positivity
        linarith
      have h3 : E * κ ^ 2 * Vn ^ 2 ≤ (m2 * P + η2') * κ ^ 2 * Vn ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE2 (sq_nonneg _)) (sq_nonneg _)
      linarith [mul_le_mul_of_nonneg_left h3 hW]
    have hterm6 : |2 * E * D * X| ≤ W * (S * (E * D ^ 2) + S * m2 * ((1 - P) * qC) +
        S * η2' * Hc * Vn ^ 2) := by
      have h1 := abs_two_mul_le E D X W qC S Hc hE hW hqC0 hS hSHc hX2
      have h2 : E * qC ≤ (m2 * (1 - P) + η2') * qC := mul_le_mul_of_nonneg_right hE1 hqC0
      have h3 : η2' * qC ≤ η2' * (Hc * Vn ^ 2) := mul_le_mul_of_nonneg_left hHcv hη2'
      have h4 : S * W * (E * qC) ≤ S * W * (m2 * ((1 - P) * qC) + η2' * (Hc * Vn ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
    have htot : |(1 - P) * qCd + E * zd * (κ * Vn ^ 2 - qC) + E3 * zd * D ^ 2 +
        2 * E * D * (κ * wv - X)| ≤
        |(1 - P) * qCd| + |E * zd * (κ * Vn ^ 2)| + |E * zd * qC| + |E3 * zd * D ^ 2| +
          |2 * E * D * (κ * wv)| + |2 * E * D * X| := by
      have e : (1 - P) * qCd + E * zd * (κ * Vn ^ 2 - qC) + E3 * zd * D ^ 2 +
          2 * E * D * (κ * wv - X) =
          (1 - P) * qCd + E * zd * (κ * Vn ^ 2) + (-(E * zd * qC)) + E3 * zd * D ^ 2 +
          2 * E * D * (κ * wv) + (-(2 * E * D * X)) := by ring
      rw [e]
      calc _ ≤ |(1 - P) * qCd + E * zd * (κ * Vn ^ 2) + (-(E * zd * qC)) + E3 * zd * D ^ 2 +
            2 * E * D * (κ * wv)| + |-(2 * E * D * X)| := abs_add_le _ _
        _ ≤ |(1 - P) * qCd + E * zd * (κ * Vn ^ 2) + (-(E * zd * qC)) + E3 * zd * D ^ 2| +
            |2 * E * D * (κ * wv)| + |-(2 * E * D * X)| := by
              gcongr; exact abs_add_le _ _
        _ ≤ |(1 - P) * qCd + E * zd * (κ * Vn ^ 2) + (-(E * zd * qC))| + |E3 * zd * D ^ 2| +
            |2 * E * D * (κ * wv)| + |-(2 * E * D * X)| := by
              gcongr; exact abs_add_le _ _
        _ ≤ |(1 - P) * qCd + E * zd * (κ * Vn ^ 2)| + |-(E * zd * qC)| + |E3 * zd * D ^ 2| +
            |2 * E * D * (κ * wv)| + |-(2 * E * D * X)| := by
              gcongr; exact abs_add_le _ _
        _ ≤ |(1 - P) * qCd| + |E * zd * (κ * Vn ^ 2)| + |-(E * zd * qC)| + |E3 * zd * D ^ 2| +
            |2 * E * D * (κ * wv)| + |-(2 * E * D * X)| := by
              gcongr; exact abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_neg]
    have hq := mul_nonneg (sub_nonneg.mpr hP1) hqC0
    have hPk : 0 ≤ P * κ * Vn ^ 2 := by positivity
    have hED : 0 ≤ E * D ^ 2 := by positivity
    have hsum : W * (2 * m1 * ((1 - P) * qC) + 2 * η1 * Γ * Vn ^ 2) +
        W * (Δ * m2 * (P * κ * Vn ^ 2) + Δ * κ * η2' * Vn ^ 2) +
        W * (Δ * m2 * ((1 - P) * qC) + Δ * η2' * Hc * Vn ^ 2) +
        W * (Δ * m2 * (E * D ^ 2) + Δ ^ 3 * η2 * Vn ^ 2) +
        W * (E * D ^ 2 + κ * m2 * (P * κ * Vn ^ 2) + κ ^ 2 * η2' * Vn ^ 2) +
        W * (S * (E * D ^ 2) + S * m2 * ((1 - P) * qC) + S * η2' * Hc * Vn ^ 2) ≤
        M * W * (lam * Vn ^ 2 + (1 - P) * qC + P * κ * Vn ^ 2 + E * D ^ 2) := by
      have c1 : (2 * m1 + Δ * m2 + S * m2) * ((1 - P) * qC) ≤ M * ((1 - P) * qC) := by
        apply mul_le_mul_of_nonneg_right _ hq
        have := mul_nonneg hκ hm2
        rw [hM]; linarith
      have c2 : (Δ * m2 + κ * m2) * (P * κ * Vn ^ 2) ≤ M * (P * κ * Vn ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hPk
        have := mul_nonneg hS.le hm2
        rw [hM]; linarith
      have c3 : (Δ * m2 + 1 + S) * (E * D ^ 2) ≤ M * (E * D ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hED
        have := mul_nonneg hS.le hm2
        have := mul_nonneg hκ hm2
        rw [hM]; linarith
      have c4 : (2 * η1 * Γ + Δ * κ * η2' + Δ * η2' * Hc + Δ ^ 3 * η2 + κ ^ 2 * η2' +
          S * η2' * Hc) * Vn ^ 2 ≤ M * lam * Vn ^ 2 :=
        mul_le_mul_of_nonneg_right hL (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add c1 c2) c3) c4) hW
      linarith
    calc _ ≤ _ := htot
      _ ≤ _ := by linarith [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6]
      _ ≤ _ := hsum

section Line

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (p p2 : ℕ) (a h w2 lam κ C0 : ℝ) {ι : Type*} [Fintype ι] (n : ι → E) (c : ι → ℝ)

lemma hasDerivAt_line (x w : E) (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • w) w t := by
  simpa using ((hasDerivAt_id t).smul_const w).const_add x

lemma inner_const_right {f : ℝ → E} {f' : E} {t : ℝ} (hf : HasDerivAt f f' t) (v : E) :
    HasDerivAt (fun s => ⟪f s, v⟫) ⟪f', v⟫ t := by
  have h := hf.inner ℝ (hasDerivAt_const t v)
  simpa using h

variable {h w2}

lemma quad_eq (x w v : E) (t : ℝ) :
    ⟪DFv p p2 a h w2 lam κ C0 n c (x + t • w) v, v⟫ =
      lam * ‖v‖ ^ 2 + (1 - sp1 p2 0 w2 (zv p a h κ C0 n c (x + t • w))) *
        (∑ i, sp2 p a h (lin n c i (x + t • w)) * ⟪n i, v⟫ ^ 2) +
        sp1 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * κ * ‖v‖ ^ 2 +
        sp2 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), v⟫ ^ 2 := by
  rw [DFv_inner, CH_inner, real_inner_self_eq_norm_sq]
  have e : ∑ i, sp2 p a h (lin n c i (x + t • w)) * (⟪n i, v⟫ * ⟪n i, v⟫) =
      ∑ i, sp2 p a h (lin n c i (x + t • w)) * ⟪n i, v⟫ ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [e]
  ring

lemma hasDerivAt_quad (hp : 2 ≤ p) (hp2 : 2 ≤ p2) (hh : 0 < h) (x w v : E)
    (t : ℝ) :
    HasDerivAt (fun t => ⟪DFv p p2 a h w2 lam κ C0 n c (x + t • w) v, v⟫)
      ((1 - sp1 p2 0 w2 (zv p a h κ C0 n c (x + t • w))) *
          (∑ i, sp3 p a h (lin n c i (x + t • w)) * ⟪n i, w⟫ * ⟪n i, v⟫ ^ 2) +
        sp2 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), w⟫ *
          (κ * ‖v‖ ^ 2 - ∑ i, sp2 p a h (lin n c i (x + t • w)) * ⟪n i, v⟫ ^ 2) +
        sp3 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), w⟫ *
          ⟪dv p a h κ n c (x + t • w), v⟫ ^ 2 +
        2 * sp2 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), v⟫ *
          (κ * ⟪w, v⟫ - ∑ i, sp2 p a h (lin n c i (x + t • w)) * (⟪n i, w⟫ * ⟪n i, v⟫))) t := by
  have hl := hasDerivAt_line x w t
  have hℓ : ∀ i, HasDerivAt (fun t => lin n c i (x + t • w)) ⟪n i, w⟫ t := by
    intro i
    have := (hasFDerivAt_lin n c i (x + t • w)).comp_hasDerivAt t hl
    exact this.congr_deriv (by simp)
  have hQ : HasDerivAt (fun t => ∑ i, sp2 p a h (lin n c i (x + t • w)) * ⟪n i, v⟫ ^ 2)
      (∑ i, sp3 p a h (lin n c i (x + t • w)) * ⟪n i, w⟫ * ⟪n i, v⟫ ^ 2) t := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      ((hasDerivAt_sp2 p a hp (lin n c i (x + t • w)) (h := h)).comp t (hℓ i)).mul_const (⟪n i, v⟫ ^ 2))
    exact this
  have hz : HasDerivAt (fun t => zv p a h κ C0 n c (x + t • w))
      ⟪dv p a h κ n c (x + t • w), w⟫ t := by
    have := (hasFDerivAt_zv p a κ C0 n c hh (x + t • w)).comp_hasDerivAt t hl
    exact this.congr_deriv (by simp)
  have hP := (hasDerivAt_sp1 p2 0 (zv p a h κ C0 n c (x + t • w)) (h := w2)).comp t hz
  have hE := (hasDerivAt_sp2 p2 0 hp2 (zv p a h κ C0 n c (x + t • w)) (h := w2)).comp t hz
  have hD : HasDerivAt (fun t => ⟪dv p a h κ n c (x + t • w), v⟫)
      (κ * ⟪w, v⟫ - ∑ i, sp2 p a h (lin n c i (x + t • w)) * (⟪n i, w⟫ * ⟪n i, v⟫)) t := by
    have h1 := (hasFDerivAt_dv p a κ n c (x + t • w) (h := h)).comp_hasDerivAt t hl
    have h2 := inner_const_right h1 v
    refine h2.congr_deriv ?_
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left, CH_inner]
  have hall := (((hasDerivAt_const t (lam * ‖v‖ ^ 2)).add
    ((hasDerivAt_const t (1 : ℝ)).sub hP |>.mul hQ)).add
    ((hP.mul_const κ).mul_const (‖v‖ ^ 2))).add (hE.mul (hD.pow 2))
  have hfun : (fun t : ℝ => ⟪DFv p p2 a h w2 lam κ C0 n c (x + t • w) v, v⟫) =
      fun t : ℝ => lam * ‖v‖ ^ 2 + (1 - sp1 p2 0 w2 (zv p a h κ C0 n c (x + t • w))) *
        (∑ i, sp2 p a h (lin n c i (x + t • w)) * ⟪n i, v⟫ ^ 2) +
        sp1 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * κ * ‖v‖ ^ 2 +
        sp2 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), v⟫ ^ 2 := by
    funext s
    exact quad_eq p p2 a lam κ C0 n c x w v s
  rw [hfun]
  refine hall.congr_deriv ?_
  simp only [Function.comp_apply, Pi.sub_apply, Pi.pow_apply,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
  ring

end Line

section Stable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (p p2 : ℕ) (a h w2 lam κ C0 : ℝ) {ι : Type*} [Fintype ι] (n : ι → E) (c : ι → ℝ)

variable {h w2}

theorem DFv_stable (hp : 2 ≤ p) (hp2 : 2 ≤ p2) (hh : 0 < h) (hw : 0 < w2) (Γ S Δ : ℝ)
    (hn : ∀ i, ‖n i‖ ≤ 2) (hΓ : ∀ v : E, ∑ i, ⟪n i, v⟫ ^ 2 ≤ Γ * ‖v‖ ^ 2) (hΓ0 : 0 ≤ Γ)
    (hband : ∀ u, |zv p a h κ C0 n c u| < w2 → ‖dv p a h κ n c u‖ ≤ Δ)
    (hκ : 0 ≤ κ) (hlam : 0 ≤ lam) (hS : 0 < S) (hΔ : 0 ≤ Δ)
    (hSHc : ((p : ℝ) + 1) / h * Γ ≤ S ^ 2)
    (hL : 2 * (4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p / h ^ 2) * Γ +
        Δ * κ * (((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2) +
        Δ * (((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2) * (((p : ℝ) + 1) / h * Γ) +
        Δ ^ 3 * (4 * (p2 : ℝ) * ((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2 ^ 2) +
        κ ^ 2 * (((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2) +
        S * (((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2) * (((p : ℝ) + 1) / h * Γ) ≤
      (2 * (4 * (p : ℝ) / h) + Δ * (4 * ((p2 : ℝ) + 1) / w2) + S * (4 * ((p2 : ℝ) + 1) / w2) +
        κ * (4 * ((p2 : ℝ) + 1) / w2) + 1 + S) * lam)
    (x y v : E) :
    ⟪DFv p p2 a h w2 lam κ C0 n c y v, v⟫ ≤
      Real.exp ((2 * (4 * (p : ℝ) / h) + Δ * (4 * ((p2 : ℝ) + 1) / w2) +
        S * (4 * ((p2 : ℝ) + 1) / w2) + κ * (4 * ((p2 : ℝ) + 1) / w2) + 1 + S) * ‖y - x‖) *
      ⟪DFv p p2 a h w2 lam κ C0 n c x v, v⟫ := by
  set m1 := 4 * (p : ℝ) / h with hm1
  set η1 := 4 * (p : ℝ) * ((p : ℝ) + 1) * (1 / 2) ^ p / h ^ 2 with hη1
  set m2 := 4 * ((p2 : ℝ) + 1) / w2 with hm2
  set η2 := 4 * (p2 : ℝ) * ((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2 ^ 2 with hη2
  set η2' := ((p2 : ℝ) + 1) * (1 / 2) ^ p2 / w2 with hη2'
  set Hc := ((p : ℝ) + 1) / h * Γ with hHc
  set M := 2 * m1 + Δ * m2 + S * m2 + κ * m2 + 1 + S with hM
  set w := y - x with hwdef
  have hm10 : 0 ≤ m1 := by positivity
  have hm20 : 0 ≤ m2 := by positivity
  have hη10 : 0 ≤ η1 := by positivity
  have hη20 : 0 ≤ η2 := by positivity
  have hη2'0 : 0 ≤ η2' := by positivity
  have hHc0 : 0 ≤ Hc := by positivity
  have hp1 : 1 ≤ p := by omega
  have hp21 : 1 ≤ p2 := by omega
  have key : ∀ t ∈ Icc (0 : ℝ) 1,
      ((1 - sp1 p2 0 w2 (zv p a h κ C0 n c (x + t • w))) *
          (∑ i, sp3 p a h (lin n c i (x + t • w)) * ⟪n i, w⟫ * ⟪n i, v⟫ ^ 2) +
        sp2 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), w⟫ *
          (κ * ‖v‖ ^ 2 - ∑ i, sp2 p a h (lin n c i (x + t • w)) * ⟪n i, v⟫ ^ 2) +
        sp3 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), w⟫ *
          ⟪dv p a h κ n c (x + t • w), v⟫ ^ 2 +
        2 * sp2 p2 0 w2 (zv p a h κ C0 n c (x + t • w)) * ⟪dv p a h κ n c (x + t • w), v⟫ *
          (κ * ⟪w, v⟫ - ∑ i, sp2 p a h (lin n c i (x + t • w)) * (⟪n i, w⟫ * ⟪n i, v⟫))) ≤
        (M * ‖w‖) * ⟪DFv p p2 a h w2 lam κ C0 n c (x + t • w) v, v⟫ := by
    intro t _
    set u := x + t • w
    set z := zv p a h κ C0 n c u
    have hb := phi_deriv_bound lam κ m1 η1 m2 η2 η2' Γ Hc S Δ ‖w‖ ‖v‖
      (fun i => sp2 p a h (lin n c i u)) (fun i => sp3 p a h (lin n c i u))
      (fun i => ⟪n i, v⟫) (fun i => ⟪n i, w⟫)
      (sp1 p2 0 w2 z) (sp2 p2 0 w2 z) (sp3 p2 0 w2 z) ⟪dv p a h κ n c u, w⟫
      ⟪dv p a h κ n c u, v⟫ ⟪w, v⟫
      (fun i => sp2_nonneg p a hh _) (fun i => abs_sp3_le p a hp hh _)
      (fun i => (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hn i)
        (norm_nonneg _)))
      (hΓ v)
      (by
        calc ∑ i, sp2 p a h (lin n c i u) * ⟪n i, v⟫ ^ 2 ≤
            ∑ i, ((p : ℝ) + 1) / h * ⟪n i, v⟫ ^ 2 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (sp2_le p a hh _)
                (sq_nonneg _)
          _ = ((p : ℝ) + 1) / h * ∑ i, ⟪n i, v⟫ ^ 2 := by rw [Finset.mul_sum]
          _ ≤ ((p : ℝ) + 1) / h * (Γ * ‖v‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (hΓ v) (by positivity)
          _ = Hc * ‖v‖ ^ 2 := by rw [hHc]; ring)
      (by
        calc ∑ i, sp2 p a h (lin n c i u) * ⟪n i, w⟫ ^ 2 ≤
            ∑ i, ((p : ℝ) + 1) / h * ⟪n i, w⟫ ^ 2 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (sp2_le p a hh _)
                (sq_nonneg _)
          _ = ((p : ℝ) + 1) / h * ∑ i, ⟪n i, w⟫ ^ 2 := by rw [Finset.mul_sum]
          _ ≤ ((p : ℝ) + 1) / h * (Γ * ‖w‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (hΓ w) (by positivity)
          _ = Hc * ‖w‖ ^ 2 := by rw [hHc]; ring)
      (sp1_nonneg p2 0 hp21 _) (sp1_le_one p2 0 hp21 _) (sp2_nonneg p2 0 hw _)
      (sp2_le_one_sub_sp1 p2 0 hp21 hw _) (sp2_le_sp1 p2 0 hp21 hw _)
      (by
        have h1 := abs_sp3_le p2 0 hp2 hw z
        have h2 : 4 * (p2 : ℝ) / w2 * sp2 p2 0 w2 z ≤ m2 * sp2 p2 0 w2 z := by
          apply mul_le_mul_of_nonneg_right _ (sp2_nonneg p2 0 hw z)
          rw [hm2]
          exact div_le_div_of_nonneg_right (by linarith) hw.le
        linarith)
      (by
        intro hne
        have hzb : |z| < w2 := by
          by_contra hc
          push Not at hc
          have hc' : w2 ≤ |z - 0| := by rw [sub_zero]; exact hc
          rcases hne with h1 | h1
          · exact h1 (sp2_eq_zero p2 0 hp21 hw hc')
          · exact h1 (sp3_eq_zero p2 0 hp2 hw hc')
        have hd := hband u hzb
        refine ⟨(abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)),
          ?_⟩
        have h1 := abs_real_inner_le_norm (dv p a h κ n c u) v
        have h2 : |⟪dv p a h κ n c u, v⟫| ≤ Δ * ‖v‖ :=
          h1.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
        have h3 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
        rw [mul_pow] at h3
        exact h3)
      ((abs_real_inner_le_norm w v)) (norm_nonneg _) (norm_nonneg _) hκ hm10 hm20 hη10 hη20 hη2'0
      hS hSHc hΔ hlam hΓ0 hHc0 hL
    rw [quad_eq p p2 a lam κ C0 n c x w v t]
    exact (le_abs_self _).trans hb
  have hg := gronwall_unit (fun t => ⟪DFv p p2 a h w2 lam κ C0 n c (x + t • w) v, v⟫) _
    (M * ‖w‖) (hasDerivAt_quad p p2 a lam κ C0 n c hp hp2 hh x w v) key
  simp only [one_smul, zero_smul, add_zero] at hg
  have hxy : x + w = y := by rw [hwdef]; abel
  rw [hxy] at hg
  exact hg

end Stable

end LongTails.Proofs.HsStability
