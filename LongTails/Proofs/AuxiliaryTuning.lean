import LongTails.Proofs.AuxiliaryDane

namespace LongTails.Proofs.AuxiliaryTuning

open LongTails.Algorithms.AuxiliarySimilarity LongTails.Proofs.AuxiliaryDane

lemma one_sub_pow_le_exp {x : ℝ} (hx1 : x ≤ 1) (n : ℕ) :
    (1 - x) ^ n ≤ Real.exp (-(x * n)) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by have := Real.add_one_le_exp (-x); linarith
  calc (1 - x) ^ n ≤ Real.exp (-x) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = Real.exp (-(x * n)) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma exp_neg_le_inv {c X : ℝ} (hX : 0 < X) (hc : Real.log X ≤ c) : Real.exp (-c) ≤ X⁻¹ := by
  have h : X⁻¹ = Real.exp (-Real.log X) := by rw [Real.exp_neg, Real.exp_log hX]
  rw [h]
  exact Real.exp_le_exp.mpr (by linarith)

lemma three_fifths_pow (n : ℕ) : (3 / 5 : ℝ) ^ n ≤ Real.exp (-(n / 3)) := by
  have h3 : (3 / 5 : ℝ) ≤ Real.exp (-(1 / 3)) := by
    have := Real.add_one_le_exp (-(1 / 3))
    linarith
  calc (3 / 5 : ℝ) ^ n ≤ Real.exp (-(1 / 3)) ^ n := pow_le_pow_left₀ (by norm_num) h3 n
    _ = Real.exp (-(n / 3)) := by rw [← Real.exp_nat_mul]; congr 1; ring

structure Abs (s ε L δ Δ ρ α db M a : ℝ) : Prop where
  hs : 0 < s
  hε : 0 < ε
  hL : 0 ≤ L
  hδ : 0 < δ
  hΔ : 0 ≤ Δ
  hρ : 0 < ρ
  hs2 : s ^ 2 = ρ * ε
  hα : α = s / 8
  hδdb : δ ≤ db
  hαdb : α ≤ db
  hdbsum : db ≤ δ + α
  hM : M = L + 2 * α + 4 * db
  ha2 : a ^ 2 = α / (4 * db)
  ha0 : 0 < a

namespace Abs

variable {s ε L δ Δ ρ α db M a : ℝ}

lemma α_pos (A : Abs s ε L δ Δ ρ α db M a) : 0 < α := by
  rw [A.hα]; have := A.hs; positivity

lemma db_pos (A : Abs s ε L δ Δ ρ α db M a) : 0 < db := A.α_pos.trans_le A.hαdb

lemma a_le (A : Abs s ε L δ Δ ρ α db M a) : a ≤ 1 := by
  have hdb := A.db_pos
  have h : α / (4 * db) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith [A.hαdb, A.α_pos]
  have h2 := A.ha2
  have h0 := A.ha0
  nlinarith

lemma M_pos (A : Abs s ε L δ Δ ρ α db M a) : 0 < M := by
  rw [A.hM]; linarith [A.hL, A.α_pos, A.db_pos]

lemma db_le_M (A : Abs s ε L δ Δ ρ α db M a) : db ≤ M := by
  rw [A.hM]; linarith [A.hL, A.α_pos, A.db_pos]

lemma ρ_eq (A : Abs s ε L δ Δ ρ α db M a) : ρ = s ^ 2 / ε := by
  rw [A.hs2, mul_div_assoc, div_self A.hε.ne', mul_one]

lemma tau_eq (A : Abs s ε L δ Δ ρ α db M a) : α / (32 * ρ) = ε / (256 * s) := by
  have hs := A.hs.ne'
  have hε := A.hε.ne'
  rw [A.hα, A.ρ_eq]
  field_simp
  ring

lemma vartheta_eq (A : Abs s ε L δ Δ ρ α db M a) :
    a * α ^ 3 / (192 * ρ * db) = a * s * ε / (98304 * db) := by
  have hs := A.hs.ne'
  have hε := A.hε.ne'
  have hdb := A.db_pos.ne'
  rw [A.hα, A.ρ_eq]
  field_simp
  ring

lemma s_le_db (A : Abs s ε L δ Δ ρ α db M a) : s ≤ 8 * db := by
  have := A.hαdb
  rw [A.hα] at this
  linarith

lemma Q_ge (A : Abs s ε L δ Δ ρ α db M a) : 1 ≤ 1 + (L + δ) / s := by
  have := div_nonneg (by linarith [A.hL, A.hδ] : 0 ≤ L + δ) A.hs.le
  linarith

lemma M_le (A : Abs s ε L δ Δ ρ α db M a) : M ≤ 5 * (1 + (L + δ) / s) * s := by
  have hs := A.hs
  have e : 5 * (1 + (L + δ) / s) * s = 5 * s + 5 * (L + δ) := by
    field_simp
  have hsum := A.hdbsum
  rw [A.hα] at hsum
  rw [e, A.hM, A.hα]
  linarith [A.hL, A.hδ]

lemma pow_T (A : Abs s ε L δ Δ ρ α db M a) {T : ℕ}
    (hT : 6 * Real.sqrt (1 + δ / s) * Real.log (8 + 8 * δ / s) ≤ T) : (1 - a) ^ T ≤ α / db := by
  have hs := A.hs
  have hαp := A.α_pos
  have hdb := A.db_pos
  have ha := A.ha0
  have hu : 1 ≤ 1 + δ / s := by have := div_nonneg A.hδ.le hs.le; linarith
  have hlog0 : 0 ≤ Real.log (8 + 8 * δ / s) := by
    apply Real.log_nonneg
    have := div_nonneg A.hδ.le hs.le
    have e : 8 * δ / s = 8 * (δ / s) := by ring
    rw [e]
    linarith
  have hau : 1 ≤ a * (6 * Real.sqrt (1 + δ / s)) := by
    have hsq : (a * (6 * Real.sqrt (1 + δ / s))) ^ 2 = 9 * α * (1 + δ / s) / db := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), A.ha2]
      field_simp
      ring
    have hαu : α * (1 + δ / s) = α + δ / 8 := by
      rw [A.hα]; field_simp
    have hge : db ≤ 9 * α * (1 + δ / s) := by
      have := A.hdbsum
      have e : 9 * α * (1 + δ / s) = 9 * (α * (1 + δ / s)) := by ring
      rw [e, hαu]
      linarith [A.hδ]
    have h1 : 1 ≤ (a * (6 * Real.sqrt (1 + δ / s))) ^ 2 := by
      rw [hsq, le_div_iff₀ hdb]; linarith
    have hnn : 0 ≤ a * (6 * Real.sqrt (1 + δ / s)) := by positivity
    nlinarith
  have hlogle : Real.log (db / α) ≤ Real.log (8 + 8 * δ / s) := by
    apply Real.log_le_log (div_pos hdb hαp)
    rw [div_le_iff₀ hαp]
    have e : (8 + 8 * δ / s) * α = 8 * α + δ := by
      rw [A.hα]; field_simp
    rw [e]
    linarith [A.hdbsum]
  have haT : Real.log (db / α) ≤ a * T := by
    calc Real.log (db / α) ≤ Real.log (8 + 8 * δ / s) := hlogle
      _ ≤ a * (6 * Real.sqrt (1 + δ / s)) * Real.log (8 + 8 * δ / s) :=
          le_mul_of_one_le_left hlog0 hau
      _ = a * (6 * Real.sqrt (1 + δ / s) * Real.log (8 + 8 * δ / s)) := by ring
      _ ≤ a * T := mul_le_mul_of_nonneg_left hT ha.le
  have h1 := one_sub_pow_le_exp A.a_le T
  have h2 := exp_neg_le_inv (div_pos hdb hαp) haT
  rw [inv_div] at h2
  linarith

lemma hCT (A : Abs s ε L δ Δ ρ α db M a) {T : ℕ}
    (hT : 6 * Real.sqrt (1 + δ / s) * Real.log (8 + 8 * δ / s) ≤ T) :
    2 * (a * α ^ 3 / (192 * ρ * db)) ^ 2 + 8 * db * ((1 - a) ^ T * (α * (α / (32 * ρ)) ^ 2) +
      6 * (a * α ^ 3 / (192 * ρ * db)) * (α / (32 * ρ)) / a) ≤ ε ^ 2 / 4 := by
  have hp := A.pow_T hT
  rw [A.vartheta_eq, A.tau_eq]
  have hs := A.hs
  have hε := A.hε
  have hdb := A.db_pos
  have ha := A.ha0
  have ha1 := A.a_le
  have hsdb := A.s_le_db
  have hαp := A.α_pos
  have hA : 2 * (a * s * ε / (98304 * db)) ^ 2 ≤ ε ^ 2 / 64 := by
    have has : a * s ≤ 1 * (8 * db) := mul_le_mul ha1 hsdb hs.le zero_le_one
    have h1 : a * s * ε / (98304 * db) ≤ ε / 12288 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul_of_nonneg_right has (by positivity : (0 : ℝ) ≤ ε * 12288)
      nlinarith
    have h0 : 0 ≤ a * s * ε / (98304 * db) := by positivity
    have h2 := pow_le_pow_left₀ h0 h1 2
    have e : (ε / 12288) ^ 2 = ε ^ 2 / 150994944 := by ring
    rw [e] at h2
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith
  have hB : 8 * db * ((1 - a) ^ T * (α * (ε / (256 * s)) ^ 2)) ≤ ε ^ 2 / 64 := by
    have hpos : 0 ≤ α * (ε / (256 * s)) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hp hpos
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * db)
    have h2 : 8 * db * (α / db * (α * (ε / (256 * s)) ^ 2)) = ε ^ 2 / 524288 := by
      rw [A.hα]; field_simp; ring
    rw [h2] at h3
    have : 0 ≤ ε ^ 2 := sq_nonneg ε
    linarith
  have hC : 8 * db * (6 * (a * s * ε / (98304 * db)) * (ε / (256 * s)) / a) = ε ^ 2 / 524288 := by
    field_simp
    ring
  rw [mul_add, hC]
  have : 0 ≤ ε ^ 2 := sq_nonneg ε
  linarith

lemma hCε (A : Abs s ε L δ Δ ρ α db M a) :
    2 * (α * (α / (32 * ρ)) ^ 2) ≤ ε ^ 2 / (16 * α) := by
  rw [A.tau_eq]
  have hs := A.hs
  have hε := A.hε
  have e1 : 2 * (α * (ε / (256 * s)) ^ 2) = ε ^ 2 / (262144 * s) := by
    rw [A.hα]; field_simp; ring
  have e2 : ε ^ 2 / (16 * α) = ε ^ 2 / (2 * s) := by
    rw [A.hα]; field_simp; ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

lemma vartheta_sq (A : Abs s ε L δ Δ ρ α db M a) :
    (a * s * ε / (98304 * db)) ^ 2 = s ^ 3 * ε ^ 2 / (32 * 98304 ^ 2 * db ^ 3) := by
  have hdb := A.db_pos.ne'
  rw [div_pow, mul_pow, mul_pow, A.ha2, A.hα]
  field_simp
  ring

lemma hCJ (A : Abs s ε L δ Δ ρ α db M a) {J : ℕ}
    (hJ : 15 * Real.log (400 * (1 + (L + δ) / s)) ≤ J) :
    2 * M * ((3 / 5) ^ J * (M / 2 * (6 * (α / (32 * ρ))) ^ 2) +
      5 / 2 * ((a * α ^ 3 / (192 * ρ * db)) ^ 2 / (60 * M * (α / (32 * ρ)))) *
        (6 * (α / (32 * ρ)))) ≤ (a * α ^ 3 / (192 * ρ * db)) ^ 2 := by
  have hϑ2 := A.vartheta_sq
  rw [A.vartheta_eq, A.tau_eq]
  have hs := A.hs
  have hε := A.hε
  have hdb := A.db_pos
  have hM := A.M_pos
  have hQ := A.Q_ge
  have hMs := A.M_le
  have hdbs := A.db_le_M.trans hMs
  have hτp : 0 < ε / (256 * s) := by positivity
  have hsec : 2 * M * (5 / 2 * ((a * s * ε / (98304 * db)) ^ 2 / (60 * M * (ε / (256 * s)))) *
      (6 * (ε / (256 * s)))) = (a * s * ε / (98304 * db)) ^ 2 / 2 := by
    field_simp
    ring
  have hX : 0 < (400 * (1 + (L + δ) / s)) ^ 5 := by positivity
  have hlog : Real.log ((400 * (1 + (L + δ) / s)) ^ 5) ≤ (J : ℝ) / 3 := by
    rw [Real.log_pow]; push_cast; linarith
  have hpow : (3 / 5 : ℝ) ^ J ≤ ((400 * (1 + (L + δ) / s)) ^ 5)⁻¹ :=
    (three_fifths_pow J).trans (exp_neg_le_inv hX hlog)
  have h1 : M ^ 2 * db ^ 3 ≤ (5 * (1 + (L + δ) / s) * s) ^ 5 := by
    calc M ^ 2 * db ^ 3 ≤ (5 * (1 + (L + δ) / s) * s) ^ 2 * (5 * (1 + (L + δ) / s) * s) ^ 3 := by
          gcongr
      _ = (5 * (1 + (L + δ) / s) * s) ^ 5 := by ring
  have key : 72 * M ^ 2 * (ε / (256 * s)) ^ 2 * (32 * 98304 ^ 2 * db ^ 3) ≤
      s ^ 3 * ε ^ 2 * (400 * (1 + (L + δ) / s)) ^ 5 := by
    have e : 72 * M ^ 2 * (ε / (256 * s)) ^ 2 * (32 * 98304 ^ 2 * db ^ 3) =
        339738624 * (ε ^ 2 / s ^ 2) * (M ^ 2 * db ^ 3) := by
      field_simp
      ring
    rw [e]
    calc 339738624 * (ε ^ 2 / s ^ 2) * (M ^ 2 * db ^ 3) ≤
          339738624 * (ε ^ 2 / s ^ 2) * (5 * (1 + (L + δ) / s) * s) ^ 5 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 339738624 * 3125 * (ε ^ 2 * s ^ 3 * (1 + (L + δ) / s) ^ 5) := by
          field_simp
          ring
      _ ≤ 400 ^ 5 * (ε ^ 2 * s ^ 3 * (1 + (L + δ) / s) ^ 5) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = s ^ 3 * ε ^ 2 * (400 * (1 + (L + δ) / s)) ^ 5 := by ring
  have hpoly : 72 * M ^ 2 * (ε / (256 * s)) ^ 2 ≤
      (a * s * ε / (98304 * db)) ^ 2 * (400 * (1 + (L + δ) / s)) ^ 5 := by
    rw [hϑ2, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact key
  have hfirst : 2 * M * ((3 / 5) ^ J * (M / 2 * (6 * (ε / (256 * s))) ^ 2)) ≤
      (a * s * ε / (98304 * db)) ^ 2 / 2 := by
    have e : 2 * M * ((3 / 5) ^ J * (M / 2 * (6 * (ε / (256 * s))) ^ 2)) =
        (3 / 5 : ℝ) ^ J * (36 * M ^ 2 * (ε / (256 * s)) ^ 2) := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hpow
      (by positivity : (0 : ℝ) ≤ 36 * M ^ 2 * (ε / (256 * s)) ^ 2)
    refine h1.trans ?_
    rw [inv_mul_le_iff₀ hX]
    linarith
  rw [mul_add, hsec]
  linarith

lemma hCN_core {s ε Q W M db G : ℝ} (hs : 0 < s) (hε : 0 < ε) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hM : 0 < M) (hdb : 0 < db) (hMs : M ≤ 5 * Q * s) (hdbs : db ≤ 5 * Q * s)
    (hG : G ≤ 4 * Q * W * ε ^ 2 + Q ^ 2 * ε ^ 2 / 32) (hG0 : 0 ≤ G) :
    1200 * (32 * 98304 ^ 2) ^ 2 * M ^ 3 * db ^ 5 * G ≤
      65536 * (2 ^ 110 * Q ^ 10 * (1 + W)) * s ^ 8 * ε ^ 2 := by
  have h1 : M ^ 3 * db ^ 5 ≤ (5 * Q * s) ^ 8 := by
    calc M ^ 3 * db ^ 5 ≤ (5 * Q * s) ^ 3 * (5 * Q * s) ^ 5 := by gcongr
      _ = (5 * Q * s) ^ 8 := by ring
  have h2 : G ≤ ε ^ 2 * Q ^ 2 * (4 * W + 1) := by
    have : Q ≤ Q ^ 2 := by nlinarith
    have : 4 * Q * W * ε ^ 2 ≤ 4 * Q ^ 2 * W * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ 4 * W * ε ^ 2)
      nlinarith
    nlinarith [sq_nonneg ε, sq_nonneg Q]
  have hc : (1200 * (32 * 98304 ^ 2) ^ 2 * 5 ^ 8 : ℝ) * 4 ≤ 65536 * 2 ^ 110 := by norm_num
  calc 1200 * (32 * 98304 ^ 2) ^ 2 * M ^ 3 * db ^ 5 * G
        = 1200 * (32 * 98304 ^ 2) ^ 2 * (M ^ 3 * db ^ 5) * G := by ring
    _ ≤ 1200 * (32 * 98304 ^ 2) ^ 2 * (5 * Q * s) ^ 8 * (ε ^ 2 * Q ^ 2 * (4 * W + 1)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 hG0 (by positivity)
    _ = (1200 * (32 * 98304 ^ 2) ^ 2 * 5 ^ 8) * (4 * W + 1) * (Q ^ 10 * s ^ 8 * ε ^ 2) := by ring
    _ ≤ (65536 * 2 ^ 110) * (1 + W) * (Q ^ 10 * s ^ 8 * ε ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
    _ = 65536 * (2 ^ 110 * Q ^ 10 * (1 + W)) * s ^ 8 * ε ^ 2 := by ring

lemma hCN (A : Abs s ε L δ Δ ρ α db M a) {N : ℕ}
    (hN : (L / δ + 6) * Real.log (2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2)) ≤
      ((N - 1 : ℕ) : ℝ)) :
    2 * M * ((1 - 3 * db / M) ^ (N - 1) * ((4 * (L + δ) * Δ + 18 * (α / (32 * ρ)) ^ 2 *
      (M + δ) ^ 2) / (6 * db))) ≤
      ((a * α ^ 3 / (192 * ρ * db)) ^ 2 / (60 * M * (α / (32 * ρ)))) ^ 2 := by
  have hϑ2 := A.vartheta_sq
  rw [A.vartheta_eq, A.tau_eq]
  have hs := A.hs
  have hε := A.hε
  have hδ := A.hδ
  have hL := A.hL
  have hdb := A.db_pos
  have hM := A.M_pos
  have hQ := A.Q_ge
  have hW : 0 ≤ Δ * s / ε ^ 2 := by have := A.hΔ; positivity
  have hX : 1 ≤ 2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2) := by
    have h1 : 1 ≤ (1 + (L + δ) / s) ^ 10 := one_le_pow₀ hQ
    have h2 : (1 : ℝ) ≤ 2 ^ 110 := by norm_num
    have h3 : 1 ≤ 1 + Δ * s / ε ^ 2 := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ 2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2) := by gcongr
  have hX0 : 0 < 2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2) := by linarith
  have hlogX := Real.log_nonneg hX
  have hx1 : 3 * db / M ≤ 1 := by
    rw [div_le_one hM, A.hM]; linarith [A.hαdb, A.α_pos]
  have hxL : 1 ≤ 3 * db / M * (L / δ + 6) := by
    have hLd : L ≤ db * (L / δ) := by
      rw [mul_div_assoc', le_div_iff₀ hδ]
      nlinarith [A.hδdb]
    have e : 3 * db / M * (L / δ + 6) = (3 * (db * (L / δ)) + 18 * db) / M := by
      field_simp
      ring
    rw [e, le_div_iff₀ hM, one_mul, A.hM]
    linarith [A.hαdb]
  have hlog : Real.log (2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2)) ≤
      3 * db / M * ((N - 1 : ℕ) : ℝ) := by
    calc _ ≤ 3 * db / M * (L / δ + 6) *
          Real.log (2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2)) :=
          le_mul_of_one_le_left hlogX hxL
      _ = 3 * db / M * ((L / δ + 6) *
          Real.log (2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2))) := by ring
      _ ≤ 3 * db / M * ((N - 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hN (by positivity)
  have hpow : (1 - 3 * db / M) ^ (N - 1) ≤
      (2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2))⁻¹ :=
    (one_sub_pow_le_exp hx1 _).trans (exp_neg_le_inv hX0 hlog)
  have hG0 : 0 ≤ 4 * (L + δ) * Δ + 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2 := by
    have := A.hΔ; positivity
  have hMs := A.M_le
  have hdbs := A.db_le_M.trans hMs
  have hGb : 4 * (L + δ) * Δ + 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2 ≤
      4 * (1 + (L + δ) / s) * (Δ * s / ε ^ 2) * ε ^ 2 + (1 + (L + δ) / s) ^ 2 * ε ^ 2 / 32 := by
    have hLd : L + δ ≤ (1 + (L + δ) / s) * s := by
      have e : (1 + (L + δ) / s) * s = s + (L + δ) := by field_simp
      rw [e]; linarith
    have h1 : 4 * (L + δ) * Δ ≤ 4 * (1 + (L + δ) / s) * (Δ * s / ε ^ 2) * ε ^ 2 := by
      have e : 4 * (1 + (L + δ) / s) * (Δ * s / ε ^ 2) * ε ^ 2 =
          4 * ((1 + (L + δ) / s) * s) * Δ := by
        field_simp
      rw [e]
      have := A.hΔ
      nlinarith
    have hMδ : M + δ ≤ 2 * (5 * (1 + (L + δ) / s) * s) := by linarith [A.hδdb, A.db_le_M]
    have h2 : 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2 ≤ (1 + (L + δ) / s) ^ 2 * ε ^ 2 / 32 := by
      have hsq : (M + δ) ^ 2 ≤ (2 * (5 * (1 + (L + δ) / s) * s)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hMδ 2
      calc 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2 ≤
            18 * (ε / (256 * s)) ^ 2 * (2 * (5 * (1 + (L + δ) / s) * s)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 1800 / 65536 * ((1 + (L + δ) / s) ^ 2 * ε ^ 2) := by
            field_simp
            ring
        _ ≤ (1 + (L + δ) / s) ^ 2 * ε ^ 2 / 32 := by
            have : 0 ≤ (1 + (L + δ) / s) ^ 2 * ε ^ 2 := by positivity
            linarith
    linarith
  have hcore := hCN_core hs hε hQ hW hM hdb hMs hdbs hGb hG0
  have hLHS := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow
    (by positivity : (0 : ℝ) ≤ (4 * (L + δ) * Δ + 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2) /
      (6 * db))) (by positivity : (0 : ℝ) ≤ 2 * M)
  refine hLHS.trans ?_
  rw [hϑ2]
  have eR : (s ^ 3 * ε ^ 2 / (32 * 98304 ^ 2 * db ^ 3) / (60 * M * (ε / (256 * s)))) ^ 2 =
      65536 * s ^ 8 * ε ^ 2 / (3600 * (32 * 98304 ^ 2) ^ 2 * M ^ 2 * db ^ 6) := by
    field_simp
    ring
  rw [eR, le_div_iff₀ (by positivity)]
  have eL : 2 * M * ((2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2))⁻¹ *
      ((4 * (L + δ) * Δ + 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2) / (6 * db))) *
      (3600 * (32 * 98304 ^ 2) ^ 2 * M ^ 2 * db ^ 6) =
      1200 * (32 * 98304 ^ 2) ^ 2 * M ^ 3 * db ^ 5 *
        (4 * (L + δ) * Δ + 18 * (ε / (256 * s)) ^ 2 * (M + δ) ^ 2) /
        (2 ^ 110 * (1 + (L + δ) / s) ^ 10 * (1 + Δ * s / ε ^ 2)) := by
    field_simp
    ring
  rw [eL, div_le_iff₀ hX0]
  linarith

lemma hK (A : Abs s ε L δ Δ ρ α db M a) {K : ℕ} (hK : 2 ^ 19 * Δ * s / ε ^ 2 + 1 ≤ K) :
    Δ < K * (α * (α / (32 * ρ)) ^ 2) := by
  rw [A.tau_eq]
  have hs := A.hs
  have hε := A.hε
  have he : α * (ε / (256 * s)) ^ 2 = ε ^ 2 / (2 ^ 19 * s) := by
    rw [A.hα]; field_simp; ring
  rw [he]
  have hpos : 0 < ε ^ 2 / (2 ^ 19 * s) := by positivity
  have h := mul_le_mul_of_nonneg_right hK hpos.le
  have e2 : (2 ^ 19 * Δ * s / ε ^ 2 + 1) * (ε ^ 2 / (2 ^ 19 * s)) = Δ + ε ^ 2 / (2 ^ 19 * s) := by
    field_simp
  rw [e2] at h
  linarith

end Abs

structure Base (L δ ρ Δ ε : ℝ) : Prop where
  hL : 0 ≤ L
  hδ : 0 < δ
  hρ : 0 < ρ
  hΔ : 0 ≤ Δ
  hε : 0 < ε

section Assemble

variable {L δ ρ Δ ε : ℝ}

lemma Base.abs (hb : Base L δ ρ Δ ε) :
    Abs (Real.sqrt (ρ * ε)) ε L δ Δ ρ (tuning L δ ρ Δ ε).α (tuning L δ ρ Δ ε).db
      (tuning L δ ρ Δ ε).M (tuning L δ ρ Δ ε).a := by
  have hs : 0 < Real.sqrt (ρ * ε) := Real.sqrt_pos.mpr (mul_pos hb.hρ hb.hε)
  have hα : 0 < Real.sqrt (ρ * ε) / 8 := by positivity
  have hdb : 0 < max δ (Real.sqrt (ρ * ε) / 8) := lt_of_lt_of_le hα (le_max_right _ _)
  exact
    { hs := hs
      hε := hb.hε
      hL := hb.hL
      hδ := hb.hδ
      hΔ := hb.hΔ
      hρ := hb.hρ
      hs2 := Real.sq_sqrt (mul_pos hb.hρ hb.hε).le
      hα := rfl
      hδdb := le_max_left _ _
      hαdb := le_max_right _ _
      hdbsum := max_le (by show δ ≤ δ + Real.sqrt (ρ * ε) / 8; linarith)
        (by show Real.sqrt (ρ * ε) / 8 ≤ δ + Real.sqrt (ρ * ε) / 8; linarith [hb.hδ])
      hM := rfl
      ha2 := Real.sq_sqrt (div_nonneg hα.le (by positivity))
      ha0 := Real.sqrt_pos.mpr (div_pos hα (by positivity)) }

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma Base.hyp (hb : Base L δ ρ Δ ε) {f h : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hh : Differentiable ℝ h)
    (hHess : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hsim : ∀ x y, ‖(gradient f x - gradient h x) - (gradient f y - gradient h y)‖ ≤ δ * ‖x - y‖)
    (hLh : ∀ x y, ‖gradient h x - gradient h y‖ ≤ L * ‖x - y‖) :
    Hyp (tuning L δ ρ Δ ε) f h L δ ρ Δ where
  hf := hf
  hh := hh
  hHess := hHess
  hsim := hsim
  hLh := hLh
  hL := hb.hL
  hδ := hb.hδ
  hρ := hb.hρ
  hα := hb.abs.α_pos
  hδdb := hb.abs.hδdb
  hαdb := hb.abs.hαdb
  hM := rfl
  ha := by
    rw [hb.abs.ha2]
    have := hb.abs.db_pos
    field_simp
  ha0 := hb.abs.ha0
  ha1 := hb.abs.a_le
  hη := rfl
  hN := Nat.le_add_left _ _
  hJ := by
    have hQ := hb.abs.Q_ge
    have hpos : 0 < 15 * Real.log (400 * (1 + (L + δ) / Real.sqrt (ρ * ε))) := by
      have := Real.log_pos (by linarith : (1 : ℝ) < 400 * (1 + (L + δ) / Real.sqrt (ρ * ε)))
      linarith
    exact Nat.ceil_pos.mpr hpos
  hCN := hb.abs.hCN (by
    have he : (tuning L δ ρ Δ ε).N - 1 = ⌈(L / δ + 6) * Real.log (2 ^ 110 *
        (1 + (L + δ) / Real.sqrt (ρ * ε)) ^ 10 * (1 + Δ * Real.sqrt (ρ * ε) / ε ^ 2))⌉₊ + 1 := by
      show _ + 2 - 1 = _
      omega
    rw [he]
    push_cast
    linarith [Nat.le_ceil ((L / δ + 6) * Real.log (2 ^ 110 *
        (1 + (L + δ) / Real.sqrt (ρ * ε)) ^ 10 * (1 + Δ * Real.sqrt (ρ * ε) / ε ^ 2)))])
  hCJ := hb.abs.hCJ (Nat.le_ceil _)
  hε := hb.hε
  hCT := hb.abs.hCT (Nat.le_ceil _)
  hCε := hb.abs.hCε

lemma Base.hK (hb : Base L δ ρ Δ ε) :
    Δ < (tuning L δ ρ Δ ε).K * ((tuning L δ ρ Δ ε).α * tau (tuning L δ ρ Δ ε) ρ ^ 2) :=
  hb.abs.hK (by
    show _ ≤ ((⌈2 ^ 19 * Δ * Real.sqrt (ρ * ε) / ε ^ 2⌉₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith [Nat.le_ceil (2 ^ 19 * Δ * Real.sqrt (ρ * ε) / ε ^ 2)])

end Assemble

end LongTails.Proofs.AuxiliaryTuning
