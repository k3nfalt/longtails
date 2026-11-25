import LongTails.Proofs.NcConcaveFailure

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveParams

open LongTails.Proofs.NcConcavePsi LongTails.Proofs.NcConcavePartTwo
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveModel
open LongTails.Setups.StochasticNonconvexConcaveMinimax

noncomputable def Λ1 (q : Params) : ℝ := q.L * q.Δ / q.ε ^ 2
noncomputable def Λ2 (q : Params) : ℝ := q.L * q.D / q.ε
noncomputable def sOf (q : Params) : ℝ := 2 ^ 32 * q.ε / q.L
noncomputable def ℓOf (q : Params) : ℝ := q.L / (6 * cF 2)
noncomputable def nOf (q : Params) : ℕ := ⌊Λ1 q / 2 ^ 58⌋₊ - 1
noncomputable def mOf (q : Params) : ℕ := ⌊Λ2 q / 2 ^ 36⌋₊ - 1
noncomputable def θOf (q : Params) : ℝ := 1 / (2 ^ 90 * Λ1 q ^ 3 * Λ2 q)
noncomputable def c0Of (q : Params) : ℝ := 51 * (ℓOf q * sOf q) ^ 2 / (mOf q + 1)
noncomputable def pOf (q : Params) : ℝ := c0Of q / (c0Of q + q.σ ^ 2)

lemma cF2_eq : cF 2 = 400250 := by unfold cF cP; norm_num

section valid

variable {q : Params} (hv : spec.valid q)
include hv

lemma hL : 0 < q.L := hv.1
lemma hΔ : 0 < q.Δ := hv.2.1
lemma hD : 0 < q.D := hv.2.2.1
lemma hσ : 0 ≤ q.σ := hv.2.2.2.1
lemma hε : 0 < q.ε := hv.2.2.2.2.1
lemma hΛ1 : 2 ^ 67 * q.ε ^ 2 ≤ q.L * q.Δ := hv.2.2.2.2.2.1
lemma hΛ2 : 2 ^ 36 * q.ε ≤ q.L * q.D := hv.2.2.2.2.2.2.1
lemma hdim : 2 ^ 180 * (q.L * q.Δ / q.ε ^ 2) ^ 9 * (q.L * q.D / q.ε) ^ 7 *
    (1 + q.σ ^ 2 * q.L * q.D / q.ε ^ 3) ≤ q.d := hv.2.2.2.2.2.2.2

lemma Λ1_ge : 2 ^ 67 ≤ Λ1 q := by
  have := hε hv
  unfold Λ1; rw [le_div_iff₀ (by positivity)]; exact hΛ1 hv

lemma Λ2_ge : 2 ^ 36 ≤ Λ2 q := by
  have := hε hv
  unfold Λ2; rw [le_div_iff₀ (by positivity)]; exact hΛ2 hv

lemma s_pos : 0 < sOf q := by have := hε hv; have := hL hv; unfold sOf; positivity

lemma ℓ_pos : 0 < ℓOf q := by have := hL hv; unfold ℓOf; rw [cF2_eq]; positivity

omit hv in
lemma radiusAB_eq : radiusAB q = 2 * sOf q := by unfold radiusAB sOf; ring

omit hv in
lemma L_eq : q.L = 6 * (ℓOf q * cF 2) := by
  have : cF 2 ≠ 0 := by rw [cF2_eq]; norm_num
  unfold ℓOf; field_simp

lemma floor1 : (1 : ℝ) ≤ ⌊Λ1 q / 2 ^ 58⌋₊ := by
  have h := Λ1_ge hv
  have : (1 : ℝ) ≤ Λ1 q / 2 ^ 58 := by rw [le_div_iff₀ (by positivity)]; linarith
  exact_mod_cast (Nat.one_le_floor_iff _).mpr this

lemma n_succ : ((nOf q : ℕ) : ℝ) + 1 = ⌊Λ1 q / 2 ^ 58⌋₊ := by
  have h := floor1 hv
  have h1 : 1 ≤ ⌊Λ1 q / 2 ^ 58⌋₊ := by exact_mod_cast h
  unfold nOf
  rw [Nat.cast_sub h1]; push_cast; ring

lemma n_succ_le : ((nOf q : ℕ) : ℝ) + 1 ≤ Λ1 q / 2 ^ 58 := by
  rw [n_succ hv]
  exact Nat.floor_le (by have := Λ1_ge hv; positivity)

lemma n_ge : Λ1 q / 2 ^ 60 ≤ (nOf q : ℝ) := by
  have h := Nat.lt_floor_add_one (Λ1 q / 2 ^ 58)
  have h2 := n_succ hv
  have h3 := Λ1_ge hv
  have : Λ1 q / 2 ^ 58 - 1 < (nOf q : ℝ) + 1 := by rw [h2]; linarith
  have : Λ1 q / 2 ^ 60 ≤ Λ1 q / 2 ^ 58 - 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : Λ1 q / 2 ^ 58 * 2 ^ 60 = 4 * Λ1 q := by field_simp; norm_num
    nlinarith
  linarith

lemma floor2 : (1 : ℝ) ≤ ⌊Λ2 q / 2 ^ 36⌋₊ := by
  have h := Λ2_ge hv
  have : (1 : ℝ) ≤ Λ2 q / 2 ^ 36 := by rw [le_div_iff₀ (by positivity)]; linarith
  exact_mod_cast (Nat.one_le_floor_iff _).mpr this

lemma m_succ : ((mOf q : ℕ) : ℝ) + 1 = ⌊Λ2 q / 2 ^ 36⌋₊ := by
  have h := floor2 hv
  have h1 : 1 ≤ ⌊Λ2 q / 2 ^ 36⌋₊ := by exact_mod_cast h
  unfold mOf
  rw [Nat.cast_sub h1]; push_cast; ring

lemma m_succ_le : ((mOf q : ℕ) : ℝ) + 1 ≤ Λ2 q / 2 ^ 36 := by
  rw [m_succ hv]
  exact Nat.floor_le (by have := Λ2_ge hv; positivity)

lemma m_succ_ge : Λ2 q / 2 ^ 37 ≤ (mOf q : ℝ) + 1 := by
  have h := Nat.lt_floor_add_one (Λ2 q / 2 ^ 36)
  have h2 := m_succ hv
  have h3 := Λ2_ge hv
  have hx : 1 ≤ Λ2 q / 2 ^ 36 := by rw [le_div_iff₀ (by positivity)]; linarith
  have : Λ2 q / 2 ^ 37 = (Λ2 q / 2 ^ 36) / 2 := by ring
  rw [this, h2]
  have := floor2 hv
  rcases le_or_gt (Λ2 q / 2 ^ 36) 2 with h4 | h4
  · linarith
  · linarith

lemma radiusU_sq : radiusU q ^ 2 = 2 ^ 14 * (q.Δ / q.L) := by
  unfold radiusU
  rw [mul_pow, Real.sq_sqrt (by have := hΔ hv; have := hL hv; positivity)]; norm_num

lemma radiusU_pos : 0 < radiusU q := by
  unfold radiusU; have := hΔ hv; have := hL hv; positivity

lemma hRU : 256 * ((nOf q : ℝ) + 1) * sOf q ^ 2 ≤ radiusU q ^ 2 := by
  rw [radiusU_sq hv]
  have h := n_succ_le hv
  have hε := hε hv
  have hL := hL hv
  have hs : sOf q ^ 2 = 2 ^ 64 * q.ε ^ 2 / q.L ^ 2 := by unfold sOf; ring
  rw [hs]
  have e : Λ1 q / 2 ^ 58 * (256 * (2 ^ 64 * q.ε ^ 2 / q.L ^ 2)) = 2 ^ 14 * (q.Δ / q.L) := by
    unfold Λ1; field_simp; ring
  calc 256 * ((nOf q : ℝ) + 1) * (2 ^ 64 * q.ε ^ 2 / q.L ^ 2) =
      ((nOf q : ℝ) + 1) * (256 * (2 ^ 64 * q.ε ^ 2 / q.L ^ 2)) := by ring
    _ ≤ Λ1 q / 2 ^ 58 * (256 * (2 ^ 64 * q.ε ^ 2 / q.L ^ 2)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := e

lemma hD8 : 8 * (sOf q * ((mOf q : ℝ) + 1)) ^ 2 ≤ (q.D / 2) ^ 2 := by
  have h := m_succ_le hv
  have hε := hε hv
  have hL := hL hv
  have hD := hD hv
  have h1 : sOf q * ((mOf q : ℝ) + 1) ≤ q.D / 16 := by
    calc sOf q * ((mOf q : ℝ) + 1) ≤ sOf q * (Λ2 q / 2 ^ 36) :=
          mul_le_mul_of_nonneg_left h (s_pos hv).le
      _ = q.D / 16 := by unfold sOf Λ2; field_simp; ring
  have h0 : 0 ≤ sOf q * ((mOf q : ℝ) + 1) := by have := s_pos hv; positivity
  nlinarith

lemma θ_pos : 0 < θOf q := by
  have := Λ1_ge hv; have := Λ2_ge hv; unfold θOf; positivity

lemma Λ1Λ2_ge : 1 ≤ Λ1 q ^ 3 * Λ2 q := by
  have h1 := Λ1_ge hv; have h2 := Λ2_ge hv
  have : (1 : ℝ) ≤ Λ1 q ^ 3 := one_le_pow₀ (by linarith)
  nlinarith

lemma θ_le_one : θOf q ≤ 1 := by
  have := Λ1Λ2_ge hv
  unfold θOf
  rw [div_le_one (by have := Λ1_ge hv; have := Λ2_ge hv; positivity)]
  nlinarith

lemma Λ1_ge_one : 1 ≤ Λ1 q := le_trans (by norm_num) (Λ1_ge hv)
lemma Λ2_ge_one : 1 ≤ Λ2 q := le_trans (by norm_num) (Λ2_ge hv)

lemma n_succ_le' : ((nOf q : ℕ) : ℝ) + 1 ≤ Λ1 q := by
  have h := n_succ_le hv; have h1 := Λ1_ge_one hv
  have : Λ1 q / 2 ^ 58 ≤ Λ1 q := div_le_self (by linarith) (by norm_num)
  linarith

lemma m_succ_le' : ((mOf q : ℕ) : ℝ) + 1 ≤ Λ2 q := by
  have h := m_succ_le hv; have h1 := Λ2_ge_one hv
  have : Λ2 q / 2 ^ 36 ≤ Λ2 q := div_le_self (by linarith) (by norm_num)
  linarith

lemma U_le : radiusU q / sOf q ≤ Λ1 q := by
  have hs := s_pos hv
  have hR := radiusU_pos hv
  have h1 := Λ1_ge_one hv
  have hsq : (radiusU q / sOf q) ^ 2 = Λ1 q / 2 ^ 50 := by
    rw [div_pow, radiusU_sq hv]
    have hε := hε hv; have hL := hL hv
    unfold sOf Λ1; field_simp
  have h2 : (radiusU q / sOf q) ^ 2 ≤ Λ1 q ^ 2 := by
    rw [hsq]
    have : Λ1 q / 2 ^ 50 ≤ Λ1 q := div_le_self (by linarith) (by norm_num)
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).mp h2

lemma Y_le : q.D / 2 / sOf q ≤ Λ2 q := by
  have hε := hε hv; have hL := hL hv; have hD := hD hv
  have e : q.D / 2 / sOf q = Λ2 q / 2 ^ 33 := by unfold sOf Λ2; field_simp
  rw [e]; exact div_le_self (by linarith [Λ2_ge_one hv]) (by norm_num)

lemma closeBound_le :
    closeBound (nOf q) (mOf q) (radiusU q / sOf q) (q.D / 2 / sOf q) ≤ 2 ^ 17 * (Λ1 q ^ 3 * Λ2 q) := by
  have hn := n_succ_le' hv
  have hm := m_succ_le' hv
  have hU := U_le hv
  have hY := Y_le hv
  have hU0 : 0 ≤ radiusU q / sOf q := div_nonneg (radiusU_pos hv).le (s_pos hv).le
  have hY0 : 0 ≤ q.D / 2 / sOf q := div_nonneg (by linarith [hD hv]) (s_pos hv).le
  have h1 := Λ1_ge_one hv
  have h2 := Λ2_ge_one hv
  have hn0 : (0 : ℝ) ≤ nOf q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ mOf q := Nat.cast_nonneg _
  unfold closeBound
  have hc : cη = 10000 := rfl
  rw [hc]
  have t1 : 10000 * ((nOf q : ℝ) + 1) * (5 + 2 * (radiusU q / sOf q)) ≤ 10000 * Λ1 q * (7 * Λ1 q) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) (by linarith) (by positivity)
      (by positivity)
  have t2 : ((nOf q : ℝ) + 1) ^ 2 * (50 + 4 * (radiusU q / sOf q)) ≤ Λ1 q ^ 2 * (54 * Λ1 q) := by
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) hn 2) (by linarith) (by positivity) (by positivity)
  have t3 : (nOf q : ℝ) * (8 * ((mOf q : ℝ) + 1) + 12 * (q.D / 2 / sOf q) + 20) ≤
      Λ1 q * (40 * Λ2 q) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hA : Λ1 q ^ 2 ≤ Λ1 q ^ 3 * Λ2 q := by
    have : Λ1 q ^ 2 ≤ Λ1 q ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ Λ1 q by linarith) 3]
  have hB : Λ1 q ^ 3 ≤ Λ1 q ^ 3 * Λ2 q := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ Λ1 q by linarith) 3]
  have hC : Λ1 q * Λ2 q ≤ Λ1 q ^ 3 * Λ2 q := by
    have : Λ1 q ≤ Λ1 q ^ 3 := by nlinarith
    nlinarith
  nlinarith

noncomputable def ηOf (q : Params) : ℝ :=
  ℓOf q * sOf q ^ 2 * (θOf q * closeBound (nOf q) (mOf q) (radiusU q / sOf q) (q.D / 2 / sOf q))

lemma θCB_le : θOf q * closeBound (nOf q) (mOf q) (radiusU q / sOf q) (q.D / 2 / sOf q) ≤ 1 / 2 ^ 73 := by
  have h := closeBound_le hv
  have h1 := Λ1Λ2_ge hv
  have hθ : θOf q = 1 / 2 ^ 90 / (Λ1 q ^ 3 * Λ2 q) := by unfold θOf; field_simp
  rw [hθ]
  have hpos : 0 < Λ1 q ^ 3 * Λ2 q := by linarith
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

lemma η_nonneg : 0 ≤ ηOf q := by
  have := closeBound_le hv
  unfold ηOf
  have h0 : 0 ≤ closeBound (nOf q) (mOf q) (radiusU q / sOf q) (q.D / 2 / sOf q) := by
    unfold closeBound
    have := div_nonneg (radiusU_pos hv).le (s_pos hv).le
    have := div_nonneg (by linarith [hD hv] : (0 : ℝ) ≤ q.D / 2) (s_pos hv).le
    have hc : (0 : ℝ) ≤ cη := by norm_num [cη]
    positivity
  have := ℓ_pos hv; have := s_pos hv; have := θ_pos hv
  positivity

lemma hηL : 32 * q.L * ηOf q ≤ (cδ / 6 * ℓOf q * sOf q) ^ 2 := by
  have h := θCB_le hv
  have hl := ℓ_pos hv
  have hs := s_pos hv
  rw [L_eq, cF2_eq]
  unfold ηOf cδ
  have hx := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 32 * (6 * (ℓOf q * 400250)) * (ℓOf q * sOf q ^ 2))
  nlinarith [mul_pos hl hs, sq_nonneg (ℓOf q * sOf q)]

lemma hsmall : cδ / 3 * ℓOf q / (2 * q.L) + θOf q / 2 ≤ 1 / 4 := by
  have hl := ℓ_pos hv
  have hθ := θ_le_one hv
  have h1 := Λ1Λ2_ge hv
  have hθ' : θOf q ≤ 1 / 2 ^ 90 := by
    unfold θOf
    rw [div_le_div_iff₀ (by have := Λ1_ge hv; have := Λ2_ge hv; positivity) (by norm_num)]
    nlinarith
  rw [L_eq, cF2_eq]
  have e : cδ / 3 * ℓOf q / (2 * (6 * (ℓOf q * 400250))) = cδ / 3 / 4803000 := by
    field_simp; ring
  rw [e]; unfold cδ; linarith

omit hv in
lemma alpha_mOf_sq : alpha (mOf q) ^ 2 = 1 / ((mOf q : ℝ) + 1) := alpha_sq _

lemma θ_secret : 18 * cF 2 ^ 2 * θOf q ^ 2 ≤ alpha (mOf q) ^ 2 := by
  rw [alpha_mOf_sq, cF2_eq]
  have hm := m_succ_le' hv
  have h1 := Λ1_ge_one hv
  have h2 := Λ2_ge_one hv
  have hθ : θOf q ≤ 1 / (2 ^ 90 * Λ2 q) := by
    unfold θOf
    apply one_div_le_one_div_of_le (by positivity)
    have : (1 : ℝ) ≤ Λ1 q ^ 3 := one_le_pow₀ h1
    nlinarith
  have hθ0 := (θ_pos hv).le
  have hsq : θOf q ^ 2 ≤ (1 / (2 ^ 90 * Λ2 q)) ^ 2 := pow_le_pow_left₀ hθ0 hθ 2
  have hm0 : (0 : ℝ) < (mOf q : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hm0]
  have : (1 / (2 ^ 90 * Λ2 q)) ^ 2 * ((mOf q : ℝ) + 1) ≤ 1 / 2 ^ 180 := by
    rw [div_pow, one_pow, mul_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

lemma c0_pos : 0 < c0Of q := by
  have := ℓ_pos hv; have := s_pos hv; unfold c0Of; positivity

lemma p_pos : 0 < pOf q := by
  have := c0_pos hv; unfold pOf; positivity

lemma p_le_one : pOf q ≤ 1 := by
  have := c0_pos hv
  unfold pOf; rw [div_le_one (by positivity)]; nlinarith [sq_nonneg q.σ]

lemma variance_le (C : ℝ) (hC : C ≤ 51 * alpha (mOf q) ^ 2) :
    (1 / pOf q - 1) * ((ℓOf q * sOf q) ^ 2 * C) ≤ q.σ ^ 2 := by
  have hc := c0_pos hv
  have e : 1 / pOf q - 1 = q.σ ^ 2 / c0Of q := by unfold pOf; field_simp; ring
  rw [e]
  rw [alpha_mOf_sq] at hC
  have hm0 : (0 : ℝ) < (mOf q : ℝ) + 1 := by positivity
  have hfin : (ℓOf q * sOf q) ^ 2 * (51 * (1 / ((mOf q : ℝ) + 1))) = c0Of q := by
    unfold c0Of; field_simp
  calc q.σ ^ 2 / c0Of q * ((ℓOf q * sOf q) ^ 2 * C) ≤
      q.σ ^ 2 / c0Of q * ((ℓOf q * sOf q) ^ 2 * (51 * (1 / ((mOf q : ℝ) + 1)))) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC (sq_nonneg _))
        exact div_nonneg (sq_nonneg _) hc.le
    _ = q.σ ^ 2 := by rw [hfin]; field_simp

noncomputable def B1 (q : Params) : ℝ := q.L ^ 2 * q.D * q.Δ / (2 ^ 100 * q.ε ^ 3)
noncomputable def B2 (q : Params) : ℝ := q.L ^ 3 * q.D ^ 2 * q.Δ * q.σ ^ 2 / (2 ^ 165 * q.ε ^ 6)

lemma B1_eq : B1 q = Λ1 q * Λ2 q / 2 ^ 100 := by
  have := hε hv; unfold B1 Λ1 Λ2; field_simp

lemma B2_eq : B2 q = Λ1 q * Λ2 q ^ 2 * q.σ ^ 2 / (2 ^ 165 * q.ε ^ 2) := by
  have := hε hv; unfold B2 Λ1 Λ2; field_simp

lemma ℓs_eq : ℓOf q * sOf q = 2 ^ 32 * q.ε / 2401500 := by
  have := hL hv; unfold ℓOf sOf; rw [cF2_eq]; field_simp; ring

lemma budget_ok (N : ℕ) (hN : (N : ℝ) ≤ B1 q + B2 q) :
    (N : ℝ) * pOf q ≤ (nOf q : ℝ) * ((mOf q : ℝ) + 1) / 8 := by
  have hn := n_ge hv
  have hm := m_succ_ge hv
  have h1 := Λ1_ge_one hv
  have h2 := Λ2_ge_one hv
  have hc := c0_pos hv
  have hε := hε hv
  set X := (nOf q : ℝ) * ((mOf q : ℝ) + 1) / 8
  have hn0 : (0 : ℝ) ≤ nOf q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) < (mOf q : ℝ) + 1 := by positivity
  have hX1 : B1 q ≤ X := by
    rw [B1_eq hv]
    have : Λ1 q / 2 ^ 60 * (Λ2 q / 2 ^ 37) ≤ (nOf q : ℝ) * ((mOf q : ℝ) + 1) :=
      mul_le_mul hn hm (by positivity) hn0
    simp only [X]
    have e : Λ1 q * Λ2 q / 2 ^ 100 = Λ1 q / 2 ^ 60 * (Λ2 q / 2 ^ 37) / 8 := by ring
    rw [e]; linarith
  have hX2 : B2 q * c0Of q ≤ X * q.σ ^ 2 := by
    rw [B2_eq hv]
    have hc0 : c0Of q = 51 * (2 ^ 32 * q.ε / 2401500) ^ 2 / ((mOf q : ℝ) + 1) := by
      unfold c0Of; rw [ℓs_eq hv]
    rw [hc0]
    have hnm : Λ1 q / 2 ^ 60 * (Λ2 q / 2 ^ 37) ^ 2 ≤ (nOf q : ℝ) * ((mOf q : ℝ) + 1) ^ 2 :=
      mul_le_mul hn (pow_le_pow_left₀ (by positivity) hm 2) (by positivity) hn0
    simp only [X]
    rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    have hσ := sq_nonneg q.σ
    have key : Λ1 q * Λ2 q ^ 2 * (51 * (2 ^ 32) ^ 2) ≤
        (nOf q : ℝ) * ((mOf q : ℝ) + 1) ^ 2 * (2 ^ 165 * 2401500 ^ 2 / 8) := by
      have hpos : 0 ≤ Λ1 q / 2 ^ 60 * (Λ2 q / 2 ^ 37) ^ 2 := by positivity
      calc Λ1 q * Λ2 q ^ 2 * (51 * (2 ^ 32) ^ 2) =
          (51 * 2 ^ 198) * (Λ1 q / 2 ^ 60 * (Λ2 q / 2 ^ 37) ^ 2) := by ring
        _ ≤ (2 ^ 165 * 2401500 ^ 2 / 8) * (Λ1 q / 2 ^ 60 * (Λ2 q / 2 ^ 37) ^ 2) :=
            mul_le_mul_of_nonneg_right (by norm_num) hpos
        _ ≤ (2 ^ 165 * 2401500 ^ 2 / 8) * ((nOf q : ℝ) * ((mOf q : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hnm (by norm_num)
        _ = _ := by ring
    have e1 : Λ1 q * Λ2 q ^ 2 * q.σ ^ 2 * (51 * (2 ^ 32 * q.ε / 2401500) ^ 2) =
        Λ1 q * Λ2 q ^ 2 * (51 * (2 ^ 32) ^ 2) * q.σ ^ 2 * q.ε ^ 2 / 2401500 ^ 2 := by ring
    have e2 : (nOf q : ℝ) * ((mOf q : ℝ) + 1) / 8 * q.σ ^ 2 * (2 ^ 165 * q.ε ^ 2 * ((mOf q : ℝ) + 1)) =
        (nOf q : ℝ) * ((mOf q : ℝ) + 1) ^ 2 * (2 ^ 165 * 2401500 ^ 2 / 8) * q.σ ^ 2 * q.ε ^ 2 /
          2401500 ^ 2 := by ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have := mul_le_mul_of_nonneg_right key (mul_nonneg hσ (sq_nonneg q.ε))
    nlinarith
  have hp : pOf q = c0Of q / (c0Of q + q.σ ^ 2) := rfl
  rw [hp, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hB2 : 0 ≤ B2 q := by rw [B2_eq hv]; positivity
  nlinarith [mul_le_mul_of_nonneg_right hN hc.le]

noncomputable def Bsq (q : Params) : ℝ :=
  12 * (radiusU q ^ 2 + 4 * sOf q ^ 2 + q.D ^ 2 / 4) / sOf q ^ 2

lemma Bsq_le : Bsq q ≤ 2 ^ 7 * (Λ1 q * Λ2 q ^ 2) := by
  have hs := s_pos hv
  have h1 := Λ1_ge_one hv
  have h2 := Λ2_ge_one hv
  have e1 : radiusU q ^ 2 / sOf q ^ 2 = Λ1 q / 2 ^ 50 := by
    rw [radiusU_sq hv]; have := hε hv; have := hL hv; unfold sOf Λ1; field_simp
  have e2 : q.D ^ 2 / 4 / sOf q ^ 2 = (Λ2 q / 2 ^ 33) ^ 2 := by
    have := hε hv; have := hL hv; unfold sOf Λ2; field_simp; ring
  have e : Bsq q = 12 * (Λ1 q / 2 ^ 50 + 4 + (Λ2 q / 2 ^ 33) ^ 2) := by
    unfold Bsq; rw [← e1, ← e2]; field_simp
  rw [e]
  have a1 : Λ1 q / 2 ^ 50 ≤ Λ1 q * Λ2 q ^ 2 := by
    have : Λ1 q / 2 ^ 50 ≤ Λ1 q := div_le_self (by linarith) (by norm_num)
    have : (1 : ℝ) ≤ Λ2 q ^ 2 := one_le_pow₀ h2
    nlinarith
  have a2 : (4 : ℝ) ≤ 4 * (Λ1 q * Λ2 q ^ 2) := by
    have : (1 : ℝ) ≤ Λ2 q ^ 2 := one_le_pow₀ h2
    nlinarith
  have a3 : (Λ2 q / 2 ^ 33) ^ 2 ≤ Λ1 q * Λ2 q ^ 2 := by
    have : (Λ2 q / 2 ^ 33) ^ 2 ≤ Λ2 q ^ 2 :=
      pow_le_pow_left₀ (by positivity) (div_le_self (by linarith) (by norm_num)) 2
    nlinarith [sq_nonneg (Λ2 q)]
  nlinarith

lemma K_le : ((LongTails.Proofs.NcConcaveEmbed.K (nOf q) (mOf q) : ℕ) : ℝ) ≤ 4 * (Λ1 q * Λ2 q) := by
  have hn := n_succ_le' hv
  have hm := m_succ_le' hv
  have hn0 : (0 : ℝ) ≤ nOf q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ mOf q := Nat.cast_nonneg _
  unfold LongTails.Proofs.NcConcaveEmbed.K
  push_cast
  have : (nOf q : ℝ) * ((mOf q : ℝ) + 4) + 1 ≤ 4 * (((nOf q : ℝ) + 1) * ((mOf q : ℝ) + 1)) := by nlinarith
  have h2 : ((nOf q : ℝ) + 1) * ((mOf q : ℝ) + 1) ≤ Λ1 q * Λ2 q :=
    mul_le_mul hn hm (by positivity) (by linarith [Λ1_ge_one hv])
  linarith

lemma dim_ok (N : ℕ) (hN : (N : ℝ) ≤ B1 q + B2 q) :
    8 * ((N + 1 : ℕ) : ℝ) * ((LongTails.Proofs.NcConcaveEmbed.K (nOf q) (mOf q) : ℕ) : ℝ) *
        (Bsq q / (θOf q / 2) ^ 2) + ((LongTails.Proofs.NcConcaveEmbed.K (nOf q) (mOf q) : ℕ) : ℝ) ≤ q.d := by
  have h1 := Λ1_ge_one hv
  have h2 := Λ2_ge_one hv
  have hΛ2 := Λ2_ge hv
  have hε := hε hv
  have hσ := sq_nonneg q.σ
  set S := q.σ ^ 2 * q.L * q.D / q.ε ^ 3
  have hS : 0 ≤ S := by have := hL hv; have := hD hv; positivity
  have hB2 : B2 q = Λ1 q * Λ2 q * S / 2 ^ 165 := by
    rw [B2_eq hv]; unfold Λ2 at *; simp only [S]; field_simp
  have hN1 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (Λ1 q * Λ2 q) * (1 + S) := by
    push_cast
    have e1 : B1 q ≤ Λ1 q * Λ2 q := by
      rw [B1_eq hv]; exact div_le_self (by positivity) (by norm_num)
    have e2 : B2 q ≤ Λ1 q * Λ2 q * S := by
      rw [hB2]; exact div_le_self (by positivity) (by norm_num)
    have e3 : (1 : ℝ) ≤ Λ1 q * Λ2 q := by nlinarith
    nlinarith
  have hK := K_le hv
  have hBs := Bsq_le hv
  have hθ : 1 / (θOf q / 2) ^ 2 = 4 * 2 ^ 180 * (Λ1 q ^ 6 * Λ2 q ^ 2) := by
    unfold θOf; field_simp; ring
  have hX : 0 ≤ Λ1 q * Λ2 q := by positivity
  have hBsq0 : 0 ≤ Bsq q := by unfold Bsq; have := s_pos hv; have := radiusU_pos hv; positivity
  have hK0 : (0 : ℝ) ≤ ((LongTails.Proofs.NcConcaveEmbed.K (nOf q) (mOf q) : ℕ) : ℝ) := Nat.cast_nonneg _
  have step : 8 * ((N + 1 : ℕ) : ℝ) * ((LongTails.Proofs.NcConcaveEmbed.K (nOf q) (mOf q) : ℕ) : ℝ) *
      (Bsq q / (θOf q / 2) ^ 2) ≤
      8 * (2 * (Λ1 q * Λ2 q) * (1 + S)) * (4 * (Λ1 q * Λ2 q)) *
        (2 ^ 7 * (Λ1 q * Λ2 q ^ 2) * (4 * 2 ^ 180 * (Λ1 q ^ 6 * Λ2 q ^ 2))) := by
    rw [div_eq_mul_one_div, hθ]
    apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hN1 (by norm_num)) hK hK0 (by positivity))
      (mul_le_mul_of_nonneg_right hBs (by positivity)) (by positivity) (by positivity)
  have e : 8 * (2 * (Λ1 q * Λ2 q) * (1 + S)) * (4 * (Λ1 q * Λ2 q)) *
      (2 ^ 7 * (Λ1 q * Λ2 q ^ 2) * (4 * 2 ^ 180 * (Λ1 q ^ 6 * Λ2 q ^ 2))) =
      2 ^ 195 * (Λ1 q ^ 9 * Λ2 q ^ 6 * (1 + S)) := by ring
  rw [e] at step
  have hd := hdim hv
  have e2 : 2 ^ 180 * (q.L * q.Δ / q.ε ^ 2) ^ 9 * (q.L * q.D / q.ε) ^ 7 * (1 + S) =
      2 ^ 180 * (Λ1 q ^ 9 * Λ2 q ^ 7 * (1 + S)) := by unfold Λ1 Λ2; ring
  rw [e2] at hd
  have hY : 0 ≤ Λ1 q ^ 9 * Λ2 q ^ 6 * (1 + S) := by positivity
  have hbig : 2 ^ 195 * (Λ1 q ^ 9 * Λ2 q ^ 6 * (1 + S)) + 4 * (Λ1 q * Λ2 q) ≤
      2 ^ 180 * (Λ1 q ^ 9 * Λ2 q ^ 7 * (1 + S)) := by
    have a1 : Λ1 q * Λ2 q ≤ Λ1 q ^ 9 * Λ2 q ^ 6 * (1 + S) := by
      have : Λ1 q ≤ Λ1 q ^ 9 := by
        calc Λ1 q = Λ1 q ^ 1 := (pow_one _).symm
          _ ≤ Λ1 q ^ 9 := pow_le_pow_right₀ h1 (by norm_num)
      have : Λ2 q ≤ Λ2 q ^ 6 := by
        calc Λ2 q = Λ2 q ^ 1 := (pow_one _).symm
          _ ≤ Λ2 q ^ 6 := pow_le_pow_right₀ h2 (by norm_num)
      have : Λ1 q * Λ2 q ≤ Λ1 q ^ 9 * Λ2 q ^ 6 := mul_le_mul (by assumption) (by assumption) (by linarith) (by positivity)
      nlinarith [pow_nonneg (show (0:ℝ) ≤ Λ1 q by linarith) 9, pow_nonneg (show (0:ℝ) ≤ Λ2 q by linarith) 6]
    have a2 : Λ1 q ^ 9 * Λ2 q ^ 7 * (1 + S) = Λ2 q * (Λ1 q ^ 9 * Λ2 q ^ 6 * (1 + S)) := by ring
    rw [a2]
    nlinarith
  linarith

end valid

end LongTails.Proofs.NcConcaveParams
