import LongTails.Proofs.RiverValleyMaster
import LongTails.Proofs.RiverValleyTuneFinal

namespace OracleTemplate.RiverValley

noncomputable def lamH (Lh ρh G Γ LJ ρJ μ Lv σu : ℝ) : ℝ :=
  256 * (Γ * Lh + 2 * LJ * G) ^ 2 / μ + 32 * Γ * (Γ * Lh + 2 * LJ * G) +
    2 * (2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2) * σu / Lv

noncomputable def Nhat (Lh ρh G Γ LJ ρJ μ Lv σu σv : ℝ) : ℝ :=
  2 * Lh * σu ^ 2 + 7 * lamH Lh ρh G Γ LJ ρJ μ Lv σu * (σv ^ 2 + σu ^ 2) +
    (Γ * Lh + 2 * LJ * G) * σu * σv + (2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2) * σu ^ 3 / μ +
    (2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2) * Γ * G * σu ^ 2 / Lv +
    2 * LJ ^ 2 * σu ^ 4 / Lv

noncomputable def Mcf (Lh ρh G Γ LJ μ Lv σu σv : ℝ) : ℝ :=
  (2 * G * ρh + Lh ^ 2) * σu ^ 2 + 4 * Lv ^ 2 * σv ^ 2 + 20 * Γ ^ 2 * μ ^ 2 * σu ^ 2 +
    8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4

lemma lamH_eq {Lh ρh G Γ LJ ρJ μ Lv σu : ℝ} (hμ : 0 < μ) :
    lamOf Lh ρh G (Γ * μ) μ Lv LJ ρJ σu = lamH Lh ρh G Γ LJ ρJ μ Lv σu := by
  have e : Γ * μ / μ = Γ := by field_simp
  simp only [lamOf, lamH, e]
  field_simp

set_option maxHeartbeats 1000000 in
lemma N_bound {Lh ρh G Γ LJ ρJ μ Lv σu σv : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv) (hLh : 0 ≤ Lh)
    (hρh : 0 ≤ ρh) (hG : 0 ≤ G) (hΓ0 : 0 ≤ Γ) (hLJ : 0 ≤ LJ) (hρJ : 0 ≤ ρJ) (hσu : 0 ≤ σu)
    (hσv : 0 ≤ σv) (hΓ : 16 * Γ ≤ 1) (hLm : 64 * (Γ * Lh + 2 * LJ * G) ≤ μ)
    (hc : 64 * (2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2) * σu ≤ μ * Lv)
    (hLh16 : 16 * Lh ≤ μ) :
    NOf Lh ρh G (Γ * μ) μ Lv LJ ρJ σu σv +
        16 * Lh * Γ ^ 2 * (4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)) ≤
      Nhat Lh ρh G Γ LJ ρJ μ Lv σu σv := by
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have e : Γ * μ / μ = Γ := by field_simp
  have hlam := lamH_eq (Lh := Lh) (ρh := ρh) (G := G) (Γ := Γ) (LJ := LJ) (ρJ := ρJ) (Lv := Lv)
    (σu := σu) hμ
  set lam := lamH Lh ρh G Γ LJ ρJ μ Lv σu
  set Lm' := Γ * Lh + 2 * LJ * G
  set c' := 2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2
  have hLm'0 : 0 ≤ Lm' := by positivity
  have hc'0 : 0 ≤ c' := by positivity
  have hlamdef : lam = 256 * Lm' ^ 2 / μ + 32 * Γ * Lm' + 2 * c' * σu / Lv := rfl
  have hlamΓ : 32 * Γ * Lm' ≤ lam := by
    have : 0 ≤ 256 * Lm' ^ 2 / μ := by positivity
    have : 0 ≤ 2 * c' * σu / Lv := by positivity
    linarith
  have hlamμ : lam ≤ μ / 8 := by
    have h1 : 256 * Lm' ^ 2 / μ ≤ μ / 16 := by
      rw [div_le_div_iff₀ hμ (by norm_num)]
      have := mul_le_mul hLm hLm (by positivity) hμ.le; nlinarith
    have h2 : 32 * Γ * Lm' ≤ μ / 32 := by nlinarith
    have h3 : 2 * c' * σu / Lv ≤ μ / 32 := by
      rw [div_le_div_iff₀ hLv (by norm_num)]; linarith
    linarith
  have hlam0 : 0 ≤ lam := le_trans (by positivity) hlamΓ
  have hΓ16 : Γ ≤ 1 / 16 := by linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
  have hΓ4 : Γ ^ 4 ≤ 1 / 65536 := by
    have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; nlinarith
  have hLm_le : Γ * Lh + LJ * G + 2 * Γ ^ 2 * LJ * G ≤ Lm' := by
    have : 2 * Γ ^ 2 * LJ * G ≤ LJ * G := by
      have := mul_le_mul_of_nonneg_right (by nlinarith : 2 * Γ ^ 2 ≤ 1) (mul_nonneg hLJ hG)
      linarith
    simp only [Lm']; linarith
  have hLJG : LJ * G ≤ Lm' / 2 := by simp only [Lm']; nlinarith
  have hΓLh : Γ * Lh ≤ Lm' := by simp only [Lm']; nlinarith [mul_nonneg hLJ hG]
  have hLJGμ : 128 * (LJ * G) ≤ μ := by linarith
  simp only [NOf, e, hlam, Nhat]
  -- term-by-term
  set Lm := Γ * Lh + LJ * G + 2 * Γ ^ 2 * LJ * G
  have hLm0 : 0 ≤ Lm := by positivity
  have t1 : 2 * (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * σu ^ 2 + 4 * lam * (Γ ^ 2 * σu ^ 2) +
      Lm * (Γ * σu ^ 2) + Γ * G * LJ * σu ^ 2 + lam * LJ * Γ * G * σu ^ 2 / (4 * Lv) +
      16 * Lh * Γ ^ 2 * (4 * (Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
        Γ * G * LJ * σu ^ 2 / (4 * Lv)) ≤ 2 * Lh * σu ^ 2 + 7 * lam * σu ^ 2 := by
    have a1 : 4 * Γ * Lm + Γ * Lm + Γ * (LJ * G) ≤ 6 * Γ * Lm' := by
      have := mul_le_mul_of_nonneg_left hLm_le hΓ0
      have := mul_le_mul_of_nonneg_left hLJG hΓ0
      nlinarith
    have a2 : 6 * Γ * Lm' ≤ lam / 5 := by linarith
    have a3 : 20 * lam * Γ ^ 2 ≤ lam / 10 := by nlinarith
    have a4 : lam * LJ * Γ * G / (4 * Lv) ≤ lam / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have b1 : LJ * G ≤ Lv := by linarith
      have := mul_le_mul_of_nonneg_left b1 (mul_nonneg hlam0 hΓ0)
      nlinarith
    have a5 : 16 * Lh * Γ ^ 2 * (20 * Γ ^ 2 + Γ * G * LJ / (4 * Lv)) ≤ Lh := by
      have b1 : Γ * G * LJ / (4 * Lv) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : G * LJ ≤ Lv := by nlinarith
        nlinarith
      have b2 : 20 * Γ ^ 2 + Γ * G * LJ / (4 * Lv) ≤ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left b2 (by positivity : (0:ℝ) ≤ 16 * Lh * Γ ^ 2)
      nlinarith
    have e1 : 2 * (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * σu ^ 2 + 4 * lam * (Γ ^ 2 * σu ^ 2) +
        Lm * (Γ * σu ^ 2) + Γ * G * LJ * σu ^ 2 + lam * LJ * Γ * G * σu ^ 2 / (4 * Lv) +
        16 * Lh * Γ ^ 2 * (4 * (Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          Γ * G * LJ * σu ^ 2 / (4 * Lv)) =
        (Lh + (4 * Γ * Lm + Γ * Lm + Γ * (LJ * G)) + 20 * lam * Γ ^ 2 +
          lam * LJ * Γ * G / (4 * Lv) + 16 * Lh * Γ ^ 2 * (20 * Γ ^ 2 + Γ * G * LJ / (4 * Lv))) *
          σu ^ 2 := by ring
    rw [e1]
    have : Lh + (4 * Γ * Lm + Γ * Lm + Γ * (LJ * G)) + 20 * lam * Γ ^ 2 +
        lam * LJ * Γ * G / (4 * Lv) + 16 * Lh * Γ ^ 2 * (20 * Γ ^ 2 + Γ * G * LJ / (4 * Lv)) ≤
        2 * Lh + 7 * lam := by linarith
    have := mul_le_mul_of_nonneg_right this (sq_nonneg σu)
    linarith
  have t2 : 4 * lam * σv ^ 2 + 16 * Lh * Γ ^ 2 * (4 * σv ^ 2) ≤ 7 * lam * σv ^ 2 := by
    have : 64 * Lh * Γ ^ 2 ≤ 2 * lam := by
      have := mul_le_mul_of_nonneg_left hΓLh hΓ0; nlinarith
    have := mul_le_mul_of_nonneg_right this (sq_nonneg σv)
    nlinarith
  have t3 : Lm * (σu * σv) ≤ Lm' * σu * σv := by
    have := mul_le_mul_of_nonneg_right hLm_le (mul_nonneg hσu hσv); linarith
  have t4 : c' * Γ * G * σu ^ 2 / (8 * Lv) ≤ c' * Γ * G * σu ^ 2 / Lv := by
    apply div_le_div_of_nonneg_left (by positivity) hLv (by linarith)
  have t5 : 8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv) +
      16 * Lh * Γ ^ 2 * (8 * LJ ^ 2 * σu ^ 4 / (μ * Lv)) ≤ 2 * LJ ^ 2 * σu ^ 4 / Lv := by
    have e1 : 8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv) + 16 * Lh * Γ ^ 2 * (8 * LJ ^ 2 * σu ^ 4 / (μ * Lv)) =
        (8 * lam + 128 * Lh * Γ ^ 2) / μ * (LJ ^ 2 * σu ^ 4 / Lv) := by field_simp; ring
    rw [e1]
    have : (8 * lam + 128 * Lh * Γ ^ 2) / μ ≤ 2 := by
      rw [div_le_iff₀ hμ]; nlinarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ LJ ^ 2 * σu ^ 4 / Lv)
    have e : 2 * LJ ^ 2 * σu ^ 4 / Lv = 2 * (LJ ^ 2 * σu ^ 4 / Lv) := by ring
    linarith
  have e2 : 4 * lam * (σv ^ 2 + Γ ^ 2 * σu ^ 2) = 4 * lam * σv ^ 2 + 4 * lam * (Γ ^ 2 * σu ^ 2) := by
    ring
  have e3 : Lm * (σu * σv + Γ * σu ^ 2) = Lm * (σu * σv) + Lm * (Γ * σu ^ 2) := by ring
  have e4 : 16 * Lh * Γ ^ 2 * (4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
      8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)) =
      16 * Lh * Γ ^ 2 * (4 * σv ^ 2) + 16 * Lh * Γ ^ 2 * (4 * (Γ ^ 2 * σu ^ 2) +
        16 * Γ ^ 2 * σu ^ 2 + Γ * G * LJ * σu ^ 2 / (4 * Lv)) +
      16 * Lh * Γ ^ 2 * (8 * LJ ^ 2 * σu ^ 4 / (μ * Lv)) := by ring
  have e5 : (2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2) * Γ * G * σu ^ 2 / (8 * Lv) =
      c' * Γ * G * σu ^ 2 / (8 * Lv) := rfl
  have e6 : 7 * lam * (σv ^ 2 + σu ^ 2) = 7 * lam * σv ^ 2 + 7 * lam * σu ^ 2 := by ring
  rw [e2, e3, e4, e6]
  linarith

lemma Mc_bounds {Lh ρh G Γ LJ μ Lv σu σv : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv)
    (hρh : 0 ≤ ρh) (hG : 0 ≤ G) (hΓ0 : 0 ≤ Γ) (hLJ : 0 ≤ LJ)
    (hΓ : 16 * Γ ≤ 1) (hLh16 : 16 * Lh ≤ μ) :
    let Hw := 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)
    let HA := 4 * (Lv ^ 2 * σv ^ 2 + (Γ * μ) ^ 2 * σu ^ 2) + 16 * (Γ * μ) ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4
    let Mc := Mcf Lh ρh G Γ LJ μ Lv σu σv
    (2 * G * ρh + Lh ^ 2) * σu ^ 2 + 8 * Lh * (Γ * μ) ^ 2 / μ * Hw ≤ Mc ∧ HA ≤ Mc ∧
      μ ^ 2 * Hw ≤ Mc ∧ 0 ≤ Hw ∧ 0 ≤ HA := by
  intro Hw HA Mc
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have hΓ16 : Γ ≤ 1 / 16 := by linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
  have hHw0 : 0 ≤ Hw := by simp only [Hw]; positivity
  have hHA : HA = 4 * Lv ^ 2 * σv ^ 2 + 20 * Γ ^ 2 * μ ^ 2 * σu ^ 2 + 8 * Lv * LJ ^ 2 * σu ^ 4 / μ +
      Γ * μ * G * LJ * σu ^ 2 / 4 := by simp only [HA]; ring
  have hMc : Mc = (2 * G * ρh + Lh ^ 2) * σu ^ 2 + HA := by
    rw [hHA]; simp only [Mc, Mcf]; ring
  have hHA0 : 0 ≤ HA := by rw [hHA]; positivity
  have hμHw : μ ^ 2 * Hw ≤ HA := by
    rw [hHA]
    have e : μ ^ 2 * Hw = 4 * μ ^ 2 * σv ^ 2 + 20 * Γ ^ 2 * μ ^ 2 * σu ^ 2 +
        8 * μ * LJ ^ 2 * σu ^ 4 / Lv + Γ * μ ^ 2 * G * LJ * σu ^ 2 / (4 * Lv) := by
      simp only [Hw]; field_simp; ring
    rw [e]
    have a1 : 4 * μ ^ 2 * σv ^ 2 ≤ 4 * Lv ^ 2 * σv ^ 2 := by
      have := pow_le_pow_left₀ hμ.le hμLv 2; nlinarith [sq_nonneg σv]
    have a2 : 8 * μ * LJ ^ 2 * σu ^ 4 / Lv ≤ 8 * Lv * LJ ^ 2 * σu ^ 4 / μ := by
      rw [div_le_div_iff₀ hLv hμ]
      have := pow_le_pow_left₀ hμ.le hμLv 2
      have : 0 ≤ 8 * LJ ^ 2 * σu ^ 4 := by positivity
      nlinarith
    have a3 : Γ * μ ^ 2 * G * LJ * σu ^ 2 / (4 * Lv) ≤ Γ * μ * G * LJ * σu ^ 2 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ Γ * μ * G * LJ * σu ^ 2 := by positivity
      nlinarith
    linarith
  refine ⟨?_, by rw [hMc]; have : 0 ≤ (2 * G * ρh + Lh ^ 2) * σu ^ 2 := by positivity
                 linarith, ?_, hHw0, hHA0⟩
  · rw [hMc]
    have e : 8 * Lh * (Γ * μ) ^ 2 / μ * Hw = (8 * Lh * Γ ^ 2 / μ) * (μ ^ 2 * Hw) := by
      field_simp
    rw [e]
    have : 8 * Lh * Γ ^ 2 / μ ≤ 1 := by
      rw [div_le_one hμ]; nlinarith
    have := mul_le_mul this hμHw (by positivity) zero_le_one
    linarith
  · rw [hMc]; have : 0 ≤ (2 * G * ρh + Lh ^ 2) * σu ^ 2 := by positivity
    linarith

noncomputable def Rf (Lh ρh G Γ LJ ρJ μ Lv σu σv ε : ℝ) : ℝ :=
  3 + Lv ^ 2 / μ ^ 2 + 4 * Lv ^ 2 * Mcf Lh ρh G Γ LJ μ Lv σu σv /
    (μ ^ 3 * (Lv * ε ^ 2 + 8 * Nhat Lh ρh G Γ LJ ρJ μ Lv σu σv))

lemma one_le_logR {Lh ρh G Γ LJ ρJ μ Lv σu σv ε : ℝ} (hμ : 0 < μ) (hLv : 0 < Lv) (hε : 0 < ε)
    (hN : 0 ≤ Nhat Lh ρh G Γ LJ ρJ μ Lv σu σv) (hM : 0 ≤ Mcf Lh ρh G Γ LJ μ Lv σu σv) :
    3 ≤ Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε ∧ 1 ≤ Real.log (Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε) := by
  have h3 : 3 ≤ Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε := by
    have : 0 ≤ Lv ^ 2 / μ ^ 2 := by positivity
    have : 0 ≤ 4 * Lv ^ 2 * Mcf Lh ρh G Γ LJ μ Lv σu σv /
        (μ ^ 3 * (Lv * ε ^ 2 + 8 * Nhat Lh ρh G Γ LJ ρJ μ Lv σu σv)) := by positivity
    simp only [Rf]; linarith
  refine ⟨h3, ?_⟩
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

set_option maxHeartbeats 4000000 in
lemma tune {Lh ρh G Γ LJ ρJ μ Lv σu σv Δ ε : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv) (hLh : 0 ≤ Lh)
    (hρh : 0 ≤ ρh) (hG : 0 ≤ G) (hΓ0 : 0 ≤ Γ) (hLJ : 0 ≤ LJ) (hρJ : 0 ≤ ρJ) (hσu : 0 ≤ σu)
    (hσv : 0 ≤ σv) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hΓ : 16 * Γ ≤ 1)
    (hLm : 64 * (Γ * Lh + 2 * LJ * G) ≤ μ)
    (hc : 64 * (2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2) * σu ≤ μ * Lv)
    (hval : 32 * Lh * Real.log (Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε) ≤ μ) :
    let Nh := Nhat Lh ρh G Γ LJ ρJ μ Lv σu σv
    let Mc := Mcf Lh ρh G Γ LJ μ Lv σu σv
    let lR := Real.log (Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε)
    let ηs := 1 / (8 * Lv + 64 * Nh / ε ^ 2)
    let T := ⌈256 * Δ * (8 * Lv + 64 * Nh / ε ^ 2) / ε ^ 2⌉₊
    let ηc := 1 / (8 * Lv + 256 * lR * Mc / (μ * ε ^ 2))
    let Kc := ⌈2 * lR * (8 * Lv + 256 * lR * Mc / (μ * ε ^ 2)) / μ⌉₊
    let N := NOf Lh ρh G (Γ * μ) μ Lv LJ ρJ σu σv
    let Sw := (8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ) / μ
    let Hw := 4 * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + 16 * Γ ^ 2 * σu ^ 2 +
          8 * LJ ^ 2 * σu ^ 4 / (μ * Lv) + Γ * G * LJ * σu ^ 2 / (4 * Lv)
    let SA := 8 * Γ ^ 2 * μ + 16 * (LJ * G) ^ 2 / μ + Γ * (LJ * G)
    let HA := 4 * (Lv ^ 2 * σv ^ 2 + (Γ * μ) ^ 2 * σu ^ 2) + 16 * (Γ * μ) ^ 2 * σu ^ 2 +
          8 * Lv * LJ ^ 2 * σu ^ 4 / μ + Γ * μ * G * LJ * σu ^ 2 / 4
    let Ca := (2 * G * ρh + Lh ^ 2) * σu ^ 2
    let θ := 8 * Lh * (Γ * μ) ^ 2 / μ
    let M : ℝ := T + 1
    let A1 := 4 * Δ / (ηs * M) + 2 * ηs * N
    let A2 := 4 * Δ / (μ ^ 2 * ηs * M) + 2 * Sw * A1 / μ + 2 * ηs * Hw / μ
    let Pb := 2 * (A1 + θ * A2 + Kc * ηc ^ 2 * (Ca + θ * Hw))
    let Qb := (1 - ηc * μ / 2) ^ Kc * (Lv ^ 2 * A2) + 2 / μ * (SA * Pb + ηc * HA)
    0 < ηs ∧ 8 * ηs * Lv ≤ 1 ∧ 0 ≤ ηc ∧ 8 * ηc * Lv ≤ 1 ∧ 10 * Lh * ηc * Kc ≤ 1 ∧
      Real.sqrt Pb + (1 + Γ) * Real.sqrt Qb ≤ ε := by
  intro Nh Mc lR ηs T ηc Kc N Sw Hw SA HA Ca θ M A1 A2 Pb Qb
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have hΓ16 : Γ ≤ 1 / 16 := by linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by
    calc Γ ^ 2 = Γ * Γ := sq Γ
      _ ≤ 1 / 16 * (1 / 16) := mul_le_mul hΓ16 hΓ16 hΓ0 (by norm_num)
      _ = 1 / 256 := by norm_num
  have hLJG0 : 0 ≤ LJ * G := mul_nonneg hLJ hG
  have hLJGμ : 128 * (LJ * G) ≤ μ := by
    have := mul_nonneg hΓ0 hLh; linarith
  -- N̂ and Mc
  have hNh0 : 0 ≤ Nh := by
    simp only [Nh, Nhat, lamH]; positivity
  obtain ⟨hR3, hlR⟩ := one_le_logR (Lh := Lh) (ρh := ρh) (G := G) (Γ := Γ) (LJ := LJ) (ρJ := ρJ)
    (σu := σu) (σv := σv) hμ hLv hε hNh0 (by simp only [Mcf]; positivity)
  have hLh32 : 32 * Lh ≤ μ := by
    have := mul_le_mul_of_nonneg_left hlR (by positivity : (0:ℝ) ≤ 32 * Lh); linarith
  have hLh16 : 16 * Lh ≤ μ := by linarith
  have hNb := N_bound hμ hμLv hLh hρh hG hΓ0 hLJ hρJ hσu hσv hΓ hLm hc hLh16
  obtain ⟨hMc1, hMc2, hMc3, hHw0, hHA0⟩ := Mc_bounds (Lh := Lh) (ρh := ρh) (G := G) (Γ := Γ)
    (LJ := LJ) (σu := σu) (σv := σv) hμ hμLv hρh hG hΓ0 hLJ hΓ hLh16
  have hN0 : 0 ≤ N := by
    simp only [N, NOf, lamOf]
    have e : Γ * μ / μ = Γ := by field_simp
    rw [e]; positivity
  have hHwθ : 16 * Lh * Γ ^ 2 * Hw ≤ Nh := by
    have : 0 ≤ 16 * Lh * Γ ^ 2 := by positivity
    have := hNb; simp only [Hw] at *; linarith
  have hNN : N ≤ Nh := by
    have : 0 ≤ 16 * Lh * Γ ^ 2 * Hw := by positivity
    have := hNb; simp only [N, Hw] at *; linarith
  have hMc0 : 0 ≤ Mc := le_trans hHA0 hMc2
  -- ηs
  set D := 8 * Lv + 64 * Nh / ε ^ 2
  have hD : 0 < D := by positivity
  have hηsD : ηs * D = 1 := by have := hD.ne'; simp only [ηs, D] at *; field_simp
  have hηs0 : 0 < ηs := by simp only [ηs]; positivity
  have hηsE : ηs * D = 8 * ηs * Lv + ηs * (64 * Nh / ε ^ 2) := by simp only [D]; ring
  have hηs8 : 8 * ηs * Lv ≤ 1 := by
    have : ηs * (64 * Nh / ε ^ 2) ≥ 0 := by positivity
    linarith
  have hηsN : 64 * ηs * Nh ≤ ε ^ 2 := by
    have h1 : ηs * (64 * Nh / ε ^ 2) ≤ 1 := by
      have : 0 ≤ 8 * ηs * Lv := by positivity
      linarith
    have e : ηs * (64 * Nh / ε ^ 2) = 64 * ηs * Nh / ε ^ 2 := by ring
    rw [e, div_le_one (by positivity)] at h1
    exact h1
  -- M
  have hMpos : 0 < M := by positivity
  have hMT : 256 * Δ * D / ε ^ 2 ≤ M := by
    have := Nat.le_ceil (256 * Δ * (8 * Lv + 64 * Nh / ε ^ 2) / ε ^ 2)
    simp only [M, T, D] at *
    linarith
  have hΔM : 4 * Δ / (ηs * M) ≤ ε ^ 2 / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 := mul_le_mul_of_nonneg_left hMT (by positivity : (0:ℝ) ≤ ηs * ε ^ 2)
    have e : ηs * ε ^ 2 * (256 * Δ * D / ε ^ 2) = 256 * Δ * (ηs * D) := by
      field_simp
    rw [e, hηsD] at h1
    have e2 : ε ^ 2 * (ηs * M) = ηs * ε ^ 2 * M := by ring
    rw [e2]; linarith
  have hA1 : A1 ≤ 3 * ε ^ 2 / 64 := by
    have : 2 * ηs * N ≤ ε ^ 2 / 32 := by
      have := mul_le_mul_of_nonneg_left hNN (by positivity : (0:ℝ) ≤ 2 * ηs); linarith
    simp only [A1]; linarith
  have hA10 : 0 ≤ A1 := by simp only [A1]; positivity
  have hSw : Sw ≤ 1 / (30 * μ) := by
    have a1 : (LJ * G) / μ ≤ 1 / 128 := by rw [div_le_iff₀ hμ]; linarith
    have a0 : 0 ≤ (LJ * G) / μ := by positivity
    have a2 : 16 * (LJ * G) ^ 2 / μ ^ 2 ≤ 1 / 1024 := by
      have e : 16 * (LJ * G) ^ 2 / μ ^ 2 = 16 * ((LJ * G) / μ) ^ 2 := by ring
      rw [e]
      have := mul_le_mul a1 a1 a0 (by norm_num)
      nlinarith
    have a3 : Γ * (LJ * G) / μ ≤ 1 / 2048 := by
      have e : Γ * (LJ * G) / μ = Γ * ((LJ * G) / μ) := by ring
      rw [e]
      have := mul_le_mul hΓ16 a1 a0 (by norm_num)
      linarith
    simp only [Sw]
    rw [div_le_div_iff₀ hμ (by positivity)]
    have : 8 * Γ ^ 2 + 16 * (LJ * G) ^ 2 / μ ^ 2 + Γ * (LJ * G) / μ ≤ 1 / 30 := by linarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 30 * μ)
    linarith
  have hSw0 : 0 ≤ Sw := by
    have : 0 ≤ Γ * (LJ * G) / μ := by positivity
    simp only [Sw]; positivity
  have hA2 : A2 ≤ ε ^ 2 / (48 * μ ^ 2) + 2 * ηs * Hw / μ := by
    have b1 : 4 * Δ / (μ ^ 2 * ηs * M) ≤ ε ^ 2 / (64 * μ ^ 2) := by
      have e1 : 4 * Δ / (μ ^ 2 * ηs * M) = (4 * Δ / (ηs * M)) / μ ^ 2 := by field_simp
      have e2 : ε ^ 2 / (64 * μ ^ 2) = (ε ^ 2 / 64) / μ ^ 2 := by field_simp
      rw [e1, e2]; exact div_le_div_of_nonneg_right hΔM (by positivity)
    have b2 : 2 * Sw * A1 / μ ≤ ε ^ 2 / (320 * μ ^ 2) := by
      have h1 := mul_le_mul hSw hA1 hA10 (by positivity)
      rw [div_le_div_iff₀ hμ (by positivity)]
      have e : 1 / (30 * μ) * (3 * ε ^ 2 / 64) = ε ^ 2 / (640 * μ) := by field_simp; ring
      rw [e] at h1
      have h2 : 2 * Sw * A1 * (320 * μ ^ 2) ≤ 2 * (ε ^ 2 / (640 * μ)) * (320 * μ ^ 2) := by
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 2 * (320 * μ ^ 2))
        linarith
      have e2 : 2 * (ε ^ 2 / (640 * μ)) * (320 * μ ^ 2) = ε ^ 2 * μ := by field_simp; ring
      linarith
    have b3 : ε ^ 2 / (64 * μ ^ 2) + ε ^ 2 / (320 * μ ^ 2) ≤ ε ^ 2 / (48 * μ ^ 2) := by
      have e : ε ^ 2 / (64 * μ ^ 2) + ε ^ 2 / (320 * μ ^ 2) = (3 / 160) * (ε ^ 2 / μ ^ 2) := by
        field_simp; ring
      have e2 : ε ^ 2 / (48 * μ ^ 2) = (1 / 48) * (ε ^ 2 / μ ^ 2) := by field_simp
      rw [e, e2]
      have : 0 ≤ ε ^ 2 / μ ^ 2 := by positivity
      linarith
    simp only [A2]; linarith
  have hθ : θ = 8 * Lh * Γ ^ 2 * μ := by simp only [θ]; field_simp
  have hθA2 : θ * A2 ≤ ε ^ 2 / 1024 + ε ^ 2 / 64 := by
    rw [hθ]
    have h0 : 0 ≤ 8 * Lh * Γ ^ 2 * μ := by positivity
    have h1 := mul_le_mul_of_nonneg_left hA2 h0
    have b1 : 8 * Lh * Γ ^ 2 * μ * (ε ^ 2 / (48 * μ ^ 2)) ≤ ε ^ 2 / 1024 := by
      have e : 8 * Lh * Γ ^ 2 * μ * (ε ^ 2 / (48 * μ ^ 2)) = (Lh * Γ ^ 2 / μ) * (ε ^ 2 / 6) := by
        field_simp; ring
      rw [e]
      have : Lh * Γ ^ 2 / μ ≤ 1 / 4096 := by
        rw [div_le_iff₀ hμ]
        have := mul_le_mul (by linarith : Lh ≤ μ / 16) hΓ2 (sq_nonneg Γ) (by positivity)
        linarith
      have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ ε ^ 2 / 6)
      linarith
    have b2 : 8 * Lh * Γ ^ 2 * μ * (2 * ηs * Hw / μ) ≤ ε ^ 2 / 64 := by
      have e : 8 * Lh * Γ ^ 2 * μ * (2 * ηs * Hw / μ) = ηs * (16 * Lh * Γ ^ 2 * Hw) := by
        field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hHwθ hηs0.le
      linarith
    linarith
  have hA20 : 0 ≤ A2 := by simp only [A2]; positivity
  have hSA : SA ≤ μ / 30 := by
    have e : SA = μ ^ 2 * Sw := by simp only [SA, Sw]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hSw (sq_nonneg μ)
    have e2 : μ ^ 2 * (1 / (30 * μ)) = μ / 30 := by field_simp
    linarith
  set X := 4 * Lv ^ 2 * Mc / (μ ^ 3 * (Lv * ε ^ 2 + 8 * Nh))
  have hRX : Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε = 3 + Lv ^ 2 / μ ^ 2 + X := rfl
  have hLA2 : Lv ^ 2 * A2 ≤ ε ^ 2 * Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε / 12 := by
    have hden : 0 < Lv * ε ^ 2 + 8 * Nh := by positivity
    have hηs' : ηs = ε ^ 2 / (8 * (Lv * ε ^ 2 + 8 * Nh)) := by
      simp only [ηs]; field_simp; ring
    have b1 : Lv ^ 2 * (ε ^ 2 / (48 * μ ^ 2)) = ε ^ 2 * (Lv ^ 2 / μ ^ 2) / 48 := by
      field_simp
    have b2 : Lv ^ 2 * (2 * ηs * Hw / μ) ≤ ε ^ 2 * X / 16 := by
      rw [hηs']
      have e1 : Lv ^ 2 * (2 * (ε ^ 2 / (8 * (Lv * ε ^ 2 + 8 * Nh))) * Hw / μ) =
          (Lv ^ 2 * ε ^ 2 / (4 * μ ^ 3 * (Lv * ε ^ 2 + 8 * Nh))) * (μ ^ 2 * Hw) := by
        field_simp; ring
      have e2 : ε ^ 2 * X / 16 =
          (Lv ^ 2 * ε ^ 2 / (4 * μ ^ 3 * (Lv * ε ^ 2 + 8 * Nh))) * Mc := by
        simp only [X]; field_simp; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hMc3 (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hA2 (sq_nonneg Lv)
    have hX0 : 0 ≤ X := by simp only [X]; positivity
    have hL0 : 0 ≤ Lv ^ 2 / μ ^ 2 := by positivity
    rw [hRX]
    have e3 : Lv ^ 2 * (ε ^ 2 / (48 * μ ^ 2) + 2 * ηs * Hw / μ) =
        Lv ^ 2 * (ε ^ 2 / (48 * μ ^ 2)) + Lv ^ 2 * (2 * ηs * Hw / μ) := by ring
    rw [e3, b1] at h1
    nlinarith [sq_nonneg ε]
  have hθ0 : 0 ≤ θ := by simp only [θ]; positivity
  have hfin := tune_final (μ := μ) (Lv := Lv) (Lh := Lh) (ε := ε) (lR := lR)
    (R := Rf Lh ρh G Γ LJ ρJ μ Lv σu σv ε) (Mc := Mc) (HA := HA) (C := Ca + θ * Hw) (SA := SA)
    (A1 := A1) (θA2 := θ * A2) (LA2 := Lv ^ 2 * A2) (Γ := Γ) hμ hμLv hε hlR rfl hR3 hMc0 hMc2
    (by simp only [Ca]; positivity) hMc1 hSA hLh hval hΓ16 hA1 hθA2 hA10
    (mul_nonneg hθ0 hA20) (by positivity) hLA2
  obtain ⟨h1, h2, h3, h4⟩ := hfin
  exact ⟨hηs0, hηs8, h1, h2, h3, h4⟩

end OracleTemplate.RiverValley
