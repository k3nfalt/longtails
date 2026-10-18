import LongTails.Proofs.DyadicHolderCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OracleTemplate.DyadicHolder

noncomputable def tEta (L ε : ℝ) : ℝ := ε / (4 * L)

noncomputable def tK (L Δ ε : ℝ) : ℕ := ⌈16 * L * Δ / ε ^ 2⌉₊

open Classical in
noncomputable def tJ (L M ν σ Δ ε : ℝ) : ℕ :=
  Nat.findGreatest (fun j => M * (2 ^ j * tEta L ε) ^ (2 * ν) ≤ σ ^ 2) (Nat.log 2 (tK L Δ ε + 1))

noncomputable def tbA (σ ε : ℝ) : ℕ := ⌈32 * σ ^ 2 / ε ^ 2⌉₊ + 1

noncomputable def tb (L M ν σ Δ ε : ℝ) (j : ℕ) : ℕ :=
  ⌈32 * ((tJ L M ν σ Δ ε : ℝ) + 1) * (M * (2 ^ j * tEta L ε) ^ (2 * ν)) / ε ^ 2⌉₊ + 1

noncomputable def tcfg (L M ν σ Δ ε : ℝ) : DyadicConfig :=
  ⟨tEta L ε, tK L Δ ε, tJ L M ν σ Δ ε, tbA σ ε, tb L M ν σ Δ ε⟩

structure TuneHyp (L M ν σ Δ ε : ℝ) : Prop where
  L_pos : 0 < L
  M_nn : 0 ≤ M
  ν_half : 1 / 2 ≤ ν
  ν_le : ν ≤ 1
  σ_nn : 0 ≤ σ
  Δ_nn : 0 ≤ Δ
  ε_pos : 0 < ε

variable {L M ν σ Δ ε : ℝ}

lemma TuneHyp.eta_pos (h : TuneHyp L M ν σ Δ ε) : 0 < tEta L ε := by
  have := h.L_pos; have := h.ε_pos; unfold tEta; positivity

lemma tbA_pos (σ ε : ℝ) : 1 ≤ tbA σ ε := by unfold tbA; omega

lemma tb_pos (L M ν σ Δ ε : ℝ) (j : ℕ) : 1 ≤ tb L M ν σ Δ ε j := by unfold tb; omega

lemma TuneHyp.beta (h : TuneHyp L M ν σ Δ ε) (j : ℕ) :
    M * (2 ^ j * tEta L ε) ^ (2 * ν) / (tb L M ν σ Δ ε j : ℝ) ≤
      ε ^ 2 / (32 * ((tJ L M ν σ Δ ε : ℝ) + 1)) := by
  have hε := h.ε_pos
  have hη := h.eta_pos
  set x := M * (2 ^ j * tEta L ε) ^ (2 * ν)
  have hx : 0 ≤ x := by have := h.M_nn; positivity
  set J := (tJ L M ν σ Δ ε : ℝ)
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hb : 32 * (J + 1) * x / ε ^ 2 ≤ (tb L M ν σ Δ ε j : ℝ) := by
    unfold tb
    push_cast
    have := Nat.le_ceil (32 * (J + 1) * x / ε ^ 2)
    linarith
  have hb0 : (0 : ℝ) < tb L M ν σ Δ ε j := by exact_mod_cast tb_pos L M ν σ Δ ε j
  rw [div_le_div_iff₀ hb0 (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hb
  nlinarith

lemma TuneHyp.variance (h : TuneHyp L M ν σ Δ ε) :
    σ ^ 2 / (tbA σ ε : ℝ) + ε ^ 2 / (32 * ((tJ L M ν σ Δ ε : ℝ) + 1)) * (tJ L M ν σ Δ ε : ℝ) ≤
      ε ^ 2 / 16 := by
  have hε := h.ε_pos
  have hA : 32 * σ ^ 2 / ε ^ 2 ≤ (tbA σ ε : ℝ) := by
    unfold tbA; push_cast
    have := Nat.le_ceil (32 * σ ^ 2 / ε ^ 2); linarith
  have hA0 : (0 : ℝ) < tbA σ ε := by exact_mod_cast tbA_pos σ ε
  have h1 : σ ^ 2 / (tbA σ ε : ℝ) ≤ ε ^ 2 / 32 := by
    rw [div_le_div_iff₀ hA0 (by norm_num)]
    rw [div_le_iff₀ (by positivity)] at hA
    nlinarith
  set J := (tJ L M ν σ Δ ε : ℝ)
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have h2 : ε ^ 2 / (32 * (J + 1)) * J ≤ ε ^ 2 / 32 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ε]
  linarith

lemma TuneHyp.accuracy (h : TuneHyp L M ν σ Δ ε) :
    Δ / (tEta L ε * ((tK L Δ ε : ℝ) + 1)) + 2 * Real.sqrt (ε ^ 2 / 16) + L / 2 * tEta L ε ≤ ε := by
  have hε := h.ε_pos
  have hL := h.L_pos
  have hη := h.eta_pos
  have hs : Real.sqrt (ε ^ 2 / 16) = ε / 4 := by
    rw [show ε ^ 2 / 16 = (ε / 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hK : 16 * L * Δ / ε ^ 2 ≤ (tK L Δ ε : ℝ) := Nat.le_ceil _
  have h1 : Δ / (tEta L ε * ((tK L Δ ε : ℝ) + 1)) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    unfold tEta
    rw [div_le_iff₀ (by positivity)] at hK
    have := h.Δ_nn
    field_simp
    nlinarith
  have h2 : L / 2 * tEta L ε = ε / 8 := by unfold tEta; field_simp; ring
  rw [hs, h2]
  linarith

lemma sq_le_of_lt_rpow {σ M ν A : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hν : 0 < ν) (hA : 0 ≤ A)
    (h : σ ^ 2 < M * A ^ (2 * ν)) : σ ^ 2 ≤ A * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) := by
  rcases hσ.eq_or_lt with h0 | hσ0
  · subst h0
    have : 0 ≤ A * M ^ (1 / (2 * ν)) * (0 : ℝ) ^ (2 - 1 / ν) := by positivity
    simpa using this
  have h2ν : 0 < 2 * ν := by positivity
  have hl : σ ^ (1 / ν) = (σ ^ 2) ^ (1 / (2 * ν)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ]
    congr 1
    field_simp
    norm_num
  have hr : (M * A ^ (2 * ν)) ^ (1 / (2 * ν)) = M ^ (1 / (2 * ν)) * A := by
    rw [Real.mul_rpow hM (by positivity), ← Real.rpow_mul hA, mul_one_div_cancel h2ν.ne',
      Real.rpow_one]
  have hlt : σ ^ (1 / ν) < M ^ (1 / (2 * ν)) * A := by
    rw [hl, ← hr]
    exact Real.rpow_lt_rpow (by positivity) h (by positivity)
  have hsplit : σ ^ 2 = σ ^ (1 / ν) * σ ^ (2 - 1 / ν) := by
    rw [← Real.rpow_add hσ0, show 1 / ν + (2 - 1 / ν) = ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hsplit]
  have hp : 0 < σ ^ (2 - 1 / ν) := Real.rpow_pos_of_pos hσ0 _
  nlinarith

lemma pow_rpow_split {ν η : ℝ} (hν : 1 / 2 ≤ ν) (hη : 0 ≤ η) {j J : ℕ} (hj : j ≤ J) :
    ((2 : ℝ) ^ j * η) ^ (2 * ν) ≤ (2 : ℝ) ^ j * (((2 : ℝ) ^ J) ^ (2 * ν - 1) * η ^ (2 * ν)) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [Real.mul_rpow h2.le hη, show 2 * ν = 1 + (2 * ν - 1) by ring, Real.rpow_add h2,
    Real.rpow_one, ← show 2 * ν = 1 + (2 * ν - 1) by ring]
  have hle : ((2 : ℝ) ^ j) ^ (2 * ν - 1) ≤ ((2 : ℝ) ^ J) ^ (2 * ν - 1) :=
    Real.rpow_le_rpow h2.le (pow_le_pow_right₀ (by norm_num) hj) (by linarith)
  have : 0 ≤ η ^ (2 * ν) := by positivity
  calc (2 : ℝ) ^ j * ((2 : ℝ) ^ j) ^ (2 * ν - 1) * η ^ (2 * ν)
      ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ J) ^ (2 * ν - 1) * η ^ (2 * ν) := by gcongr
    _ = _ := by ring

lemma pow_rpow_eq {ν η : ℝ} (hη : 0 ≤ η) (J : ℕ) :
    ((2 : ℝ) ^ J * η) ^ (2 * ν) = (2 : ℝ) ^ J * (((2 : ℝ) ^ J) ^ (2 * ν - 1) * η ^ (2 * ν)) := by
  have h2 : (0 : ℝ) < 2 ^ J := by positivity
  rw [Real.mul_rpow h2.le hη, show 2 * ν = 1 + (2 * ν - 1) by ring, Real.rpow_add h2,
    Real.rpow_one, ← show 2 * ν = 1 + (2 * ν - 1) by ring]
  ring

lemma TuneHyp.batch_le (h : TuneHyp L M ν σ Δ ε) (k : ℕ) :
    ((tcfg L M ν σ Δ ε).batch k : ℝ) ≤
      (if (tcfg L M ν σ Δ ε).pos k = 0 then 1 else 0) * (tbA σ ε : ℝ) + 2 +
        32 * ((tJ L M ν σ Δ ε : ℝ) + 1) / ε ^ 2 *
          (M * (((2 : ℝ) ^ tJ L M ν σ Δ ε) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν))) *
          (lvl ((tcfg L M ν σ Δ ε).pos k) : ℝ) := by
  set cfg := tcfg L M ν σ Δ ε
  have hε := h.ε_pos
  have hη := h.eta_pos
  have hc : 0 ≤ 32 * ((tJ L M ν σ Δ ε : ℝ) + 1) / ε ^ 2 := by positivity
  have hQ : 0 ≤ M * (((2 : ℝ) ^ tJ L M ν σ Δ ε) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν)) := by
    have := h.M_nn; positivity
  rw [DyadicConfig.lvl_pos]
  unfold DyadicConfig.batch
  split_ifs with hk
  · change (tbA σ ε : ℝ) ≤ _
    simp
  · have hj : cfg.level k < cfg.J := cfg.level_lt hk
    change ((tb L M ν σ Δ ε (cfg.level k) : ℕ) : ℝ) ≤ _
    set x := M * (2 ^ cfg.level k * tEta L ε) ^ (2 * ν)
    set Q := M * (((2 : ℝ) ^ tJ L M ν σ Δ ε) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν))
    set c := 32 * ((tJ L M ν σ Δ ε : ℝ) + 1) / ε ^ 2
    have hb : (tb L M ν σ Δ ε (cfg.level k) : ℝ) ≤
        32 * ((tJ L M ν σ Δ ε : ℝ) + 1) * x / ε ^ 2 + 2 := by
      unfold tb; push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ 32 * ((tJ L M ν σ Δ ε : ℝ) + 1) * x / ε ^ 2 by
        have := h.M_nn; positivity)
      linarith
    have hs := pow_rpow_split h.ν_half hη.le (J := tJ L M ν σ Δ ε)
      (show cfg.level k ≤ tJ L M ν σ Δ ε from hj.le)
    have hx : x ≤ 2 ^ cfg.level k * Q := by
      calc x ≤ M * (2 ^ cfg.level k * (((2 : ℝ) ^ tJ L M ν σ Δ ε) ^ (2 * ν - 1) *
            tEta L ε ^ (2 * ν))) := mul_le_mul_of_nonneg_left hs h.M_nn
        _ = 2 ^ cfg.level k * Q := by ring
    have key : 32 * ((tJ L M ν σ Δ ε : ℝ) + 1) * x / ε ^ 2 ≤ c * Q * 2 ^ cfg.level k := by
      have e : 32 * ((tJ L M ν σ Δ ε : ℝ) + 1) * x / ε ^ 2 = c * x := by ring
      rw [e, mul_assoc, mul_comm Q]
      exact mul_le_mul_of_nonneg_left hx hc
    push_cast
    linarith

lemma TuneHyp.level_sum (h : TuneHyp L M ν σ Δ ε) (N : ℕ) :
    32 * ((tJ L M ν σ Δ ε : ℝ) + 1) / ε ^ 2 *
        (M * (((2 : ℝ) ^ tJ L M ν σ Δ ε) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν))) *
        (∑ k ∈ Finset.range N, (lvl ((tcfg L M ν σ Δ ε).pos k) : ℝ)) ≤
      ((N / 2 ^ tJ L M ν σ Δ ε : ℕ) + 1) *
        (16 * (tJ L M ν σ Δ ε : ℝ) * ((tJ L M ν σ Δ ε : ℝ) + 1) * (σ ^ 2 / ε ^ 2)) := by
  set J := tJ L M ν σ Δ ε
  set Q := M * (((2 : ℝ) ^ J) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν))
  have hε := h.ε_pos
  have hη := h.eta_pos
  have hQ : 0 ≤ Q := by have := h.M_nn; positivity
  have hc : 0 ≤ 32 * ((J : ℝ) + 1) / ε ^ 2 := by positivity
  have hcount := level_count (tcfg L M ν σ Δ ε) N
  have hcount' : 2 * ∑ k ∈ Finset.range N, (lvl ((tcfg L M ν σ Δ ε).pos k) : ℝ) ≤
      ((N / 2 ^ J : ℕ) + 1) * (J * 2 ^ J) := by exact_mod_cast hcount
  have hJQ : (J : ℝ) * (2 ^ J * Q) ≤ J * σ ^ 2 := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · simp [h0]
    · have hP : M * (2 ^ J * tEta L ε) ^ (2 * ν) ≤ σ ^ 2 :=
        Nat.findGreatest_of_ne_zero rfl h0.ne'
      rw [pow_rpow_eq hη.le J] at hP
      have : 2 ^ J * Q ≤ σ ^ 2 := by
        calc 2 ^ J * Q = M * (2 ^ J * (((2 : ℝ) ^ J) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν))) := by
              simp only [Q]; ring
          _ ≤ σ ^ 2 := hP
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hq : (0 : ℝ) ≤ ((N / 2 ^ J : ℕ) : ℝ) + 1 := by positivity
  calc 32 * ((J : ℝ) + 1) / ε ^ 2 * Q * (∑ k ∈ Finset.range N, (lvl ((tcfg L M ν σ Δ ε).pos k) : ℝ))
      = 16 * ((J : ℝ) + 1) / ε ^ 2 * Q *
          (2 * ∑ k ∈ Finset.range N, (lvl ((tcfg L M ν σ Δ ε).pos k) : ℝ)) := by ring
    _ ≤ 16 * ((J : ℝ) + 1) / ε ^ 2 * Q * (((N / 2 ^ J : ℕ) + 1) * (J * 2 ^ J)) := by
        gcongr
    _ = ((N / 2 ^ J : ℕ) + 1) * (16 * ((J : ℝ) + 1) / ε ^ 2 * (J * (2 ^ J * Q))) := by ring
    _ ≤ ((N / 2 ^ J : ℕ) + 1) * (16 * ((J : ℝ) + 1) / ε ^ 2 * (J * σ ^ 2)) := by gcongr
    _ = _ := by ring

lemma TuneHyp.quot (h : TuneHyp L M ν σ Δ ε) :
    ((((tK L Δ ε + 1) / 2 ^ tJ L M ν σ Δ ε : ℕ) : ℝ)) * (σ ^ 2 / ε ^ 2) ≤
      2 * (σ ^ 2 / ε ^ 2) + 24 * (Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3) := by
  set J := tJ L M ν σ Δ ε
  set N := tK L Δ ε + 1
  set q := N / 2 ^ J
  have hε := h.ε_pos
  have hη := h.eta_pos
  have hL := h.L_pos
  have hA2 : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
  have hT : 0 ≤ Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3 := by
    have := h.Δ_nn; have := h.M_nn; have := h.σ_nn; positivity
  rcases Nat.lt_or_ge q 3 with hq | hq
  · have : (q : ℝ) ≤ 2 := by exact_mod_cast (show q ≤ 2 by omega)
    nlinarith
  · have hn : 0 < 2 ^ J := by positivity
    have hqn : q * 2 ^ J ≤ N := Nat.div_mul_le_self N _
    have h2n : 2 ^ (J + 1) ≤ N := by rw [pow_succ]; nlinarith
    have hlog : J + 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) h2n
    have hnot : ¬ (M * (2 ^ (J + 1) * tEta L ε) ^ (2 * ν) ≤ σ ^ 2) := by
      have := Nat.findGreatest_is_greatest (P := fun j => M * (2 ^ j * tEta L ε) ^ (2 * ν) ≤ σ ^ 2)
        (n := Nat.log 2 (tK L Δ ε + 1)) (k := J + 1) (Nat.lt_succ_self _) hlog
      exact this
    have hlt : σ ^ 2 < M * (2 ^ (J + 1) * tEta L ε) ^ (2 * ν) := lt_of_not_ge hnot
    have hsq := sq_le_of_lt_rpow h.σ_nn h.M_nn (by linarith [h.ν_half]) (by positivity) hlt
    set x := 16 * L * Δ / ε ^ 2
    have hK2 : 2 ≤ tK L Δ ε := by
      have : 3 ≤ N := by nlinarith
      omega
    have hx1 : 1 < x := by
      have := Nat.lt_ceil.mp (show (1 : ℕ) < tK L Δ ε by omega)
      simpa using this
    have hKx : (tK L Δ ε : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
    have hN3 : (N : ℝ) ≤ 3 * x := by
      have : (N : ℝ) = tK L Δ ε + 1 := by simp [N]
      linarith
    have hqnR : (q : ℝ) * 2 ^ J ≤ N := by exact_mod_cast hqn
    set S := M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν)
    have hS : 0 ≤ S := by have := h.M_nn; have := h.σ_nn; positivity
    have hsq' : σ ^ 2 ≤ 2 ^ J * (2 * tEta L ε) * S := by
      have e : (2 : ℝ) ^ (J + 1) * tEta L ε * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) =
          2 ^ J * (2 * tEta L ε) * S := by simp only [S]; ring
      linarith
    have h1 : (q : ℝ) * σ ^ 2 ≤ N * (2 * tEta L ε) * S := by
      calc (q : ℝ) * σ ^ 2 ≤ q * (2 ^ J * (2 * tEta L ε) * S) :=
            mul_le_mul_of_nonneg_left hsq' (Nat.cast_nonneg _)
        _ = (q * 2 ^ J) * (2 * tEta L ε) * S := by ring
        _ ≤ N * (2 * tEta L ε) * S := by gcongr
    have h2 : (N : ℝ) * (2 * tEta L ε) * S ≤ 24 * (Δ * S / ε) := by
      have e : 3 * x * (2 * tEta L ε) = 24 * Δ / ε := by
        simp only [x, tEta]; field_simp; ring
      calc (N : ℝ) * (2 * tEta L ε) * S ≤ 3 * x * (2 * tEta L ε) * S := by gcongr
        _ = 24 * (Δ * S / ε) := by rw [e]; ring
    have h3 : (q : ℝ) * (σ ^ 2 / ε ^ 2) ≤ 24 * (Δ * S / ε ^ 3) := by
      have := h1.trans h2
      rw [show (q : ℝ) * (σ ^ 2 / ε ^ 2) = q * σ ^ 2 / ε ^ 2 by ring, div_le_iff₀ (by positivity)]
      calc (q : ℝ) * σ ^ 2 ≤ 24 * (Δ * S / ε) := this
        _ = 24 * (Δ * S / ε ^ 3) * ε ^ 2 := by field_simp
    have e : Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3 = Δ * S / ε ^ 3 := by
      simp only [S]; ring
    rw [e]
    linarith

lemma TuneHyp.log_bound (h : TuneHyp L M ν σ Δ ε) :
    (tJ L M ν σ Δ ε : ℝ) + 1 ≤ 1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2) := by
  have hε := h.ε_pos
  have hL := h.L_pos
  have hx : 0 ≤ 16 * L * Δ / ε ^ 2 := by have := h.Δ_nn; positivity
  set N := tK L Δ ε + 1
  have hJ : tJ L M ν σ Δ ε ≤ Nat.log 2 N := Nat.findGreatest_le _
  have hN0 : N ≠ 0 := by omega
  have hpow : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 hN0
  have hlogN : (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact hpow
  have hNx : (N : ℝ) ≤ 2 + 16 * L * Δ / ε ^ 2 := by
    have := Nat.ceil_lt_add_one hx
    have e : (N : ℝ) = tK L Δ ε + 1 := by simp [N]
    rw [e]; unfold tK; linarith
  have hmono : Real.logb 2 N ≤ Real.logb 2 (2 + 16 * L * Δ / ε ^ 2) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hNx
  have : (tJ L M ν σ Δ ε : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hJ
  linarith

lemma TuneHyp.calls (h : TuneHyp L M ν σ Δ ε) :
    (off (tcfg L M ν σ Δ ε) (tK L Δ ε + 1) : ℝ) ≤
      800 * (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 *
        (1 + (L * Δ + σ ^ 2) / ε ^ 2 + Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3) := by
  set cfg := tcfg L M ν σ Δ ε
  set J := tJ L M ν σ Δ ε
  set N := tK L Δ ε + 1
  set q := N / 2 ^ J
  set A2 := σ ^ 2 / ε ^ 2
  set T := Δ * M ^ (1 / (2 * ν)) * σ ^ (2 - 1 / ν) / ε ^ 3
  set Λ := 1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)
  set c := 32 * ((J : ℝ) + 1) / ε ^ 2
  set Q := M * (((2 : ℝ) ^ J) ^ (2 * ν - 1) * tEta L ε ^ (2 * ν))
  have hε := h.ε_pos
  have hL := h.L_pos
  have hA2 : 0 ≤ A2 := by positivity
  have hT : 0 ≤ T := by have := h.Δ_nn; have := h.M_nn; have := h.σ_nn; positivity
  have hx : 0 ≤ 16 * L * Δ / ε ^ 2 := by have := h.Δ_nn; positivity
  have hsum : (off cfg N : ℝ) ≤ ∑ k ∈ Finset.range N,
      ((if cfg.pos k = 0 then 1 else 0) * (tbA σ ε : ℝ) + 2 + c * Q * (lvl (cfg.pos k) : ℝ)) := by
    rw [off_eq_sum, Nat.cast_sum]
    exact Finset.sum_le_sum fun k _ => h.batch_le k
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hanch : ∑ k ∈ Finset.range N, (if cfg.pos k = 0 then (1 : ℝ) else 0) ≤ (q : ℝ) + 1 := by
    have := anchor_count cfg N
    exact_mod_cast this
  have hbA : (tbA σ ε : ℝ) ≤ 32 * A2 + 2 := by
    unfold tbA; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 32 * σ ^ 2 / ε ^ 2 by positivity)
    have e : 32 * σ ^ 2 / ε ^ 2 = 32 * (σ ^ 2 / ε ^ 2) := by ring
    simp only [A2]; linarith
  have hlev := h.level_sum N
  have hquot := h.quot
  have hlog := h.log_bound
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hΛ : (J : ℝ) + 1 ≤ Λ := hlog
  have hΛ2 : ((J : ℝ) + 1) ^ 2 ≤ Λ ^ 2 := by
    have : (0 : ℝ) ≤ J + 1 := by positivity
    nlinarith
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N _
  have hN : (N : ℝ) ≤ 2 + 16 * L * Δ / ε ^ 2 := by
    have := Nat.ceil_lt_add_one hx
    have e : (N : ℝ) = tK L Δ ε + 1 := by simp [N]
    rw [e]; unfold tK; linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hbA0 : (0 : ℝ) ≤ tbA σ ε := Nat.cast_nonneg _
  have step1 : (off cfg N : ℝ) ≤ ((q : ℝ) + 1) * (32 * A2 + 2) + 2 * N +
      ((q : ℝ) + 1) * (16 * J * (J + 1) * A2) := by
    have h1 : (∑ k ∈ Finset.range N, (if cfg.pos k = 0 then (1 : ℝ) else 0)) * (tbA σ ε : ℝ) ≤
        ((q : ℝ) + 1) * (32 * A2 + 2) := by
      calc (∑ k ∈ Finset.range N, (if cfg.pos k = 0 then (1 : ℝ) else 0)) * (tbA σ ε : ℝ)
          ≤ ((q : ℝ) + 1) * (tbA σ ε : ℝ) := by gcongr
        _ ≤ ((q : ℝ) + 1) * (32 * A2 + 2) := by gcongr
    have h2 : c * Q * ∑ k ∈ Finset.range N, (lvl (cfg.pos k) : ℝ) ≤
        ((q : ℝ) + 1) * (16 * J * (J + 1) * A2) := hlev
    linarith
  have step2 : (off cfg N : ℝ) ≤ 4 * N + 2 + 32 * ((J : ℝ) + 1) ^ 2 * (3 * A2 + 24 * T) := by
    have hqA : (q : ℝ) * A2 ≤ 2 * A2 + 24 * T := hquot
    have e1 : ((q : ℝ) + 1) * (32 * A2 + 2) + ((q : ℝ) + 1) * (16 * J * (J + 1) * A2) ≤
        2 * q + 2 + 32 * ((J : ℝ) + 1) ^ 2 * (q * A2 + A2) := by
      have : (32 + 16 * (J : ℝ) * (J + 1)) ≤ 32 * ((J : ℝ) + 1) ^ 2 := by nlinarith
      have hqA0 : 0 ≤ (q : ℝ) * A2 + A2 := by positivity
      nlinarith
    have e2 : 32 * ((J : ℝ) + 1) ^ 2 * (q * A2 + A2) ≤
        32 * ((J : ℝ) + 1) ^ 2 * (3 * A2 + 24 * T) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hJ1 : (1 : ℝ) ≤ ((J : ℝ) + 1) ^ 2 := by nlinarith
  calc (off cfg N : ℝ) ≤ 4 * N + 2 + 32 * ((J : ℝ) + 1) ^ 2 * (3 * A2 + 24 * T) := step2
    _ ≤ 800 * ((J : ℝ) + 1) ^ 2 * (1 + (L * Δ + σ ^ 2) / ε ^ 2 + T) := by
        have e : (L * Δ + σ ^ 2) / ε ^ 2 = L * Δ / ε ^ 2 + A2 := by simp only [A2]; ring
        have e2 : 16 * L * Δ / ε ^ 2 = 16 * (L * Δ / ε ^ 2) := by ring
        have hLD : 0 ≤ L * Δ / ε ^ 2 := by have := h.Δ_nn; positivity
        rw [e]
        rw [e2] at hN
        nlinarith
    _ ≤ 800 * Λ ^ 2 * (1 + (L * Δ + σ ^ 2) / ε ^ 2 + T) := by
        have : 0 ≤ 1 + (L * Δ + σ ^ 2) / ε ^ 2 + T := by
          have := h.Δ_nn; positivity
        gcongr

end OracleTemplate.DyadicHolder
