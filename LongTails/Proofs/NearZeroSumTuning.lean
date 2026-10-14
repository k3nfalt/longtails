import LongTails.Proofs.NearZeroSumPotential
import LongTails.Algorithms.NearZeroSumFoam
import LongTails.Proofs.GdPL
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

lemma geometric_accuracy {α A ε : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    A * (1 - α / 2) ^ ⌈2 / α * Real.log (2 + A / ε)⌉₊ ≤ ε := by
  have hK : ⌈2 / α * Real.log (1 + A / ε)⌉₊ ≤ ⌈2 / α * Real.log (2 + A / ε)⌉₊ := by
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log (by positivity) (by linarith)
  have h := PLGradient.geometric_budget 2 α A ε hα (by linarith) hA hε
    (K := ⌈2 / α * Real.log (2 + A / ε)⌉₊) hK
  simpa only [mul_comm] using h

lemma ceil_double_bound {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  linarith

lemma inner_count_bounds {L M : ℝ} (hM : 0 < M) (hML : M ≤ L) :
    let K := ⌈2048 * L / M⌉₊
    1 ≤ K ∧ 16 ≤ (1 / (8 * L)) * ((M / 2) / 8) * K ∧
      (K : ℝ) ≤ 2049 * L / M := by
  dsimp only
  have hL : 0 < L := hM.trans_le hML
  have hratio : 1 ≤ L / M := (le_div_iff₀ hM).mpr (by simpa using hML)
  have hlo := Nat.le_ceil (2048 * L / M)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2048 * L / M by positivity)
  have hlo' : 2048 * (L / M) ≤ (⌈2048 * L / M⌉₊ : ℝ) := by simpa only [mul_div_assoc] using hlo
  have hval : 1 ≤ (⌈2048 * L / M⌉₊ : ℝ) := by linarith
  refine ⟨by exact_mod_cast hval, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (1 / (8 * L)) * ((M / 2) / 8) by positivity)
    have he : (1 / (8 * L)) * ((M / 2) / 8) * (2048 * L / M) = 16 := by field_simp; ring
    rwa [he] at h
  · simp only [mul_div_assoc] at hhi ⊢
    linarith

lemma log_accuracy_lower {x : ℝ} (hx : 0 ≤ x) : 1 / 2 ≤ Real.log (2 + x) := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show 2 ≤ 2 + x by linarith)
  have h2 := Real.log_two_gt_d9
  linarith

lemma foam_count_bound {α A ε : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    (⌈2 / α * Real.log (2 + A / ε)⌉₊ : ℝ) ≤ 4 / α * Real.log (2 + A / ε) := by
  have hl := log_accuracy_lower (div_nonneg hA hε.le)
  have hh : 1 ≤ 2 / α * Real.log (2 + A / ε) := by
    have h := (le_div_iff₀ hα).mpr (show 1 * α ≤ 2 * Real.log (2 + A / ε) by linarith)
    convert h using 1; ring
  have h := ceil_double_bound hh
  convert h using 1; ring


lemma regularized_scales {L M m δ : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hML : M ≤ L) (hδ : 0 ≤ δ) (hδL : δ ≤ L) :
    let β := m + 16 * δ
    0 < m + β ∧ m + β ≤ M + β ∧ M + β ≤ 2 * L + β ∧
      2 * L + β ≤ 19 * L ∧ δ ≤ (m + β) / 8 ∧ 0 < β := by
  dsimp only
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma regularized_ratio_bound {M m δ : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hδ : 0 ≤ δ) :
    (2 * m + 16 * δ) / (M + m + 16 * δ) ≤ 16 * ((m + δ) / (M + m + δ)) := by
  have hM : 0 < M := hm.trans_le hmM
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he : 16 * (m + δ) * (M + m + 16 * δ) -
      (2 * m + 16 * δ) * (M + m + δ) =
      14 * M * m + 14 * m ^ 2 + 254 * m * δ + 240 * δ ^ 2 := by ring
  have hp : 0 ≤ 14 * M * m + 14 * m ^ 2 + 254 * m * δ + 240 * δ ^ 2 := by positivity
  linarith

lemma regularized_sqrt_bound {M m δ : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hδ : 0 ≤ δ) :
    Real.sqrt ((2 * m + 16 * δ) / (M + m + 16 * δ)) ≤
      4 * Real.sqrt ((m + δ) / (M + m + δ)) := by
  have h := Real.sqrt_le_sqrt (regularized_ratio_bound hm hmM hδ)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)] at h
  norm_num at h ⊢
  exact h

lemma regularized_log_bound {L M m δ D ε : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hML : M ≤ L) (hδ : 0 ≤ δ) (hδL : δ ≤ L) (hε : 0 < ε) :
    2 + 1024 * (2 * L + m + 16 * δ) ^ 2 * D ^ 2 * (2 * m + 16 * δ) /
      ((M + m + 16 * δ) * m ^ 2 * ε) ≤ 2 + 524288 * L ^ 2 * D ^ 2 / (m ^ 2 * ε) := by
  have hM : 0 < M := hm.trans_le hmM
  have hL : 0 < L := hM.trans_le hML
  have hLF : 2 * L + m + 16 * δ ≤ 19 * L := by linarith
  have hrat : (2 * m + 16 * δ) / (M + m + 16 * δ) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hid : 1024 * (2 * L + m + 16 * δ) ^ 2 * D ^ 2 * (2 * m + 16 * δ) /
      ((M + m + 16 * δ) * m ^ 2 * ε) =
      (1024 * (2 * L + m + 16 * δ) ^ 2 * D ^ 2 / (m ^ 2 * ε)) *
        ((2 * m + 16 * δ) / (M + m + 16 * δ)) := by
        have hd : 0 < M + m + 16 * δ := by positivity
        field_simp
  rw [hid]
  apply add_le_add_right
  calc
    _ ≤ (1024 * (2 * L + m + 16 * δ) ^ 2 * D ^ 2 / (m ^ 2 * ε)) * 1 :=
      mul_le_mul_of_nonneg_left hrat (by positivity)
    _ ≤ 524288 * L ^ 2 * D ^ 2 / (m ^ 2 * ε) := by
      rw [mul_one]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg D)
      have hh := mul_self_le_mul_self (show 0 ≤ 2 * L + m + 16 * δ by positivity) hLF
      nlinarith [sq_nonneg L]


structure TunedFoamFacts (M m δ : ℝ) (cfg : FoamConfig) : Prop where
  a_pos : 0 < cfg.a
  b_pos : 0 < cfg.b
  c_pos : 0 < cfg.b - δ
  b_le_a : cfg.b ≤ cfg.a
  alpha_pos : 0 < cfg.α
  alpha_le_one : cfg.α ≤ 1
  alpha_sq : cfg.α ^ 2 = cfg.b / cfg.a
  small : 8 * δ ^ 2 ≤ cfg.a * cfg.α * (cfg.b - δ)
  large_curvature : M = 2 * cfg.a
  small_curvature : m = 2 * cfg.b
  a_le_L : cfg.a ≤ cfg.L
  delta_le_L : δ ≤ cfg.L
  eta_pos : 0 < cfg.η
  eta_L : cfg.η * (2 * cfg.L) ≤ 1 / 4
  inner_pos : 1 ≤ cfg.innerSteps
  inner_accuracy : 16 ≤ cfg.η * (cfg.a / 8) * cfg.innerSteps

lemma tuned_foam_facts {L M m δ : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hML : M ≤ L) (hδ : 0 ≤ δ) (hδL : δ ≤ L) (D ε : ℝ) :
    TunedFoamFacts (M + (m + 16 * δ)) (m + (m + 16 * δ)) δ (tunedFoamConfig L M m δ D ε) := by
  obtain ⟨hmr, hmrMr, hMrLF, hLFL, hsmall, hβ⟩ := regularized_scales hm hmM hML hδ hδL
  obtain ⟨hα, hα₁, hαsq, hc, herr⟩ := foam_tuning hmr hmrMr hδ hsmall
  obtain ⟨hk, hK, _⟩ := inner_count_bounds (hmr.trans_le hmrMr) hMrLF
  have hLF : 0 < 2 * L + (m + 16 * δ) := (hmr.trans_le hmrMr).trans_le hMrLF
  unfold tunedFoamConfig
  dsimp only
  refine ⟨by linarith, by linarith, hc, by linarith, hα, hα₁, hαsq, herr,
    by ring, by ring, by linarith, by linarith, by positivity, ?_, hk, hK⟩
  have he : 1 / (8 * (2 * L + (m + 16 * δ))) * (2 * (2 * L + (m + 16 * δ))) = 1 / 4 := by
    field_simp
    ring
  exact he.le

lemma tuned_foam_accuracy {L M m δ D ε : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hML : M ≤ L) (hδ : 0 ≤ δ) (hδL : δ ≤ L) (hε : 0 < ε) :
    let cfg := tunedFoamConfig L M m δ D ε
    16 * cfg.L ^ 2 * D ^ 2 / (cfg.α ^ 2 * cfg.a ^ 2) * (1 - cfg.α / 2) ^ cfg.outerSteps ≤
      m ^ 2 * ε / (16 * (m + (m + 16 * δ)) ^ 2) := by
  let cfg := tunedFoamConfig L M m δ D ε
  have hf := tuned_foam_facts hm hmM hML hδ hδL D ε
  have htol : 0 < m ^ 2 * ε / (16 * (m + (m + 16 * δ)) ^ 2) := by positivity
  have hA : 0 ≤ 16 * cfg.L ^ 2 * D ^ 2 / (cfg.α ^ 2 * cfg.a ^ 2) := by positivity
  have h := geometric_accuracy hf.alpha_pos hf.alpha_le_one hA htol
  have hM : 0 < M + (m + 16 * δ) := by linarith
  have hm' : 0 < m + (m + 16 * δ) := by linarith
  have hs : cfg.α ^ 2 = (m + (m + 16 * δ)) / (M + (m + 16 * δ)) := by
    exact Real.sq_sqrt (by positivity)
  have he : (16 * cfg.L ^ 2 * D ^ 2 / (cfg.α ^ 2 * cfg.a ^ 2)) /
      (m ^ 2 * ε / (16 * (m + (m + 16 * δ)) ^ 2)) =
      1024 * (2 * L + (m + 16 * δ)) ^ 2 * D ^ 2 * (m + (m + 16 * δ)) /
        ((M + (m + 16 * δ)) * m ^ 2 * ε) := by
    rw [hs]
    dsimp [cfg, tunedFoamConfig]
    field_simp
    ring
  rw [he] at h
  exact h


lemma outer_geometric_accuracy {m β D ε : ℝ} (hm : 0 < m) (hβ : 0 ≤ β)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    (β / (m + β)) ^ ⌈2 * (m + β) / m * Real.log (2 + D ^ 2 / ε)⌉₊ * D ≤ Real.sqrt ε / 4 := by
  let A := 2 + D ^ 2 / ε
  let N := ⌈2 * (m + β) / m * Real.log A⌉₊
  have hmr : 0 < m + β := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hss := Real.sq_sqrt hε.le
  have hbase : β / (m + β) ≤ Real.exp (-(m / (m + β))) := by
    have he : β / (m + β) = 1 - m / (m + β) := by field_simp; ring
    rw [he]
    linarith [Real.add_one_le_exp (-(m / (m + β)))]
  have hpow := pow_le_pow_left₀ (div_nonneg hβ hmr.le) hbase N
  rw [← Real.exp_nat_mul] at hpow
  have hn := Nat.le_ceil (2 * (m + β) / m * Real.log A)
  have hn' := mul_le_mul_of_nonneg_left hn (show 0 ≤ m / (m + β) by positivity)
  have hid : m / (m + β) * (2 * (m + β) / m * Real.log A) = 2 * Real.log A := by
    field_simp
  rw [hid] at hn'
  have he : Real.exp ((N : ℝ) * -(m / (m + β))) ≤ 1 / A ^ 2 := by
    calc
      _ ≤ Real.exp (-(2 * Real.log A)) := Real.exp_le_exp.mpr (by dsimp [N]; nlinarith only [hn'])
      _ = 1 / A ^ 2 := by
        rw [show 2 * Real.log A = Real.log (A ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_neg, Real.exp_log (sq_pos_of_pos hA)]
        simp only [one_div]
  have hbound := mul_le_mul_of_nonneg_right (hpow.trans he) hD
  have hpoly : 4 * (D / Real.sqrt ε) ≤ (2 + (D / Real.sqrt ε) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg ((D / Real.sqrt ε) ^ 2), sq_nonneg (2 * (D / Real.sqrt ε) - 1)]
  have hAr : A = 2 + (D / Real.sqrt ε) ^ 2 := by rw [div_pow, hss]
  rw [← hAr] at hpoly
  have hmultip := mul_le_mul_of_nonneg_right hpoly hs.le
  have hcancel : 4 * (D / Real.sqrt ε) * Real.sqrt ε = 4 * D := by field_simp
  rw [hcancel] at hmultip
  have hlast : 1 / A ^ 2 * D ≤ Real.sqrt ε / 4 := by
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
    nlinarith only [hmultip]
  exact hbound.trans hlast

lemma tolerance_from_square {t m β ε : ℝ} (_ht : 0 ≤ t) (hm : 0 < m) (hβ : 0 ≤ β)
    (hε : 0 < ε) (hb : t ^ 2 ≤ m ^ 2 * ε / (16 * (m + β) ^ 2)) :
    t ≤ m * Real.sqrt ε / (4 * (m + β)) := by
  have hmr : 0 < m + β := by linarith
  have hs := Real.sq_sqrt hε.le
  have he : (m * Real.sqrt ε / (4 * (m + β))) ^ 2 = m ^ 2 * ε / (16 * (m + β) ^ 2) := by
    rw [div_pow, mul_pow, hs]
    ring
  have hp : 0 ≤ m * Real.sqrt ε / (4 * (m + β)) := by positivity
  nlinarith

lemma outer_tolerance_sum {m β ε : ℝ} (hm : 0 < m) (hβ : 0 ≤ β) :
    (m * Real.sqrt ε / (4 * (m + β))) / (1 - β / (m + β)) = Real.sqrt ε / 4 := by
  have hmr : 0 < m + β := by linarith
  have hq : 1 - β / (m + β) = m / (m + β) := by field_simp; ring
  rw [hq]
  field_simp


lemma foam_calls_cast (cfg : FoamConfig) :
    (foamCalls cfg : ℝ) = 4 + (4 * (cfg.innerSteps : ℝ) + 2) * cfg.outerSteps := by
  simp only [foamCalls, foamStepCalls, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

lemma foam_calls_bound (cfg : FoamConfig) {L M ℓ : ℝ} (hM : 0 < M) (hML : M ≤ L)
    (hα : 0 < cfg.α) (hα₁ : cfg.α ≤ 1) (hlog : 1 / 2 ≤ ℓ)
    (hk : (cfg.innerSteps : ℝ) ≤ 2049 * L / M)
    (hj : (cfg.outerSteps : ℝ) ≤ 4 / cfg.α * ℓ) :
    (foamCalls cfg : ℝ) ≤ 32800 * L / (M * cfg.α) * ℓ := by
  have hL : 0 < L := hM.trans_le hML
  have ht : 1 ≤ L / M := (le_div_iff₀ hM).mpr (by simpa using hML)
  have hs : 1 / 2 ≤ ℓ / cfg.α := (le_div_iff₀ hα).mpr (by nlinarith)
  have hts : 1 / 2 ≤ (L / M) * (ℓ / cfg.α) := by
    have hh := mul_le_mul_of_nonneg_right ht (show 0 ≤ ℓ / cfg.α by positivity)
    linarith
  have hstep : 4 * (cfg.innerSteps : ℝ) + 2 ≤ 8198 * (L / M) := by
    simp only [mul_div_assoc] at hk
    linarith
  have hj' : (cfg.outerSteps : ℝ) ≤ 4 * (ℓ / cfg.α) := by convert hj using 1; ring
  have hh := mul_le_mul hstep hj' (Nat.cast_nonneg cfg.outerSteps) (by positivity)
  rw [foam_calls_cast]
  have he : 32800 * L / (M * cfg.α) * ℓ = 32800 * ((L / M) * (ℓ / cfg.α)) := by ring
  rw [he]
  nlinarith only [hh, hts]

lemma outer_count_bound {m β x : ℝ} (hm : 0 < m) (hβ : 0 ≤ β) (hx : 0 ≤ x) :
    (⌈2 * (m + β) / m * Real.log (2 + x)⌉₊ : ℝ) ≤
      4 * (m + β) / m * Real.log (2 + x) := by
  have hl := log_accuracy_lower hx
  have hr : 1 ≤ (m + β) / m := (le_div_iff₀ hm).mpr (by linarith)
  have hh := mul_le_mul hr hl (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : 0 ≤ (m + β) / m)
  have harg : 1 ≤ 2 * (m + β) / m * Real.log (2 + x) := by
    simp only [mul_div_assoc]
    nlinarith only [hh]
  have h := ceil_double_bound harg
  convert h using 1; ring

lemma total_calls_bound (cfg : FoamConfig) {L M mr m ℓA ℓB : ℝ} {N : ℕ}
    (hL : 0 < L) (hM : 0 < M) (hm : 0 < m) (_hmr : 0 < mr)
    (hα : 0 < cfg.α) (hαsq : cfg.α ^ 2 = mr / M)
    (_hA : 0 ≤ ℓA) (hB : 0 ≤ ℓB)
    (hfoam : (foamCalls cfg : ℝ) ≤ 32800 * L / (M * cfg.α) * ℓB)
    (hN : (N : ℝ) ≤ 4 * mr / m * ℓA) :
    ((foamCalls cfg * N : ℕ) : ℝ) ≤ 131200 * L / m * cfg.α * ℓA * ℓB := by
  have hh := mul_le_mul hfoam hN (Nat.cast_nonneg N) (by positivity)
  have hsq := (eq_div_iff hM.ne').mp hαsq
  have he : (32800 * L / (M * cfg.α) * ℓB) * (4 * mr / m * ℓA) =
      131200 * L / m * cfg.α * ℓA * ℓB := by
    rw [← hsq]
    field_simp
    ring
  rw [he] at hh
  simpa only [Nat.cast_mul] using hh


set_option maxHeartbeats 700000 in
lemma tuned_total_calls {L M m δ D ε : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hML : M ≤ L) (hδ : 0 ≤ δ) (hδL : δ ≤ L) (hε : 0 < ε) :
    let β := m + 16 * δ
    let cfg := tunedFoamConfig L M m δ D ε
    let N := ⌈2 * (m + β) / m * Real.log (2 + D ^ 2 / ε)⌉₊
    foamCalls cfg * N ≤ ⌈16777216 * L / m * Real.sqrt ((m + δ) / (M + m + δ)) *
      Real.log (2 + D ^ 2 / ε) * Real.log (2 + 524288 * L ^ 2 * D ^ 2 / (m ^ 2 * ε))⌉₊ := by
  let β := m + 16 * δ
  let mr := m + β
  let Mr := M + β
  let LF := 2 * L + β
  let cfg := tunedFoamConfig L M m δ D ε
  let N := ⌈2 * mr / m * Real.log (2 + D ^ 2 / ε)⌉₊
  let B := 1024 * LF ^ 2 * D ^ 2 * mr / (Mr * m ^ 2 * ε)
  let ℓA := Real.log (2 + D ^ 2 / ε)
  let ℓB := Real.log (2 + B)
  let ℓC := Real.log (2 + 524288 * L ^ 2 * D ^ 2 / (m ^ 2 * ε))
  obtain ⟨hmr, hmrMr, hMrLF, hLFL, _, hβ⟩ := regularized_scales hm hmM hML hδ hδL
  have hMr : 0 < Mr := hmr.trans_le hmrMr
  have hLF : 0 < LF := hMr.trans_le hMrLF
  have hL : 0 < L := (hm.trans_le hmM).trans_le hML
  have hA : 1 / 2 ≤ ℓA := log_accuracy_lower (by positivity)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB : 1 / 2 ≤ ℓB := log_accuracy_lower hB0
  have hC : 1 / 2 ≤ ℓC := log_accuracy_lower (by positivity)
  have hf := tuned_foam_facts hm hmM hML hδ hδL D ε
  obtain ⟨_, _, hk⟩ := inner_count_bounds hMr hMrLF
  have hj : (cfg.outerSteps : ℝ) ≤ 4 / cfg.α * ℓB := by
    have h := foam_count_bound (A := B) (ε := 1) hf.alpha_pos hf.alpha_le_one hB0 (by norm_num)
    simpa only [div_one, cfg, tunedFoamConfig, ℓB, B, LF, mr, Mr, β] using h
  have hc := foam_calls_bound cfg hMr hMrLF hf.alpha_pos hf.alpha_le_one hB hk hj
  have hN := outer_count_bound (x := D ^ 2 / ε) hm hβ.le (by positivity)
  have hαsq : cfg.α ^ 2 = mr / Mr := Real.sq_sqrt (by positivity)
  have ht := total_calls_bound cfg hLF hMr hm hmr hf.alpha_pos hαsq
    (by linarith : 0 ≤ ℓA) (by linarith : 0 ≤ ℓB) hc hN
  have hratio : cfg.α ≤ 4 * Real.sqrt ((m + δ) / (M + m + δ)) := by
    convert regularized_sqrt_bound hm hmM hδ using 1
    dsimp [cfg, tunedFoamConfig]
    congr 2 <;> ring
  have harg : 2 + B ≤ 2 + 524288 * L ^ 2 * D ^ 2 / (m ^ 2 * ε) := by
    convert regularized_log_bound hm hmM hML hδ hδL hε (D := D) using 1;
      dsimp [B, LF, mr, Mr, β]; ring
  have hlog : ℓB ≤ ℓC := Real.log_le_log (by dsimp [B]; positivity) harg
  have hreal : ((foamCalls cfg * N : ℕ) : ℝ) ≤
      16777216 * L / m * Real.sqrt ((m + δ) / (M + m + δ)) * ℓA * ℓC := by
    calc
      _ ≤ 131200 * LF / m * cfg.α * ℓA * ℓB := ht
      _ ≤ 131200 * (19 * L) / m * (4 * Real.sqrt ((m + δ) / (M + m + δ))) * ℓA * ℓC := by
        gcongr
        exact hf.alpha_pos.le
      _ = 9971200 * (L / m * Real.sqrt ((m + δ) / (M + m + δ)) * ℓA * ℓC) := by ring
      _ ≤ 16777216 * (L / m * Real.sqrt ((m + δ) / (M + m + δ)) * ℓA * ℓC) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring
  have hh := hreal.trans (Nat.le_ceil _)
  exact_mod_cast hh


lemma game_calls_bound (p : Public) (hμ : 0 < p.μ) (hν : 0 < p.ν)
    (hμL : p.μ ≤ p.L) (hνL : p.ν ≤ p.L) (hδ : 0 ≤ p.δ) (hδL : p.δ ≤ p.L) (hε : 0 < p.ε) :
    let m := min p.μ p.ν
    let β := m + 16 * p.δ
    let cfg := tunedFoamConfig p.L (max p.μ p.ν) m p.δ p.D p.ε
    let N := ⌈2 * (m + β) / m * Real.log (2 + p.D ^ 2 / p.ε)⌉₊
    foamCalls cfg * N ≤ ⌈16777216 * p.L / min p.μ p.ν *
      Real.sqrt ((min p.μ p.ν + p.δ) / (p.μ + p.ν + p.δ)) * Real.log (2 + p.D ^ 2 / p.ε) *
      Real.log (2 + 524288 * p.L ^ 2 * p.D ^ 2 / ((min p.μ p.ν) ^ 2 * p.ε))⌉₊ := by
  have h := tuned_total_calls (lt_min hμ hν) (show min p.μ p.ν ≤ max p.μ p.ν from min_le_max)
    (max_le hμL hνL) hδ hδL hε (D := p.D)
  simpa only [max_add_min] using h

end OracleTemplate.NearZeroSum
