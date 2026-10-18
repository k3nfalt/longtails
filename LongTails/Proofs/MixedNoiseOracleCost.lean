import LongTails.Proofs.MixedNoiseConvergence

namespace OracleTemplate.MixedNoise

lemma tuned_edge_grid_cost (L r M σ Δ ε : ℝ) (hr : 0 ≤ r) {l n : ℕ}
    (hl : l < hierarchyDepth L M σ Δ ε)
    (hT : (tunedConfig L r M σ Δ ε).T = n * 4 ^ l) :
    (∑ t ∈ Finset.range (tunedConfig L r M σ Δ ε).T,
      if t % 4 ^ l = 0 then ((max 1 ((tunedConfig L r M σ Δ ε).batch t l) : ℕ) : ℝ) else 0) ≤
    ((tunedConfig L r M σ Δ ε).T : ℝ) / (4 : ℝ) ^ l *
      (1 + 4096 * (r * 2 ^ l + M ^ 2 * (1 / (2 * L)) ^ 2 *
        2 ^ hierarchyDepth L M σ Δ ε * ((2 : ℝ) ^ l) ^ 3)) +
      4 * (1 + 4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l) := by
  let b := 1 + 4096 * (r * 2 ^ l + M ^ 2 * (1 / (2 * L)) ^ 2 *
    2 ^ hierarchyDepth L M σ Δ ε * ((2 : ℝ) ^ l) ^ 3)
  let s := 1 + 4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hw (t : ℕ) :
      ((max 1 ((tunedConfig L r M σ Δ ε).batch t l) : ℕ) : ℝ) ≤
        b + if t < 4 * 4 ^ l then s else 0 := by
    have hp : 1 ≤ (tunedConfig L r M σ Δ ε).batch t l := by
      simp only [tunedConfig, Nat.ne_of_lt hl, ↓reduceIte]
      omega
    rw [max_eq_right hp]
    simp only [tunedConfig, Nat.ne_of_lt hl, ↓reduceIte, Nat.cast_add]
    have hb := rounded_batch_upper (show 0 ≤ 4096 * (r * 2 ^ l + M ^ 2 * (1 / (2 * L)) ^ 2 *
      2 ^ hierarchyDepth L M σ Δ ε * ((2 : ℝ) ^ l) ^ 3) by positivity)
    have hsu := (Nat.ceil_lt_add_one (show 0 ≤ 4096 * r * 2 ^ hierarchyDepth L M σ Δ ε * (2 : ℝ) ^ l by positivity)).le
    have hperiod : 4 ^ (l + 1) = 4 * 4 ^ l := by rw [pow_succ, Nat.mul_comm]
    rw [hperiod]
    push_cast at hb
    split_ifs <;> dsimp [b, s] <;> push_cast <;> linarith
  have H := periodic_prefix_bound
    (fun t => ((max 1 ((tunedConfig L r M σ Δ ε).batch t l) : ℕ) : ℝ)) n (4 ^ l) 4
    (by positivity) b s hs (fun t _ => hw t)
  have hn : (n : ℝ) = ((tunedConfig L r M σ Δ ε).T : ℝ) / (4 : ℝ) ^ l := by
    rw [hT, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  rw [← hT, hn] at H
  exact H

lemma tuned_root_grid_cost (L r M σ Δ ε : ℝ) (hr : 0 ≤ r) {n : ℕ}
    (hT : (tunedConfig L r M σ Δ ε).T = n * 4 ^ hierarchyDepth L M σ Δ ε) :
    (∑ t ∈ Finset.range (tunedConfig L r M σ Δ ε).T,
      if t % 4 ^ hierarchyDepth L M σ Δ ε = 0 then
        ((max 1 ((tunedConfig L r M σ Δ ε).batch t (hierarchyDepth L M σ Δ ε)) : ℕ) : ℝ) else 0) ≤
      4096 * (r * (4 : ℝ) ^ hierarchyDepth L M σ Δ ε + σ ^ 2 / ε ^ 2) + 1 +
      ((tunedConfig L r M σ Δ ε).T : ℝ) / (4 : ℝ) ^ hierarchyDepth L M σ Δ ε *
        (1 + 4096 * (r + σ ^ 2 / ε ^ 2)) := by
  let m := hierarchyDepth L M σ Δ ε
  let b := 1 + 4096 * (r + σ ^ 2 / ε ^ 2)
  let s := 4096 * (r * (4 : ℝ) ^ m + σ ^ 2 / ε ^ 2) + 1
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hq : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
  have hb := rounded_batch_upper (show 0 ≤ 4096 * (r + σ ^ 2 / ε ^ 2) by positivity)
  have hsu := (Nat.ceil_lt_add_one (show 0 ≤ 4096 * (r * (4 : ℝ) ^ m + σ ^ 2 / ε ^ 2) by positivity)).le
  have hbs : ((max 1 ⌈4096 * (r + σ ^ 2 / ε ^ 2)⌉₊ : ℕ) : ℝ) ≤ s := by
    have hh := mul_le_mul_of_nonneg_left hq hr
    dsimp [s]
    nlinarith only [hh, hb]
  have hw (t : ℕ) :
      ((max 1 ((tunedConfig L r M σ Δ ε).batch t m) : ℕ) : ℝ) ≤
        b + if t < 1 * 4 ^ m then s else 0 := by
    have hp : 1 ≤ (tunedConfig L r M σ Δ ε).batch t m := by
      simp only [tunedConfig, m, ↓reduceIte]
      split_ifs <;> omega
    rw [max_eq_right hp]
    by_cases ht : t = 0
    · subst t
      have h0 : 0 < 1 * 4 ^ m := by positivity
      simp only [tunedConfig, m, ↓reduceIte, Nat.cast_max, Nat.cast_pow, Nat.cast_ofNat]
      rw [ite_eq_left h0]
      push_cast at hbs
      simp only [Nat.cast_one]
      exact max_le (hbs.trans (le_add_of_nonneg_left hb0))
        (hsu.trans (by change s ≤ b + s; exact le_add_of_nonneg_left hb0))
    · simp only [tunedConfig, m, ht, ↓reduceIte]
      split_ifs <;> dsimp [b] <;> linarith
  have H := periodic_prefix_bound
    (fun t => ((max 1 ((tunedConfig L r M σ Δ ε).batch t m) : ℕ) : ℝ)) n (4 ^ m) 1
    (by positivity) b s hs (fun t _ => hw t)
  have hn : (n : ℝ) = ((tunedConfig L r M σ Δ ε).T : ℝ) / (4 : ℝ) ^ m := by
    rw [hT, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [m]
    field_simp
  rw [← hT, hn] at H
  simpa only [Nat.cast_one, one_mul, b, s, m, add_comm] using H

lemma tuned_calls_grid_bound (L r M σ Δ ε : ℝ) (hr : 0 ≤ r)
    (hdiv : ∀ l ≤ hierarchyDepth L M σ Δ ε,
      ∃ n, (tunedConfig L r M σ Δ ε).T = n * 4 ^ l)
    (hT : (4 : ℝ) ^ hierarchyDepth L M σ Δ ε ≤ (tunedConfig L r M σ Δ ε).T) :
    ((tunedConfig L r M σ Δ ε).calls : ℝ) ≤
      16 * 4096 * (1 + r) * (tunedConfig L r M σ Δ ε).T +
      (if hierarchyDepth L M σ Δ ε = 0 then 0 else
        2 * 4096 * (M ^ 2 * (1 / (2 * L)) ^ 2) *
          (4 : ℝ) ^ hierarchyDepth L M σ Δ ε * (tunedConfig L r M σ Δ ε).T) +
      2 * 4096 * (σ ^ 2 / ε ^ 2) *
        (1 + ((tunedConfig L r M σ Δ ε).T : ℝ) / (4 : ℝ) ^ hierarchyDepth L M σ Δ ε) + 2 := by
  let cfg := tunedConfig L r M σ Δ ε
  have hc : (cfg.calls : ℝ) ≤ 2 * ∑ l ∈ Finset.range (cfg.m + 1),
      ∑ t ∈ Finset.range cfg.T, if t % 4 ^ l = 0 then ((max 1 (cfg.batch t l) : ℕ) : ℝ) else 0 := by
    exact_mod_cast calls_grid_bound cfg
  rw [Finset.sum_range_succ] at hc
  obtain ⟨n, hn⟩ := hdiv cfg.m le_rfl
  have he (l : ℕ) (hl : l ∈ Finset.range cfg.m) :=
    tuned_edge_grid_cost L r M σ Δ ε hr (Finset.mem_range.mp hl) (hdiv l (Finset.mem_range.mp hl).le).choose_spec
  have hroot := tuned_root_grid_cost L r M σ Δ ε hr hn
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add (Finset.sum_le_sum he) hroot) (by norm_num : (0 : ℝ) ≤ 2)
  exact hc.trans (hh.trans (geometric_total_cost cfg.m (by norm_num : (1 : ℝ) ≤ 4096)
    hr (by positivity : 0 ≤ M ^ 2 * (1 / (2 * L)) ^ 2) hT))

lemma positive_hierarchy_bounds {L M σ Δ ε : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hσ : 0 < σ) (hε : 0 < ε)
    (hN : 0 < iterationTarget L Δ ε) :
    let q := 4 ^ hierarchyDepth L M σ Δ ε
    q ≤ iterationTarget L Δ ε ∧
    1 / (q : ℝ) ≤ 4 / (iterationTarget L Δ ε : ℝ) + 8 / (2 * L * σ / (M * ε)) ∧
    (1 < q → (q : ℝ) ≤ 2 * L * σ / (M * ε)) := by
  let W := 2 * L * σ / (M * ε)
  let N := iterationTarget L Δ ε
  have hW : 0 < W := by dsimp [W]; positivity
  have hH : 0 < min N (max 1 ⌊W⌋₊) := lt_min hN (by omega)
  have hb := lower_power_four (min N (max 1 ⌊W⌋₊)) hH
  have he : hierarchyDepth L M σ Δ ε = Nat.log 4 (min N (max 1 ⌊W⌋₊)) := by
    simp only [hierarchyDepth, hM.ne', hσ.ne', ↓reduceIte, N, W]
  dsimp only
  rw [he]
  refine ⟨hb.1.trans (min_le_left _ _), clamped_inverse_bound hN (by positivity) hW hb.2, ?_⟩
  intro hq
  have hfloor : 4 ^ Nat.log 4 (min N (max 1 ⌊W⌋₊)) ≤ ⌊W⌋₊ := by
    have hh := hb.1.trans (min_le_right _ _)
    omega
  exact (show (4 ^ Nat.log 4 (min N (max 1 ⌊W⌋₊)) : ℕ) ≤ (⌊W⌋₊ : ℝ) by exact_mod_cast hfloor).trans
    (Nat.floor_le hW.le)

lemma quartic_spatial_cost {A Z q T : ℝ} (hA : 0 ≤ A) (hZ : 0 ≤ Z)
    (hq : 1 ≤ q) (hT : 0 ≤ T) (hsp : A * q ^ 2 ≤ Z) :
    A * q * T ≤ Z * T ∧ Z * (T / q) ≤ Z * T := by
  have hq0 : 0 < q := by linarith
  have hAq : A * q ≤ Z := by
    have hp := mul_nonneg (mul_nonneg hA hq0.le) (sub_nonneg.mpr hq)
    nlinarith only [hsp, hp]
  refine ⟨mul_le_mul_of_nonneg_right hAq hT, ?_⟩
  apply mul_le_mul_of_nonneg_left _ hZ
  apply (div_le_iff₀ hq0).mpr
  nlinarith only [mul_nonneg hT (sub_nonneg.mpr hq)]

lemma rounded_root_ratio {N q W T D : ℝ}
    (hN : 0 < N) (hW : 0 < W) (hT : 0 ≤ T)
    (hTN : T ≤ 2 * N) (hND : N ≤ 18 * D)
    (hinv : 1 / q ≤ 4 / N + 8 / W) :
    T / q ≤ 8 + 288 * D / W := by
  have h1 := mul_le_mul_of_nonneg_left hinv hT
  have h2 := mul_le_mul_of_nonneg_right hTN (show 0 ≤ 4 / N + 8 / W by positivity)
  have h3 := div_le_div_of_nonneg_right hND hW.le
  have he : 2 * N * (4 / N + 8 / W) = 8 + 16 * (N / W) := by field_simp; ring
  rw [he] at h2
  have heT : T * (1 / q) = T / q := by ring
  rw [heT] at h1
  have he3 : 18 * D / W = 18 * (D / W) := by ring
  have he4 : 288 * D / W = 288 * (D / W) := by ring
  rw [he3] at h3
  rw [he4]
  linarith only [h1, h2, h3]

lemma cubic_root_cost {C Z T q D W K : ℝ} (hC : 0 ≤ C) (hZ : 0 ≤ Z)
    (hratio : T / q ≤ 8 + 288 * D / W) (hK : D * Z / W = K / 2) :
    2 * C * Z * (1 + T / q) ≤ 18 * C * Z + 288 * C * K := by
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * C * Z by positivity)
  have he : 2 * C * Z * (8 + 288 * D / W) = 16 * C * Z + 288 * C * K := by
    calc
      _ = 16 * C * Z + 576 * C * (D * Z / W) := by ring
      _ = _ := by rw [hK]; ring
  rw [he] at h
  nlinarith only [h]

lemma cost_minimum_bound {c D Z K r : ℝ}
    (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hK : 0 ≤ K)
    (hcubic : c ≤ 576 * 4096 * (1 + r) * D + 324 * 4096 * K + 18 * 4096 * Z + 2)
    (hquartic : c ≤ 576 * 4096 * (1 + r) * D + 144 * 4096 * D * Z + 2 * 4096 * Z + 2) :
    c ≤ 576 * 4096 * (1 + r) * D + 32 * 4096 * Z + 512 * 4096 * min K (D * Z) + 2 := by
  by_cases h : K ≤ D * Z
  · rw [min_eq_left h]
    nlinarith only [hcubic, hZ, hK]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith only [hquartic, hZ, mul_nonneg hD hZ]

lemma cost_ceiling_bound {c : ℕ} {r D Z K : ℝ}
    (hr : 0 ≤ r) (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hK : 0 ≤ K)
    (hc : (c : ℝ) ≤ 576 * 4096 * (1 + r) * D + 32 * 4096 * Z +
      512 * 4096 * min K (D * Z) + 2) :
    c ≤ 16777216 * ⌈1 + (1 + r) * D + Z + min K (D * Z)⌉₊ := by
  have hmin : 0 ≤ min K (D * Z) := le_min hK (mul_nonneg hD hZ)
  have hrel : 0 ≤ (1 + r) * D := mul_nonneg (by linarith) hD
  have hceil := Nat.le_ceil (1 + (1 + r) * D + Z + min K (D * Z))
  have h : (c : ℝ) ≤ 16777216 * (⌈1 + (1 + r) * D + Z + min K (D * Z)⌉₊ : ℝ) := by
    nlinarith only [hc, hceil, hmin, hrel, hZ]
  exact_mod_cast h

lemma positive_cost_components {A Z W D K q T : ℝ}
    (hA : 0 ≤ A) (hW : 0 < W)
    (hq : 0 ≤ q) (hT : 0 ≤ T) (hqW : q ≤ W) (hTD : T ≤ 36 * D)
    (hAW : A * W * D = K / 2) (hAW2 : A * W ^ 2 = Z) :
    2 * 4096 * A * q * T ≤ 36 * 4096 * K ∧
      A * q ^ 2 ≤ Z := by
  have h1 := mul_le_mul_of_nonneg_left hqW hA
  have h2 := mul_le_mul_of_nonneg_right h1 hT
  have h3 := mul_le_mul_of_nonneg_left hTD (mul_nonneg hA hW.le)
  have he : A * W * (36 * D) = 18 * K := by
    calc
      _ = 36 * (A * W * D) := by ring
      _ = _ := by rw [hAW]; ring
  rw [he] at h3
  refine ⟨by nlinarith only [h2, h3], ?_⟩
  rw [← hAW2]
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ hq hW.le |>.mpr hqW) hA

lemma positive_grid_cost_bound {c A Z W D K q T r : ℝ} {m : ℕ}
    (hr : 0 ≤ r) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hW : 0 < W)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hq : 1 ≤ q) (hT : 0 ≤ T)
    (hqW : m ≠ 0 → q ≤ W) (hTD : T ≤ 36 * D)
    (hAW : A * W * D = K / 2) (hAW2 : A * W ^ 2 = Z)
    (hDZ : D * Z / W = K / 2) (hratio : T / q ≤ 8 + 288 * D / W)
    (hc : c ≤ 16 * 4096 * (1 + r) * T +
      (if m = 0 then 0 else 2 * 4096 * A * q * T) +
      2 * 4096 * Z * (1 + T / q) + 2) :
    c ≤ 576 * 4096 * (1 + r) * D + 32 * 4096 * Z +
      512 * 4096 * min K (D * Z) + 2 := by
  have hbase := mul_le_mul_of_nonneg_left hTD
    (show 0 ≤ 16 * 4096 * (1 + r) by positivity)
  have hroot := cubic_root_cost (by norm_num : (0 : ℝ) ≤ 4096) hZ hratio hDZ
  have hs : (if m = 0 then 0 else 2 * 4096 * A * q * T) ≤ 36 * 4096 * K ∧
      (if m = 0 then 0 else 2 * 4096 * A * q * T) ≤ 2 * 4096 * Z * T := by
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte]
      constructor <;> positivity
    · simp only [hm, ↓reduceIte]
      have hh := positive_cost_components hA hW (by linarith : 0 ≤ q)
        hT (hqW hm) hTD hAW hAW2
      refine ⟨hh.1, ?_⟩
      have hz := (quartic_spatial_cost hA hZ hq hT hh.2).1
      nlinarith only [hz]
  have hrootq : Z * (T / q) ≤ Z * T := by
    apply mul_le_mul_of_nonneg_left _ hZ
    apply (div_le_iff₀ (by linarith : 0 < q)).mpr
    nlinarith only [mul_nonneg hT (sub_nonneg.mpr hq)]
  have hZT := mul_le_mul_of_nonneg_left hTD hZ
  apply cost_minimum_bound hD hZ hK
  · by_cases hm : m = 0 <;> simp only [hm, ↓reduceIte] at hc hs <;>
      nlinarith only [hc, hbase, hroot, hs.1]
  · by_cases hm : m = 0 <;> simp only [hm, ↓reduceIte] at hc hs <;>
      nlinarith only [hc, hbase, hs.2, hrootq, hZT]

lemma tuned_size_control {L r M σ Δ ε : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hlarge : ε ^ 2 < 2 * L * Δ) :
    (4 : ℝ) ^ hierarchyDepth L M σ Δ ε ≤ (tunedConfig L r M σ Δ ε).T ∧
    ((tunedConfig L r M σ Δ ε).T : ℝ) ≤ 2 * (iterationTarget L Δ ε : ℝ) := by
  let N := iterationTarget L Δ ε
  let q := 4 ^ hierarchyDepth L M σ Δ ε
  have hN := iterationTarget_bounds hL hΔ hε hlarge
  have hqN : q ≤ N := hierarchy_power_le_target L M σ Δ ε (by omega)
  have hb := rounded_multiple_bounds N q (by dsimp [q]; positivity) hqN
  have hT : (tunedConfig L r M σ Δ ε).T = q * ⌈(N : ℝ) / q⌉₊ := by
    simp only [tunedConfig, not_le.mpr hlarge, ↓reduceIte, q, N]
  rw [hT]
  constructor
  · exact_mod_cast hqN.trans hb.1
  · exact_mod_cast hb.2

lemma tuned_positive_calls {L r M σ Δ ε : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hM : 0 < M) (hσ : 0 < σ)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hlarge : ε ^ 2 < 2 * L * Δ) :
    ((tunedConfig L r M σ Δ ε).calls : ℝ) ≤
      576 * 4096 * (1 + r) * (L * Δ / ε ^ 2) + 32 * 4096 * (σ ^ 2 / ε ^ 2) +
      512 * 4096 * min (M * σ * Δ / ε ^ 3) ((L * Δ / ε ^ 2) * (σ ^ 2 / ε ^ 2)) + 2 := by
  let N := iterationTarget L Δ ε
  let m := hierarchyDepth L M σ Δ ε
  let q : ℝ := 4 ^ m
  let W := 2 * L * σ / (M * ε)
  let A := M ^ 2 * (1 / (2 * L)) ^ 2
  let D := L * Δ / ε ^ 2
  let Z := σ ^ 2 / ε ^ 2
  let K := M * σ * Δ / ε ^ 3
  have hN := iterationTarget_bounds hL hΔ hε hlarge
  have hNp : 0 < N := by omega
  have hh := positive_hierarchy_bounds hL hM hσ hε hNp
  have ht := tuned_size_control (r := r) (M := M) (σ := σ) hL hΔ hε hlarge
  have hq : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hqW (hm : m ≠ 0) : q ≤ W := by
    have hp : 1 < (4 : ℕ) ^ m := one_lt_pow₀ (by norm_num) hm
    simpa only [q, m, W, Nat.cast_pow, Nat.cast_ofNat] using hh.2.2 hp
  have hAW : A * W * D = K / 2 := by dsimp [A, W, D, K]; field_simp
  have hAW2 : A * W ^ 2 = Z := by dsimp [A, W, Z]; field_simp
  have hDZ : D * Z / W = K / 2 := by dsimp [D, Z, W, K]; field_simp
  have hratio : ((tunedConfig L r M σ Δ ε).T : ℝ) / q ≤ 8 + 288 * D / W := by
    apply rounded_root_ratio (by exact_mod_cast hNp) (by dsimp [W]; positivity)
      (by positivity) ht.2
    · convert hN.2.1 using 1; dsimp [D]; ring
    · simpa only [q, m, W, Nat.cast_pow, Nat.cast_ofNat] using hh.2.1
  apply positive_grid_cost_bound (A := A) (W := W) (T := ((tunedConfig L r M σ Δ ε).T : ℝ))
    hr (by dsimp [A]; positivity) (by positivity)
    (by dsimp [W]; positivity) (by positivity) (by positivity)
    hq (by positivity) hqW
  · convert (tuned_iterations_bounds (r := r) (M := M) (σ := σ) hL hΔ hε hlarge).2.2 using 1; ring
  · exact hAW
  · exact hAW2
  · exact hDZ
  · exact hratio
  · exact tuned_calls_grid_bound L r M σ Δ ε hr
      (fun l hl => tuned_iterations_divisible L r M σ Δ ε l hl) ht.1

lemma tuned_degenerate_calls {L r M σ Δ ε : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hlarge : ε ^ 2 < 2 * L * Δ) (hz : M = 0 ∨ σ = 0) :
    ((tunedConfig L r M σ Δ ε).calls : ℝ) ≤
      576 * 4096 * (1 + r) * (L * Δ / ε ^ 2) + 32 * 4096 * (σ ^ 2 / ε ^ 2) + 2 := by
  have ht := tuned_size_control (r := r) (M := M) (σ := σ) hL hΔ hε hlarge
  have hc := tuned_calls_grid_bound L r M σ Δ ε hr
    (fun l hl => tuned_iterations_divisible L r M σ Δ ε l hl) ht.1
  have hb := mul_le_mul_of_nonneg_left
    (tuned_iterations_bounds (r := r) (M := M) (σ := σ) hL hΔ hε hlarge).2.2
    (show 0 ≤ 16 * 4096 * (1 + r) by positivity)
  have hbase : 16 * 4096 * (1 + r) * (tunedConfig L r M σ Δ ε).T ≤
      576 * 4096 * (1 + r) * (L * Δ / ε ^ 2) := by
    convert hb using 1; ring
  by_cases hσ : σ = 0
  · rw [hσ] at hbase
    simp only [hσ, hierarchyDepth, ↓reduceIte, pow_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, mul_zero, zero_mul, add_zero] at hc ⊢
    linarith only [hc, hbase]
  · have hM : M = 0 := hz.resolve_right hσ
    have hdepth : hierarchyDepth L M σ Δ ε = Nat.log 4 (iterationTarget L Δ ε) := by
      simp only [hierarchyDepth, hσ, hM, ↓reduceIte]
    have hN := iterationTarget_bounds hL hΔ hε hlarge
    have hp := (lower_power_four (iterationTarget L Δ ε) (by omega)).2
    have hpR : (iterationTarget L Δ ε : ℝ) < 4 * (4 : ℝ) ^ hierarchyDepth L M σ Δ ε := by
      rw [hdepth]
      exact_mod_cast hp
    have hratio : ((tunedConfig L r M σ Δ ε).T : ℝ) /
        (4 : ℝ) ^ hierarchyDepth L M σ Δ ε ≤ 8 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith only [ht.2, hpR]
    have hroot := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 2 * 4096 * (σ ^ 2 / ε ^ 2) by positivity)
    have hs : (if hierarchyDepth L M σ Δ ε = 0 then (0 : ℝ) else
        2 * 4096 * (M ^ 2 * (1 / (2 * L)) ^ 2) *
          4 ^ hierarchyDepth L M σ Δ ε * (tunedConfig L r M σ Δ ε).T) = 0 := by
      simp only [hM, zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, ite_self]
    rw [hs] at hc
    have hZ : 0 ≤ σ ^ 2 / ε ^ 2 := by positivity
    nlinarith only [hc, hbase, hroot, hZ]

lemma tuned_calls_bound {L r M σ Δ ε : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hM : 0 ≤ M) (hσ : 0 ≤ σ)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (tunedConfig L r M σ Δ ε).calls ≤
      if 2 * L * Δ ≤ ε ^ 2 then 0 else
        16777216 * ⌈1 + (1 + r) * L * Δ / ε ^ 2 + σ ^ 2 / ε ^ 2 +
          min (M * σ * Δ / ε ^ 3) (L * Δ * σ ^ 2 / ε ^ 4)⌉₊ := by
  by_cases hsmall : 2 * L * Δ ≤ ε ^ 2
  · rw [ite_eq_left hsmall, calls_sum_levels]
    simp only [tunedConfig, hsmall, ↓reduceIte, Finset.range_zero, Finset.sum_empty, mul_zero, le_refl]
  · rw [ite_eq_right hsmall]
    have hlarge := lt_of_not_ge hsmall
    have hc : ((tunedConfig L r M σ Δ ε).calls : ℝ) ≤
        576 * 4096 * (1 + r) * (L * Δ / ε ^ 2) + 32 * 4096 * (σ ^ 2 / ε ^ 2) +
        512 * 4096 * min (M * σ * Δ / ε ^ 3) ((L * Δ / ε ^ 2) * (σ ^ 2 / ε ^ 2)) + 2 := by
      by_cases hz : M = 0 ∨ σ = 0
      · have hd := tuned_degenerate_calls hL hr hΔ hε hlarge hz
        have hm : M * σ * Δ / ε ^ 3 = 0 := by rcases hz with h | h <;> simp [h]
        have hn : 0 ≤ (L * Δ / ε ^ 2) * (σ ^ 2 / ε ^ 2) := by positivity
        simpa only [hm, min_eq_left hn, mul_zero, add_zero] using hd
      · have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm (fun h => hz (Or.inl h)))
        have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm (fun h => hz (Or.inr h)))
        exact tuned_positive_calls hL hr hMp hσp hΔ hε hlarge
    have hh := cost_ceiling_bound hr (by positivity : 0 ≤ L * Δ / ε ^ 2)
      (by positivity : 0 ≤ σ ^ 2 / ε ^ 2) (by positivity : 0 ≤ M * σ * Δ / ε ^ 3) hc
    have he1 : (1 + r) * (L * Δ / ε ^ 2) = (1 + r) * L * Δ / ε ^ 2 := by ring
    have he2 : (L * Δ / ε ^ 2) * (σ ^ 2 / ε ^ 2) = L * Δ * σ ^ 2 / ε ^ 4 := by ring
    simpa only [he1, he2] using hh

end OracleTemplate.MixedNoise
