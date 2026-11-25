import LongTails.Proofs.StagewiseSarahPotential

namespace OracleTemplate.StagewiseSarah

variable {L Lbar μ σ Δ ε : ℝ}

lemma after_append (μ σ : ℝ) (l₁ l₂ : List Epoch) (a : ℝ) :
    after μ σ (l₁ ++ l₂) a = after μ σ l₂ (after μ σ l₁ a) := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.cons_append, after]
    exact ih _

lemma after_mono (hμ : 0 < μ) (σ : ℝ) (l : List Epoch) (hl : ∀ e ∈ l, Good L Lbar μ e)
    {a b : ℝ} (h : a ≤ b) : after μ σ l a ≤ after μ σ l b := by
  rw [after_affine μ σ l a, after_affine μ σ l b]
  have := mul_le_mul_of_nonneg_left h (slope_nonneg hμ l hl)
  linarith

lemma after_nonneg (hμ : 0 < μ) (σ : ℝ) (l : List Epoch) (hl : ∀ e ∈ l, Good L Lbar μ e)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ after μ σ l a := by
  rw [after_affine]
  exact add_nonneg (mul_nonneg (slope_nonneg hμ l hl) ha) (after_zero_nonneg hμ σ l hl)

lemma gain_mul_le {e : Epoch} (he : Good L Lbar μ e) (hμ : 0 < μ) :
    gain μ e * (1 + ((e.m : ℝ) + 1) * (e.η * μ)) ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := he.theta_bounds hμ
  have hx : 0 ≤ e.η * μ := mul_nonneg he.hη.le hμ.le
  have hb := one_add_mul_le_pow (a := e.η * μ) (by linarith) (e.m + 1)
  push_cast at hb
  have hp : (1 - e.η * μ) ^ (e.m + 1) * (1 + e.η * μ) ^ (e.m + 1) ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  unfold gain
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) _)).trans hp

lemma after_replicate {e : Epoch} (he : Good L Lbar μ e) (hμ : 0 < μ) (σ : ℝ) (R : ℕ)
    (a a₀ : ℝ) (k : ℕ) (ha : 0 ≤ a)
    (h : a ≤ a₀ / (1 + ((e.m : ℝ) + 1) * (e.η * μ)) ^ k + σ ^ 2 / (μ * e.B)) :
    after μ σ (List.replicate R e) a ≤
      a₀ / (1 + ((e.m : ℝ) + 1) * (e.η * μ)) ^ (k + R) + σ ^ 2 / (μ * e.B) := by
  induction R generalizing a k with
  | zero => simpa [after] using h
  | succ R ih =>
    have hη := he.hη
    have hu : 0 < ((e.m : ℝ) + 1) * (e.η * μ) := by positivity
    have hB : (0 : ℝ) < e.B := by exact_mod_cast he.hB
    have hg := gain_mul_le he hμ
    have hg0 := (he.gain_bounds hμ).1
    have hn := he.noise_nonneg σ
    have hnoise : noise σ e = ((e.m : ℝ) + 1) * (e.η * μ) * (σ ^ 2 / (μ * e.B)) := by
      unfold noise
      field_simp
    rw [List.replicate_succ]
    simp only [after]
    have hstep : gain μ e * (a + noise σ e) ≤
        a₀ / (1 + ((e.m : ℝ) + 1) * (e.η * μ)) ^ (k + 1) + σ ^ 2 / (μ * e.B) := by
      set u := ((e.m : ℝ) + 1) * (e.η * μ) with hudef
      set N := σ ^ 2 / (μ * e.B) with hN
      have h1u : 0 < 1 + u := by linarith
      have hgle : gain μ e ≤ 1 / (1 + u) := by
        rw [le_div_iff₀ h1u]
        exact hg
      have hsum : 0 ≤ a + noise σ e := add_nonneg ha hn
      have h2 : gain μ e * (a + noise σ e) ≤ 1 / (1 + u) * (a + noise σ e) :=
        mul_le_mul_of_nonneg_right hgle hsum
      have h3 : 1 / (1 + u) * (a + noise σ e) ≤
          1 / (1 + u) * (a₀ / (1 + u) ^ k + N + u * N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hnoise]
        linarith
      have h4 : 1 / (1 + u) * (a₀ / (1 + u) ^ k + N + u * N) = a₀ / (1 + u) ^ (k + 1) + N := by
        rw [pow_succ]
        field_simp
        ring
      linarith
    have := ih (gain μ e * (a + noise σ e)) (k + 1)
      (mul_nonneg (by linarith) (add_nonneg ha hn)) hstep
    rw [show k + (R + 1) = k + 1 + R by omega]
    exact this

lemma stageEpoch_B (L Lbar μ σ Δ : ℝ) (j : ℕ) :
    (stageEpoch L Lbar μ σ Δ j).B = max 1 ⌈stageBatch μ σ Δ j⌉₊ := by
  unfold stageEpoch
  dsimp only
  split_ifs <;> rfl

lemma floor_sq_pos (hμ : 0 < μ) (hLbar : μ ≤ Lbar) : 1 ≤ ⌊(Lbar / μ) ^ 2⌋₊ := by
  apply Nat.le_floor
  have h1 : 1 ≤ Lbar / μ := by rwa [le_div_iff₀ hμ, one_mul]
  have : (1 : ℝ) ≤ (Lbar / μ) ^ 2 := by nlinarith
  simpa using this

lemma stageEpoch_good (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (σ Δ : ℝ) (j : ℕ) :
    Good L Lbar μ (stageEpoch L Lbar μ σ Δ j) := by
  have hL0 : 0 < L := lt_of_lt_of_le hμ hL
  have hLb0 : 0 < Lbar := lt_of_lt_of_le hL0 hLbar
  unfold stageEpoch
  dsimp only
  split_ifs with hbr
  · set B := max 1 ⌈stageBatch μ σ Δ j⌉₊ with hBdef
    set F := ⌊(Lbar / μ) ^ 2⌋₊ with hF
    have hF1 : 1 ≤ F := floor_sq_pos hμ (hL.trans hLbar)
    have hB1 : 1 ≤ B := le_max_left _ _
    have hs1 : 1 ≤ min B F := le_min hB1 hF1
    have hsR : (1 : ℝ) ≤ ((min B F : ℕ) : ℝ) := by exact_mod_cast hs1
    have hsqrt1 : 1 ≤ √((min B F : ℕ) : ℝ) := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt hsR
    have hsq : √((min B F : ℕ) : ℝ) ^ 2 = ((min B F : ℕ) : ℝ) := Real.sq_sqrt (by linarith)
    have hcast : (((min B F - 1 : ℕ)) : ℝ) = ((min B F : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub hs1]
      simp
    have hFle : ((min B F : ℕ) : ℝ) ≤ (Lbar / μ) ^ 2 := by
      have h1 : ((min B F : ℕ) : ℝ) ≤ (F : ℝ) := by exact_mod_cast min_le_right B F
      exact h1.trans (Nat.floor_le (by positivity))
    have hsqle : √((min B F : ℕ) : ℝ) ≤ Lbar / μ := by
      rw [show Lbar / μ = √((Lbar / μ) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt hFle
    have hden : 0 < 2 * Lbar * √((min B F : ℕ) : ℝ) := by positivity
    refine ⟨hB1, by positivity, ?_, ?_, ?_⟩
    · change 1 / (2 * Lbar * √((min B F : ℕ) : ℝ)) * L ≤ 1 / 2
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden]
      nlinarith
    · change 4 * Lbar ^ 2 * (1 / (2 * Lbar * √((min B F : ℕ) : ℝ))) ^ 2 *
        ((min B F - 1 : ℕ) : ℝ) ≤ 1
      rw [hcast, div_pow, mul_pow, mul_pow, hsq]
      rw [show 4 * Lbar ^ 2 * (1 ^ 2 / (2 ^ 2 * Lbar ^ 2 * ((min B F : ℕ) : ℝ))) *
          (((min B F : ℕ) : ℝ) - 1) = (((min B F : ℕ) : ℝ) - 1) / ((min B F : ℕ) : ℝ) by
        field_simp
        ring]
      rw [div_le_one (by linarith)]
      linarith
    · change (((min B F - 1 : ℕ) : ℝ) + 1) * (1 / (2 * Lbar * √((min B F : ℕ) : ℝ)) * μ) ≤ 1 / 2
      rw [hcast, sub_add_cancel]
      have hsqle' : √((min B F : ℕ) : ℝ) * μ ≤ Lbar := by
        rwa [le_div_iff₀ hμ] at hsqle
      rw [show ((min B F : ℕ) : ℝ) * (1 / (2 * Lbar * √((min B F : ℕ) : ℝ)) * μ) =
          (√((min B F : ℕ) : ℝ) ^ 2 * μ) / (2 * Lbar * √((min B F : ℕ) : ℝ)) by
        rw [hsq]
        field_simp]
      rw [div_le_iff₀ hden]
      nlinarith [Real.sqrt_nonneg ((min B F : ℕ) : ℝ)]
  · refine ⟨le_max_left _ _, by positivity, ?_, ?_, ?_⟩
    · change 1 / (2 * L) * L ≤ 1 / 2
      rw [show 1 / (2 * L) * L = 1 / 2 by field_simp]
    · change 4 * Lbar ^ 2 * (1 / (2 * L)) ^ 2 * ((0 : ℕ) : ℝ) ≤ 1
      simp
    · change (((0 : ℕ) : ℝ) + 1) * (1 / (2 * L) * μ) ≤ 1 / 2
      rw [Nat.cast_zero, zero_add, one_mul, div_mul_eq_mul_div, one_mul,
        div_le_iff₀ (by positivity)]
      linarith

lemma stage_good (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (σ Δ : ℝ) (j : ℕ) :
    ∀ e ∈ stage L Lbar μ σ Δ j, Good L Lbar μ e := by
  intro e he
  rw [stage, List.mem_replicate] at he
  rw [he.2]
  exact stageEpoch_good hμ hL hLbar σ Δ j

lemma stages_good (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (σ Δ : ℝ) (K : ℕ) :
    ∀ e ∈ (List.range K).flatMap (stage L Lbar μ σ Δ), Good L Lbar μ e := by
  intro e he
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp he
  exact stage_good hμ hL hLbar σ Δ j e hj

lemma after_stage (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (hΔ : 0 < Δ) (σ : ℝ) (j : ℕ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ Δ / 2 ^ j) :
    after μ σ (stage L Lbar μ σ Δ j) a ≤ Δ / 2 ^ (j + 1) := by
  have he := stageEpoch_good hμ hL hLbar σ Δ j
  set e := stageEpoch L Lbar μ σ Δ j with hedef
  have hη := he.hη
  set u := ((e.m : ℝ) + 1) * (e.η * μ) with hu
  have hupos : 0 < u := by positivity
  have hBnat : e.B = max 1 ⌈stageBatch μ σ Δ j⌉₊ := stageEpoch_B L Lbar μ σ Δ j
  have hB1 : (1 : ℝ) ≤ e.B := by exact_mod_cast he.hB
  have hBb : stageBatch μ σ Δ j ≤ e.B := by
    rw [hBnat]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  have hN : σ ^ 2 / (μ * e.B) ≤ Δ / 2 ^ j / 8 := by
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    rw [div_le_iff₀ (by positivity), div_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    unfold stageBatch at hBb
    rw [div_le_iff₀ (by positivity)] at hBb
    nlinarith
  have hN0 : 0 ≤ σ ^ 2 / (μ * e.B) := by positivity
  have hrep := after_replicate he hμ σ (stageRepeats L Lbar μ σ Δ j) a a 0 ha0
    (by rw [pow_zero, div_one]; linarith)
  rw [Nat.zero_add] at hrep
  have hR : 3 ≤ (stageRepeats L Lbar μ σ Δ j : ℝ) * u := by
    have h1 : 3 / u ≤ (stageRepeats L Lbar μ σ Δ j : ℝ) := Nat.le_ceil _
    rwa [div_le_iff₀ hupos] at h1
  have hpow : 4 ≤ (1 + u) ^ stageRepeats L Lbar μ σ Δ j := by
    have hb := one_add_mul_le_pow (a := u) (by linarith) (stageRepeats L Lbar μ σ Δ j)
    linarith
  have hfrac : a / (1 + u) ^ stageRepeats L Lbar μ σ Δ j ≤ a / 4 :=
    div_le_div_of_nonneg_left ha0 (by norm_num) hpow
  have hD : Δ / 2 ^ (j + 1) = Δ / 2 ^ j / 2 := by
    rw [pow_succ]
    field_simp
  have hDpos : 0 ≤ Δ / 2 ^ j := by positivity
  rw [stage, hD]
  linarith

lemma after_stages (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (hΔ : 0 < Δ) (σ : ℝ) (K : ℕ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ Δ) :
    after μ σ ((List.range K).flatMap (stage L Lbar μ σ Δ)) a ≤ Δ / 2 ^ K := by
  induction K with
  | zero => simpa [after] using ha
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, after_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact after_stage hμ hL hLbar hΔ σ K _
      (after_nonneg hμ σ _ (stages_good hμ hL hLbar σ Δ K) ha0) ih

lemma two_pow_stage_count (hε : 0 < ε) (hΔ : ε < Δ) :
    Δ / ε ≤ (2 : ℝ) ^ ⌈Real.logb 2 (Δ / ε)⌉₊ ∧ (2 : ℝ) ^ ⌈Real.logb 2 (Δ / ε)⌉₊ ≤ 2 * (Δ / ε) := by
  have hx : 0 < Δ / ε := div_pos (hε.trans hΔ) hε
  have hx1 : 1 < Δ / ε := by rwa [lt_div_iff₀ hε, one_mul]
  have hlog : 0 ≤ Real.logb 2 (Δ / ε) := Real.logb_nonneg (by norm_num) hx1.le
  have hid : (2 : ℝ) ^ Real.logb 2 (Δ / ε) = Δ / ε :=
    Real.rpow_logb (by norm_num) (by norm_num) hx
  constructor
  · rw [← Real.rpow_natCast]
    calc Δ / ε = (2 : ℝ) ^ Real.logb 2 (Δ / ε) := hid.symm
      _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 (Δ / ε)⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  · have h1 : ((⌈Real.logb 2 (Δ / ε)⌉₊ : ℕ) : ℝ) ≤ Real.logb 2 (Δ / ε) + 1 :=
      (Nat.ceil_lt_add_one hlog).le
    have h2 := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) h1
    rw [Real.rpow_natCast, Real.rpow_add (by norm_num), hid, Real.rpow_one] at h2
    linarith

lemma schedule_good (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (σ Δ ε : ℝ) :
    ∀ e ∈ schedule L Lbar μ σ Δ ε, Good L Lbar μ e :=
  stages_good hμ hL hLbar σ Δ _

theorem after_schedule_le (hμ : 0 < μ) (hL : μ ≤ L) (hLbar : L ≤ Lbar) (hε : 0 < ε) (σ : ℝ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ Δ) :
    after μ σ (schedule L Lbar μ σ Δ ε) a ≤ ε := by
  by_cases hΔε : Δ ≤ ε
  · have hK : ⌈Real.logb 2 (Δ / ε)⌉₊ = 0 := by
      rw [Nat.ceil_eq_zero]
      exact Real.logb_nonpos (by norm_num) (div_nonneg (ha0.trans ha) hε.le)
        ((div_le_one hε).mpr hΔε)
    simp only [schedule, hK, List.range_zero, List.flatMap_nil, after]
    linarith
  · push Not at hΔε
    have hΔ : 0 < Δ := hε.trans hΔε
    have h1 := after_stages hμ hL hLbar hΔ σ ⌈Real.logb 2 (Δ / ε)⌉₊ a ha0 ha
    have h2 := (two_pow_stage_count hε hΔε).1
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at h2
    linarith

end OracleTemplate.StagewiseSarah
