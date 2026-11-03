import LongTails.Proofs.ComparisonTrustPlans

namespace LongTails.Proofs.ComparisonTrustDirection

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion LongTails.Proofs.ComparisonTrustPlans
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "nE" => Module.finrank ℝ E

def mid (lh : ℝ × ℝ) : ℝ := (lh.1 + lh.2) / 2

def sigmaOf (tst : E → Bool) : ℕ → ℝ :=
  loopPure (fun i σ => Function.update σ i (if tst (basisVec i) then 1 else -1)) nE 0 (fun _ => 1)

def champOf (tst : E → Bool) (σ : ℕ → ℝ) : ℕ :=
  loopPure (fun i j => if tst (σ i • (basisVec i : E) - σ j • basisVec j) then i else j) nE 0 0

def bisectOf (tst : E → Bool) (σ : ℕ → ℝ) (i j m : ℕ) : ℝ × ℝ :=
  loopPure (fun _ lh => if tst ((basisVec i : E) - (mid lh * σ j) • basisVec j) then
    (mid lh, lh.2) else (lh.1, mid lh)) m 0 (-2, 2)

def coefOf (tst : E → Bool) (σ : ℕ → ℝ) (j m : ℕ) : ℕ → ℝ :=
  loopPure (fun i coef => Function.update coef i (mid (bisectOf tst σ i j m))) nE 0 (fun _ => 0)

def dirPure (tst : E → Bool) (m : ℕ) : E :=
  assemble (sigmaOf tst) (champOf tst (sigmaOf tst))
    (coefOf tst (sigmaOf tst) (champOf tst (sigmaOf tst)) m)

lemma eval_dirPlan (g : E × E → Bool) (t : Tuning) (y : E) :
    QueryPlan.eval g (dirPlan t y) = dirPure (fun w => g (y - t.τ • w, y + t.τ • w)) t.m := by
  simp only [dirPlan, QueryPlan.eval_bind, QueryPlan.eval_map, eval_loop, dirPure, sigmaOf,
    champOf, coefOf, bisectOf, signStep, champStep, ratioStep, bisectStep, testPlan, eval_cmpPlan,
    mid]
  rfl

section Basis

lemma basisVec_of_lt {i : ℕ} (h : i < nE) :
    (basisVec i : E) = stdOrthonormalBasis ℝ E ⟨i, h⟩ := by
  simp [basisVec, h]

lemma basisVec_of_ge {i : ℕ} (h : ¬ i < nE) : (basisVec i : E) = 0 := by
  simp [basisVec, h]

lemma norm_basisVec_le (i : ℕ) : ‖(basisVec i : E)‖ ≤ 1 := by
  by_cases h : i < nE
  · rw [basisVec_of_lt h, (stdOrthonormalBasis ℝ E).orthonormal.1]
  · rw [basisVec_of_ge h, norm_zero]
    norm_num

lemma inner_basisVec {i j : ℕ} (hi : i < nE) (hj : j < nE) :
    ⟪(basisVec i : E), basisVec j⟫ = if i = j then 1 else 0 := by
  rw [basisVec_of_lt hi, basisVec_of_lt hj, orthonormal_iff_ite.mp
    (stdOrthonormalBasis ℝ E).orthonormal]
  simp [Fin.ext_iff]

lemma sum_range_basis (F : ℕ → E → ℝ) :
    ∑ i ∈ Finset.range nE, F i (basisVec i) =
      ∑ i : Fin nE, F i (stdOrthonormalBasis ℝ E i) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basisVec_of_lt i.2]

lemma sum_range_basis_vec (F : ℕ → E → E) :
    ∑ i ∈ Finset.range nE, F i (basisVec i) =
      ∑ i : Fin nE, F i (stdOrthonormalBasis ℝ E i) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basisVec_of_lt i.2]

lemma expand (x : E) : ∑ i ∈ Finset.range nE, ⟪(basisVec i : E), x⟫ • (basisVec i : E) = x := by
  rw [sum_range_basis_vec (fun _ v => ⟪v, x⟫ • v)]
  exact (stdOrthonormalBasis ℝ E).sum_repr' x

lemma norm_sq_expand (x : E) : ‖x‖ ^ 2 = ∑ i ∈ Finset.range nE, ⟪(basisVec i : E), x⟫ ^ 2 := by
  rw [sum_range_basis (fun _ v => ⟪v, x⟫ ^ 2), ← real_inner_self_eq_norm_sq]
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm x]
  ring

lemma norm_sq_combo (c : ℕ → ℝ) :
    ‖∑ i ∈ Finset.range nE, c i • (basisVec i : E)‖ ^ 2 = ∑ i ∈ Finset.range nE, c i ^ 2 := by
  rw [norm_sq_expand]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_right, inner_basisVec hi' hi']
    simp
  · intro j hj hji
    rw [real_inner_smul_right, inner_basisVec hi' (Finset.mem_range.mp hj)]
    simp [Ne.symm hji]
  · intro h
    exact absurd hi h

end Basis

section Analysis

variable (tst : E → Bool) (gr : E) (ζ : ℝ)

def TestSpec : Prop :=
  ∀ w : E, ‖w‖ ≤ 3 → (tst w = true → -ζ ≤ ⟪gr, w⟫) ∧ (tst w = false → ⟪gr, w⟫ ≤ ζ)

variable {tst gr ζ}

lemma sigma_spec : (∀ i < nE, sigmaOf tst i = if tst (basisVec i) then 1 else -1) ∧
    ∀ i, sigmaOf tst i = 1 ∨ sigmaOf tst i = -1 := by
  have h := loopPure_induction
    (fun i σ => Function.update σ i (if tst (basisVec i) then (1 : ℝ) else -1))
    (fun k σ => (∀ i < k, σ i = if tst (basisVec i) then 1 else -1) ∧ ∀ i, σ i = 1 ∨ σ i = -1)
    (fun _ => 1) ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun _ => Or.inl rfl⟩
    (fun k σ ⟨h1, h2⟩ => by
      refine ⟨fun i hi => ?_, fun i => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · rw [Function.update_of_ne (by omega)]
          exact h1 i hi
        · subst hi
          simp
      · by_cases hik : i = k
        · subst hik
          simp only [Function.update_self]
          split_ifs <;> simp
        · rw [Function.update_of_ne hik]
          exact h2 i) nE
  exact h

lemma sigma_sq (i : ℕ) : sigmaOf tst i * sigmaOf tst i = 1 := by
  rcases (sigma_spec (tst := tst)).2 i with h | h <;> rw [h] <;> norm_num

lemma norm_sigma_smul (i : ℕ) : ‖sigmaOf tst i • (basisVec i : E)‖ ≤ 1 := by
  rw [norm_smul]
  rcases (sigma_spec (tst := tst)).2 i with h | h <;> rw [h] <;> simp [norm_basisVec_le]

lemma sigma_abs (h : TestSpec tst gr ζ) (hζ : 0 ≤ ζ) (i : ℕ) (hi : i < nE) :
    |⟪gr, basisVec i⟫| - 2 * ζ ≤ sigmaOf tst i * ⟪gr, basisVec i⟫ := by
  have hw : ‖(basisVec i : E)‖ ≤ 3 := (norm_basisVec_le i).trans (by norm_num)
  have hs := (sigma_spec (tst := tst)).1 i hi
  have hT := h _ hw
  cases ht : tst (basisVec i)
  · rw [hs, ht]
    have := hT.2 ht
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases abs_cases ⟪gr, (basisVec i : E)⟫ with ⟨ha, _⟩ | ⟨ha, _⟩ <;> linarith
  · rw [hs, ht]
    have := hT.1 ht
    simp only [↓reduceIte]
    rcases abs_cases ⟪gr, (basisVec i : E)⟫ with ⟨ha, _⟩ | ⟨ha, _⟩ <;> linarith

lemma champ_spec (h : TestSpec tst gr ζ) (hζ : 0 ≤ ζ) :
    champOf tst (sigmaOf tst) < max nE 1 ∧ ∀ l < nE,
      sigmaOf tst l * ⟪gr, basisVec l⟫ ≤
        sigmaOf tst (champOf tst (sigmaOf tst)) * ⟪gr, basisVec (champOf tst (sigmaOf tst))⟫ +
          nE * ζ := by
  set σ := sigmaOf tst
  have key := loopPure_induction
    (fun i j => if tst (σ i • (basisVec i : E) - σ j • basisVec j) then i else j)
    (fun k j => j < max k 1 ∧ ∀ l < k, σ l * ⟪gr, basisVec l⟫ ≤ σ j * ⟪gr, basisVec j⟫ + k * ζ)
    0 ⟨by simp, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
    (fun k j ⟨hj, hl⟩ => by
      have hw : ‖σ k • (basisVec k : E) - σ j • basisVec j‖ ≤ 3 := by
        calc _ ≤ ‖σ k • (basisVec k : E)‖ + ‖σ j • (basisVec j : E)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (norm_sigma_smul k) (norm_sigma_smul j)
          _ ≤ 3 := by norm_num
      have hT := h _ hw
      have hin : ⟪gr, σ k • (basisVec k : E) - σ j • basisVec j⟫ =
          σ k * ⟪gr, basisVec k⟫ - σ j * ⟪gr, basisVec j⟫ := by
        rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
      have hk1 : ((k + 1 : ℕ) : ℝ) = k + 1 := by push_cast; ring
      have hkζ : 0 ≤ ((k : ℝ) + 1) * ζ := mul_nonneg (by positivity) hζ
      cases ht : tst (σ k • (basisVec k : E) - σ j • basisVec j)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have h2 := hT.2 ht
        rw [hin] at h2
        refine ⟨by omega, fun l hl' => ?_⟩
        rw [hk1]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hl' | hl'
        · linarith [hl l hl']
        · subst hl'
          nlinarith
      · simp only [↓reduceIte]
        have h1 := hT.1 ht
        rw [hin] at h1
        refine ⟨by omega, fun l hl' => ?_⟩
        rw [hk1]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hl' | hl'
        · linarith [hl l hl']
        · subst hl'
          linarith [hkζ]) nE
  exact key


lemma bisect_spec (h : TestSpec tst gr ζ) (hζ : 0 ≤ ζ) {σ : ℕ → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    {i j : ℕ} {D ρ : ℝ} (hD : 0 < D) (hDj : σ j * ⟪gr, basisVec j⟫ = D)
    (hρ : ⟪gr, basisVec i⟫ = ρ * D) (hρ2 : |ρ| ≤ 2) (m : ℕ) :
    |mid (bisectOf tst σ i j m) - ρ| ≤ 2 / 2 ^ m + ζ / D := by
  have hσj : σ j * σ j = 1 := by rcases hσ j with h | h <;> rw [h] <;> norm_num
  have key := loopPure_induction
    (fun _ lh => if tst ((basisVec i : E) - (mid lh * σ j) • basisVec j) then
      (mid lh, lh.2) else (lh.1, mid lh))
    (fun k lh => -2 ≤ lh.1 ∧ lh.2 ≤ 2 ∧ lh.2 - lh.1 = 4 / 2 ^ k ∧
      lh.1 - ζ / D ≤ ρ ∧ ρ ≤ lh.2 + ζ / D)
    (-2, 2)
    ⟨le_rfl, le_rfl, by norm_num, by
      have : 0 ≤ ζ / D := div_nonneg hζ hD.le
      have := (abs_le.mp hρ2).1
      simp only
      linarith, by
      have : 0 ≤ ζ / D := div_nonneg hζ hD.le
      have := (abs_le.mp hρ2).2
      simp only
      linarith⟩
    (fun k lh ⟨h1, h2, h3, h4, h5⟩ => by
      have hmid1 : lh.1 ≤ mid lh := by
        unfold mid
        have : 0 ≤ lh.2 - lh.1 := by rw [h3]; positivity
        linarith
      have hmid2 : mid lh ≤ lh.2 := by
        unfold mid
        have : 0 ≤ lh.2 - lh.1 := by rw [h3]; positivity
        linarith
      have hw : ‖(basisVec i : E) - (mid lh * σ j) • basisVec j‖ ≤ 3 := by
        calc _ ≤ ‖(basisVec i : E)‖ + ‖(mid lh * σ j) • (basisVec j : E)‖ := norm_sub_le _ _
          _ ≤ 1 + 2 * 1 := by
            refine add_le_add (norm_basisVec_le i) ?_
            rw [norm_smul]
            refine mul_le_mul ?_ (norm_basisVec_le j) (norm_nonneg _) (by norm_num)
            rw [Real.norm_eq_abs, abs_mul]
            have : |σ j| = 1 := by rcases hσ j with h | h <;> rw [h] <;> norm_num
            rw [this, mul_one, abs_le]
            constructor <;> linarith
          _ = 3 := by norm_num
      have hT := h _ hw
      have hin : ⟪gr, (basisVec i : E) - (mid lh * σ j) • basisVec j⟫ = (ρ - mid lh) * D := by
        rw [inner_sub_right, real_inner_smul_right, hρ, mul_assoc, hDj]
        ring
      have hpow : (4 : ℝ) / 2 ^ (k + 1) = (4 / 2 ^ k) / 2 := by rw [pow_succ]; ring
      cases ht : tst ((basisVec i : E) - (mid lh * σ j) • basisVec j)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have := hT.2 ht
        rw [hin] at this
        have hle : ρ - mid lh ≤ ζ / D := by
          rw [le_div_iff₀ hD]
          linarith
        refine ⟨h1, by linarith, by rw [hpow, ← h3]; unfold mid; ring, h4, by linarith⟩
      · simp only [↓reduceIte]
        have := hT.1 ht
        rw [hin] at this
        have hle : -(ζ / D) ≤ ρ - mid lh := by
          rw [neg_le, le_div_iff₀ hD]
          linarith
        refine ⟨by linarith, h2, by rw [hpow, ← h3]; unfold mid; ring, by linarith, h5⟩) m
  obtain ⟨_, _, h3, h4, h5⟩ := key
  set lh := loopPure (fun _ lh => if tst ((basisVec i : E) - (mid lh * σ j) • basisVec j) then
      (mid lh, lh.2) else (lh.1, mid lh)) m 0 ((-2 : ℝ), (2 : ℝ))
  have hb : bisectOf tst σ i j m = lh := rfl
  rw [hb, abs_le]
  have h4' : (4 : ℝ) / 2 ^ m / 2 = 2 / 2 ^ m := by ring
  unfold mid
  constructor <;> nlinarith

lemma coef_spec (σ : ℕ → ℝ) (j m : ℕ) (i : ℕ) (hi : i < nE) :
    coefOf tst σ j m i = mid (bisectOf tst σ i j m) := by
  have key := loopPure_induction
    (fun i coef => Function.update coef i (mid (bisectOf tst σ i j m)))
    (fun k coef => ∀ i < k, coef i = mid (bisectOf tst σ i j m)) (fun _ => 0)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
    (fun k coef h i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · rw [Function.update_of_ne (by omega)]
        exact h i hi
      · subst hi
        simp) nE
  exact key i hi

omit [FiniteDimensional ℝ E] in
lemma normalize_dist (a b : E) (hb : b ≠ 0) :
    ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  by_cases ha : a = 0
  · subst ha
    simp only [norm_zero, inv_zero, zero_smul, zero_sub, norm_neg, norm_smul, norm_inv,
      norm_norm]
    rw [inv_mul_cancel₀ hb'.ne', le_div_iff₀ hb']
    linarith
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have h1 : ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • a‖ = |‖b‖ - ‖a‖| / ‖b‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have : ‖a‖⁻¹ - ‖b‖⁻¹ = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by field_simp
    rw [this, abs_div, abs_of_pos (by positivity : 0 < ‖a‖ * ‖b‖)]
    field_simp
  have h2 : ‖‖b‖⁻¹ • a - ‖b‖⁻¹ • b‖ = ‖a - b‖ / ‖b‖ := by
    rw [← smul_sub, norm_smul, norm_inv, norm_norm]
    field_simp
  have h3 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le a b
  calc ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖
      ≤ ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • a‖ + ‖‖b‖⁻¹ • a - ‖b‖⁻¹ • b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |‖b‖ - ‖a‖| / ‖b‖ + ‖a - b‖ / ‖b‖ := by rw [h1, h2]
    _ ≤ ‖a - b‖ / ‖b‖ + ‖a - b‖ / ‖b‖ := by gcongr
    _ = 2 * ‖a - b‖ / ‖b‖ := by ring

lemma exists_large_coord (x : E) (hn : 0 < nE) :
    ∃ k < nE, ‖x‖ / Real.sqrt nE ≤ |⟪x, basisVec k⟫| := by
  by_contra hcon
  push Not at hcon
  have hsq : ∀ k ∈ Finset.range nE, ⟪(basisVec k : E), x⟫ ^ 2 < (‖x‖ / Real.sqrt nE) ^ 2 := by
    intro k hk
    rw [real_inner_comm, ← sq_abs]
    have h := hcon k (Finset.mem_range.mp hk)
    exact pow_lt_pow_left₀ h (abs_nonneg _) (by norm_num)
  have hsum := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hn.ne') hsq
  rw [← norm_sq_expand, Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)] at hsum
  have hn' : (0 : ℝ) < nE := by exact_mod_cast hn
  rw [mul_div_cancel₀ _ hn'.ne'] at hsum
  exact lt_irrefl _ hsum

theorem dir_accuracy (h : TestSpec tst gr ζ) (hζ : 0 ≤ ζ) (hgr : gr ≠ 0)
    (hsmall : ((nE : ℝ) + 2) * ζ ≤ ‖gr‖ / (2 * Real.sqrt nE)) (m : ℕ) :
    ‖dirPure tst m - ‖gr‖⁻¹ • gr‖ ≤
      2 * Real.sqrt nE * (2 / 2 ^ m + 2 * Real.sqrt nE * ζ / ‖gr‖) := by
  have hn : 0 < nE := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨gr, hgr⟩
  have hn' : (0 : ℝ) < nE := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt nE := Real.sqrt_pos.mpr hn'
  have hgr' : 0 < ‖gr‖ := norm_pos_iff.mpr hgr
  set σ := sigmaOf tst with hσdef
  set j := champOf tst σ with hjdef
  obtain ⟨hj, hchamp⟩ := champ_spec (tst := tst) h hζ
  rw [← hσdef, ← hjdef] at hj hchamp
  have hjn : j < nE := by simpa [max_eq_left (Nat.one_le_iff_ne_zero.mpr hn.ne')] using hj
  set D := σ j * ⟪gr, basisVec j⟫ with hDdef
  obtain ⟨k, hk, hkbig⟩ := exists_large_coord gr hn
  have hkσ := sigma_abs (tst := tst) h hζ k hk
  have hkc := hchamp k hk
  rw [real_inner_comm] at hkbig
  have hDlow : ‖gr‖ / (2 * Real.sqrt nE) ≤ D := by
    have h2 : ‖gr‖ / Real.sqrt nE = 2 * (‖gr‖ / (2 * Real.sqrt nE)) := by field_simp
    have hkbig' : ‖gr‖ / Real.sqrt nE ≤ |⟪gr, (basisVec k : E)⟫| := by
      rwa [real_inner_comm] at hkbig
    nlinarith
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hDlow
  have hσ := (sigma_spec (tst := tst)).2
  have hσj : σ j * σ j = 1 := sigma_sq j
  have hgj : ⟪gr, (basisVec j : E)⟫ = σ j * D := by
    rw [hDdef, ← mul_assoc, hσj, one_mul]
  have hDle : D ≤ ‖gr‖ := by
    have : |⟪gr, (basisVec j : E)⟫| ≤ ‖gr‖ := by
      calc _ ≤ ‖gr‖ * ‖(basisVec j : E)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖gr‖ * 1 := by gcongr; exact norm_basisVec_le j
        _ = ‖gr‖ := mul_one _
    have : D ≤ |⟪gr, (basisVec j : E)⟫| := by
      rw [hgj, abs_mul]
      have : |σ j| = 1 := by rcases hσ j with h | h <;> rw [hσdef, h] <;> norm_num
      rw [this, one_mul]
      exact le_abs_self D
    linarith
  set err := 2 / 2 ^ m + ζ / D with herr
  have herr0 : 0 ≤ err := by positivity
  have hcoef : ∀ i < nE, |(if i = j then σ j else coefOf tst σ j m i) -
      ⟪(basisVec i : E), gr⟫ / D| ≤ err := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, real_inner_comm, hgj, mul_div_cancel_right₀ _ hD.ne', sub_self, abs_zero]
      exact herr0
    · rw [ite_eq_right hij, coef_spec σ j m i hi, real_inner_comm]
      have hiσ := sigma_abs (tst := tst) h hζ i hi
      have hic := hchamp i hi
      have hρ2 : |⟪gr, (basisVec i : E)⟫ / D| ≤ 2 := by
        rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
        have : ((nE : ℝ) + 2) * ζ ≤ D := by
          have : ‖gr‖ / (2 * Real.sqrt nE) ≤ D := hDlow
          linarith
        nlinarith
      exact bisect_spec h hζ hσ hD hDdef.symm
        (by rw [div_mul_cancel₀ _ hD.ne']) hρ2 m
  set v : E := ∑ i ∈ Finset.range nE, (if i = j then σ j else coefOf tst σ j m i) • basisVec i
  have hw : D⁻¹ • gr = ∑ i ∈ Finset.range nE, (⟪(basisVec i : E), gr⟫ / D) • basisVec i := by
    conv_lhs => rw [← expand gr]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, div_eq_inv_mul]
  have hdiff : ‖v - D⁻¹ • gr‖ ≤ Real.sqrt nE * err := by
    have heq : v - D⁻¹ • gr = ∑ i ∈ Finset.range nE,
        ((if i = j then σ j else coefOf tst σ j m i) - ⟪(basisVec i : E), gr⟫ / D) •
          (basisVec i : E) := by
      rw [hw, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_smul]
    have hsq2 : ‖v - D⁻¹ • gr‖ ^ 2 ≤ (Real.sqrt nE * err) ^ 2 := by
      rw [heq, norm_sq_combo, mul_pow, Real.sq_sqrt hn'.le]
      calc _ ≤ ∑ _i ∈ Finset.range nE, err ^ 2 := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hcoef i (Finset.mem_range.mp hi)) 2
        _ = _ := by simp
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq2
  have hwnorm : 1 ≤ ‖D⁻¹ • gr‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hD, ← div_eq_inv_mul,
      le_div_iff₀ hD, one_mul]
    exact hDle
  have hwne : D⁻¹ • gr ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hwnorm
    linarith
  have hnorm : ‖D⁻¹ • gr‖⁻¹ • (D⁻¹ • gr) = ‖gr‖⁻¹ • gr := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hD, smul_smul]
    congr 1
    field_simp
  have hmain := normalize_dist v (D⁻¹ • gr) hwne
  rw [hnorm] at hmain
  have hdirv : dirPure tst m = ‖v‖⁻¹ • v := rfl
  rw [hdirv]
  have hζD : ζ / D ≤ 2 * Real.sqrt nE * ζ / ‖gr‖ := by
    rw [div_le_div_iff₀ hD hgr']
    have : ‖gr‖ ≤ 2 * Real.sqrt nE * D := by
      have := hDlow
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    nlinarith
  calc ‖‖v‖⁻¹ • v - ‖gr‖⁻¹ • gr‖ ≤ 2 * ‖v - D⁻¹ • gr‖ / ‖D⁻¹ • gr‖ := hmain
    _ ≤ 2 * ‖v - D⁻¹ • gr‖ / 1 := by
        gcongr
    _ ≤ 2 * (Real.sqrt nE * err) := by rw [div_one]; gcongr
    _ ≤ 2 * Real.sqrt nE * (2 / 2 ^ m + 2 * Real.sqrt nE * ζ / ‖gr‖) := by
        rw [herr]
        nlinarith

end Analysis

end

end LongTails.Proofs.ComparisonTrustDirection
