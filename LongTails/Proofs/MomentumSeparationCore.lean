import LongTails.Proofs.SeparationInstance
import LongTails.Proofs.MomentumMuonRate

namespace LongTails.Proofs.MomentumSeparationCore

noncomputable def impulse (β ℓ : ℝ) (α : ℕ → ℝ) (u : ℕ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 =>
      let W := β * (impulse β ℓ α u t).2 +
        (1 - β) * (ℓ * (impulse β ℓ α u t).1 + if t = u then 1 else 0)
      ((impulse β ℓ α u t).1 - α t * W, W)

lemma impulse_before (β ℓ : ℝ) (α : ℕ → ℝ) (u : ℕ) :
    ∀ t, t ≤ u → impulse β ℓ α u t = (0, 0) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have h := ih (by omega)
      have hne : t ≠ u := by omega
      simp only [impulse, h, hne, ↓reduceIte]
      simp

lemma impulse_first (β ℓ : ℝ) (α : ℕ → ℝ) (u : ℕ) :
    (impulse β ℓ α u (u + 1)).1 = -(α u * (1 - β)) := by
  simp only [impulse, impulse_before β ℓ α u u le_rfl, ↓reduceIte]
  ring

lemma impulse_momentum_closed (β ℓ : ℝ) (α : ℕ → ℝ) (u t : ℕ) :
    (impulse β ℓ α u (t + 1)).2 =
      (if u ≤ t then (1 - β) * β ^ (t - u) else 0) +
        (1 - β) * ℓ * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) * (impulse β ℓ α u τ).1 := by
  induction t with
  | zero =>
      simp only [impulse, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
      by_cases hu : u = 0
      · subst hu; simp
      · have h0 : (0 : ℕ) ≠ u := Ne.symm hu
        simp [h0, hu]
  | succ t ih =>
      change β * (impulse β ℓ α u (t + 1)).2 +
        (1 - β) * (ℓ * (impulse β ℓ α u (t + 1)).1 + if t + 1 = u then 1 else 0) = _
      rw [ih, Finset.sum_range_succ (fun τ => β ^ (t + 1 - τ) * (impulse β ℓ α u τ).1) (t + 1)]
      have hsum : β * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) * (impulse β ℓ α u τ).1 =
          ∑ τ ∈ Finset.range (t + 1), β ^ (t + 1 - τ) * (impulse β ℓ α u τ).1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ hτ
        have : τ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hτ)
        rw [show t + 1 - τ = (t - τ) + 1 by omega, pow_succ]
        ring
      by_cases h1 : u ≤ t
      · have h2 : u ≤ t + 1 := by omega
        have h3 : t + 1 ≠ u := by omega
        simp only [h1, h2, h3, ↓reduceIte, Nat.sub_self, pow_zero, add_zero]
        rw [show t + 1 - u = (t - u) + 1 by omega, pow_succ]
        rw [← hsum]
        ring
      · by_cases h4 : u = t + 1
        · subst h4
          have hz : (impulse β ℓ α (t + 1) (t + 1)).1 = 0 := by
            rw [impulse_before β ℓ α (t + 1) (t + 1) le_rfl]
          simp only [h1, ↓reduceIte, le_refl, Nat.sub_self, pow_zero, hz, mul_zero, add_zero]
          rw [← hsum]
          ring
        · have h2 : ¬ u ≤ t + 1 := by omega
          have h3 : t + 1 ≠ u := by omega
          have hz : (impulse β ℓ α u (t + 1)).1 = 0 := by
            rw [impulse_before β ℓ α u (t + 1) (by omega)]
          simp only [h1, h2, h3, ↓reduceIte, hz, mul_zero, add_zero, zero_add]
          rw [← hsum]
          ring

lemma impulse_deviation {β ℓ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hℓ : 0 ≤ ℓ) {α : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (u : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∀ k, (∀ τ, τ < u + k → |(impulse β ℓ α u τ).1| ≤ M) →
      |(impulse β ℓ α u (u + k)).1 +
          ∑ i ∈ Finset.range k, α (u + i) * ((1 - β) * β ^ i)| ≤
        ℓ * M * ∑ i ∈ Finset.range k, α (u + i) := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [impulse_before β ℓ α u u le_rfl]
  | succ k ih =>
      intro hb
      have hprev := ih (fun τ hτ => hb τ (by omega))
      have hstep : (impulse β ℓ α u (u + (k + 1))).1 =
          (impulse β ℓ α u (u + k)).1 - α (u + k) * (impulse β ℓ α u (u + k + 1)).2 := by
        rw [show u + (k + 1) = (u + k) + 1 by omega]
        rfl
      have hW := impulse_momentum_closed β ℓ α u (u + k)
      have hif : (if u ≤ u + k then (1 - β) * β ^ (u + k - u) else 0) = (1 - β) * β ^ k := by
        rw [ite_eq_left (by omega : u ≤ u + k), show u + k - u = k by omega]
      rw [hif] at hW
      have hsumbound : |∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ) *
          (impulse β ℓ α u τ).1| ≤ M / (1 - β + 1) * 0 + M * ∑ τ ∈ Finset.range (u + k + 1),
            β ^ (u + k - τ) := by
        rw [mul_zero, zero_add, Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ hτ => ?_)
        rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 _), mul_comm M]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ0 _)
        have hτ' : τ < u + k + 1 := Finset.mem_range.mp hτ
        by_cases hτu : τ ≤ u
        · rw [impulse_before β ℓ α u τ hτu]
          simpa using hM
        · exact hb τ (by omega)
      have hgeo : (1 - β) * ∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ) ≤ 1 := by
        have h := Finset.sum_range_reflect (fun j => β ^ j) (u + k + 1)
        simp only [Nat.add_sub_cancel] at h
        rw [h, mul_comm, geom_sum_mul_neg]
        linarith [pow_nonneg hβ0 (u + k + 1)]
      have hfeed : |(impulse β ℓ α u (u + k + 1)).2 - (1 - β) * β ^ k| ≤ ℓ * M := by
        rw [hW, add_sub_cancel_left]
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - β), abs_of_nonneg hℓ]
        have h1 : |∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ) * (impulse β ℓ α u τ).1| ≤
            M * ∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ) := by
          simpa using hsumbound
        have h2 : (1 - β) * |∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ) *
            (impulse β ℓ α u τ).1| ≤ M := by
          calc _ ≤ (1 - β) * (M * ∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ)) :=
                mul_le_mul_of_nonneg_left h1 (by linarith)
            _ = M * ((1 - β) * ∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ)) := by ring
            _ ≤ M * 1 := mul_le_mul_of_nonneg_left hgeo hM
            _ = M := mul_one M
        calc (1 - β) * ℓ * |∑ τ ∈ Finset.range (u + k + 1), β ^ (u + k - τ) *
              (impulse β ℓ α u τ).1| = ℓ * ((1 - β) * |∑ τ ∈ Finset.range (u + k + 1),
                β ^ (u + k - τ) * (impulse β ℓ α u τ).1|) := by ring
          _ ≤ ℓ * M := mul_le_mul_of_nonneg_left h2 hℓ
      rw [hstep, Finset.sum_range_succ, Finset.sum_range_succ]
      have he : (impulse β ℓ α u (u + k)).1 - α (u + k) * (impulse β ℓ α u (u + k + 1)).2 +
          (∑ i ∈ Finset.range k, α (u + i) * ((1 - β) * β ^ i) + α (u + k) * ((1 - β) * β ^ k)) =
          ((impulse β ℓ α u (u + k)).1 + ∑ i ∈ Finset.range k, α (u + i) * ((1 - β) * β ^ i)) -
            α (u + k) * ((impulse β ℓ α u (u + k + 1)).2 - (1 - β) * β ^ k) := by ring
      rw [he]
      have hαk := hα (u + k)
      calc _ ≤ |(impulse β ℓ α u (u + k)).1 + ∑ i ∈ Finset.range k, α (u + i) * ((1 - β) * β ^ i)| +
            |α (u + k) * ((impulse β ℓ α u (u + k + 1)).2 - (1 - β) * β ^ k)| := abs_sub _ _
        _ ≤ ℓ * M * ∑ i ∈ Finset.range k, α (u + i) + α (u + k) * (ℓ * M) := by
            rw [abs_mul, abs_of_nonneg hαk]
            exact add_le_add hprev (mul_le_mul_of_nonneg_left hfeed hαk)
        _ = _ := by ring

lemma persistence {β ℓ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hℓ : 0 ≤ ℓ) {α : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (u k : ℕ) (hk : 1 ≤ k)
    (hwin : ℓ * ∑ i ∈ Finset.range k, α (u + i) ≤ 1 / 3) :
    (1 - β) * α u / 2 ≤ |(impulse β ℓ α u (u + k)).1| := by
  set Y := ∑ i ∈ Finset.range k, α (u + i) * ((1 - β) * β ^ i) with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hα _) (mul_nonneg (by linarith) (pow_nonneg hβ0 _))
  have hYu : (1 - β) * α u ≤ Y := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hY, Finset.sum_range_succ']
    simp only [Nat.add_zero, pow_zero, mul_one]
    have : 0 ≤ ∑ i ∈ Finset.range k', α (u + (i + 1)) * ((1 - β) * β ^ (i + 1)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hα _) (mul_nonneg (by linarith) (pow_nonneg hβ0 _))
    linarith
  have hYmono : ∀ j, j ≤ k → ∑ i ∈ Finset.range j, α (u + i) * ((1 - β) * β ^ i) ≤ Y := by
    intro j hj
    rw [hY]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj)
    intro i _ _
    exact mul_nonneg (hα _) (mul_nonneg (by linarith) (pow_nonneg hβ0 _))
  have hΛmono : ∀ j, j ≤ k → ∑ i ∈ Finset.range j, α (u + i) ≤ ∑ i ∈ Finset.range k, α (u + i) := by
    intro j hj
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hj)
    intro i _ _
    exact hα _
  have hbound : ∀ j, j ≤ k → ∀ τ, τ < u + j → |(impulse β ℓ α u τ).1| ≤ 3 / 2 * Y := by
    intro j
    induction j with
    | zero =>
        intro _ τ hτ
        rw [impulse_before β ℓ α u τ (by omega)]
        simp only [abs_zero]
        positivity
    | succ j ih =>
        intro hj τ hτ
        by_cases hτj : τ < u + j
        · exact ih (by omega) τ hτj
        · have hτeq : τ = u + j := by omega
          subst hτeq
          have hdev := impulse_deviation hβ0 hβ1 hℓ hα u (by positivity : (0 : ℝ) ≤ 3 / 2 * Y) j
            (ih (by omega))
          have hyj := hYmono j (by omega)
          have hyj0 : 0 ≤ ∑ i ∈ Finset.range j, α (u + i) * ((1 - β) * β ^ i) :=
            Finset.sum_nonneg fun i _ =>
              mul_nonneg (hα _) (mul_nonneg (by linarith) (pow_nonneg hβ0 _))
          have hΛj := hΛmono j (by omega)
          have hfeed : ℓ * (3 / 2 * Y) * ∑ i ∈ Finset.range j, α (u + i) ≤ 1 / 2 * Y := by
            have h1 : ℓ * ∑ i ∈ Finset.range j, α (u + i) ≤ 1 / 3 :=
              (mul_le_mul_of_nonneg_left hΛj hℓ).trans hwin
            nlinarith
          have habs := abs_sub_abs_le_abs_sub ((impulse β ℓ α u (u + j)).1)
            (-(∑ i ∈ Finset.range j, α (u + i) * ((1 - β) * β ^ i)))
          rw [sub_neg_eq_add, abs_neg, abs_of_nonneg hyj0] at habs
          linarith
  have hdev := impulse_deviation hβ0 hβ1 hℓ hα u (by positivity : (0 : ℝ) ≤ 3 / 2 * Y) k
    (hbound k le_rfl)
  have hfeed : ℓ * (3 / 2 * Y) * ∑ i ∈ Finset.range k, α (u + i) ≤ 1 / 2 * Y := by
    nlinarith
  have habs := abs_sub_abs_le_abs_sub (-Y) ((impulse β ℓ α u (u + k)).1)
  rw [abs_neg, abs_of_nonneg hY0] at habs
  have hsym : |-Y - (impulse β ℓ α u (u + k)).1| = |(impulse β ℓ α u (u + k)).1 + Y| := by
    rw [← abs_neg]; congr 1; ring
  rw [hsym] at habs
  linarith

open LongTails.Proofs.SeparationInstance

noncomputable def flat (β c w D : ℝ) (α : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 =>
      let M := β * (flat β c w D α t).2 + (1 - β) * (c * valleySlope w D (flat β c w D α t).1)
      ((flat β c w D α t).1 - α t * M, M)

lemma flat_momentum_bound {β c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hc : 0 ≤ c) (w D : ℝ)
    (α : ℕ → ℝ) (t : ℕ) : |(flat β c w D α t).2| ≤ c := by
  induction t with
  | zero => simpa [flat] using hc
  | succ t ih =>
      change |β * (flat β c w D α t).2 + (1 - β) * (c * valleySlope w D (flat β c w D α t).1)| ≤ c
      have hs := abs_valleySlope_le w D (flat β c w D α t).1
      calc _ ≤ |β * (flat β c w D α t).2| + |(1 - β) * (c * valleySlope w D (flat β c w D α t).1)| :=
            abs_add_le _ _
        _ = β * |(flat β c w D α t).2| + (1 - β) * (c * |valleySlope w D (flat β c w D α t).1|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hβ0, abs_of_nonneg (by linarith : 0 ≤ 1 - β),
              abs_of_nonneg hc]
        _ ≤ β * c + (1 - β) * (c * 1) := by
            gcongr
        _ = c := by ring

lemma flat_position_bound {β c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hc : 0 ≤ c) (w D : ℝ)
    {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (t : ℕ) :
    (flat β c w D α t).1 ≤ c * ∑ i ∈ Finset.range t, α i := by
  induction t with
  | zero => simp [flat]
  | succ t ih =>
      change (flat β c w D α t).1 - α t * (β * (flat β c w D α t).2 +
        (1 - β) * (c * valleySlope w D (flat β c w D α t).1)) ≤ _
      have hm := flat_momentum_bound hβ0 hβ1 hc w D α (t + 1)
      change |β * (flat β c w D α t).2 + (1 - β) * (c * valleySlope w D (flat β c w D α t).1)| ≤ c
        at hm
      have h1 := (abs_le.mp hm).1
      rw [Finset.sum_range_succ, mul_add]
      nlinarith [hα t]

lemma flat_travel {β c w D ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hc : 0 ≤ c) (hw : 0 < w)
    (hDw : 0 ≤ D - w)
    {r : ℕ} (hrc : ((r - 1 : ℕ) : ℝ) * c = 8 * ε) (hε : 0 < ε) {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)
    (T : ℕ) (hflat : ∑ t ∈ Finset.range (T + 1),
      ((r - 1 : ℕ) : ℝ) * c * |valleySlope w D (flat β c w D α t).1| ≤ 3 * (T + 1) * ε) :
    1 ≤ T ∧ D - w ≤ c * ∑ i ∈ Finset.range T, α i := by
  by_contra hcon
  have hall : ∀ t ∈ Finset.range (T + 1), (flat β c w D α t).1 ≤ D - w := by
    intro t ht
    by_contra hlt
    push Not at hlt
    apply hcon
    have ht' : t ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hpos := flat_position_bound hβ0 hβ1 hc w D hα t
    have hmono : ∑ i ∈ Finset.range t, α i ≤ ∑ i ∈ Finset.range T, α i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr ht')
        (fun i _ _ => hα i)
    have ht1 : 1 ≤ t := by
      by_contra h0
      have : t = 0 := by omega
      subst this
      simp only [flat] at hlt
      linarith
    exact ⟨le_trans ht1 ht', by nlinarith [mul_le_mul_of_nonneg_left hmono hc]⟩
  have hterm : ∀ t ∈ Finset.range (T + 1), 4 * ε ≤
      ((r - 1 : ℕ) : ℝ) * c * |valleySlope w D (flat β c w D α t).1| := by
    intro t ht
    have hs := valleySlope_far hw (hall t ht)
    rw [abs_of_neg (by linarith), hrc]
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum
  nlinarith

lemma impulse_fresh_momentum (β ℓ : ℝ) (α : ℕ → ℝ) (t : ℕ) :
    (impulse β ℓ α t (t + 1)).2 = 1 - β := by
  simp only [impulse, impulse_before β ℓ α t t le_rfl, ↓reduceIte]
  ring

lemma sqrt_sum_sq_ge {ι : Type*} (S : Finset ι) (F : ι → ℝ) {i : ι} (hi : i ∈ S) :
    |F i| ≤ Real.sqrt (∑ j ∈ S, F j ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun j => F j ^ 2) (fun j _ => sq_nonneg _) hi

lemma fresh_injection {β ℓ : ℝ} (α : ℕ → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ1 : β ≤ 1) {T t : ℕ}
    (ht : t < T) :
    α t * (1 - β) ≤ Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).1) ^ 2) := by
  have h := sqrt_sum_sq_ge (Finset.range T) (fun u => (impulse β ℓ α u (t + 1)).1)
    (Finset.mem_range.mpr ht)
  rw [impulse_first, abs_neg, abs_of_nonneg (mul_nonneg (hα t) (by linarith))] at h
  exact h

lemma kick_bound {β ℓ ν ε : ℝ} (hβ1 : β ≤ 1) (hℓ : 0 ≤ ℓ) (hν : 0 ≤ ν) {α : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (T : ℕ)
    (hstiff : ∑ t ∈ Finset.range (T + 1), ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
      ((impulse β ℓ α u t).1) ^ 2)) ≤ 3 * (T + 1) * ε) :
    ℓ * ν * (1 - β) * ∑ t ∈ Finset.range T, α t ≤ 3 * (T + 1) * ε := by
  have hle : ∀ t ∈ Finset.range T, ℓ * ν * (1 - β) * α t ≤
      ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).1) ^ 2)) := by
    intro t ht
    have h := fresh_injection (ℓ := ℓ) α hα hβ1 (Finset.mem_range.mp ht)
    have hlν : 0 ≤ ℓ * ν := mul_nonneg hℓ hν
    nlinarith [mul_le_mul_of_nonneg_left h hlν]
  have hshift : ∑ t ∈ Finset.range T,
      ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).1) ^ 2)) ≤
      ∑ t ∈ Finset.range (T + 1), ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
        ((impulse β ℓ α u t).1) ^ 2)) := by
    rw [Finset.sum_range_succ']
    have : 0 ≤ ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u 0).1) ^ 2)) := by
      positivity
    linarith
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum hle).trans (hshift.trans hstiff)

lemma abs_sum_le_sqrt_card {ι : Type*} (S : Finset ι) (F : ι → ℝ) :
    ∑ j ∈ S, |F j| ≤ Real.sqrt S.card * Real.sqrt (∑ j ∈ S, F j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun j => |F j|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  linarith

lemma window_sum {α : ℕ → ℝ} {αmax : ℝ} (hαmax : 0 ≤ αmax) {T L j : ℕ}
    (hLT : L ≤ T) (hj : j < L) (hαbar : ∀ i < T, α i ≤ αmax) :
    ∑ i ∈ Finset.range T, α i - L * αmax ≤ ∑ t ∈ Finset.range (T + 1 - L), α (j + t) := by
  set M := T + 1 - L with hM
  have hsplit : T = j + M + (T - j - M) := by omega
  have hdecomp : ∑ i ∈ Finset.range T, α i = ∑ i ∈ Finset.range j, α i +
      ∑ t ∈ Finset.range M, α (j + t) + ∑ t ∈ Finset.range (T - j - M), α (j + M + t) := by
    conv_lhs => rw [hsplit]
    rw [Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range j, α i ≤ j * αmax := by
    calc _ ≤ ∑ _i ∈ Finset.range j, αmax := Finset.sum_le_sum fun i hi =>
          hαbar i (by have := Finset.mem_range.mp hi; omega)
      _ = j * αmax := by simp
  have h2 : ∑ t ∈ Finset.range (T - j - M), α (j + M + t) ≤ (T - j - M : ℕ) * αmax := by
    calc _ ≤ ∑ _t ∈ Finset.range (T - j - M), αmax := Finset.sum_le_sum fun t ht =>
          hαbar _ (by have := Finset.mem_range.mp ht; omega)
      _ = _ := by simp
  have hcount : (j : ℝ) + ((T - j - M : ℕ) : ℝ) ≤ L := by
    have : j + (T - j - M) ≤ L := by omega
    exact_mod_cast this
  nlinarith

lemma floor_bound {β ℓ αmax : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hℓ : 0 ≤ ℓ) {α : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hαmax : 0 ≤ αmax) (T L : ℕ) (hL : 1 ≤ L) (hαbar : ∀ i < T, α i ≤ αmax)
    (hwin : ℓ * (L * αmax) ≤ 1 / 3) :
    (1 - β) / 2 * Real.sqrt L * (∑ i ∈ Finset.range T, α i - L * αmax) ≤
      ∑ t ∈ Finset.range (T + 1),
        Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u t).1) ^ 2) := by
  have hδ : 0 ≤ (1 - β) / 2 := by linarith
  have hRHS : 0 ≤ ∑ t ∈ Finset.range (T + 1),
      Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u t).1) ^ 2) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  by_cases hLT : L ≤ T
  swap
  · have hΛ : ∑ i ∈ Finset.range T, α i ≤ L * αmax := by
      calc _ ≤ ∑ _i ∈ Finset.range T, αmax := Finset.sum_le_sum fun i hi =>
            hαbar i (Finset.mem_range.mp hi)
        _ = T * αmax := by simp
        _ ≤ L * αmax := mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt (not_le.mp hLT))) hαmax
    have : (1 - β) / 2 * Real.sqrt L * (∑ i ∈ Finset.range T, α i - L * αmax) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδ (Real.sqrt_nonneg _)) (by linarith)
    linarith
  set M := T + 1 - L with hM
  have hrange : T + 1 = L + M := by omega
  have hsub : ∑ t ∈ Finset.range M, Real.sqrt (∑ u ∈ Finset.range T,
      ((impulse β ℓ α u (L + t)).1) ^ 2) ≤ ∑ t ∈ Finset.range (T + 1),
        Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u t).1) ^ 2) := by
    rw [hrange, Finset.sum_range_add]
    have : 0 ≤ ∑ t ∈ Finset.range L, Real.sqrt (∑ u ∈ Finset.range T,
        ((impulse β ℓ α u t).1) ^ 2) := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hpoint : ∀ t ∈ Finset.range M, (1 - β) / 2 / Real.sqrt L * ∑ j ∈ Finset.range L, α (t + j) ≤
      Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (L + t)).1) ^ 2) := by
    intro t ht
    have htM : t < M := Finset.mem_range.mp ht
    have hpers : ∀ j ∈ Finset.range L, (1 - β) * α (t + j) / 2 ≤
        |(impulse β ℓ α (t + j) (L + t)).1| := by
      intro j hj
      have hjL : j < L := Finset.mem_range.mp hj
      have hidx : L + t = (t + j) + (L - j) := by omega
      rw [hidx]
      apply persistence hβ0 hβ1 hℓ hα (t + j) (L - j) (by omega)
      calc ℓ * ∑ i ∈ Finset.range (L - j), α (t + j + i) ≤ ℓ * ((L - j : ℕ) * αmax) := by
            apply mul_le_mul_of_nonneg_left _ hℓ
            calc _ ≤ ∑ _i ∈ Finset.range (L - j), αmax := Finset.sum_le_sum fun i hi =>
                  hαbar _ (by have := Finset.mem_range.mp hi; omega)
              _ = _ := by simp
        _ ≤ ℓ * (L * αmax) := by
            apply mul_le_mul_of_nonneg_left _ hℓ
            apply mul_le_mul_of_nonneg_right _ hαmax
            exact_mod_cast Nat.sub_le L j
        _ ≤ 1 / 3 := hwin
    have hinj : (Finset.range L).image (fun j => t + j) ⊆ Finset.range T := by
      intro u hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      have := Finset.mem_range.mp hj
      exact Finset.mem_range.mpr (by omega)
    have hsubsum : ∑ j ∈ Finset.range L, ((impulse β ℓ α (t + j) (L + t)).1) ^ 2 ≤
        ∑ u ∈ Finset.range T, ((impulse β ℓ α u (L + t)).1) ^ 2 := by
      rw [← Finset.sum_image (f := fun u => ((impulse β ℓ α u (L + t)).1) ^ 2)
        (fun a _ b _ h => by simpa using h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg hinj (fun _ _ _ => sq_nonneg _)
    have hcs := abs_sum_le_sqrt_card (Finset.range L) (fun j => (impulse β ℓ α (t + j) (L + t)).1)
    rw [Finset.card_range] at hcs
    have hlow : (1 - β) / 2 * ∑ j ∈ Finset.range L, α (t + j) ≤
        ∑ j ∈ Finset.range L, |(impulse β ℓ α (t + j) (L + t)).1| := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => by have := hpers j hj; linarith
    have hchain : (1 - β) / 2 * ∑ j ∈ Finset.range L, α (t + j) ≤
        Real.sqrt L * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (L + t)).1) ^ 2) :=
      (hlow.trans hcs).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsubsum) (Real.sqrt_nonneg _))
    rw [div_mul_eq_mul_div, div_le_iff₀ hsqL]
    linarith [mul_comm (Real.sqrt L)
      (Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (L + t)).1) ^ 2))]
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum, Finset.sum_comm] at hsum
  have hwinsum : ∀ j ∈ Finset.range L, ∑ i ∈ Finset.range T, α i - L * αmax ≤
      ∑ t ∈ Finset.range M, α (t + j) := by
    intro j hj
    have h := window_sum hαmax hLT (Finset.mem_range.mp hj) hαbar
    simpa only [add_comm j] using h
  have htot := Finset.sum_le_sum hwinsum
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htot
  have hcoef : 0 ≤ (1 - β) / 2 / Real.sqrt L := div_nonneg hδ hsqL.le
  have hfin := mul_le_mul_of_nonneg_left htot hcoef
  have hLsq : (L : ℝ) / Real.sqrt L = Real.sqrt L := by
    rw [div_eq_iff hsqL.ne']; exact (Real.mul_self_sqrt hLpos.le).symm
  have heq : (1 - β) / 2 / Real.sqrt L * (L * (∑ i ∈ Finset.range T, α i - L * αmax)) =
      (1 - β) / 2 * Real.sqrt L * (∑ i ∈ Finset.range T, α i - L * αmax) := by
    calc (1 - β) / 2 / Real.sqrt L * (L * (∑ i ∈ Finset.range T, α i - L * αmax)) =
          (1 - β) / 2 * (∑ i ∈ Finset.range T, α i - L * αmax) * ((L : ℝ) / Real.sqrt L) := by ring
      _ = (1 - β) / 2 * (∑ i ∈ Finset.range T, α i - L * αmax) * Real.sqrt L := by rw [hLsq]
      _ = _ := by ring
  rw [heq] at hfin
  linarith

lemma ema_step (β : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    (1 - β) * ∑ τ ∈ Finset.range (t + 2), β ^ (t + 1 - τ) * x τ =
      β * ((1 - β) * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) * x τ) + (1 - β) * x (t + 1) := by
  rw [Finset.sum_range_succ (fun τ => β ^ (t + 1 - τ) * x τ) (t + 1), Nat.sub_self, pow_zero,
    one_mul, mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  have : τ ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hτ)
  rw [show t + 1 - τ = (t - τ) + 1 by omega, pow_succ]
  ring

lemma ema_sum_identity (β : ℝ) (x : ℕ → ℝ) (T : ℕ) :
    (1 - β) * ∑ t ∈ Finset.range (T + 1), ((1 - β) * ∑ τ ∈ Finset.range (t + 1),
        β ^ (t - τ) * x τ) +
      β * ((1 - β) * ∑ τ ∈ Finset.range (T + 1), β ^ (T - τ) * x τ) =
      (1 - β) * ∑ t ∈ Finset.range (T + 1), x t := by
  induction T with
  | zero => simp; ring
  | succ T ih =>
      rw [Finset.sum_range_succ (fun t => (1 - β) * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) * x τ),
        Finset.sum_range_succ x, ema_step]
      nlinarith [ih]

lemma ema_sum_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t) (T : ℕ) :
    ∑ t ∈ Finset.range T, ((1 - β) * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) * x τ) ≤
      ∑ t ∈ Finset.range T, x t := by
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  have hid := ema_sum_identity β x T'
  have hlast : 0 ≤ β * ((1 - β) * ∑ τ ∈ Finset.range (T' + 1), β ^ (T' - τ) * x τ) :=
    mul_nonneg hβ0 (mul_nonneg (by linarith)
      (Finset.sum_nonneg fun τ _ => mul_nonneg (pow_nonneg hβ0 _) (hx τ)))
  have hδ : 0 < 1 - β := by linarith
  have h := (le_of_eq hid).trans' (le_add_of_nonneg_right hlast)
  exact le_of_mul_le_mul_left h hδ

noncomputable def vecOf (T : ℕ) (g : ℕ → ℝ) : EuclideanSpace ℝ (Fin T) :=
  WithLp.toLp 2 (fun u : Fin T => g u)

lemma norm_vecOf (T : ℕ) (g : ℕ → ℝ) :
    ‖vecOf T g‖ = Real.sqrt (∑ u ∈ Finset.range T, g u ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun u => g u ^ 2) T]
  simp [vecOf, sq_abs]

lemma momentum_norm_le {β ℓ ν : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hℓ : 0 ≤ ℓ) (hν : 0 ≤ ν)
    (α : ℕ → ℝ) (T t : ℕ) :
    ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) ≤
      ν * Real.sqrt (1 - β) + ℓ * ((1 - β) * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) *
        (ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u τ).1) ^ 2))) := by
  have hnorm := norm_vecOf T
  have hdecomp : vecOf T (fun u => (impulse β ℓ α u (t + 1)).2) =
      vecOf T (fun u => if u ≤ t then (1 - β) * β ^ (t - u) else 0) +
        ∑ τ ∈ Finset.range (t + 1), ((1 - β) * ℓ * β ^ (t - τ)) •
          vecOf T (fun u => (impulse β ℓ α u τ).1) := by
    ext u
    simp only [vecOf, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      smul_eq_mul, impulse_momentum_closed]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro τ _
    ring
  have htri := norm_add_le (vecOf T (fun u => if u ≤ t then (1 - β) * β ^ (t - u) else 0))
    (∑ τ ∈ Finset.range (t + 1), ((1 - β) * ℓ * β ^ (t - τ)) •
      vecOf T (fun u => (impulse β ℓ α u τ).1))
  rw [← hdecomp] at htri
  have hsum := norm_sum_le (Finset.range (t + 1)) (fun τ => ((1 - β) * ℓ * β ^ (t - τ)) •
      vecOf T (fun u => (impulse β ℓ α u τ).1))
  simp only [norm_smul, Real.norm_eq_abs] at hsum
  have hcoef (τ : ℕ) : |(1 - β) * ℓ * β ^ (t - τ)| = (1 - β) * ℓ * β ^ (t - τ) :=
    abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) hℓ) (pow_nonneg hβ0 _))
  simp only [hcoef] at hsum
  have hfirst : ‖vecOf T (fun u => if u ≤ t then (1 - β) * β ^ (t - u) else 0)‖ ≤
      Real.sqrt (1 - β) := by
    rw [hnorm]
    apply Real.sqrt_le_sqrt
    calc ∑ u ∈ Finset.range T, (if u ≤ t then (1 - β) * β ^ (t - u) else 0) ^ 2 ≤
          ∑ u ∈ Finset.range (t + 1), ((1 - β) * β ^ (t - u)) ^ 2 := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun u => u ≤ t)]
          have h0 : ∑ u ∈ (Finset.range T).filter (fun u => ¬ u ≤ t),
              (if u ≤ t then (1 - β) * β ^ (t - u) else 0) ^ 2 = 0 :=
            Finset.sum_eq_zero fun u hu => by
              rw [ite_eq_right (Finset.mem_filter.mp hu).2]; ring
          rw [h0, add_zero, Finset.sum_congr rfl (fun u hu => by
            rw [ite_eq_left (Finset.mem_filter.mp hu).2])]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hu).2)
          · intro _ _ _; exact sq_nonneg _
        _ ≤ (1 - β) * (1 - β ^ (t + 1)) :=
          LongTails.Proofs.MomentumMuonRate.reflect_square_sum hβ0 hβ1.le t
        _ ≤ 1 - β := by
          have : 0 ≤ β ^ (t + 1) := pow_nonneg hβ0 _
          nlinarith
  rw [← hnorm]
  have hmain : ‖vecOf T (fun u => (impulse β ℓ α u (t + 1)).2)‖ ≤ Real.sqrt (1 - β) +
      ∑ τ ∈ Finset.range (t + 1), (1 - β) * ℓ * β ^ (t - τ) *
        ‖vecOf T (fun u => (impulse β ℓ α u τ).1)‖ := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hmain hν
  have hre : ν * (Real.sqrt (1 - β) + ∑ τ ∈ Finset.range (t + 1), (1 - β) * ℓ * β ^ (t - τ) *
        ‖vecOf T (fun u => (impulse β ℓ α u τ).1)‖) =
      ν * Real.sqrt (1 - β) + ℓ * ((1 - β) * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) *
        (ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u τ).1) ^ 2))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro τ _
    rw [hnorm]
    ring
  linarith

lemma momentum_norm_ge {β ℓ : ℝ} (hβ1 : β ≤ 1) (α : ℕ → ℝ) {T t : ℕ} (ht : t < T) :
    1 - β ≤ Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) := by
  have h := sqrt_sum_sq_ge (Finset.range T) (fun u => (impulse β ℓ α u (t + 1)).2)
    (Finset.mem_range.mpr ht)
  rw [impulse_fresh_momentum, abs_of_nonneg (by linarith)] at h
  exact h

lemma window_length {ℓ αmax : ℝ} (hℓ : 0 < ℓ) (hαmax : 0 < αmax) (hsmall : ℓ * αmax < 1 / 3) :
    ∃ L : ℕ, 1 ≤ L ∧ ℓ * (L * αmax) ≤ 1 / 3 ∧ 1 ≤ 6 * ℓ * αmax * L := by
  set x := 1 / (3 * (ℓ * αmax)) with hx
  have hpos : 0 < ℓ * αmax := mul_pos hℓ hαmax
  have hx1 : 1 < x := by
    rw [hx, lt_div_iff₀ (by positivity)]
    linarith
  refine ⟨⌊x⌋₊, ?_, ?_, ?_⟩
  · exact Nat.one_le_floor_iff _ |>.mpr hx1.le
  · have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have : ℓ * (⌊x⌋₊ * αmax) = (ℓ * αmax) * ⌊x⌋₊ := by ring
    rw [this]
    calc (ℓ * αmax) * ⌊x⌋₊ ≤ (ℓ * αmax) * x := mul_le_mul_of_nonneg_left hfl hpos.le
      _ = 1 / 3 := by rw [hx]; field_simp
  · have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have hge1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _ |>.mpr hx1.le)
    have h2 : x ≤ 2 * ⌊x⌋₊ := by linarith
    have hxe : (ℓ * αmax) * x = 1 / 3 := by rw [hx]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 hpos.le]

lemma shift_sum_le {F : ℕ → ℝ} (hF : ∀ t, 0 ≤ F t) (T : ℕ) :
    ∑ t ∈ Finset.range T, F (t + 1) ≤ ∑ t ∈ Finset.range (T + 1), F t := by
  rw [Finset.sum_range_succ']
  linarith [hF 0]

set_option maxHeartbeats 1000000 in
theorem core_sgd {β ℓ c w D ν η ε : ℝ} {r T : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hw : 0 < w) (hε : 0 < ε) (hν : 0 < ν) (hη : 0 < η)
    (hrc : ((r - 1 : ℕ) : ℝ) * c = 8 * ε) (hDw : 0 ≤ D - w) (hDl : 2 * c ≤ 3 * ℓ * (D - w))
    (hstiff : ∑ t ∈ Finset.range (T + 1), ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
      ((impulse β ℓ (fun _ => η) u t).1) ^ 2)) ≤ 3 * (T + 1) * ε)
    (hflat : ∑ t ∈ Finset.range (T + 1),
      ((r - 1 : ℕ) : ℝ) * c * |valleySlope w D (flat β c w D (fun _ => η) t).1| ≤
        3 * (T + 1) * ε) :
    (D - w) * ℓ * (1 - β) ^ 3 * ν ^ 2 ≤ 6912 * c * ε ^ 2 * (T + 1) := by
  have hα : ∀ i, 0 ≤ (fun _ : ℕ => η) i := fun _ => hη.le
  obtain ⟨hT1, htravel⟩ := flat_travel hβ0 hβ1.le hc.le hw hDw hrc hε hα T hflat
  have hkick := kick_bound hβ1.le hℓ.le hν.le hα T hstiff
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htravel hkick
  set δ := 1 - β with hδdef
  have hδ : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  set sd := Real.sqrt δ with hsd
  have hsd0 : 0 < sd := Real.sqrt_pos.mpr hδ
  have hsd2 : sd ^ 2 = δ := Real.sq_sqrt hδ.le
  have hsd1 : sd ≤ 1 := by nlinarith
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hTp : (0 : ℝ) < T + 1 := by positivity
  by_cases hreg : ν * sd ^ 3 < 128 * ε
  · have h1 : (D - w) * ℓ * ν * δ ≤ 3 * c * ε * (T + 1) := by
      have := mul_le_mul_of_nonneg_left htravel (by positivity : 0 ≤ ℓ * ν * δ)
      nlinarith
    have h2 : ν * δ ^ 2 ≤ 128 * ε := by
      have : δ ^ 2 ≤ sd ^ 3 := by
        rw [← hsd2]; nlinarith [pow_le_one₀ hsd0.le hsd1 (n := 1)]
      nlinarith
    have hDwℓ : 0 ≤ (D - w) * ℓ * ν * δ := by positivity
    calc (D - w) * ℓ * δ ^ 3 * ν ^ 2 = ((D - w) * ℓ * ν * δ) * (ν * δ ^ 2) := by ring
      _ ≤ (3 * c * ε * (T + 1)) * (128 * ε) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ ≤ 6912 * c * ε ^ 2 * (T + 1) := by nlinarith
  push Not at hreg
  have hνδ : 128 * ε ≤ ν * δ := by
    have : sd ^ 3 ≤ δ := by rw [← hsd2]; nlinarith
    nlinarith
  by_cases hbig : 1 / 3 ≤ ℓ * η
  · exfalso
    have hterm : ∀ t ∈ Finset.range T, 42 * ε ≤
        ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
          ((impulse β ℓ (fun _ => η) u (t + 1)).1) ^ 2)) := by
      intro t ht
      have hf := fresh_injection (ℓ := ℓ) (fun _ => η) hα hβ1.le (Finset.mem_range.mp ht)
      have hlν : 0 ≤ ℓ * ν := by positivity
      have h3 := mul_le_mul_of_nonneg_left hf hlν
      have h4 : ν * δ / 3 ≤ ℓ * ν * (η * δ) := by nlinarith
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hsh := shift_sum_le (F := fun t => ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
      ((impulse β ℓ (fun _ => η) u t).1) ^ 2))) (fun t => by positivity) T
    nlinarith
  push Not at hbig
  obtain ⟨L, hL1, hLwin, hL6⟩ := window_length hℓ hη hbig
  have hfloor := floor_bound hβ0 hβ1.le hℓ.le hα hη.le T L hL1 (fun _ _ => le_rfl) hLwin
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hfloor
  have hΛ : 2 / (3 * ℓ) ≤ T * η := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left htravel (by positivity : (0 : ℝ) ≤ 3 * ℓ)
    have h2 : c * 2 ≤ c * (T * η * (3 * ℓ)) := by
      have : 3 * ℓ * (c * (T * η)) = c * (T * η * (3 * ℓ)) := by ring
      linarith
    exact le_of_mul_le_mul_left h2 hc
  have hLη : (L : ℝ) * η ≤ 1 / (3 * ℓ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [show (L : ℝ) * η * (3 * ℓ) = 3 * (ℓ * (L * η)) by ring]
  have hhalf : T * η / 2 ≤ T * η - L * η := by
    have : 1 / (3 * ℓ) = (2 / (3 * ℓ)) / 2 := by ring
    linarith
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by exact_mod_cast hL1)
  have hfl2 : δ / 2 * Real.sqrt L * (T * η / 2) ≤ ∑ t ∈ Finset.range (T + 1),
      Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ (fun _ => η) u t).1) ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_left hhalf (by positivity)) hfloor
  have hst : ℓ * ν * ∑ t ∈ Finset.range (T + 1),
      Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ (fun _ => η) u t).1) ^ 2) ≤
        3 * (T + 1) * ε := by
    rw [Finset.mul_sum]
    calc _ = ∑ t ∈ Finset.range (T + 1), ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
          ((impulse β ℓ (fun _ => η) u t).1) ^ 2)) := by
          apply Finset.sum_congr rfl; intro t _; ring
      _ ≤ _ := hstiff
  have hkey : ℓ * ν * (δ / 4 * Real.sqrt L * (T * η)) ≤ 3 * (T + 1) * ε := by
    have := mul_le_mul_of_nonneg_left hfl2 (by positivity : 0 ≤ ℓ * ν)
    nlinarith
  have hsqL2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by positivity)
  have hsquare : (ℓ * ν * (δ / 4 * Real.sqrt L * (T * η))) ^ 2 ≤ (3 * (T + 1) * ε) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkey 2
  have hexp : (ℓ * ν * (δ / 4 * Real.sqrt L * (T * η))) ^ 2 =
      ℓ ^ 2 * ν ^ 2 * δ ^ 2 * L * T ^ 2 * η ^ 2 / 16 := by
    rw [show (ℓ * ν * (δ / 4 * Real.sqrt L * (T * η))) ^ 2 =
      ℓ ^ 2 * ν ^ 2 * δ ^ 2 * Real.sqrt L ^ 2 * T ^ 2 * η ^ 2 / 16 by ring, hsqL2]
  rw [hexp] at hsquare
  have h6 : ℓ * ν ^ 2 * δ ^ 2 * T ^ 2 * η ≤ 864 * (T + 1) ^ 2 * ε ^ 2 := by
    have hA : 0 ≤ ℓ * ν ^ 2 * δ ^ 2 * T ^ 2 * η / 16 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hL6 hA]
  have h7 : ℓ * ν ^ 2 * δ ^ 2 * (T * η) ≤ 1728 * (T + 1) * ε ^ 2 := by
    have hT2 : (T + 1 : ℝ) ^ 2 ≤ 2 * T * (T + 1) := by nlinarith
    have hTpos : (0 : ℝ) < T := by linarith
    have : T * (ℓ * ν ^ 2 * δ ^ 2 * (T * η)) ≤ T * (1728 * (T + 1) * ε ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hT2 (by positivity : (0 : ℝ) ≤ 864 * ε ^ 2)]
    exact le_of_mul_le_mul_left this hTpos
  have h8 : (D - w) * ℓ * ν ^ 2 * δ ^ 2 ≤ 1728 * c * (T + 1) * ε ^ 2 := by
    have h9 := mul_le_mul_of_nonneg_left htravel (by positivity : 0 ≤ ℓ * ν ^ 2 * δ ^ 2)
    have h10 := mul_le_mul_of_nonneg_left h7 hc.le
    calc (D - w) * ℓ * ν ^ 2 * δ ^ 2 = ℓ * ν ^ 2 * δ ^ 2 * (D - w) := by ring
      _ ≤ ℓ * ν ^ 2 * δ ^ 2 * (c * (T * η)) := h9
      _ = c * (ℓ * ν ^ 2 * δ ^ 2 * (T * η)) := by ring
      _ ≤ c * (1728 * (T + 1) * ε ^ 2) := h10
      _ = 1728 * c * (T + 1) * ε ^ 2 := by ring
  have hd32 : δ ^ 3 ≤ δ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hδ1 (sq_nonneg δ)
    calc δ ^ 3 = δ ^ 2 * δ := by ring
      _ ≤ δ ^ 2 * 1 := this
      _ = δ ^ 2 := by ring
  have hδ3 : (D - w) * ℓ * δ ^ 3 * ν ^ 2 ≤ (D - w) * ℓ * ν ^ 2 * δ ^ 2 := by
    have h0 : 0 ≤ (D - w) * ℓ * ν ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hd32 h0
    calc (D - w) * ℓ * δ ^ 3 * ν ^ 2 = (D - w) * ℓ * ν ^ 2 * δ ^ 3 := by ring
      _ ≤ (D - w) * ℓ * ν ^ 2 * δ ^ 2 := this
  have hfin : 0 ≤ c * (T + 1) * ε ^ 2 := by positivity
  linarith

lemma sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have hm := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = _ := Real.sqrt_sq (by positivity)

set_option maxHeartbeats 2000000 in
theorem core_nsgd {β ℓ c w D ν η ε : ℝ} {r T : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hw : 0 < w) (hε : 0 < ε) (hν : 0 < ν) (hη : 0 < η)
    (hrc : ((r - 1 : ℕ) : ℝ) * c = 8 * ε) (hr1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ))
    (hDw : 0 ≤ D - w) (hDl : 2 * c ≤ 3 * ℓ * (D - w)) {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i)
    (hnorm : ∀ t < T, α t * Real.sqrt (ν ^ 2 * ∑ u ∈ Finset.range T,
      ((impulse β ℓ α u (t + 1)).2) ^ 2 + ((r - 1 : ℕ) : ℝ) * ((flat β c w D α (t + 1)).2) ^ 2) = η)
    (hstiff : ∑ t ∈ Finset.range (T + 1), ℓ * (ν * Real.sqrt (∑ u ∈ Finset.range T,
      ((impulse β ℓ α u t).1) ^ 2)) ≤ 3 * (T + 1) * ε)
    (hflat : ∑ t ∈ Finset.range (T + 1),
      ((r - 1 : ℕ) : ℝ) * c * |valleySlope w D (flat β c w D α t).1| ≤ 3 * (T + 1) * ε) :
    (D - w) * ℓ * (1 - β) ^ 3 * ν ^ 2 ≤ 6912 * c * ε ^ 2 * (T + 1) := by
  obtain ⟨hT1, htravel⟩ := flat_travel hβ0 hβ1.le hc.le hw hDw hrc hε hα T hflat
  have hkick := kick_bound hβ1.le hℓ.le hν.le hα T hstiff
  set Λ := ∑ t ∈ Finset.range T, α t with hΛdef
  set δ := 1 - β with hδdef
  have hδ : 0 < δ := by linarith
  have hδ1 : δ ≤ 1 := by linarith
  set sd := Real.sqrt δ with hsd
  have hsd0 : 0 < sd := Real.sqrt_pos.mpr hδ
  have hsd2 : sd ^ 2 = δ := Real.sq_sqrt hδ.le
  have hsd1 : sd ≤ 1 := by nlinarith
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hTp : (0 : ℝ) < T + 1 := by positivity
  have hd32 : δ ^ 3 ≤ δ ^ 2 * sd := by
    rw [← hsd2]
    calc (sd ^ 2) ^ 3 = sd ^ 6 := by ring
      _ ≤ sd ^ 5 := pow_le_pow_of_le_one hsd0.le hsd1 (by norm_num)
      _ = (sd ^ 2) ^ 2 * sd := by ring
  by_cases hreg : ν * sd ^ 3 < 128 * ε
  · have h1 : (D - w) * ℓ * ν * δ ≤ 3 * c * ε * (T + 1) := by
      have h9 := mul_le_mul_of_nonneg_left htravel (by positivity : 0 ≤ ℓ * ν * δ)
      have h10 := mul_le_mul_of_nonneg_left hkick hc.le
      calc (D - w) * ℓ * ν * δ = ℓ * ν * δ * (D - w) := by ring
        _ ≤ ℓ * ν * δ * (c * Λ) := h9
        _ = c * (ℓ * ν * (1 - β) * Λ) := by rw [hδdef]; ring
        _ ≤ c * (3 * (T + 1) * ε) := h10
        _ = 3 * c * ε * (T + 1) := by ring
    have h2 : ν * δ ^ 2 ≤ 128 * ε := by
      have h' : δ ^ 2 ≤ sd ^ 3 := by
        rw [← hsd2]
        calc (sd ^ 2) ^ 2 = sd ^ 4 := by ring
          _ ≤ sd ^ 3 := pow_le_pow_of_le_one hsd0.le hsd1 (by norm_num)
      have := mul_le_mul_of_nonneg_left h' hν.le
      linarith
    calc (D - w) * ℓ * δ ^ 3 * ν ^ 2 = ((D - w) * ℓ * ν * δ) * (ν * δ ^ 2) := by ring
      _ ≤ (3 * c * ε * (T + 1)) * (128 * ε) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 384 * (c * ε ^ 2 * (T + 1)) := by ring
      _ ≤ 6912 * c * ε ^ 2 * (T + 1) := by
          have : 0 ≤ c * ε ^ 2 * (T + 1) := by positivity
          linarith
  push Not at hreg
  have hνsd : 128 * ε ≤ ν * sd := by
    have : sd ^ 3 ≤ sd := by nlinarith [pow_le_one₀ hsd0.le hsd1 (n := 2)]
    nlinarith
  set x := fun τ => ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u τ).1) ^ 2) with hxdef
  have hx0 : ∀ τ, 0 ≤ x τ := fun τ => by positivity
  set Abar := fun t => (1 - β) * ∑ τ ∈ Finset.range (t + 1), β ^ (t - τ) * x τ with hAbar
  have hA0 : ∀ t, 0 ≤ Abar t := fun t => mul_nonneg hδ.le
    (Finset.sum_nonneg fun τ _ => mul_nonneg (pow_nonneg hβ0 _) (hx0 τ))
  set F := fun t => Real.sqrt (ν ^ 2 * ∑ u ∈ Finset.range T,
    ((impulse β ℓ α u (t + 1)).2) ^ 2 + ((r - 1 : ℕ) : ℝ) * ((flat β c w D α (t + 1)).2) ^ 2)
    with hFdef
  have hFge : ∀ t < T, ν * δ ≤ F t := by
    intro t ht
    have hW := momentum_norm_ge (ℓ := ℓ) hβ1.le α ht
    have h1 : ν * δ ≤ ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) :=
      mul_le_mul_of_nonneg_left hW hν.le
    have h2 : ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) =
        Real.sqrt (ν ^ 2 * ∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg ν), Real.sqrt_sq hν.le]
    have h3 : Real.sqrt (ν ^ 2 * ∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) ≤ F t :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _)))
    linarith
  have hFle : ∀ t < T, F t ≤ ν * sd + ℓ * Abar t + 8 * ε := by
    intro t _
    have hm := momentum_norm_le hβ0 hβ1 hℓ.le hν.le α T t
    have hn1 : 0 ≤ ν ^ 2 * ∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2 := by
      positivity
    have hn2 : 0 ≤ ((r - 1 : ℕ) : ℝ) * ((flat β c w D α (t + 1)).2) ^ 2 := by positivity
    have hsplit := sqrt_add_le_add_sqrt hn1 hn2
    have h2 : Real.sqrt (ν ^ 2 * ∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) =
        ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg ν), Real.sqrt_sq hν.le]
    have hmb := flat_momentum_bound hβ0 hβ1.le hc.le w D α (t + 1)
    have h3 : Real.sqrt (((r - 1 : ℕ) : ℝ) * ((flat β c w D α (t + 1)).2) ^ 2) ≤ 8 * ε := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
      have hsr : Real.sqrt ((r - 1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      calc Real.sqrt ((r - 1 : ℕ) : ℝ) * |(flat β c w D α (t + 1)).2| ≤
            ((r - 1 : ℕ) : ℝ) * c :=
            mul_le_mul hsr hmb (abs_nonneg _) (by linarith)
        _ = 8 * ε := hrc
    change Real.sqrt _ ≤ _
    rw [h2] at hsplit
    have hm' : ν * Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u (t + 1)).2) ^ 2) ≤
        ν * sd + ℓ * Abar t := hm
    linarith
  have hαF : ∀ t < T, α t = η / F t := by
    intro t ht
    have hpos : 0 < F t := lt_of_lt_of_le (by positivity) (hFge t ht)
    rw [eq_div_iff hpos.ne']
    exact hnorm t ht
  set αmax := η / (ν * δ) with hαmaxdef
  have hαmax : 0 < αmax := by positivity
  have hαle : ∀ t < T, α t ≤ αmax := by
    intro t ht
    rw [hαF t ht]
    exact div_le_div_of_nonneg_left hη.le (by positivity) (hFge t ht)
  set good := (Finset.range T).filter (fun t => ℓ * Abar t ≤ ν * sd / 2) with hgood
  set bad := (Finset.range T).filter (fun t => ¬ ℓ * Abar t ≤ ν * sd / 2) with hbad
  have hcard : (good.card : ℝ) + bad.card = T := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range T)
      (fun t => ℓ * Abar t ≤ ν * sd / 2)
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hbadsum : (bad.card : ℝ) * (ν * sd / 2) ≤ 3 * (T + 1) * ε := by
    have h1 : (bad.card : ℝ) * (ν * sd / 2) ≤ ∑ t ∈ bad, ℓ * Abar t := by
      have h := Finset.card_nsmul_le_sum bad (fun t => ℓ * Abar t) (ν * sd / 2)
        (fun t ht => le_of_lt (not_le.mp (Finset.mem_filter.mp ht).2))
      rwa [nsmul_eq_mul] at h
    have h2 : ∑ t ∈ bad, ℓ * Abar t ≤ ∑ t ∈ Finset.range T, ℓ * Abar t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => mul_nonneg hℓ.le (hA0 t))
    have h3 : ∑ t ∈ Finset.range T, ℓ * Abar t ≤ ∑ t ∈ Finset.range T, ℓ * x t := by
      have hE : ∑ t ∈ Finset.range T, Abar t ≤ ∑ t ∈ Finset.range T, x t :=
        ema_sum_le hβ0 hβ1 hx0 T
      calc ∑ t ∈ Finset.range T, ℓ * Abar t = ℓ * ∑ t ∈ Finset.range T, Abar t := by
            rw [Finset.mul_sum]
        _ ≤ ℓ * ∑ t ∈ Finset.range T, x t := mul_le_mul_of_nonneg_left hE hℓ.le
        _ = ∑ t ∈ Finset.range T, ℓ * x t := by rw [Finset.mul_sum]
    have h4 : ∑ t ∈ Finset.range T, ℓ * x t ≤ ∑ t ∈ Finset.range (T + 1), ℓ * x t := by
      rw [Finset.sum_range_succ]
      linarith [mul_nonneg hℓ.le (hx0 T)]
    linarith
  have hgoodcard : (T : ℝ) / 2 ≤ good.card := by
    have hb : (bad.card : ℝ) * (64 * ε) ≤ 3 * (T + 1) * ε := by
      have : (bad.card : ℝ) * (64 * ε) ≤ (bad.card : ℝ) * (ν * sd / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      linarith
    have hb' : (bad.card : ℝ) * 64 ≤ 3 * (T + 1) := by
      have h := hb
      rw [show (bad.card : ℝ) * (64 * ε) = ((bad.card : ℝ) * 64) * ε by ring] at h
      exact le_of_mul_le_mul_right h hε
    linarith
  have hgoodα : ∀ t ∈ good, η / (2 * ν * sd) ≤ α t := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    have htT := Finset.mem_range.mp ht'.1
    rw [hαF t htT]
    apply div_le_div_of_nonneg_left hη.le (lt_of_lt_of_le (by positivity) (hFge t htT))
    have := hFle t htT
    linarith
  have hΛgood : (T : ℝ) * αmax * sd / 4 ≤ Λ := by
    have h1 : ∑ t ∈ good, α t ≤ Λ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t _ _ => hα t)
    have h2 : (good.card : ℝ) * (η / (2 * ν * sd)) ≤ ∑ t ∈ good, α t := by
      have h := Finset.card_nsmul_le_sum good α (η / (2 * ν * sd)) hgoodα
      rwa [nsmul_eq_mul] at h
    have h3 : (T : ℝ) / 2 * (η / (2 * ν * sd)) ≤ (good.card : ℝ) * (η / (2 * ν * sd)) :=
      mul_le_mul_of_nonneg_right hgoodcard (by positivity)
    have h4 : (T : ℝ) * αmax * sd / 4 = (T : ℝ) / 2 * (η / (2 * ν * sd)) := by
      rw [hαmaxdef, ← hsd2]
      field_simp
      norm_num
    linarith
  by_cases hbig : 1 / 3 ≤ ℓ * αmax
  · exfalso
    have hterm : ∀ t ∈ good, 21 * ε ≤ ℓ * x (t + 1) := by
      intro t ht
      have htT := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      have hf := fresh_injection (ℓ := ℓ) α hα hβ1.le htT
      have hga := hgoodα t ht
      have h1 : ℓ * ν * (α t * δ) ≤ ℓ * x (t + 1) := by
        have := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ) ≤ ℓ * ν)
        simp only [hxdef]
        linarith [show ℓ * ν * (α t * (1 - β)) = ℓ * ν * (α t * δ) by rw [hδdef]]
      have h2 : ℓ * ν * (η / (2 * ν * sd) * δ) ≤ ℓ * ν * (α t * δ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hga hδ.le
      have h3 : ℓ * ν * (η / (2 * ν * sd) * δ) = ℓ * (αmax * ν * δ) * sd / 2 := by
        rw [hαmaxdef, ← hsd2]
        field_simp
      have h4 : ν * δ / 3 ≤ ℓ * (αmax * ν * δ) := by
        have := mul_le_mul_of_nonneg_left hbig (by positivity : (0 : ℝ) ≤ ν * δ)
        nlinarith
      have h5 : ν * δ / 3 * sd / 2 ≤ ℓ * (αmax * ν * δ) * sd / 2 := by
        have := mul_le_mul_of_nonneg_right h4 hsd0.le
        linarith
      have h6 : ν * δ / 3 * sd / 2 = ν * sd ^ 3 / 6 := by rw [← hsd2]; ring
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hsub : ∑ t ∈ good, ℓ * x (t + 1) ≤ ∑ t ∈ Finset.range T, ℓ * x (t + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun t _ _ => mul_nonneg hℓ.le (hx0 _))
    have hsh := shift_sum_le (F := fun t => ℓ * x t) (fun t => mul_nonneg hℓ.le (hx0 t)) T
    have hst : ∑ t ∈ Finset.range (T + 1), ℓ * x t ≤ 3 * (T + 1) * ε := hstiff
    have hlow : (T : ℝ) / 2 * (21 * ε) ≤ (good.card : ℝ) * (21 * ε) :=
      mul_le_mul_of_nonneg_right hgoodcard (by positivity)
    nlinarith
  push Not at hbig
  obtain ⟨L, hL1, hLwin, hL6⟩ := window_length hℓ hαmax hbig
  have hfloor := floor_bound hβ0 hβ1.le hℓ.le hα hαmax.le T L hL1 hαle hLwin
  have hΛ2 : 2 / (3 * ℓ) ≤ Λ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left htravel (by positivity : (0 : ℝ) ≤ 3 * ℓ)
    have h2 : c * 2 ≤ c * (Λ * (3 * ℓ)) := by
      have : 3 * ℓ * (c * Λ) = c * (Λ * (3 * ℓ)) := by ring
      linarith
    exact le_of_mul_le_mul_left h2 hc
  have hLα : (L : ℝ) * αmax ≤ 1 / (3 * ℓ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [show (L : ℝ) * αmax * (3 * ℓ) = 3 * (ℓ * (L * αmax)) by ring]
  have hhalf : Λ / 2 ≤ Λ - L * αmax := by
    have : 1 / (3 * ℓ) = (2 / (3 * ℓ)) / 2 := by ring
    linarith
  have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by exact_mod_cast hL1)
  have hfl2 : δ / 2 * Real.sqrt L * (Λ / 2) ≤ ∑ t ∈ Finset.range (T + 1), x t / ν := by
    have hx : ∀ t ∈ Finset.range (T + 1), x t / ν =
        Real.sqrt (∑ u ∈ Finset.range T, ((impulse β ℓ α u t).1) ^ 2) := by
      intro t _
      simp only [hxdef]
      field_simp
    rw [Finset.sum_congr rfl hx]
    exact le_trans (mul_le_mul_of_nonneg_left hhalf (by positivity)) hfloor
  have hst : ℓ * ν * ∑ t ∈ Finset.range (T + 1), x t / ν ≤ 3 * (T + 1) * ε := by
    rw [Finset.mul_sum]
    calc _ = ∑ t ∈ Finset.range (T + 1), ℓ * x t := by
          apply Finset.sum_congr rfl; intro t _; field_simp
      _ ≤ _ := hstiff
  have hkey : ℓ * ν * (δ / 4 * Real.sqrt L * Λ) ≤ 3 * (T + 1) * ε := by
    have := mul_le_mul_of_nonneg_left hfl2 (by positivity : 0 ≤ ℓ * ν)
    nlinarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity) hΛ2
  have hsqL2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by positivity)
  have hsquare : (ℓ * ν * (δ / 4 * Real.sqrt L * Λ)) ^ 2 ≤ (3 * (T + 1) * ε) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkey 2
  have hexp : (ℓ * ν * (δ / 4 * Real.sqrt L * Λ)) ^ 2 =
      ℓ ^ 2 * ν ^ 2 * δ ^ 2 * L * Λ ^ 2 / 16 := by
    rw [show (ℓ * ν * (δ / 4 * Real.sqrt L * Λ)) ^ 2 =
      ℓ ^ 2 * ν ^ 2 * δ ^ 2 * Real.sqrt L ^ 2 * Λ ^ 2 / 16 by ring, hsqL2]
  rw [hexp] at hsquare
  have h6 : ℓ * ν ^ 2 * δ ^ 2 * Λ ^ 2 ≤ 864 * αmax * (T + 1) ^ 2 * ε ^ 2 := by
    have hA : 0 ≤ ℓ * ν ^ 2 * δ ^ 2 * Λ ^ 2 / 16 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hL6 hA
    have h2 : ℓ ^ 2 * ν ^ 2 * δ ^ 2 * L * Λ ^ 2 / 16 * (6 * αmax) ≤
        (3 * (T + 1) * ε) ^ 2 * (6 * αmax) := mul_le_mul_of_nonneg_right hsquare (by positivity)
    have heq1 : ℓ * ν ^ 2 * δ ^ 2 * Λ ^ 2 / 16 * (6 * ℓ * αmax * L) =
        ℓ ^ 2 * ν ^ 2 * δ ^ 2 * L * Λ ^ 2 / 16 * (6 * αmax) := by ring
    have heq2 : ℓ * ν ^ 2 * δ ^ 2 * Λ ^ 2 / 16 * 1 = ℓ * ν ^ 2 * δ ^ 2 * Λ ^ 2 / 16 := by ring
    have heq3 : (3 * (T + 1) * ε) ^ 2 * (6 * αmax) = 54 * αmax * (T + 1) ^ 2 * ε ^ 2 := by ring
    linarith
  have h7 : ℓ * ν ^ 2 * δ ^ 2 * sd * Λ ≤ 6912 * (T + 1) * ε ^ 2 := by
    have hTpos : (0 : ℝ) < T := by linarith
    have h1 : (T : ℝ) * αmax * sd ≤ 4 * Λ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ T * sd)
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 864 * (T + 1) ^ 2 * ε ^ 2)
    have heqa : T * sd * (ℓ * ν ^ 2 * δ ^ 2 * Λ ^ 2) = ((T : ℝ) * (ℓ * ν ^ 2 * δ ^ 2 * sd * Λ)) * Λ := by
      ring
    have heqb : T * sd * (864 * αmax * (T + 1) ^ 2 * ε ^ 2) =
        864 * (T + 1) ^ 2 * ε ^ 2 * ((T : ℝ) * αmax * sd) := by ring
    have heqc : 864 * (T + 1) ^ 2 * ε ^ 2 * (4 * Λ) = (3456 * (T + 1) ^ 2 * ε ^ 2) * Λ := by ring
    have h4 : ((T : ℝ) * (ℓ * ν ^ 2 * δ ^ 2 * sd * Λ)) * Λ ≤ (3456 * (T + 1) ^ 2 * ε ^ 2) * Λ := by
      linarith
    have h5 : (T : ℝ) * (ℓ * ν ^ 2 * δ ^ 2 * sd * Λ) ≤ 3456 * (T + 1) ^ 2 * ε ^ 2 :=
      le_of_mul_le_mul_right h4 hΛpos
    have hT2 : (T + 1 : ℝ) ^ 2 ≤ 2 * T * (T + 1) := by nlinarith
    have h6' := mul_le_mul_of_nonneg_left hT2 (by positivity : (0 : ℝ) ≤ 3456 * ε ^ 2)
    have h7' : (T : ℝ) * (ℓ * ν ^ 2 * δ ^ 2 * sd * Λ) ≤ T * (6912 * (T + 1) * ε ^ 2) := by
      have : 3456 * ε ^ 2 * (2 * T * (T + 1)) = T * (6912 * (T + 1) * ε ^ 2) := by ring
      have : 3456 * (T + 1) ^ 2 * ε ^ 2 = 3456 * ε ^ 2 * (T + 1) ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_left h7' hTpos
  have h8 : (D - w) * ℓ * ν ^ 2 * δ ^ 2 * sd ≤ 6912 * c * (T + 1) * ε ^ 2 := by
    have h9 := mul_le_mul_of_nonneg_left htravel (by positivity : 0 ≤ ℓ * ν ^ 2 * δ ^ 2 * sd)
    have h10 := mul_le_mul_of_nonneg_left h7 hc.le
    calc (D - w) * ℓ * ν ^ 2 * δ ^ 2 * sd = ℓ * ν ^ 2 * δ ^ 2 * sd * (D - w) := by ring
      _ ≤ ℓ * ν ^ 2 * δ ^ 2 * sd * (c * Λ) := h9
      _ = c * (ℓ * ν ^ 2 * δ ^ 2 * sd * Λ) := by ring
      _ ≤ c * (6912 * (T + 1) * ε ^ 2) := h10
      _ = 6912 * c * (T + 1) * ε ^ 2 := by ring
  have hδ3 : (D - w) * ℓ * δ ^ 3 * ν ^ 2 ≤ (D - w) * ℓ * ν ^ 2 * δ ^ 2 * sd := by
    have h0 : 0 ≤ (D - w) * ℓ * ν ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hd32 h0
    calc (D - w) * ℓ * δ ^ 3 * ν ^ 2 = (D - w) * ℓ * ν ^ 2 * δ ^ 3 := by ring
      _ ≤ (D - w) * ℓ * ν ^ 2 * (δ ^ 2 * sd) := this
      _ = (D - w) * ℓ * ν ^ 2 * δ ^ 2 * sd := by ring
  have hfin : 0 ≤ c * (T + 1) * ε ^ 2 := by positivity
  linarith

end LongTails.Proofs.MomentumSeparationCore
