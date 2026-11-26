import LongTails.Proofs.EscapeChainPast

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainAverage

open scoped RealInnerProductSpace BigOperators
open EscapeChainFunction EscapeChainOracle EscapeChainSimulator EscapeChainFamily EscapeChainSmooth
open EscapeChainCounting EscapeChainRun EscapeChainInvariance EscapeChainPast EscapeChainReveal
open EscapeChainCoordinates EscapeChainCertificate

variable {d : ℕ} (c : Ctx d) (alg : Algorithm (Sp d) (Sp d) (Sp d))

noncomputable def winInd (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) : ℝ :=
  open Classical in if Win c alg θ j z t then 1 else 0

lemma winInd_nonneg (θ : Hid c.n c.b) (j : ℕ) (z) (t : ℕ) : 0 ≤ winInd c alg θ j z t := by
  unfold winInd; split_ifs <;> norm_num

lemma V_eq (θ : Hid c.n c.b) {j : ℕ} (hj : 2 * j + 1 < c.n) :
    V c θ j = dirOf c.hnb θ ⟨2 * j + 1, hj⟩ := by
  simp [V, vOf, hj]

theorem reveal_average {j : ℕ} (hj : j < c.K) (z : alg.Seed × (ℕ → ℝ)) (t : ℕ) :
    ∑ θ : Hid c.n c.b, winInd c alg θ j z t * prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t) ≤
      2 ^ 30 / (c.A * c.b * (c.n - (2 * c.K + 1))) * ∑ θ : Hid c.n c.b, winInd c alg θ j z t := by
  classical
  have hA0 : 0 < c.A := lt_of_lt_of_le (by norm_num) c.hA
  have hjn : 2 * j + 1 < c.n := by have := c.hK; omega
  set i : Fin c.n := ⟨2 * j + 1, hjn⟩
  let X : Hid c.n c.b → Sp d := fun θ =>
    if resid (U c θ) (V c θ) j (yq c alg θ j z t) ≤ 16 then
      projL (U c θ) (V c θ) j (yq c alg θ j z t) else 0
  let w : Hid c.n c.b → ℝ := fun θ => winInd c alg θ j z t
  have hX : ∀ θ, ‖X θ‖ ^ 2 ≤ 16 := by
    intro θ
    simp only [X]
    split_ifs with h
    · rw [projL_norm (frameθ c θ) hj.le]; exact h
    · simp
  have hpointwise : ∀ θ, w θ * prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t) ≤
      2 ^ 26 / c.A * (⟪dirOf c.hnb θ i, X θ⟫ ^ 2 * w θ) := by
    intro θ
    have hp := prob_amplitude (frameθ c θ) hA0 hj (yq c alg θ j z t)
    have hw := winInd_nonneg c alg θ j z t
    have hXe : (if resid (U c θ) (V c θ) j (yq c alg θ j z t) ≤ 16 then
        ⟪V c θ j, projL (U c θ) (V c θ) j (yq c alg θ j z t)⟫ ^ 2 else 0) =
        ⟪dirOf c.hnb θ i, X θ⟫ ^ 2 := by
      simp only [X]; split_ifs <;> simp [V_eq c θ hjn, i]
    rw [hXe] at hp
    calc w θ * prob c.K c.A (U c θ) (V c θ) j (yq c alg θ j z t)
        ≤ w θ * (2 ^ 26 / c.A * ⟪dirOf c.hnb θ i, X θ⟫ ^ 2) := mul_le_mul_of_nonneg_left hp hw
      _ = _ := by ring
  have hswap : ∀ θ : Hid c.n c.b, ∀ k : Fin c.n, i ≤ k →
      X (θ.1 * Equiv.swap i k, θ.2) = X θ ∧ w (θ.1 * Equiv.swap i k, θ.2) = w θ := by
    intro θ k hk
    have hag := agree_swap c θ hk (show 2 * j ≤ (i : ℕ) by simp [i])
    simp only [X, w, winInd, yq_agree c alg hag, resid_agree c hag, projL_agree c hag,
      win_agree c alg hag, and_self]
  have hsign : ∀ θ : Hid c.n c.b, ∀ k : Fin c.n, i ≤ k → ∀ σs,
      X (θ.1, Function.update θ.2 (θ.1 k) σs) = X θ ∧
        w (θ.1, Function.update θ.2 (θ.1 k) σs) = w θ := by
    intro θ k hk σs
    have hag := agree_sign c θ (show 2 * j ≤ (k : ℕ) by
      have : (i : ℕ) ≤ k := hk; simp [i] at this; omega) σs
    simp only [X, w, winInd, yq_agree c alg hag, resid_agree c hag, projL_agree c hag,
      win_agree c alg hag, and_self]
  have hsm := second_moment c.hnb c.hb i X w (fun θ => winInd_nonneg c alg θ j z t) hswap hsign
  have hgap : (0 : ℝ) < c.n - (2 * c.K + 1) := by
    have := c.hK
    have : ((2 * c.K + 2 : ℕ) : ℝ) ≤ c.n := by exact_mod_cast this
    push_cast at this; linarith
  have hni : (c.n : ℝ) - (2 * c.K + 1) ≤ c.n - i := by
    simp only [i]; push_cast
    have : ((j : ℝ)) + 1 ≤ c.K := by exact_mod_cast hj
    linarith
  have hb0 : (0 : ℝ) < c.b := by exact_mod_cast c.hb
  have hS := Finset.sum_le_sum fun θ (_ : θ ∈ (Finset.univ : Finset (Hid c.n c.b))) => hpointwise θ
  rw [← Finset.mul_sum] at hS
  have hsum16 : ∑ θ : Hid c.n c.b, ‖X θ‖ ^ 2 * w θ ≤ 16 * ∑ θ : Hid c.n c.b, w θ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun θ _ => by
      have := winInd_nonneg c alg θ j z t; nlinarith [hX θ]
  have hdir0 : 0 ≤ ∑ θ : Hid c.n c.b, ⟪dirOf c.hnb θ i, X θ⟫ ^ 2 * w θ :=
    Finset.sum_nonneg fun θ _ => by have := winInd_nonneg c alg θ j z t; positivity
  have hmain : ∑ θ : Hid c.n c.b, ⟪dirOf c.hnb θ i, X θ⟫ ^ 2 * w θ ≤
      16 / (c.b * (c.n - (2 * c.K + 1))) * ∑ θ : Hid c.n c.b, w θ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h1 : ((c.n : ℝ) - (2 * c.K + 1)) * ∑ θ : Hid c.n c.b, ⟪dirOf c.hnb θ i, X θ⟫ ^ 2 * w θ ≤
        ((c.n : ℝ) - i) * ∑ θ : Hid c.n c.b, ⟪dirOf c.hnb θ i, X θ⟫ ^ 2 * w θ :=
      mul_le_mul_of_nonneg_right hni hdir0
    have h2 := h1.trans hsm
    have h3 : (1 / (c.b : ℝ)) * ∑ θ : Hid c.n c.b, ‖X θ‖ ^ 2 * w θ ≤
        (1 / c.b) * (16 * ∑ θ : Hid c.n c.b, w θ) := by gcongr
    have h4 := h2.trans h3
    have h5 := mul_le_mul_of_nonneg_left h4 hb0.le
    have h6 : (c.b : ℝ) * (1 / c.b * (16 * ∑ θ : Hid c.n c.b, w θ)) = 16 * ∑ θ : Hid c.n c.b, w θ := by
      field_simp
    linarith [h5, h6]
  calc _ ≤ 2 ^ 26 / c.A * ∑ θ : Hid c.n c.b, ⟪dirOf c.hnb θ i, X θ⟫ ^ 2 * w θ := hS
    _ ≤ 2 ^ 26 / c.A * (16 / (c.b * (c.n - (2 * c.K + 1))) * ∑ θ : Hid c.n c.b, w θ) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by
        simp only [w]
        field_simp
        ring

theorem window_count (θ : Hid c.n c.b) (j : ℕ) (z : alg.Seed × (ℕ → ℝ)) :
    ∑ t ∈ Finset.range c.N, winInd c alg θ j z t ≤ c.m + 1 := by
  classical
  unfold winInd
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : ∃ a : ℕ, (Finset.range c.N).filter (fun t => Win c alg θ j z t) ⊆
      Finset.Icc a (a + c.m) := by
    by_cases hj : j = 0
    · refine ⟨0, fun t ht => ?_⟩
      obtain ⟨-, h⟩ := Finset.mem_filter.1 ht
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact Finset.mem_Icc.2 ⟨Nat.zero_le _, by omega⟩
      · exact absurd hj h
    · by_cases hex : ∃ s, rev c alg θ j (j - 1) z s
      · let s0 := Nat.find hex
        refine ⟨s0 + 1, fun t ht => ?_⟩
        obtain ⟨-, h⟩ := Finset.mem_filter.1 ht
        rcases h with ⟨h, -⟩ | ⟨-, s, hs, hst, hr, hmin⟩
        · exact absurd h hj
        · have hs0 : s = s0 := by
            apply le_antisymm
            · by_contra hlt
              push Not at hlt
              exact hmin s0 hlt (Nat.find_spec hex)
            · exact Nat.find_min' hex hr
          subst hs0
          exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
      · refine ⟨0, fun t ht => ?_⟩
        obtain ⟨-, h⟩ := Finset.mem_filter.1 ht
        rcases h with ⟨h, -⟩ | ⟨-, s, -, -, hr, -⟩
        · exact absurd h hj
        · exact absurd ⟨s, hr⟩ hex
  obtain ⟨a, ha⟩ := hsub
  have := Finset.card_le_card ha
  rw [Nat.card_Icc] at this
  have : (((Finset.range c.N).filter (fun t => Win c alg θ j z t)).card : ℝ) ≤ c.m + 1 := by
    exact_mod_cast (by omega : ((Finset.range c.N).filter (fun t => Win c alg θ j z t)).card ≤ c.m + 1)
  exact this

end LongTails.Proofs.EscapeChainAverage
