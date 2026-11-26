import LongTails.Proofs.EscapeChainPast

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainBadCount

open scoped RealInnerProductSpace BigOperators
open EscapeChainFunction EscapeChainOracle EscapeChainSimulator EscapeChainFamily EscapeChainSmooth
open EscapeChainCounting EscapeChainRun EscapeChainInvariance EscapeChainPast EscapeChainCertificate

variable {d : ℕ} (c : Ctx d) (alg : Algorithm (Sp d) (Sp d) (Sp d))

noncomputable def pt (θ : Hid c.n c.b) (j t : ℕ) (z : alg.Seed × (ℕ → ℝ)) : Sp d :=
  if t < c.N then yq c alg θ j z t else yo c alg θ j z

noncomputable def ev (θ : Hid c.n c.b) (j t l s : ℕ) (z : alg.Seed × (ℕ → ℝ)) : ℝ :=
  open Classical in
  if j ≤ l ∧ 2 * l + s < c.n ∧ ‖pt c alg θ j t z‖ ≤ 2 * radius c.K ∧
    (∀ h : 2 * l + s < c.n, 1 / 128 ≤ |⟪dirOf c.hnb θ ⟨2 * l + s, h⟩, pt c alg θ j t z⟫|) then 1 else 0

lemma ev_nonneg (θ : Hid c.n c.b) (j t l s : ℕ) (z) : 0 ≤ ev c alg θ j t l s z := by
  unfold ev; split_ifs <;> norm_num

lemma bad_le (θ : Hid c.n c.b) (z : alg.Seed × (ℕ → ℝ)) (h : Bad c alg θ z) :
    1 ≤ ∑ j ∈ Finset.range (c.K + 1), ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K,
      ∑ s ∈ Finset.range 2, ev c alg θ j t l s z := by
  classical
  obtain ⟨j, hj, hbad⟩ := h
  have key : ∃ t ≤ c.N, ‖pt c alg θ j t z‖ ≤ 2 * radius c.K ∧
      ¬ Clean c.K (U c θ) (V c θ) j (pt c alg θ j t z) := by
    rcases hbad with ⟨t, ht, hn, hc⟩ | ⟨hn, hc⟩
    · refine ⟨t, ht.le, ?_, ?_⟩ <;> simp only [pt, ite_eq_left ht] <;> assumption
    · refine ⟨c.N, le_rfl, ?_, ?_⟩ <;> simp only [pt, lt_irrefl, ite_false]
      · linarith [radius_pos c.K]
      · exact hc
  obtain ⟨t, ht, hn, hc⟩ := key
  unfold Clean at hc
  push Not at hc
  obtain ⟨l, hjl, hlK, hl⟩ := hc
  have hl2 : 2 * l + 1 < c.n := by have := c.hK; omega
  have hterm : ∃ s ∈ Finset.range 2, ev c alg θ j t l s z = 1 := by
    by_cases hu : 1 / 128 < |⟪U c θ l, pt c alg θ j t z⟫|
    · refine ⟨0, by simp, ?_⟩
      unfold ev
      rw [ite_eq_left]
      refine ⟨hjl, by omega, hn, fun h => ?_⟩
      have : U c θ l = dirOf c.hnb θ ⟨2 * l + 0, h⟩ := by simp [U, uOf, show 2 * l < c.n by omega]
      rw [← this]; exact hu.le
    · have hv := hl (le_of_not_gt hu)
      refine ⟨1, by simp, ?_⟩
      unfold ev
      rw [ite_eq_left]
      refine ⟨hjl, hl2, hn, fun h => ?_⟩
      have : V c θ l = dirOf c.hnb θ ⟨2 * l + 1, h⟩ := by simp [V, vOf, hl2]
      rw [← this]; exact hv.le
  obtain ⟨s, hs, hev⟩ := hterm
  have h1 : 1 ≤ ∑ s ∈ Finset.range 2, ev c alg θ j t l s z := by
    rw [← hev]; exact Finset.single_le_sum (fun s _ => ev_nonneg c alg θ j t l s z) hs
  have h2 : ∑ s ∈ Finset.range 2, ev c alg θ j t l s z ≤ ∑ l ∈ Finset.range c.K,
      ∑ s ∈ Finset.range 2, ev c alg θ j t l s z :=
    Finset.single_le_sum (f := fun l => ∑ s ∈ Finset.range 2, ev c alg θ j t l s z)
      (fun l _ => Finset.sum_nonneg fun s _ => ev_nonneg c alg θ j t l s z) (Finset.mem_range.2 hlK)
  have h3 : ∑ l ∈ Finset.range c.K, ∑ s ∈ Finset.range 2, ev c alg θ j t l s z ≤
      ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K, ∑ s ∈ Finset.range 2,
        ev c alg θ j t l s z :=
    Finset.single_le_sum (f := fun t => ∑ l ∈ Finset.range c.K, ∑ s ∈ Finset.range 2,
        ev c alg θ j t l s z)
      (fun t _ => Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun s _ => ev_nonneg c alg θ j t l s z)
      (Finset.mem_range.2 (by omega))
  have h4 : ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K, ∑ s ∈ Finset.range 2,
      ev c alg θ j t l s z ≤ ∑ j ∈ Finset.range (c.K + 1), ∑ t ∈ Finset.range (c.N + 1),
        ∑ l ∈ Finset.range c.K, ∑ s ∈ Finset.range 2, ev c alg θ j t l s z :=
    Finset.single_le_sum (f := fun j => ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K,
        ∑ s ∈ Finset.range 2, ev c alg θ j t l s z)
      (fun j _ => Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun s _ => ev_nonneg c alg θ j t l s z)
      (Finset.mem_range.2 (by omega))
  linarith

lemma pt_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) (t : ℕ) (z) :
    pt c alg θ' j t z = pt c alg θ j t z := by
  unfold pt; rw [yq_agree c alg h, yo_agree c alg h]

theorem ev_sum (j t l s : ℕ) (z : alg.Seed × (ℕ → ℝ)) :
    ∑ θ : Hid c.n c.b, ev c alg θ j t l s z ≤
      Fintype.card (Hid c.n c.b) * (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2)))) := by
  classical
  by_cases hcond : j ≤ l ∧ 2 * l + s < c.n
  · obtain ⟨hjl, hn⟩ := hcond
    set i : Fin c.n := ⟨2 * l + s, hn⟩
    have hR := radius_pos c.K
    have hsign : ∀ θ : Hid c.n c.b, ∀ σs, pt c alg (θ.1, Function.update θ.2 (θ.1 i) σs) j t z =
        pt c alg θ j t z := by
      intro θ σs
      exact pt_agree c alg (agree_sign c θ (show 2 * j ≤ (i : ℕ) by simp [i]; omega) σs) t z
    have h := hoeffding c.hnb c.hb i (fun θ => pt c alg θ j t z) hsign (t := 1 / 128)
      (ρ := 2 * radius c.K) (by norm_num) (by positivity)
    refine le_trans (Finset.sum_le_sum fun θ _ => ?_) (h.trans (le_of_eq ?_))
    · unfold ev
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso; exact h2 ⟨h1.2.2.2 hn, h1.2.2.1⟩
      · exact zero_le_one
      · exact le_rfl
    · congr 3
      field_simp
      ring
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun θ _ => ?_)) (by positivity)
    unfold ev
    rw [ite_eq_right]
    rintro ⟨h1, h2, -, -⟩
    exact hcond ⟨h1, h2⟩

theorem bad_count (z : alg.Seed × (ℕ → ℝ)) :
    ∑ θ : Hid c.n c.b, (open Classical in if Bad c alg θ z then (1 : ℝ) else 0) ≤
      Fintype.card (Hid c.n c.b) * ((c.K + 1) * (c.N + 1) * c.K * 2 *
        (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2))))) := by
  classical
  have hpt : ∀ θ : Hid c.n c.b, (if Bad c alg θ z then (1 : ℝ) else 0) ≤
      ∑ j ∈ Finset.range (c.K + 1), ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K,
        ∑ s ∈ Finset.range 2, ev c alg θ j t l s z := by
    intro θ
    split_ifs with h
    · exact bad_le c alg θ z h
    · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun s _ => ev_nonneg c alg θ j t l s z
  refine (Finset.sum_le_sum fun θ _ => hpt θ).trans ?_
  rw [Finset.sum_comm]
  set B := Fintype.card (Hid c.n c.b) * (2 * Real.exp (-(c.b / (2 ^ 17 * radius c.K ^ 2))))
  calc ∑ j ∈ Finset.range (c.K + 1), ∑ θ : Hid c.n c.b, ∑ t ∈ Finset.range (c.N + 1),
        ∑ l ∈ Finset.range c.K, ∑ s ∈ Finset.range 2, ev c alg θ j t l s z
      = ∑ j ∈ Finset.range (c.K + 1), ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K,
          ∑ s ∈ Finset.range 2, ∑ θ : Hid c.n c.b, ev c alg θ j t l s z := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range (c.K + 1), ∑ t ∈ Finset.range (c.N + 1), ∑ l ∈ Finset.range c.K,
          ∑ s ∈ Finset.range 2, B :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun l _ =>
          Finset.sum_le_sum fun s _ => ev_sum c alg j t l s z
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, B]
        push_cast
        ring

end LongTails.Proofs.EscapeChainBadCount
