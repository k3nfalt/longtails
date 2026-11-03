import LongTails.Proofs.MinimaxLmoExit

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO constantMomentum)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax clip)
open OracleTemplate.NormBallLMO

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)} {R ρ ζ : ℝ}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}
  {lmo : Space d₁ → Space d₁}

omit [MeasurableSpace Ω] in
lemma cpath_move (hlmo : IsBallLMO N ρ lmo) {γ a β c : ℝ} (hγ : 0 ≤ γ) (ξ : ℕ → Ω) (k : ℕ) :
    N ((cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).1 - (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1) ≤ γ * ρ := by
  have h : (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).1 =
      (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 + γ • lmo (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).2.2 := by
    simp only [cpath_succ]
  rw [h, add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hγ]
  exact mul_le_mul_of_nonneg_left (hlmo.feasible _) hγ

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
include H

lemma G_path_le (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hlmo : IsBallLMO N ρ lmo)
    {γ a β c : ℝ} (hγ : 0 ≤ γ) (hρ : 0 < ρ) (hloc : L₁ * ((1 + L₀ / μ) * (γ * ρ)) ≤ 1) (ξ : ℕ → Ω) :
    ∀ k : ℕ, dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1) ≤
      (dualNorm N (gPhi H hμ x₁) + (1 + L₀ / μ) * L₀ * (γ * ρ) * k) *
        (1 + (1 + L₀ / μ) * L₁ * (γ * ρ)) ^ k := by
  have hK : 1 ≤ 1 + L₀ / μ := by have := div_nonneg hL₀ hμ.le; linarith
  have hs : 0 ≤ γ * ρ := mul_nonneg hγ hρ.le
  intro k
  induction k with
  | zero => simp [cpath, gpath]
  | succ k ih =>
      have hm := cpath_move (x₁ := x₁) (y₁ := y₁) (ox := ox) (oy := oy) hlmo (a := a) (β := β) (c := c) hγ ξ k
      set X := (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1
      set X' := (cpath lmo γ a β c x₁ y₁ ox oy ξ (k + 1)).1
      have hN0 := apply_nonneg N (X' - X)
      have hl : L₁ * ((1 + L₀ / μ) * N (X' - X)) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by linarith)) hL₁).trans hloc
      have hg := G_growth H hμ hR hL₀ hL₁ hK X X' hl
      set G := dualNorm N (gPhi H hμ X)
      set G₀ := dualNorm N (gPhi H hμ x₁)
      set K := 1 + L₀ / μ
      set s := γ * ρ
      set E := 1 + K * L₁ * s
      have hG : 0 ≤ G := dualNorm_nonneg hR _
      have hG₀ : 0 ≤ G₀ := dualNorm_nonneg hR _
      have hE : 1 ≤ E := by have : 0 ≤ K * L₁ * s := by positivity
                            linarith
      have hEk : 1 ≤ E ^ k := one_le_pow₀ hE
      have hstep : K * (L₀ + L₁ * G) * N (X' - X) ≤ K * (L₀ + L₁ * G) * s :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      have h1 : dualNorm N (gPhi H hμ X') ≤ E * G + K * L₀ * s := by
        have : K * (L₀ + L₁ * G) * s = K * L₁ * s * G + K * L₀ * s := by ring
        simp only [E]; nlinarith
      have h2 : E * G ≤ E * ((G₀ + K * L₀ * s * k) * E ^ k) := mul_le_mul_of_nonneg_left ih (by linarith)
      have h3 : K * L₀ * s ≤ K * L₀ * s * E ^ (k + 1) := by
        have : 1 ≤ E ^ (k + 1) := one_le_pow₀ hE
        have : 0 ≤ K * L₀ * s := by positivity
        nlinarith
      have e : (G₀ + K * L₀ * s * ((k + 1 : ℕ) : ℝ)) * E ^ (k + 1) =
          E * ((G₀ + K * L₀ * s * k) * E ^ k) + K * L₀ * s * E ^ (k + 1) := by
        push_cast; ring
      rw [e]
      linarith

set_option maxHeartbeats 1000000 in
theorem good_sum (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0) (hL₀ : 0 ≤ L₀)
    (hL₁ : 0 ≤ L₁) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo) (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖)
    {γ a β c r : ℝ} (hγ : 0 < γ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hsa : 16 * (1 + L₀ / μ) * L₁ * (γ * ρ) ≤ a) (hr : 16 * L₁ * r ≤ 1) (ξ : ℕ → Ω) (n : ℕ) (hn : 1 ≤ n)
    (htrk : ∀ j, j ≤ n → trk H hμ lmo γ a β c ξ j ≤ r) :
    ∑ k ∈ Finset.range n, dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1) ≤
      2 * Δ / (γ * ρ) + 4 * (L₀ + L₁ * dualNorm N (gPhi H hμ x₁)) * W / a +
        4 * n * (1 + L₀ / μ) * L₀ * (γ * ρ) / a + (1 + L₀ / μ) * L₀ * (γ * ρ) / 4 +
        n * (1 + L₀ / μ) * L₀ * (γ * ρ) +
        4 * L₀ * ∑ j ∈ Finset.range n, trk H hμ lmo γ a β c ξ (j + 1) +
        4 * ζ * ∑ k ∈ Finset.range n, ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖ := by
  have hK : 1 ≤ 1 + L₀ / μ := by have := div_nonneg hL₀ hμ.le; linarith
  have hs0 : 0 < γ * ρ := mul_pos hγ hρ
  have hKL : (1 + L₀ / μ) * L₁ * (γ * ρ) ≤ 1 / 16 := by linarith
  have hloc : L₁ * ((1 + L₀ / μ) * (γ * ρ)) ≤ 1 := by nlinarith
  have hP := pathwise_sum H hμ hR hdef hL₀ hL₁ hρ hlmo hζ (a := a) (β := β) (c := c) hγ.le ha0 ha1 hloc ξ n
  have hgap := Phi_gap H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ n).1
  have hX0 : (cpath lmo γ a β c x₁ y₁ ox oy ξ 0).1 = x₁ := rfl
  rw [hX0] at hP
  set K := 1 + L₀ / μ with hKdef
  set s := γ * ρ with hsdef
  set X : ℕ → Space d₁ := fun k => (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1 with hXdef
  set G : ℕ → ℝ := fun k => dualNorm N (gPhi H hμ (X k)) with hGdef
  set t : ℕ → ℝ := fun k => trk H hμ lmo γ a β c ξ k with htdef
  set b : ℕ → ℝ := fun k => dualNorm N (xBias lmo γ a β c H hμ ξ k) with hbdef
  set SG := ∑ k ∈ Finset.range n, G k
  set ST := ∑ j ∈ Finset.range n, t (j + 1)
  set SZ := ∑ k ∈ Finset.range n, ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖
  set SGs := ∑ j ∈ Finset.range n, G (j + 1)
  have hGnn : ∀ k, 0 ≤ G k := fun k => dualNorm_nonneg hR _
  have htnn : ∀ k, 0 ≤ t k := fun k => norm_nonneg _
  have hbias : ∀ k, k ≤ n → b k ≤ (L₀ + L₁ * G k) * t k := by
    intro k hk
    have hD : L₁ * t k ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (htrk k hk) hL₁
      linarith
    exact bias_bound H hμ hR (X k) (cpath lmo γ a β c x₁ y₁ ox oy ξ k).2.1 hD
  have hw : t 0 ≤ W := by
    have hw := H.warm_start (ystar H hμ x₁) (ystar_max H hμ x₁)
    simpa [t, trk, cpath, gpath] using hw
  have hb0 : b 0 ≤ (L₀ + L₁ * G 0) * W :=
    (hbias 0 (Nat.zero_le _)).trans (mul_le_mul_of_nonneg_left hw (by have := hGnn 0; positivity))
  have hbj : ∀ j ∈ Finset.range n, K * (L₀ + L₁ * G j) * s + a * b (j + 1) ≤
      K * L₀ * s + K * L₁ * s * G j + a * L₀ * t (j + 1) + a * L₁ * r * G (j + 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 := hbias (j + 1) (by omega)
    have h2 : L₁ * G (j + 1) * t (j + 1) ≤ L₁ * G (j + 1) * r :=
      mul_le_mul_of_nonneg_left (htrk (j + 1) (by omega)) (mul_nonneg hL₁ (hGnn _))
    have h3 : a * b (j + 1) ≤ a * (L₀ * t (j + 1) + L₁ * r * G (j + 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ ha0.le
      nlinarith
    nlinarith
  have hsum1 : ∑ j ∈ Finset.range n, (K * (L₀ + L₁ * G j) * s + a * b (j + 1)) ≤
      n * (K * L₀ * s) + K * L₁ * s * SG + a * L₀ * ST + a * L₁ * r * SGs := by
    refine (Finset.sum_le_sum hbj).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hsum2 : ∑ k ∈ Finset.range n, K * (L₀ + L₁ * G k) / 2 * s ^ 2 =
      n * (K * L₀ * s ^ 2 / 2) + K * L₁ * s ^ 2 / 2 * SG := by
    have e : ∀ k, K * (L₀ + L₁ * G k) / 2 * s ^ 2 = K * L₀ * s ^ 2 / 2 + K * L₁ * s ^ 2 / 2 * G k :=
      fun k => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hGs : SGs + G 0 = SG + G (m + 1) := by
    simp only [SGs, SG]
    rw [← Finset.sum_range_succ' G (m + 1), Finset.sum_range_succ]
  have hGm : G m ≤ SG := Finset.single_le_sum (fun k _ => hGnn k) (Finset.self_mem_range_succ m)
  have hGn : G (m + 1) ≤ (1 + K * L₁ * s) * G m + K * L₀ * s := by
    have hm := cpath_move (x₁ := x₁) (y₁ := y₁) (ox := ox) (oy := oy) hlmo (a := a) (β := β) (c := c) hγ.le ξ m
    have hl : L₁ * (K * N (X (m + 1) - X m)) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by linarith)) hL₁).trans hloc
    have hg := G_growth H hμ hR hL₀ hL₁ hK (X m) (X (m + 1)) hl
    have hstep : K * (L₀ + L₁ * G m) * N (X (m + 1) - X m) ≤ K * (L₀ + L₁ * G m) * s :=
      mul_le_mul_of_nonneg_left hm (by have := hGnn m; positivity)
    have : K * (L₀ + L₁ * G m) * s = K * L₁ * s * G m + K * L₀ * s := by ring
    change G (m + 1) ≤ _
    simp only [G] at hg hstep this ⊢
    nlinarith
  have hSGs : SGs ≤ (33 / 16) * SG + K * L₀ * s := by
    have h0 := hGnn 0
    have : K * L₁ * s * G m ≤ (1 / 16) * SG := by
      have := mul_le_mul hKL hGm (hGnn m) (by norm_num)
      linarith
    nlinarith
  have hSG0 : 0 ≤ SG := Finset.sum_nonneg fun k _ => hGnn k
  have hSGs0 : 0 ≤ SGs := Finset.sum_nonneg fun k _ => hGnn _
  have hST0 : 0 ≤ ST := Finset.sum_nonneg fun k _ => htnn _
  have F1 : 2 * s / a * (K * L₁ * s * SG) ≤ s / 8 * SG := by
    have : 2 * s / a * (K * L₁ * s) ≤ s / 8 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha0]
      nlinarith
    have := mul_le_mul_of_nonneg_right this hSG0
    linarith
  have F2 : 2 * s / a * (a * L₁ * r * SGs) ≤ s / 8 * SGs := by
    have e : 2 * s / a * (a * L₁ * r * SGs) = (2 * L₁ * r) * (s * SGs) := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_right (by linarith : 2 * L₁ * r ≤ 1 / 8) (mul_nonneg hs0.le hSGs0)
    linarith
  have F3 : K * L₁ * s ^ 2 / 2 * SG ≤ s / 32 * SG := by
    have : K * L₁ * s ^ 2 / 2 ≤ s / 32 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hSG0
  have F4 : s / 8 * SGs ≤ s / 8 * ((33 / 16) * SG + K * L₀ * s) :=
    mul_le_mul_of_nonneg_left hSGs (by positivity)
  have e1 : 2 * s / a * (a * L₀ * ST) = 2 * s * L₀ * ST := by field_simp
  have hb0' : 2 * s / a * b 0 ≤ 2 * s / a * ((L₀ + L₁ * G 0) * W) :=
    mul_le_mul_of_nonneg_left hb0 (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hsum1 (by positivity : (0 : ℝ) ≤ 2 * s / a)
  rw [hsum2] at hP
  have hlin : s * SG * (75 / 128) ≤ Δ + 2 * s / a * ((L₀ + L₁ * G 0) * W) + 2 * s / a * (((m + 1 : ℕ) : ℝ) * (K * L₀ * s)) +
      2 * s * L₀ * ST + s / 8 * (K * L₀ * s) + 2 * s * ζ * SZ + ((m + 1 : ℕ) : ℝ) * (K * L₀ * s ^ 2 / 2) := by
    have e2 : 2 * s / a * (((m + 1 : ℕ) : ℝ) * (K * L₀ * s) + K * L₁ * s * SG + a * L₀ * ST + a * L₁ * r * SGs) =
        2 * s / a * (((m + 1 : ℕ) : ℝ) * (K * L₀ * s)) + 2 * s / a * (K * L₁ * s * SG) + 2 * s / a * (a * L₀ * ST) +
          2 * s / a * (a * L₁ * r * SGs) := by ring
    have e3 : 2 * s / a * (b 0 + ∑ j ∈ Finset.range (m + 1), (K * (L₀ + L₁ * G j) * s + a * b (j + 1))) =
        2 * s / a * b 0 + 2 * s / a * ∑ j ∈ Finset.range (m + 1), (K * (L₀ + L₁ * G j) * s + a * b (j + 1)) := by
      ring
    have hP' : s * SG ≤ Phi H hμ x₁ - Phi H hμ (X (m + 1)) +
        2 * s / a * (b 0 + ∑ j ∈ Finset.range (m + 1), (K * (L₀ + L₁ * G j) * s + a * b (j + 1))) +
        2 * s * ζ * SZ + (((m + 1 : ℕ) : ℝ) * (K * L₀ * s ^ 2 / 2) + K * L₁ * s ^ 2 / 2 * SG) := by
      convert hP using 2
    rw [e3] at hP'
    rw [e2, e1] at hmain
    nlinarith
  have hfin : s * SG ≤ s * (2 * Δ / s + 4 * (L₀ + L₁ * G 0) * W / a + 4 * ((m + 1 : ℕ) : ℝ) * K * L₀ * s / a +
      K * L₀ * s / 4 + ((m + 1 : ℕ) : ℝ) * K * L₀ * s + 4 * L₀ * ST + 4 * ζ * SZ) := by
    have e : s * (2 * Δ / s + 4 * (L₀ + L₁ * G 0) * W / a + 4 * ((m + 1 : ℕ) : ℝ) * K * L₀ * s / a +
        K * L₀ * s / 4 + ((m + 1 : ℕ) : ℝ) * K * L₀ * s + 4 * L₀ * ST + 4 * ζ * SZ) =
        2 * (Δ + 2 * s / a * ((L₀ + L₁ * G 0) * W) + 2 * s / a * (((m + 1 : ℕ) : ℝ) * (K * L₀ * s)) +
          2 * s * L₀ * ST + s / 8 * (K * L₀ * s) + 2 * s * ζ * SZ +
          ((m + 1 : ℕ) : ℝ) * (K * L₀ * s ^ 2 / 2)) := by
      field_simp; ring
    rw [e]
    nlinarith
  exact le_of_mul_le_mul_left hfin hs0

omit H in
lemma gp_cases (γ a β c r₀ : ℝ) (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p)
    (ξ : ℕ → Ω) (k : ℕ) :
    gp H hμ lmo γ a β c r₀ ξ k = 0 ∨ gp H hμ lmo γ a β c r₀ ξ k = 1 := by
  unfold gp; split_ifs <;> simp

lemma gp_anti (γ a β c r₀ : ℝ) (ξ : ℕ → Ω) {k m : ℕ} (hkm : k ≤ m) :
    gp H hμ lmo γ a β c r₀ ξ m ≤ gp H hμ lmo γ a β c r₀ ξ k := by
  induction hkm with
  | refl => exact le_rfl
  | step _ ih => exact (gp_succ_le H hμ γ a β c r₀ ξ _).trans ih

lemma gp_one_trk (γ a β c r₀ : ℝ) (ξ : ℕ → Ω) (n : ℕ) (h : gp H hμ lmo γ a β c r₀ ξ (n + 1) = 1) :
    ∀ j, j ≤ n → trk H hμ lmo γ a β c ξ j ≤ r₀ := by
  intro j hj
  unfold gp at h
  split_ifs at h with h1
  · exact h1 j (by omega)
  · norm_num at h

omit H in
lemma sqrt_decay {q V W : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hV : 0 ≤ V) (hW : 0 ≤ W) (k : ℕ) :
    Real.sqrt ((1 - q) ^ k * W ^ 2 + V) ≤ (1 - q / 2) ^ k * W + Real.sqrt V := by
  have h1 : (1 - q) ^ k * W ^ 2 ≤ ((1 - q / 2) ^ k * W) ^ 2 := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) ?_ k) (sq_nonneg W)
    nlinarith
  have h2 : 0 ≤ (1 - q / 2) ^ k * W := mul_nonneg (pow_nonneg (by linarith) k) hW
  calc Real.sqrt ((1 - q) ^ k * W ^ 2 + V) ≤ Real.sqrt (((1 - q / 2) ^ k * W) ^ 2 + V) :=
        Real.sqrt_le_sqrt (by linarith)
    _ ≤ (1 - q / 2) ^ k * W + Real.sqrt V := by
        rw [Real.sqrt_le_left (by positivity)]
        have := Real.sq_sqrt hV
        nlinarith [Real.sqrt_nonneg V]

set_option maxHeartbeats 4000000 in
theorem expected_sum [IsProbabilityMeasure p] (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hdef : ∀ x, N x = 0 → x = 0)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hρ : 0 < ρ) (hlmo : IsBallLMO N ρ lmo) (hlmo_m : Measurable lmo)
    (hζ : ∀ u, dualNorm N u ≤ ζ * ‖u‖) (hζ0 : 0 ≤ ζ) (hσx : 0 ≤ σx) {γ a β c r : ℝ} (hγ : 0 < γ) (ha0 : 0 < a)
    (ha1 : a ≤ 1) (hsa : 16 * (1 + L₀ / μ) * L₁ * (γ * ρ) ≤ a) (hr : 16 * L₁ * r ≤ 1) (hβ : 0 < β)
    (hβ2 : 2 * β * L₀ ^ 2 ≤ μ) (hβμ : β * μ ≤ 1) (hc : 0 < c) (hrc : L₀ * r ≤ c / 2) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ξ => ∑ k ∈ Finset.range n, dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1))
        (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ∑ k ∈ Finset.range n, dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1)
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        2 * Δ / (γ * ρ) + 4 * (L₀ + L₁ * dualNorm N (gPhi H hμ x₁)) * W / a +
          4 * n * (1 + L₀ / μ) * L₀ * (γ * ρ) / a + (1 + L₀ / μ) * L₀ * (γ * ρ) / 4 +
          n * (1 + L₀ / μ) * L₀ * (γ * ρ) +
          4 * L₀ * (8 * W / (β * μ) + n * Real.sqrt (4 / (β * μ) * (2 * (8 * β * σy ^ 4 / (μ * c ^ 2) +
            2 * β ^ 2 * σy ^ 2) + 5 * (L₀ / μ * (γ * ρ)) ^ 2 / (β * μ)))) +
          4 * ζ * (Real.sqrt 2 * σx * (1 / a + n * Real.sqrt a)) +
          n * ((dualNorm N (gPhi H hμ x₁) + (1 + L₀ / μ) * L₀ * (γ * ρ) * n) *
            (1 + (1 + L₀ / μ) * L₁ * (γ * ρ)) ^ n) *
            ∫ ξ, (1 - gp H hμ lmo γ a β c r ξ (n + 1)) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set K := 1 + L₀ / μ
  set s := γ * ρ
  set G₀ := dualNorm N (gPhi H hμ x₁)
  set E := 1 + K * L₁ * s
  set Gm := (G₀ + K * L₀ * s * n) * E ^ n
  set V := 4 / (β * μ) * (2 * (8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2) + 5 * (L₀ / μ * s) ^ 2 / (β * μ))
  set G : (ℕ → Ω) → ℕ → ℝ := fun ξ k => dualNorm N (gPhi H hμ (cpath lmo γ a β c x₁ y₁ ox oy ξ k).1)
  set t : (ℕ → Ω) → ℕ → ℝ := fun ξ k => trk H hμ lmo γ a β c ξ k
  set g : (ℕ → Ω) → ℕ → ℝ := fun ξ k => gp H hμ lmo γ a β c r ξ k
  set Z : (ℕ → Ω) → ℕ → ℝ := fun ξ k => ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖
  have hK : 1 ≤ K := by have := div_nonneg hL₀ hμ.le; simp only [K]; linarith
  have hs0 : 0 < s := mul_pos hγ hρ
  have hKL : K * L₁ * s ≤ 1 / 16 := by linarith
  have hloc : L₁ * (K * s) ≤ 1 := by nlinarith
  have hloc1 : L₁ * s ≤ 1 := by nlinarith
  have hR0 : 0 ≤ R := by have := hR 0 (by simp); simpa using this
  have hΔ : 0 ≤ Δ := by have := Phi_gap H hμ x₁; linarith
  have hG₀ : 0 ≤ G₀ := dualNorm_nonneg hR _
  have hE : 1 ≤ E := by have : 0 ≤ K * L₁ * s := by positivity
                        simp only [E]; linarith
  have hκs : 0 ≤ L₀ / μ * s := by have := div_nonneg hL₀ hμ.le; positivity
  have hpath := measurable_gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy
    hlmo_m H.measurable_x H.measurable_y
  have hgPhi : Continuous fun x => dualNorm N (gPhi H hμ x) :=
    (continuous_dualNorm hR hR0).comp ((gx_continuous H hR hL₀ hL₁).comp
      (continuous_id.prodMk (ystar_continuous H hμ hL₀ hL₁)))
  have hGm : ∀ k, Measurable fun ξ => G ξ k := fun k => hgPhi.measurable.comp (hpath k).fst
  have hGle : ∀ ξ k, k ≤ n → G ξ k ≤ Gm := by
    intro ξ k hk
    have h := G_path_le H hμ hR hL₀ hL₁ hlmo (a := a) (β := β) (c := c) hγ.le hρ hloc ξ k
    refine h.trans ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    have h1 : G₀ + K * L₀ * s * k ≤ G₀ + K * L₀ * s * n := by
      have : 0 ≤ K * L₀ * s := by positivity
      nlinarith
    have h2 : E ^ k ≤ E ^ n := pow_le_pow_right₀ hE hk
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hGnn : ∀ ξ k, 0 ≤ G ξ k := fun ξ k => dualNorm_nonneg hR _
  have hGi : ∀ k, k ≤ n → Integrable (fun ξ => G ξ k) P := fun k hk =>
    Integrable.of_bound (hGm k).aestronglyMeasurable Gm (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (hGnn ξ k)]; exact hGle ξ k hk)
  have hSGi : Integrable (fun ξ => ∑ k ∈ Finset.range n, G ξ k) P :=
    integrable_finsetSum _ fun k hk => hGi k (Finset.mem_range.mp hk).le
  refine ⟨hSGi, ?_⟩
  have hgm : ∀ k, Measurable fun ξ => g ξ k := fun k => gp_measurable H hμ γ a β c hL₀ hL₁ hlmo_m r k
  have htm : ∀ k, Measurable fun ξ => t ξ k := fun k => trk_measurable H hμ γ a β c hL₀ hL₁ hlmo_m k
  have hg01 : ∀ ξ k, 0 ≤ g ξ k ∧ g ξ k ≤ 1 := fun ξ k =>
    ⟨gp_nonneg (lmo := lmo) H hμ γ a β c r ξ k, gp_le_one (lmo := lmo) H hμ γ a β c r ξ k⟩
  have hgti : ∀ j, Integrable (fun ξ => g ξ (j + 1 + 1) * t ξ (j + 1)) P := by
    intro j
    refine Integrable.of_bound ((hgm _).mul (htm _)).aestronglyMeasurable
      (W + (j + 1 : ℕ) * (β * c + L₀ / μ * s)) (Filter.Eventually.of_forall fun ξ => ?_)
    have hb := trk_bound H hμ γ a β c hL₀ hL₁ hlmo hγ.le hloc1 hβ.le hc.le ξ (j + 1)
    have ht0 : 0 ≤ t ξ (j + 1) := norm_nonneg _
    obtain ⟨h0, h1⟩ := hg01 ξ (j + 1 + 1)
    rw [Real.norm_of_nonneg (mul_nonneg h0 ht0)]
    change g ξ (j + 1 + 1) * t ξ (j + 1) ≤ _
    have : t ξ (j + 1) ≤ W + (j + 1 : ℕ) * (β * c + L₀ / μ * s) := hb
    nlinarith
  have hZi : ∀ k, Integrable (fun ξ => Z ξ k) P := fun k =>
    (noise_bound H hR hL₀ hL₁ hlmo_m hσx (γ := γ) (β := β) (c := c) ha0 ha1 k).1
  have hbi : Integrable (fun ξ => 1 - g ξ (n + 1)) P :=
    (integrable_const 1).sub (Integrable.of_bound (hgm _).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (hg01 ξ _).1]; exact (hg01 ξ _).2))
  set C₀ := 2 * Δ / s + 4 * (L₀ + L₁ * G₀) * W / a + 4 * n * K * L₀ * s / a + K * L₀ * s / 4 + n * K * L₀ * s
  have hC₀ : 0 ≤ C₀ := by
    have : 0 ≤ L₀ + L₁ * G₀ := by positivity
    have : 0 ≤ W := by have := H.warm_start (ystar H hμ x₁) (ystar_max H hμ x₁); linarith [norm_nonneg (y₁ - ystar H hμ x₁)]
    positivity
  have hW0 : 0 ≤ W := by
    have := H.warm_start (ystar H hμ x₁) (ystar_max H hμ x₁); linarith [norm_nonneg (y₁ - ystar H hμ x₁)]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hGm0 : 0 ≤ Gm := by positivity
  have hpt : ∀ ξ, ∑ k ∈ Finset.range n, G ξ k ≤ C₀ +
      4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) + 4 * ζ * ∑ k ∈ Finset.range n, Z ξ k +
      n * Gm * (1 - g ξ (n + 1)) := by
    intro ξ
    have hgt0 : 0 ≤ ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hg01 ξ _).1 (norm_nonneg _)
    have hZ0 : 0 ≤ ∑ k ∈ Finset.range n, Z ξ k := Finset.sum_nonneg fun k _ => norm_nonneg _
    rcases gp_cases hμ γ a β c r H ξ (n + 1) (lmo := lmo) with h | h
    · have hs : ∑ k ∈ Finset.range n, G ξ k ≤ ∑ k ∈ Finset.range n, Gm :=
        Finset.sum_le_sum fun k hk => hGle ξ k (Finset.mem_range.mp hk).le
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
      change g ξ (n + 1) = 0 at h
      rw [h]
      have : 0 ≤ 4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) := by positivity
      have : 0 ≤ 4 * ζ * ∑ k ∈ Finset.range n, Z ξ k := by positivity
      nlinarith
    · have htrk := gp_one_trk H hμ γ a β c r ξ n h
      have hgood := good_sum H hμ hR hdef hL₀ hL₁ hρ hlmo hζ (β := β) (c := c) hγ ha0 ha1 hsa hr ξ n hn htrk
      have hsum : ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) =
          ∑ j ∈ Finset.range n, trk H hμ lmo γ a β c ξ (j + 1) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        have h1 := gp_anti H hμ γ a β c r ξ (lmo := lmo) (show j + 1 + 1 ≤ n + 1 by omega)
        have h2 := (hg01 ξ (j + 1 + 1)).2
        change gp H hμ lmo γ a β c r ξ (n + 1) = 1 at h
        have : g ξ (j + 1 + 1) = 1 := by change gp H hμ lmo γ a β c r ξ (j + 1 + 1) = 1; linarith
        rw [this, one_mul]
      change g ξ (n + 1) = 1 at h
      rw [hsum, h]
      simp only [C₀, G, Z]
      linarith
  have hRi : Integrable (fun ξ => C₀ + 4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) +
      4 * ζ * ∑ k ∈ Finset.range n, Z ξ k + n * Gm * (1 - g ξ (n + 1))) P :=
    (((integrable_const C₀).add ((integrable_finsetSum _ fun j _ => hgti j).const_mul _)).add
      ((integrable_finsetSum _ fun k _ => hZi k).const_mul _)).add (hbi.const_mul _)
  have hmono := integral_mono hSGi hRi hpt
  have hcalc : ∫ ξ, (C₀ + 4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) +
      4 * ζ * ∑ k ∈ Finset.range n, Z ξ k + n * Gm * (1 - g ξ (n + 1))) ∂P =
      C₀ + 4 * L₀ * ∑ j ∈ Finset.range n, ∫ ξ, g ξ (j + 1 + 1) * t ξ (j + 1) ∂P +
        4 * ζ * ∑ k ∈ Finset.range n, ∫ ξ, Z ξ k ∂P + n * Gm * ∫ ξ, (1 - g ξ (n + 1)) ∂P := by
    have h1 : Integrable (fun ξ => ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1)) P :=
      integrable_finsetSum _ fun j _ => hgti j
    have h2 : Integrable (fun ξ => ∑ k ∈ Finset.range n, Z ξ k) P := integrable_finsetSum _ fun k _ => hZi k
    have hA : Integrable (fun ξ => C₀ + 4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1)) P :=
      (integrable_const C₀).add (h1.const_mul _)
    have hB : Integrable (fun ξ => C₀ + 4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1) +
        4 * ζ * ∑ k ∈ Finset.range n, Z ξ k) P := hA.add (h2.const_mul _)
    have hC : Integrable (fun ξ => (n : ℝ) * Gm * (1 - g ξ (n + 1))) P := hbi.const_mul _
    have h1' : Integrable (fun ξ => 4 * L₀ * ∑ j ∈ Finset.range n, g ξ (j + 1 + 1) * t ξ (j + 1)) P :=
      h1.const_mul _
    have h2' : Integrable (fun ξ => 4 * ζ * ∑ k ∈ Finset.range n, Z ξ k) P := h2.const_mul _
    rw [integral_add hB hC, integral_add hA h2', integral_add (integrable_const C₀) h1', integral_const_mul,
      integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ => hgti j,
      integral_finsetSum _ fun k _ => hZi k]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hcalc] at hmono
  have hq0 : 0 ≤ β * μ / 4 := by positivity
  have hq1 : β * μ / 4 ≤ 1 := by linarith
  have hV0 : 0 ≤ V := by positivity
  have htrack : ∀ j, ∫ ξ, g ξ (j + 1 + 1) * t ξ (j + 1) ∂P ≤ (1 - β * μ / 4 / 2) ^ (j + 1) * W + Real.sqrt V := by
    intro j
    obtain ⟨hti, htb⟩ := track_total H hμ γ a β c hL₀ hL₁ hlmo_m hρ hlmo hγ.le hloc1 (r₀ := r) hβ hβ2 hβμ hc
      (by linarith) hrc (j + 1)
    have hsq : ∀ ξ, ‖g ξ (j + 1 + 1) * t ξ (j + 1)‖ ^ 2 = g ξ (j + 1 + 1) * t ξ (j + 1) ^ 2 := by
      intro ξ
      rw [Real.norm_eq_abs, sq_abs, mul_pow]
      rcases gp_cases hμ γ a β c r H ξ (j + 1 + 1) (lmo := lmo) with h | h <;>
        · change g ξ (j + 1 + 1) = _ at h; rw [h]; norm_num
    have h2 : Integrable (fun ξ => ‖g ξ (j + 1 + 1) * t ξ (j + 1)‖ ^ 2) P := by
      simp only [hsq]; exact hti
    have hfm : Measurable (fun ξ => g ξ (j + 1 + 1) * t ξ (j + 1)) := (hgm _).mul (htm _)
    have hJ := OracleTemplate.NormalizedStorm.integral_norm_le_sqrt hfm.aestronglyMeasurable h2
    have hn1 : ∫ ξ, ‖g ξ (j + 1 + 1) * t ξ (j + 1)‖ ∂P = ∫ ξ, g ξ (j + 1 + 1) * t ξ (j + 1) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
        Real.norm_of_nonneg (mul_nonneg (hg01 ξ _).1 (norm_nonneg _)))
    have hn2 : ∫ ξ, ‖g ξ (j + 1 + 1) * t ξ (j + 1)‖ ^ 2 ∂P = ∫ ξ, g ξ (j + 1 + 1) * t ξ (j + 1) ^ 2 ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hsq)
    rw [hn1, hn2] at hJ
    refine hJ.trans ((Real.sqrt_le_sqrt htb).trans ?_)
    exact sqrt_decay hq0 hq1 hV0 hW0 (j + 1)
  have hx0 : 0 ≤ 1 - β * μ / 4 / 2 := by linarith
  have hx1 : 1 - β * μ / 4 / 2 < 1 := by have : 0 < β * μ := mul_pos hβ hμ; linarith
  have htsum : ∑ j ∈ Finset.range n, ∫ ξ, g ξ (j + 1 + 1) * t ξ (j + 1) ∂P ≤ 8 * W / (β * μ) + n * Real.sqrt V := by
    refine (Finset.sum_le_sum fun j _ => htrack j).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul]
    have hg : ∑ j ∈ Finset.range n, (1 - β * μ / 4 / 2) ^ (j + 1) ≤ 8 / (β * μ) := by
      calc ∑ j ∈ Finset.range n, (1 - β * μ / 4 / 2) ^ (j + 1) ≤ ∑ j ∈ Finset.range n, (1 - β * μ / 4 / 2) ^ j :=
            Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one hx0 hx1.le (Nat.le_succ j)
        _ ≤ 1 / (1 - (1 - β * μ / 4 / 2)) := geom_sum_le hx0 hx1 n
        _ = 8 / (β * μ) := by field_simp; ring
    have := mul_le_mul_of_nonneg_right hg hW0
    have e : 8 / (β * μ) * W = 8 * W / (β * μ) := by ring
    linarith
  have hzsum : ∑ k ∈ Finset.range n, ∫ ξ, Z ξ k ∂P ≤ Real.sqrt 2 * σx * (1 / a + n * Real.sqrt a) := by
    refine (Finset.sum_le_sum fun k _ =>
      (noise_bound H hR hL₀ hL₁ hlmo_m hσx (γ := γ) (β := β) (c := c) ha0 ha1 k).2).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hy0 : 0 ≤ 1 - a := by linarith
    have hy1 : 1 - a < 1 := by linarith
    have hg := geom_sum_le hy0 hy1 n
    rw [sub_sub_cancel] at hg
    have : 0 ≤ Real.sqrt 2 * σx := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have hb0 : 0 ≤ ∫ ξ, (1 - g ξ (n + 1)) ∂P := integral_nonneg fun ξ => by
    show (0 : ℝ) ≤ 1 - g ξ (n + 1); linarith [(hg01 ξ (n + 1)).2]
  have h1 := mul_le_mul_of_nonneg_left htsum (by positivity : (0 : ℝ) ≤ 4 * L₀)
  have h2 := mul_le_mul_of_nonneg_left hzsum (by positivity : (0 : ℝ) ≤ 4 * ζ)
  change _ ≤ _ + 4 * L₀ * (8 * W / (β * μ) + n * Real.sqrt V) + 4 * ζ * (Real.sqrt 2 * σx * (1 / a + n * Real.sqrt a)) +
    n * Gm * ∫ ξ, (1 - g ξ (n + 1)) ∂P
  linarith

end OracleTemplate.MinimaxLmo
