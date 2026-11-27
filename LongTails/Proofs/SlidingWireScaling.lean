import LongTails.Proofs.SlidingWireFailure
import LongTails.Proofs.SlidingLowerScaling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingWireScaling

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingWireSim SlidingWireGap SlidingWireAdmissible SlidingWireFailure SlidingLowerScaling

noncomputable def wireRoot (q : Params) : ℝ := Real.sqrt (Real.sqrt (q.L / q.ℓ))

noncomputable def wireR (q : Params) : ℕ := ⌊wireRoot q / 8⌋₊

noncomputable def wireT (q : Params) : ℕ := ⌊q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 30⌋₊

noncomputable def wireK (q : Params) : ℕ := wireT q * (wireR q ^ 2 + 2)

noncomputable def wireScale (q : Params) : WScale :=
  let r := wireR q
  let δ : ℝ := 1 / (4 * r)
  let s : ℝ := 512 * 530 * q.ε / q.ℓ
  ⟨r, δ, 2 ^ 20 * (1 + q.ℓ * q.Δ / q.ε ^ 2) * (1 + Real.sqrt (q.L / q.ℓ)) ^ 2,
    8 * ((r : ℝ) ^ 2 + 7) ^ 2 + 1026,
    δ / (2 * ((r : ℝ) ^ 2 + 7)), 512 * q.ε * s, s, q.ℓ⟩

lemma root_facts (q : Params) (hℓ : 0 < q.ℓ) (hL : q.ℓ ≤ q.L) :
    0 ≤ wireRoot q ∧ wireRoot q ^ 2 = Real.sqrt (q.L / q.ℓ) ∧
      wireRoot q ^ 4 = q.L / q.ℓ := by
  have h0 : 0 ≤ q.L / q.ℓ := div_nonneg (by linarith) hℓ.le
  have h1 : 0 ≤ Real.sqrt (q.L / q.ℓ) := Real.sqrt_nonneg _
  have h2 : wireRoot q ^ 2 = Real.sqrt (q.L / q.ℓ) := Real.sq_sqrt h1
  refine ⟨Real.sqrt_nonneg _, h2, ?_⟩
  rw [show wireRoot q ^ 4 = (wireRoot q ^ 2) ^ 2 by ring, h2, Real.sq_sqrt h0]

lemma r_bounds (q : Params) (hroot : 64 ≤ wireRoot q) :
    1 ≤ wireR q ∧ wireRoot q / 16 ≤ (wireR q : ℝ) ∧ (wireR q : ℝ) ≤ wireRoot q / 8 := by
  have h0 : 0 ≤ wireRoot q / 8 := by linarith
  have hfl := Nat.floor_le h0
  have hlt := Nat.sub_one_lt_floor (wireRoot q / 8)
  refine ⟨?_, by unfold wireR; linarith, hfl⟩
  have : (1 : ℝ) ≤ wireR q := by unfold wireR; linarith
  exact_mod_cast this


lemma regime_root (q : Params) (hq : spec.valid q)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) : 64 ≤ wireRoot q := by
  obtain ⟨hℓ, hL, hσ, hε, hX⟩ := valid_facts q hq
  have h1 : (2 : ℝ) ^ 12 ≤ Real.sqrt (q.L / q.ℓ) := by
    have : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
    nlinarith
  unfold wireRoot
  rw [show (64 : ℝ) = Real.sqrt (2 ^ 12) by
    rw [show (2 : ℝ) ^ 12 = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt h1

structure Facts (q : Params) : Prop where
  ℓ_pos : 0 < q.ℓ
  ε_pos : 0 < q.ε
  X_big : 2 ^ 62 ≤ q.ℓ * q.Δ / q.ε ^ 2
  r_one : 1 ≤ wireR q
  r_sq : ((wireR q : ℝ)) ^ 2 ≤ Real.sqrt (q.L / q.ℓ) / 64
  r_sq_lower : Real.sqrt (q.L / q.ℓ) / 256 ≤ ((wireR q : ℝ)) ^ 2
  T_upper : (wireT q : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 30
  T_lower : q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 31 ≤ wireT q
  L_ratio : q.L / q.ℓ = Real.sqrt (q.L / q.ℓ) ^ 2
  sqrt_big : 2 ^ 12 ≤ Real.sqrt (q.L / q.ℓ)

lemma facts (q : Params) (hq : spec.valid q)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) : Facts q := by
  obtain ⟨hℓ, hL, hσ, hε, hX⟩ := valid_facts q hq
  have hroot := regime_root q hq hB
  have hrf := root_facts q hℓ hL
  have hr := r_bounds q hroot
  have hs0 : (2 : ℝ) ^ 12 ≤ Real.sqrt (q.L / q.ℓ) := by
    have : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
    nlinarith
  refine ⟨hℓ, hε, hX, hr.1, ?_, ?_, ?_, ?_, ?_, hs0⟩
  · have h1 : ((wireR q : ℝ)) ^ 2 ≤ (wireRoot q / 8) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hr.2.2 2
    rw [div_pow, hrf.2.1] at h1
    linarith
  · have h1 : (wireRoot q / 16) ^ 2 ≤ ((wireR q : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hr.2.1 2
    rw [div_pow, hrf.2.1] at h1
    linarith
  · exact Nat.floor_le (by apply div_nonneg _ (by norm_num); linarith)
  · have h1 := Nat.sub_one_lt_floor (q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 30)
    unfold wireT
    have : (2 : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 31 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have e : q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 30 = 2 * (q.ℓ * q.Δ / q.ε ^ 2 / 2 ^ 31) := by ring
    linarith
  · rw [Real.sq_sqrt (div_nonneg (by linarith) hℓ.le)]


lemma k_bound (q : Params) (F : Facts q) :
    ((wireK q : ℕ) : ℝ) + 1 ≤ 3 * (1 + q.ℓ * q.Δ / q.ε ^ 2) * (1 + Real.sqrt (q.L / q.ℓ)) := by
  have hs := Real.sqrt_nonneg (q.L / q.ℓ)
  have hX0 : 0 ≤ q.ℓ * q.Δ / q.ε ^ 2 := by linarith [F.X_big]
  unfold wireK
  push_cast
  have h1 : ((wireR q : ℝ)) ^ 2 + 2 ≤ 3 * (1 + Real.sqrt (q.L / q.ℓ)) := by
    linarith [F.r_sq]
  have h2 : (wireT q : ℝ) ≤ q.ℓ * q.Δ / q.ε ^ 2 := by linarith [F.T_upper]
  have h3 : (wireT q : ℝ) * (((wireR q : ℝ)) ^ 2 + 2) ≤
      (q.ℓ * q.Δ / q.ε ^ 2) * (3 * (1 + Real.sqrt (q.L / q.ℓ))) :=
    mul_le_mul h2 h1 (by positivity) hX0
  linarith

set_option maxHeartbeats 400000 in
lemma wire_valid (q : Params) (hq : spec.valid q)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) :
    WVal q (wireT q) (wireScale q) ∧ WValid (wireScale q) (wireK q) := by
  have F := facts q hq hB
  have hL := (valid_facts q hq).2.1
  set X := q.ℓ * q.Δ / q.ε ^ 2 with hXdef
  set Y := 1 + Real.sqrt (q.L / q.ℓ) with hYdef
  have hs := Real.sqrt_nonneg (q.L / q.ℓ)
  have hY1 : 1 ≤ Y := by linarith
  have hX0 : 0 ≤ X := by linarith [F.X_big]
  have hk := k_bound q F
  rw [← hXdef, ← hYdef] at hk
  have hr1 : (1 : ℝ) ≤ wireR q := by exact_mod_cast F.r_one
  have hr2 : ((wireR q : ℝ)) ^ 2 ≤ Y := by linarith [F.r_sq]
  have hR : 2 ^ 20 * (1 + X) * Y ^ 2 = (wireScale q).R := rfl
  have hRpos : 1 ≤ (wireScale q).R := by
    rw [← hR]; nlinarith [mul_le_mul hY1 hY1 zero_le_one (by linarith)]
  have hkY : ((wireK q : ℕ) : ℝ) + 1 ≤ 3 * (1 + X) * Y := hk
  have hK0 : (0 : ℝ) ≤ (wireK q : ℕ) := Nat.cast_nonneg _
  have hRY : 2 ^ 18 * (((wireK q : ℕ) : ℝ) + 1) * Y ≤ (wireScale q).R := by
    rw [← hR]
    have : 2 ^ 18 * (((wireK q : ℕ) : ℝ) + 1) * Y ≤ 2 ^ 18 * (3 * (1 + X) * Y) * Y := by gcongr
    nlinarith
  have hΛ1 : 1 ≤ (wireScale q).Λ := by
    show 1 ≤ 8 * (((wireR q : ℕ) : ℝ) ^ 2 + 7) ^ 2 + 1026
    have := sq_nonneg (((wireR q : ℕ) : ℝ) ^ 2 + 7)
    linarith
  have hθ : (wireScale q).θ = 1 / (8 * (wireR q : ℝ) * (((wireR q : ℝ)) ^ 2 + 7)) := by
    show 1 / (4 * (wireR q : ℝ)) / (2 * (((wireR q : ℝ)) ^ 2 + 7)) = _
    field_simp
    ring
  have hRbig : 4 + 4 * ((wireK q : ℕ) : ℝ) + (((wireK q : ℕ) : ℝ) + 1) * (((wireR q : ℝ)) ^ 2 + 7) ^ 2 ≤
      (wireScale q).R ^ 2 := by
    have h1 : (((wireR q : ℝ)) ^ 2 + 7) ^ 2 ≤ 64 * Y ^ 2 := by nlinarith
    have h2 : (wireScale q).R ^ 2 ≥ (2 ^ 18 * (((wireK q : ℕ) : ℝ) + 1) * Y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRY 2
    have h3 : (((wireK q : ℕ) : ℝ) + 1) * (((wireR q : ℝ)) ^ 2 + 7) ^ 2 ≤
        (((wireK q : ℕ) : ℝ) + 1) * (64 * Y ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hY2 : (1 : ℝ) ≤ Y ^ 2 := by nlinarith
    have h4 : (((wireK q : ℕ) : ℝ) + 1) * Y ^ 2 ≤ (((wireK q : ℕ) : ℝ) + 1) ^ 2 * Y ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    have h5 : ((wireK q : ℕ) : ℝ) + 1 ≤ (((wireK q : ℕ) : ℝ) + 1) * Y ^ 2 := by
      have := mul_le_mul_of_nonneg_left hY2 (by linarith : (0 : ℝ) ≤ ((wireK q : ℕ) : ℝ) + 1)
      linarith
    have h6 : (2 ^ 18 * (((wireK q : ℕ) : ℝ) + 1) * Y) ^ 2 =
        2 ^ 36 * ((((wireK q : ℕ) : ℝ) + 1) ^ 2 * Y ^ 2) := by ring
    have h7 : 0 ≤ (((wireK q : ℕ) : ℝ) + 1) * Y ^ 2 := by positivity
    linarith [h2, h3, h4, h5, h6, h7]
  have hgap : GapHyp (wireScale q) (wireT q) := by
    refine ⟨F.r_one, ?_, ?_, hRpos, hΛ1, ?_, ?_, ?_, hRbig, ?_, ?_, ?_, F.ℓ_pos⟩
    · show (0 : ℝ) ≤ 1 / (4 * (wireR q : ℝ)); positivity
    · show (wireR q : ℝ) * (1 / (4 * (wireR q : ℝ))) ≤ 1 / 4
      field_simp; linarith
    · rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    · show 8 + 8 * ((wireK q : ℕ) : ℝ) ≤ _
      nlinarith
    · show 320 * (4 + 38 * ((wireK q : ℕ) : ℝ)) ≤ _
      nlinarith
    · show (0 : ℝ) ≤ 512 * q.ε * (512 * 530 * q.ε / q.ℓ)
      have := F.ε_pos; have := F.ℓ_pos; positivity
    · show (0 : ℝ) < 512 * 530 * q.ε / q.ℓ
      have := F.ε_pos; have := F.ℓ_pos; positivity
    · show 512 * q.ε * (512 * 530 * q.ε / q.ℓ) / (512 * 530 * q.ε / q.ℓ) ^ 2 * 530 = q.ℓ
      have := F.ε_pos; have := F.ℓ_pos
      field_simp
  refine ⟨⟨hgap, rfl, le_rfl, ?_, ?_, ?_⟩, ⟨F.r_one, hgap.δ_nonneg, ?_, ?_, ?_, ?_, hΛ1, hRbig⟩⟩
  · show 1 + 2 * (((wireR q : ℕ) : ℝ) ^ 2 + 23) * (((wireK q : ℕ) : ℝ) + 1) ≤ _
    have : 2 * (((wireR q : ℕ) : ℝ) ^ 2 + 23) * (((wireK q : ℕ) : ℝ) + 1) ≤
        2 * (24 * Y) * (((wireK q : ℕ) : ℝ) + 1) := by gcongr; linarith
    nlinarith
  · show q.ℓ + 512 * q.ε * (512 * 530 * q.ε / q.ℓ) / (512 * 530 * q.ε / q.ℓ) ^ 2 *
      (512 * (8 * (((wireR q : ℕ) : ℝ) ^ 2 + 7) ^ 2 + 1026)) ≤ q.L
    have hε := F.ε_pos
    have hℓ := F.ℓ_pos
    have e : 512 * q.ε * (512 * 530 * q.ε / q.ℓ) / (512 * 530 * q.ε / q.ℓ) ^ 2 = q.ℓ / 530 := by
      field_simp
    rw [e]
    have hr4 : (((wireR q : ℕ) : ℝ) ^ 2) ^ 2 ≤ (Real.sqrt (q.L / q.ℓ) / 64) ^ 2 :=
      pow_le_pow_left₀ (by positivity) F.r_sq 2
    have hLr : q.L = q.ℓ * Real.sqrt (q.L / q.ℓ) ^ 2 := by
      rw [← F.L_ratio]; field_simp
    have hsb := F.sqrt_big
    have hsq2 : (2 : ℝ) ^ 24 ≤ Real.sqrt (q.L / q.ℓ) ^ 2 := by nlinarith
    rw [hLr]
    have : 8 * (((wireR q : ℕ) : ℝ) ^ 2 + 7) ^ 2 + 1026 ≤
        16 * (Real.sqrt (q.L / q.ℓ) / 64) ^ 2 + 1810 := by nlinarith [sq_nonneg (((wireR q : ℕ) : ℝ) ^ 2 - 7)]
    have h2 : q.ℓ / 530 * (512 * (8 * (((wireR q : ℕ) : ℝ) ^ 2 + 7) ^ 2 + 1026)) ≤
        q.ℓ / 530 * (512 * (16 * (Real.sqrt (q.L / q.ℓ) / 64) ^ 2 + 1810)) := by gcongr
    have h3 : q.ℓ / 530 * (512 * (16 * (Real.sqrt (q.L / q.ℓ) / 64) ^ 2 + 1810)) =
        q.ℓ * Real.sqrt (q.L / q.ℓ) ^ 2 / 265 + q.ℓ * (926720 / 530) := by ring
    have h4 : q.ℓ * 2 ^ 24 ≤ q.ℓ * Real.sqrt (q.L / q.ℓ) ^ 2 := mul_le_mul_of_nonneg_left hsq2 hℓ.le
    linarith
  · show 512 * q.ε * (512 * 530 * q.ε / q.ℓ) * (4 + 4 * (wireT q : ℝ)) ≤ q.Δ
    have hε := F.ε_pos
    have hℓ := F.ℓ_pos
    have e : 512 * q.ε * (512 * 530 * q.ε / q.ℓ) * (4 + 4 * (wireT q : ℝ)) =
        4 * (512 * 512 * 530) * (1 + (wireT q : ℝ)) * q.ε ^ 2 / q.ℓ := by field_simp
    rw [e, div_le_iff₀ hℓ]
    have hXe : X * q.ε ^ 2 = q.ℓ * q.Δ := by rw [hXdef]; field_simp
    have h1 : 4 * (512 * 512 * 530) * (1 + (wireT q : ℝ)) ≤ X := by
      have := F.T_upper; have := F.X_big; nlinarith
    nlinarith [sq_nonneg q.ε]
  · show 2 * (((wireR q : ℕ) : ℝ) ^ 2 + 7) * (1 / (4 * (wireR q : ℝ)) / (2 * (((wireR q : ℝ)) ^ 2 + 7))) ≤
      1 / (4 * (wireR q : ℝ))
    rw [mul_div_cancel₀ _ (by positivity)]
  · rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · rw [hθ]; positivity
  · linarith

lemma wire_acc (q : Params) (hq : spec.valid q)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) :
    q.ε ^ 2 / (8 * q.ℓ) < (7 / 8) * cminB (wireScale q) := by
  have F := facts q hq hB
  have hε := F.ε_pos
  have hℓ := F.ℓ_pos
  unfold cminB
  show q.ε ^ 2 / (8 * q.ℓ) < (7 / 8) * min ((512 * q.ε * (512 * 530 * q.ε / q.ℓ) /
    (512 * 530 * q.ε / q.ℓ)) ^ 2 / (819200 * q.ℓ)) (49 * q.ℓ * (512 * 530 * q.ε / q.ℓ) ^ 2 / 128)
  have e1 : (512 * q.ε * (512 * 530 * q.ε / q.ℓ) / (512 * 530 * q.ε / q.ℓ)) ^ 2 / (819200 * q.ℓ) =
      262144 * q.ε ^ 2 / (819200 * q.ℓ) := by
    field_simp
    ring
  have e2 : 49 * q.ℓ * (512 * 530 * q.ε / q.ℓ) ^ 2 / 128 = 49 * (512 * 530) ^ 2 * q.ε ^ 2 / (128 * q.ℓ) := by
    field_simp
  rw [e1, e2]
  have h1 : 262144 * q.ε ^ 2 / (819200 * q.ℓ) ≤ 49 * (512 * 530) ^ 2 * q.ε ^ 2 / (128 * q.ℓ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg q.ε]
  rw [min_eq_left h1, div_lt_iff₀ (by positivity)]
  have : (7 / 8) * (262144 * q.ε ^ 2 / (819200 * q.ℓ)) * (8 * q.ℓ) = 7 * 262144 / 819200 * q.ε ^ 2 := by
    field_simp
  rw [this]
  nlinarith [sq_pos_of_pos hε]


lemma wire_hb (q : Params) (hq : spec.valid q)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) (n : ℕ)
    (hn : n ≤ ⌊q.ℓ * q.Δ / q.ε ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) / 2 ^ 60⌋₊) :
    n ≤ wireK q := by
  have F := facts q hq hB
  set X := q.ℓ * q.Δ / q.ε ^ 2 with hX
  set S := Real.sqrt (q.L / q.ℓ)
  have hX0 : 0 ≤ X := by linarith [F.X_big]
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hH : X * (1 + q.σ ^ 2 / q.ε ^ 2 + S) ≤ 2 * X * S := by
    have : 1 + q.σ ^ 2 / q.ε ^ 2 ≤ S := by nlinarith
    nlinarith
  have hn' : (n : ℝ) ≤ X * (1 + q.σ ^ 2 / q.ε ^ 2 + S) / 2 ^ 60 := by
    have h0 : 0 ≤ X * (1 + q.σ ^ 2 / q.ε ^ 2 + S) / 2 ^ 60 := by
      have : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
      positivity
    exact (Nat.cast_le.mpr hn).trans (Nat.floor_le h0)
  have hk : X * S / 2 ^ 39 ≤ (wireK q : ℝ) := by
    unfold wireK
    push_cast
    have h1 : (wireT q : ℝ) * ((wireR q : ℝ) ^ 2) ≤ (wireT q : ℝ) * ((wireR q : ℝ) ^ 2 + 2) := by
      have := Nat.cast_nonneg (α := ℝ) (wireT q); nlinarith
    have h2 : X / 2 ^ 31 * (S / 256) ≤ (wireT q : ℝ) * ((wireR q : ℝ) ^ 2) :=
      mul_le_mul F.T_lower F.r_sq_lower (by positivity) (Nat.cast_nonneg _)
    have e : X * S / 2 ^ 39 = X / 2 ^ 31 * (S / 256) := by ring
    linarith
  have : (n : ℝ) ≤ wireK q := by
    have h3 : X * (1 + q.σ ^ 2 / q.ε ^ 2 + S) / 2 ^ 60 ≤ X * S / 2 ^ 39 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hX0 hS0]
    linarith
  exact_mod_cast this

set_option maxHeartbeats 400000 in
lemma wire_dim (q : Params) (hq : spec.valid q)
    (hB : 2 ^ 12 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ Real.sqrt (q.L / q.ℓ)) (b : Fin 2 → ℕ)
    (hb0 : b 0 ≤ q.K)
    (hb1 : b 1 ≤ ⌊q.ℓ * q.Δ / q.ε ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) / 2 ^ 60⌋₊) :
    16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (wireK q + 1 : ℕ) * ((6 * (wireScale q).R) ^ 2 / (wireScale q).θ ^ 2) +
      (wireK q + 1 : ℕ) ≤ q.d := by
  have F := facts q hq hB
  have hvalid := hq.2.2.2.2.2
  set X := q.ℓ * q.Δ / q.ε ^ 2 with hX
  set Y := 1 + Real.sqrt (q.L / q.ℓ) with hY
  set H := X * (1 + q.σ ^ 2 / q.ε ^ 2 + Real.sqrt (q.L / q.ℓ)) with hH
  have hs := Real.sqrt_nonneg (q.L / q.ℓ)
  have hY1 : 1 ≤ Y := by linarith
  have hX0 : 0 ≤ X := by linarith [F.X_big]
  have hH0 : 0 ≤ H := by
    have : (0 : ℝ) ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
    positivity
  have hN : (((∑ i, b i : ℕ) : ℝ) + 1) ≤ 1 + q.K + H := by
    rw [Fin.sum_univ_two]
    push_cast
    have h0 : (b 0 : ℝ) ≤ q.K := by exact_mod_cast hb0
    have h1 : (b 1 : ℝ) ≤ H / 2 ^ 60 := (Nat.cast_le.mpr hb1).trans (Nat.floor_le (by positivity))
    have : H / 2 ^ 60 ≤ H := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hk := k_bound q F
  rw [← hX, ← hY] at hk
  have hkc : ((wireK q + 1 : ℕ) : ℝ) ≤ 3 * (1 + X) * Y := by push_cast; exact hk
  have hr1 : (1 : ℝ) ≤ wireR q := by exact_mod_cast F.r_one
  have hr2 : ((wireR q : ℝ)) ^ 2 ≤ Y := by linarith [F.r_sq]
  have hθinv : (6 * (wireScale q).R) ^ 2 / (wireScale q).θ ^ 2 ≤ 2 ^ 58 * (1 + X) ^ 2 * Y ^ 8 := by
    have hθ : (wireScale q).θ = 1 / (8 * (wireR q : ℝ) * (((wireR q : ℝ)) ^ 2 + 7)) := by
      show 1 / (4 * (wireR q : ℝ)) / (2 * (((wireR q : ℝ)) ^ 2 + 7)) = _
      field_simp
      ring
    have hR : (wireScale q).R = 2 ^ 20 * (1 + X) * Y ^ 2 := rfl
    rw [hθ, hR, one_div, inv_pow, div_inv_eq_mul]
    have hrr : (wireR q : ℝ) ≤ Y := by nlinarith
    have h7 : ((wireR q : ℝ)) ^ 2 + 7 ≤ 8 * Y := by linarith
    have hprod : (8 * (wireR q : ℝ) * (((wireR q : ℝ)) ^ 2 + 7)) ^ 2 ≤ (64 * Y ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      have := mul_le_mul hrr h7 (by positivity) (by positivity)
      linarith
    have hR2 : (6 * (2 ^ 20 * (1 + X) * Y ^ 2)) ^ 2 = 36 * 2 ^ 40 * (1 + X) ^ 2 * Y ^ 4 := by ring
    rw [hR2]
    calc 36 * 2 ^ 40 * (1 + X) ^ 2 * Y ^ 4 * (8 * (wireR q : ℝ) * (((wireR q : ℝ)) ^ 2 + 7)) ^ 2
        ≤ 36 * 2 ^ 40 * (1 + X) ^ 2 * Y ^ 4 * (64 * Y ^ 2) ^ 2 := by gcongr
      _ = 36 * 4096 * 2 ^ 40 * (1 + X) ^ 2 * Y ^ 8 := by ring
      _ ≤ 2 ^ 58 * (1 + X) ^ 2 * Y ^ 8 := by
          have h0 : (0 : ℝ) ≤ (1 + X) ^ 2 * Y ^ 8 := by positivity
          have hc := mul_le_mul_of_nonneg_right (show (36 * 4096 * 2 ^ 40 : ℝ) ≤ 2 ^ 58 by norm_num) h0
          linarith
  have hY9 : Y ≤ Y ^ 9 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ 9 := pow_le_pow_right₀ hY1 (by norm_num)
  have hX3 : (1 + X) ≤ (1 + X) ^ 3 := by
    calc (1 + X) = (1 + X) ^ 1 := (pow_one _).symm
      _ ≤ (1 + X) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hK1 : (1 : ℝ) ≤ 1 + q.K + H := by have := Nat.cast_nonneg (α := ℝ) q.K; linarith
  calc 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (wireK q + 1 : ℕ) * ((6 * (wireScale q).R) ^ 2 / (wireScale q).θ ^ 2) +
        (wireK q + 1 : ℕ)
      ≤ 16 * (1 + q.K + H) * (3 * (1 + X) * Y) * (2 ^ 58 * (1 + X) ^ 2 * Y ^ 8) + 3 * (1 + X) * Y := by
        gcongr
    _ ≤ 2 ^ 200 * (1 + q.K + H) * (1 + X) ^ 3 * Y ^ 9 := by
        have e : 16 * (1 + q.K + H) * (3 * (1 + X) * Y) * (2 ^ 58 * (1 + X) ^ 2 * Y ^ 8) =
            48 * 2 ^ 58 * (1 + q.K + H) * (1 + X) ^ 3 * Y ^ 9 := by ring
        rw [e]
        have h1 : 3 * (1 + X) * Y ≤ 3 * (1 + q.K + H) * (1 + X) ^ 3 * Y ^ 9 := by
          have h4 := mul_le_mul hX3 hY9 (by linarith) (by positivity)
          have h2 : 0 ≤ (1 + X) ^ 3 * Y ^ 9 := by positivity
          have h5 := mul_le_mul_of_nonneg_right hK1 h2
          linarith
        have h3 : 0 ≤ (1 + q.K + H) * (1 + X) ^ 3 * Y ^ 9 := by positivity
        linarith
    _ ≤ q.d := hvalid

end LongTails.Proofs.SlidingWireScaling
