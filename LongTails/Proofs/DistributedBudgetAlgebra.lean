import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace LongTails.Proofs.DistributedBudgetAlgebra

noncomputable def frontier (H R U S d n q : ℝ) : ℝ :=
  max H (max U (max S (max (d * U / n) (max (d * S / Real.sqrt n)
    (max ((d ^ 3 * U * S ^ 2 / n) ^ (1 / 3 : ℝ))
      (max (H * R / n) (max (Real.sqrt (d * H * R * U / n)) (d * S * q))))))))

noncomputable def compact (H R U S d n q : ℝ) : ℝ :=
  H * (1 + R / n) + (U + S) * (1 + d / n ^ (1 / 3 : ℝ)) +
    d * S * q + Real.sqrt (d * H * R * U / n)

lemma cube_root_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  simpa using Real.rpow_inv_natCast_pow hx (by norm_num : (3 : ℕ) ≠ 0)

lemma cube_root_of_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ 3) ^ (1 / 3 : ℝ) = x := by
  simpa using Real.pow_rpow_inv_natCast hx (by norm_num : (3 : ℕ) ≠ 0)

lemma cube_root_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y ^ 3) :
    x ^ (1 / 3 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow hx h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [cube_root_of_cube y hy] at hr

lemma le_cube_root {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 3 ≤ y) :
    x ≤ y ^ (1 / 3 : ℝ) := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 3) h (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rwa [cube_root_of_cube x hx] at hr

lemma cube_root_bounds {n : ℝ} (hn : 1 ≤ n) :
    1 ≤ n ^ (1 / 3 : ℝ) ∧ n ^ (1 / 3 : ℝ) ≤ Real.sqrt n ∧
      n ^ (1 / 3 : ℝ) ≤ n := by
  have hnp : 0 < n := by linarith
  have hs := Real.sqrt_nonneg n
  have hs2 := Real.sq_sqrt hnp.le
  have hs1 : 1 ≤ Real.sqrt n := by nlinarith
  refine ⟨le_cube_root (by norm_num) (by simpa), ?_, ?_⟩
  · apply cube_root_le hnp.le hs
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt n - 1 by linarith) hnp.le]
  · apply cube_root_le hnp.le hnp.le
    nlinarith [mul_nonneg (show 0 ≤ n - 1 by linarith) (show 0 ≤ n ^ 2 by positivity)]

lemma mixed_upper {d U S n : ℝ} (hd : 0 ≤ d) (hU : 0 ≤ U) (hS : 0 ≤ S)
    (hn : 0 < n) :
    (d ^ 3 * U * S ^ 2 / n) ^ (1 / 3 : ℝ) ≤ (U + S) * d / n ^ (1 / 3 : ℝ) := by
  have hz : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn _
  have hz3 := cube_root_cube n hn.le
  apply cube_root_le (by positivity) (by positivity)
  rw [div_pow, hz3]
  apply (div_le_div_iff_of_pos_right hn).mpr
  have hpoly : U * S ^ 2 ≤ (U + S) ^ 3 := by
    nlinarith [mul_nonneg hU (sq_nonneg U), mul_nonneg hS (sq_nonneg S),
      mul_nonneg hU (sq_nonneg S), mul_nonneg hS (sq_nonneg U)]
  nlinarith [mul_le_mul_of_nonneg_left hpoly (pow_nonneg hd 3)]

lemma mixed_lower {d U S n : ℝ} (hd : 0 ≤ d) (hS : 0 ≤ S) (hSU : S ≤ U)
    (hn : 0 < n) :
    d * S / n ^ (1 / 3 : ℝ) ≤ (d ^ 3 * U * S ^ 2 / n) ^ (1 / 3 : ℝ) := by
  have hU : 0 ≤ U := hS.trans hSU
  have hz := Real.rpow_pos_of_pos hn (1 / 3 : ℝ)
  have hz3 := cube_root_cube n hn.le
  apply le_cube_root (by positivity)
  rw [div_pow, hz3]
  apply (div_le_div_iff_of_pos_right hn).mpr
  nlinarith [mul_le_mul_of_nonneg_left hSU (show 0 ≤ d ^ 3 * S ^ 2 by positivity)]



lemma compact_expansion (H R U S d n q : ℝ) :
    compact H R U S d n q = H + H * R / n + U + S +
      (U + S) * d / n ^ (1 / 3 : ℝ) + d * S * q + Real.sqrt (d * H * R * U / n) := by
  unfold compact
  ring

lemma frontier_le_compact {H R U S d n q : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hU : 0 ≤ U) (hS : 0 ≤ S) (hd : 0 ≤ d) (hn : 1 ≤ n) (hq : 0 ≤ q) :
    frontier H R U S d n q ≤ compact H R U S d n q := by
  have hnp : 0 < n := by linarith
  obtain ⟨hz1, hzs, hzn⟩ := cube_root_bounds hn
  have hz : 0 < n ^ (1 / 3 : ℝ) := by linarith
  have ha : 0 ≤ H * R / n := by positivity
  have hb : 0 ≤ (U + S) * d / n ^ (1 / 3 : ℝ) := by positivity
  have hc : 0 ≤ d * S * q := by positivity
  have hw := Real.sqrt_nonneg (d * H * R * U / n)
  have hu : d * U / n ≤ (U + S) * d / n ^ (1 / 3 : ℝ) := by
    calc
      _ ≤ d * U / n ^ (1 / 3 : ℝ) := div_le_div_of_nonneg_left (by positivity) hz hzn
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hd hS]) hz.le
  have hs : d * S / Real.sqrt n ≤ (U + S) * d / n ^ (1 / 3 : ℝ) := by
    calc
      _ ≤ d * S / n ^ (1 / 3 : ℝ) := div_le_div_of_nonneg_left (by positivity) hz hzs
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hd hU]) hz.le
  have hm := mixed_upper hd hU hS hnp
  rw [compact_expansion]
  unfold frontier
  repeat' apply max_le
  all_goals linarith

lemma compact_le_frontier {H R U S d n q : ℝ} (hH : 0 ≤ H)
    (hU : 0 ≤ U) (hS : 0 ≤ S) (hd : 0 ≤ d) (hn : 1 ≤ n)
    (hwidth : n ≤ d ^ 3 → S ≤ U ∧ U ≤ 8 * S) :
    compact H R U S d n q ≤ 16 * frontier H R U S d n q := by
  let F := frontier H R U S d n q
  have hf : frontier H R U S d n q ≤ F := le_rfl
  simp only [frontier, max_le_iff] at hf
  obtain ⟨hfH, hfU, hfS, _, _, hfM, hfA, hfW, hfC⟩ := hf
  have hnp : 0 < n := by linarith
  have hz := Real.rpow_pos_of_pos hnp (1 / 3 : ℝ)
  have hz3 := cube_root_cube n hnp.le
  have hf0 : 0 ≤ F := hH.trans hfH
  have hb : (U + S) * d / n ^ (1 / 3 : ℝ) ≤ 9 * F := by
    by_cases hdroot : d ≤ n ^ (1 / 3 : ℝ)
    · have ht : (U + S) * d / n ^ (1 / 3 : ℝ) ≤ U + S := by
        apply (div_le_iff₀ hz).mpr
        exact mul_le_mul_of_nonneg_left hdroot (add_nonneg hU hS)
      linarith
    · have hn3 : n ≤ d ^ 3 := by
        have ht := pow_le_pow_left₀ hz.le (le_of_lt (lt_of_not_ge hdroot)) 3
        rwa [hz3] at ht
      obtain ⟨hSU, hUS⟩ := hwidth hn3
      have hm := (mixed_lower hd hS hSU hnp).trans hfM
      have ht : (U + S) * d / n ^ (1 / 3 : ℝ) ≤ 9 * (d * S / n ^ (1 / 3 : ℝ)) := by
        have ht := mul_le_mul_of_nonneg_right (show U + S ≤ 9 * S by linarith) hd
        have ht' := div_le_div_of_nonneg_right ht hz.le
        calc
          _ ≤ 9 * S * d / n ^ (1 / 3 : ℝ) := ht'
          _ = _ := by ring
      linarith
  rw [compact_expansion]
  change H + H * R / n + U + S + (U + S) * d / n ^ (1 / 3 : ℝ) +
    d * S * q + Real.sqrt (d * H * R * U / n) ≤ 16 * F
  linarith



lemma frontier_mono {H R U S V W d n q : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hU : 0 ≤ U) (hS : 0 ≤ S) (hd : 0 ≤ d) (hn : 0 < n) (hq : 0 ≤ q)
    (hUV : U ≤ V) (hSW : S ≤ W) :
    frontier H R U S d n q ≤ frontier H R V W d n q := by
  have hV : 0 ≤ V := hU.trans hUV
  unfold frontier
  gcongr


lemma frontier_scale {H R U S V W d n q c : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hd : 0 ≤ d) (hn : 0 < n) (hq : 0 ≤ q) (hc : 1 ≤ c)
    (hVU : V ≤ c * U) (hWS : W ≤ c * S) :
    frontier H R V W d n q ≤ c * frontier H R U S d n q := by
  let F := frontier H R U S d n q
  have hf : frontier H R U S d n q ≤ F := le_rfl
  simp only [frontier, max_le_iff] at hf
  obtain ⟨hfH, hfU, hfS, hfDU, hfDS, hfM, hfA, hfW, hfC⟩ := hf
  have hc0 : 0 ≤ c := by linarith
  have hf0 : 0 ≤ F := hH.trans hfH
  have hFF : F ≤ c * F := by nlinarith [mul_nonneg (show 0 ≤ c - 1 by linarith) hf0]
  have hu : d * V / n ≤ c * (d * U / n) := by
    calc
      _ ≤ d * (c * U) / n := by gcongr
      _ = _ := by ring
  have hs : d * W / Real.sqrt n ≤ c * (d * S / Real.sqrt n) := by
    calc
      _ ≤ d * (c * S) / Real.sqrt n := by gcongr
      _ = _ := by ring
  have hcurv : d * W * q ≤ c * (d * S * q) := by
    calc
      _ ≤ d * (c * S) * q := by gcongr
      _ = _ := by ring
  have hm : (d ^ 3 * V * W ^ 2 / n) ^ (1 / 3 : ℝ) ≤
      c * (d ^ 3 * U * S ^ 2 / n) ^ (1 / 3 : ℝ) := by
    have hp : 0 ≤ d ^ 3 * U * S ^ 2 / n := by positivity
    have he := cube_root_cube (d ^ 3 * U * S ^ 2 / n) hp
    have hb : d ^ 3 * V * W ^ 2 / n ≤ c ^ 3 * (d ^ 3 * U * S ^ 2 / n) := by
      calc
        _ ≤ d ^ 3 * (c * U) * (c * S) ^ 2 / n := by gcongr
        _ = _ := by ring
    apply cube_root_le (by positivity) (by positivity)
    rwa [mul_pow, he]
  have hw : Real.sqrt (d * H * R * V / n) ≤ c * Real.sqrt (d * H * R * U / n) := by
    have hp : 0 ≤ d * H * R * U / n := by positivity
    have hb : d * H * R * V / n ≤ c * (d * H * R * U / n) := by
      calc
        _ ≤ d * H * R * (c * U) / n := by gcongr
        _ = _ := by ring
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hp]
    have hcc : c ≤ c ^ 2 := by nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right hcc hp)
  have hcu := mul_le_mul_of_nonneg_left hfU hc0
  have hcs := mul_le_mul_of_nonneg_left hfS hc0
  have hcdu := mul_le_mul_of_nonneg_left hfDU hc0
  have hcds := mul_le_mul_of_nonneg_left hfDS hc0
  have hcm := mul_le_mul_of_nonneg_left hfM hc0
  have hcw := mul_le_mul_of_nonneg_left hfW hc0
  have hcc := mul_le_mul_of_nonneg_left hfC hc0
  change frontier H R V W d n q ≤ c * F
  unfold frontier
  repeat' apply max_le
  all_goals linarith

end LongTails.Proofs.DistributedBudgetAlgebra
