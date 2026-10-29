import LongTails.Proofs.KnownValueNondualCounting
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Set

namespace LongTails.Proofs.KnownValueNondualBudget

open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open KnownValueNondualCounting KnownValueNondualTrajectory KnownValueNondualExecution

noncomputable def aScale (p : Public) : ℝ := p.L0 * p.R ^ 2 / p.ε
noncomputable def bScale (p : Public) : ℝ := p.L1 * p.R
noncomputable def totalScale (p : Public) : ℝ := 2 + aScale p + bScale p
noncomputable def size (p : Public) : ℝ := 1 + aScale p ^ (1 / 3 : ℝ) + bScale p ^ (2 / 3 : ℝ)
noncomputable def logScale (p : Public) : ℝ := 1 + Real.log (2 * p.d) + Real.log (totalScale p)
noncomputable def rounds (p : Public) : ℕ := ⌈(2 : ℝ) ^ 30 * size p * logScale p⌉₊

lemma scale_pos (p : Public) (hp : spec.valid p) : 0 < aScale p ∧ 0 < bScale p ∧ 2 ≤ totalScale p := by
  rcases hp with ⟨_, h0, h1, hR, he⟩
  dsimp [aScale, bScale, totalScale]
  have ha : 0 < p.L0 * p.R ^ 2 / p.ε := by positivity
  have hb : 0 < p.L1 * p.R := by positivity
  exact ⟨ha, hb, by linarith⟩

lemma rpow_fraction_le_add_one {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    x ^ q ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_one hx h hq).trans (by linarith)
  · exact (Real.rpow_le_self_of_one_le h hq1).trans (by linarith)

lemma root_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma root_square {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma size_bounds (p : Public) (hp : spec.valid p) : 1 ≤ size p ∧ size p ≤ 3 * totalScale p := by
  have h := scale_pos p hp
  have ha := Real.rpow_nonneg h.1.le (1 / 3 : ℝ)
  have hb := Real.rpow_nonneg h.2.1.le (2 / 3 : ℝ)
  have ha' := rpow_fraction_le_add_one h.1.le (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hb' := rpow_fraction_le_add_one h.2.1.le (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) ≤ 1)
  dsimp only [size, totalScale]
  constructor <;> linarith

lemma logScale_bounds (p : Public) (hp : spec.valid p) :
    1 ≤ logScale p ∧ 1 + Real.log (totalScale p) ≤ logScale p ∧
      0 ≤ Real.log (2 * p.d) ∧ 0 ≤ Real.log (totalScale p) := by
  have hd : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hS := (scale_pos p hp).2.2
  have hld : 0 ≤ Real.log (2 * p.d) := Real.log_nonneg (by linarith)
  have hls : 0 ≤ Real.log (totalScale p) := Real.log_nonneg (by linarith)
  dsimp only [logScale]
  exact ⟨by linarith, by linarith, hld, hls⟩

lemma natLog_bound (n : ℕ) (hn : 0 < n) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.natLog_le_logb n 2
  have hlog := Real.log_nonneg hn'
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hdiv : Real.logb 2 n ≤ 2 * Real.log n := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  exact h.trans hdiv

lemma bitlength_bound (n : ℕ) (hn : 0 < n) :
    ((1 + Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := natLog_bound n hn
  rw [Real.log_mul (by norm_num) hn'.ne']
  push_cast
  linarith [Real.log_two_gt_d9]

lemma warmScale_bounds (p : Public) (hp : spec.valid p) :
    bScale p ^ (1 / 3 : ℝ) ≤ warmScale p ∧ warmScale p ≤ 2 + bScale p ^ (1 / 3 : ℝ) := by
  have hB := (scale_pos p hp).2.1
  have hlo := Nat.le_ceil (bScale p ^ (1 / 3 : ℝ))
  have hhi := Nat.ceil_lt_add_one (Real.rpow_nonneg hB.le (1 / 3 : ℝ))
  change _ ≤ 1 + (⌈bScale p ^ (1 / 3 : ℝ)⌉₊ : ℝ) ∧ 1 + (⌈bScale p ^ (1 / 3 : ℝ)⌉₊ : ℝ) ≤ _
  constructor <;> linarith

lemma initial_target_bound (p : Public) (hp : spec.valid p) :
    (initialControl p).target ≤ p.ε * (1 + 4 * aScale p * Real.exp (warmScale p)) := by
  rcases hp with ⟨_, h0, h1, hR, he⟩
  have hx : 1 ≤ Real.exp (warmScale p) := Real.one_le_exp_iff.mpr
    (by linarith [KnownValueNondualGeometry.warmScale_one_le p])
  have ha : p.ε * aScale p = p.L0 * p.R ^ 2 := by unfold aScale; field_simp
  have hrhs : p.ε * (1 + 4 * aScale p * Real.exp (warmScale p)) =
      p.ε + 4 * p.L0 * p.R ^ 2 * Real.exp (warmScale p) := by
    calc
      _ = p.ε + 4 * (p.ε * aScale p) * Real.exp (warmScale p) := by ring
      _ = _ := by rw [ha]; ring
  rw [hrhs]
  dsimp only [initialControl]
  split_ifs with hB
  · apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · have hh := mul_le_mul_of_nonneg_left hB.le
        (show 0 ≤ 4 * p.L0 * p.R * Real.exp (warmScale p) by positivity)
      have hc : 4 * p.L0 * p.R / p.L1 * Real.exp (warmScale p) ≤
          4 * p.L0 * p.R ^ 2 * Real.exp (warmScale p) := by
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ h1).mpr
        nlinarith only [hh]
      linarith
  · apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · nlinarith [mul_nonneg (show 0 ≤ p.L0 * p.R ^ 2 by positivity) (sub_nonneg.mpr hx)]

lemma phase_count_bound (p : Public) (hp : spec.valid p) (f : Point p → ℝ) (g : Point p → Point p) (n : ℕ) :
    ((trajectory p f g n).phase : ℝ) + 1 ≤
      10 + 2 * bScale p ^ (1 / 3 : ℝ) + 2 * Real.log (totalScale p) := by
  let q := (trajectory p f g n).phase
  have he := hp.2.2.2.2
  have hs := scale_pos p hp
  have hA := hs.1
  have hr := Real.rpow_nonneg hs.2.1.le (1 / 3 : ℝ)
  have hlogS := (logScale_bounds p hp).2.2.2
  change (q : ℝ) + 1 ≤ _
  by_cases hq : q = 0
  · simp only [hq, Nat.cast_zero, zero_add]
    linarith
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hphase := phase_exponential_bound p f g he.le n (Nat.pos_of_ne_zero hq)
    have hinit := initial_target_bound p hp
    have hpow : (2 : ℝ) ^ (q - 1) ≤ 1 + 4 * aScale p * Real.exp (warmScale p) := by
      apply (mul_le_mul_iff_right₀ he).mp
      exact hphase.le.trans hinit
    have hexp : 1 ≤ Real.exp (warmScale p) := Real.one_le_exp_iff.mpr
      (by linarith [KnownValueNondualGeometry.warmScale_one_le p])
    have hpow' : (2 : ℝ) ^ (q - 1) ≤ (1 + 4 * aScale p) * Real.exp (warmScale p) := by
      nlinarith only [hpow, hexp]
    have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) (q - 1)) hpow'
    rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Nat.cast_sub hq1, Nat.cast_one] at hl
    have hlogA : Real.log (1 + 4 * aScale p) ≤ 2 + Real.log (totalScale p) := by
      have hnum : 1 + 4 * aScale p ≤ 4 * totalScale p := by dsimp [totalScale]; linarith [hs.2.1]
      have h := Real.log_le_log (by positivity : 0 < 1 + 4 * aScale p) hnum
      rw [Real.log_mul (by norm_num) (by linarith [hs.2.2] : totalScale p ≠ 0)] at h
      have hfour : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
        linarith [Real.log_two_lt_d9]
      linarith
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_left htwo (sub_nonneg.mpr hq1')
    have hw := (warmScale_bounds p hp).2
    nlinarith

lemma count_algebra {a u K h w l v q n : ℝ}
    (ha : 0 ≤ a) (hu : 0 < u) (hK : 1 ≤ K) (hhu : u ≤ h)
    (hw : 0 ≤ w) (hl : 0 ≤ l) (hv : 0 ≤ v)
    (hwarm : w * (7 * h) ≤ 192 * u ^ 3 * K)
    (hlow : l ^ 3 ≤ 4320 * a ^ 3 * K ^ 2)
    (hhigh : v ^ 2 ≤ 240 * u ^ 3 * (q + 1) * K)
    (hq : q + 1 ≤ 10 * K + 2 * u) (hn : n ≤ w + l + v + q) :
    n ≤ 128 * (1 + a + u ^ 2) * K := by
  have hK0 : 0 ≤ K := by linarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have hu3 : 0 ≤ u ^ 3 * K := by positivity
  have hw' : w ≤ 28 * u ^ 2 * K := by
    apply (mul_le_mul_iff_left₀ hu).mp
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hhu)]
  have hl' : l ≤ 17 * a * K := by
    apply (pow_le_pow_iff_left₀ hl (show 0 ≤ 17 * a * K by positivity) (by decide : 3 ≠ 0)).mp
    have hKK' : K ^ 2 ≤ K ^ 3 := by nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
    calc
      _ ≤ 4320 * a ^ 3 * K ^ 2 := hlow
      _ ≤ 4913 * a ^ 3 * K ^ 3 := by gcongr; norm_num
      _ = (17 * a * K) ^ 3 := by ring
  have hu3' : u ^ 3 ≤ (1 + u ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg (u - 1)), pow_nonneg hu.le 3]
  have hu4 : u ^ 4 ≤ (1 + u ^ 2) ^ 2 := by nlinarith [sq_nonneg u]
  have hv' : v ≤ 54 * (1 + u ^ 2) * K := by
    apply (sq_le_sq₀ hv (by positivity)).mp
    have hqh := mul_le_mul_of_nonneg_left hq (show 0 ≤ 240 * u ^ 3 * K by positivity)
    have hbound : v ^ 2 ≤ 2400 * u ^ 3 * K ^ 2 + 480 * u ^ 4 * K := by nlinarith only [hhigh, hqh]
    calc
      _ ≤ 2400 * u ^ 3 * K ^ 2 + 480 * u ^ 4 * K := hbound
      _ ≤ 2400 * (1 + u ^ 2) ^ 2 * K ^ 2 + 480 * (1 + u ^ 2) ^ 2 * K ^ 2 := by gcongr
      _ ≤ 2916 * (1 + u ^ 2) ^ 2 * K ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (1 + u ^ 2)) (sq_nonneg K)]
      _ = (54 * (1 + u ^ 2) * K) ^ 2 := by ring
  have huQ : u ≤ 1 + a + u ^ 2 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hQ : 1 ≤ 1 + a + u ^ 2 := by nlinarith [sq_nonneg u]
  have huK : u ≤ (1 + a + u ^ 2) * K := huQ.trans (le_mul_of_one_le_right (by positivity) hK)
  have hKQ : K ≤ (1 + a + u ^ 2) * K := le_mul_of_one_le_left hK0 hQ
  have hq' : q ≤ 12 * (1 + a + u ^ 2) * K := by nlinarith only [hq, huK, hKQ]
  have hwQ : w ≤ 28 * (1 + a + u ^ 2) * K := hw'.trans (by gcongr; linarith)
  have hlQ : l ≤ 17 * (1 + a + u ^ 2) * K := hl'.trans (by gcongr; nlinarith [sq_nonneg u])
  have hvQ : v ≤ 54 * (1 + a + u ^ 2) * K := hv'.trans (by gcongr; linarith)
  nlinarith [mul_nonneg (show 0 ≤ 1 + a + u ^ 2 by positivity) hK0]

lemma movement_log_bound (p : Public) (hp : spec.valid p) {f : Point p → ℝ} {g : Point p → Point p}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range n, movement p f g k) ≤
      12 * p.R * (logScale p + Real.log (2 * n)) := by
  obtain ⟨hd, h0, h1, hR, he⟩ := hp
  have hp : spec.valid p := ⟨hd, h0, h1, hR, he⟩
  have hM := trajectory_movement p hd hconv hgrad hg h0 h1 hR he hgs xstar hmin hval hprior n
  have hdlog := bitlength_bound p.d hd
  have hnlog := bitlength_bound n hn
  have hld := (logScale_bounds p hp).2.2.1
  have hls := (logScale_bounds p hp).2.2.2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hprod := mul_le_mul hdlog hnlog (Nat.cast_nonneg (1 + Nat.log 2 n)) (by positivity)
  have hsqrt : Real.sqrt (((1 + Nat.log 2 p.d : ℕ) : ℝ) * (1 + Nat.log 2 n : ℕ)) ≤
      Real.log (2 * p.d) + Real.log (2 * n) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [sq_nonneg (Real.log (2 * p.d) - Real.log (2 * n))]⟩
  have hsum : Real.log (2 * p.d) + Real.log (2 * n) ≤ logScale p + Real.log (2 * n) := by
    dsimp only [logScale]
    linarith
  exact hM.trans (mul_le_mul_of_nonneg_left (hsqrt.trans hsum) (by positivity))

lemma unfinished_bound (p : Public) (hp : spec.valid p) {f : Point p → ℝ} {g : Point p → Point p}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) (n : ℕ) (hn : 0 < n)
    (hunfinished : (trajectory p f g n).finished = false) :
    (n : ℝ) ≤ 128 * size p * (logScale p + Real.log (2 * n)) := by
  obtain ⟨hd, h0, h1, hR, he⟩ := hp
  have hp : spec.valid p := ⟨hd, h0, h1, hR, he⟩
  let a := aScale p ^ (1 / 3 : ℝ)
  let u := bScale p ^ (1 / 3 : ℝ)
  let K := logScale p + Real.log (2 * n)
  let M := ∑ k ∈ Finset.range n, movement p f g k
  have hA := (scale_pos p hp).1
  have hB := (scale_pos p hp).2.1
  have ha : 0 ≤ a := Real.rpow_nonneg hA.le _
  have hu : 0 < u := Real.rpow_pos_of_pos hB _
  have ha3 : a ^ 3 = aScale p := root_cube hA.le
  have hu3 : u ^ 3 = bScale p := root_cube hB.le
  have hu2 : u ^ 2 = bScale p ^ (2 / 3 : ℝ) := root_square hB.le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have hK : 1 ≤ K := by dsimp only [K]; linarith [(logScale_bounds p hp).1]
  have hKlog : 1 + Real.log (totalScale p) ≤ K := by
    dsimp only [K]
    linarith [(logScale_bounds p hp).2.1]
  have hM : M ≤ 12 * p.R * K := movement_log_bound p hp hconv hgrad hg hgs xstar hmin hval hprior n hn
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hwarm : ((warmFailures p f g n).card : ℝ) * (7 * warmScale p) ≤ 192 * u ^ 3 * K := by
    have h := warm_failure_count p hd hconv hgrad hg h0 h1 hR he hgs xstar hmin hval hprior n
    calc
      _ ≤ 16 * p.L1 * M := h
      _ ≤ 16 * p.L1 * (12 * p.R * K) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by rw [hu3]; dsimp only [bScale]; ring
  have hlow : ((lowFailures p f g n).card : ℝ) ^ 3 ≤ 4320 * a ^ 3 * K ^ 2 := by
    have h := low_failure_count p hd hconv hgrad hg h0 h1 hR he hgs xstar hmin hval hprior n
    calc
      _ ≤ 30 * p.L0 / p.ε * M ^ 2 := h
      _ ≤ 30 * p.L0 / p.ε * (12 * p.R * K) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM 2) (by positivity)
      _ = _ := by rw [ha3]; dsimp only [aScale]; ring
  have hhigh : ((highFailures p f g n).card : ℝ) ^ 2 ≤
      240 * u ^ 3 * (((trajectory p f g n).phase : ℝ) + 1) * K := by
    have h := high_failure_count p hd hconv hgrad hg h0 h1 hR he hgs xstar hmin hval hprior n
    calc
      _ ≤ 20 * p.L1 * (1 + ((trajectory p f g n).phase : ℝ)) * M := h
      _ ≤ 20 * p.L1 * (1 + ((trajectory p f g n).phase : ℝ)) * (12 * p.R * K) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by rw [hu3]; dsimp only [bScale]; ring
  have hq : ((trajectory p f g n).phase : ℝ) + 1 ≤ 10 * K + 2 * u := by
    have h := phase_count_bound p hp f g n
    have hs := (logScale_bounds p hp).2.2.2
    change _ ≤ 10 * K + 2 * bScale p ^ (1 / 3 : ℝ)
    linarith
  have h := count_algebra ha hu hK (warmScale_bounds p hp).1
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hwarm hlow hhigh hq (round_partition p f g n hunfinished)
  simpa only [hu2, a, K, size] using h

lemma rounds_bounds (p : Public) (hp : spec.valid p) :
    0 < rounds p ∧ (2 : ℝ) ^ 30 * size p * logScale p ≤ rounds p ∧
      (rounds p : ℝ) ≤ (2 : ℝ) ^ 30 * size p * logScale p + 1 ∧
      (rounds p : ℝ) ≤ (2 : ℝ) ^ 31 * size p * logScale p := by
  have hQ := (size_bounds p hp).1
  have hL := (logScale_bounds p hp).1
  have hX : 0 < (2 : ℝ) ^ 30 * size p * logScale p := by positivity
  have hlo := Nat.le_ceil ((2 : ℝ) ^ 30 * size p * logScale p)
  have hhi := (Nat.ceil_lt_add_one hX.le).le
  have hprod : 1 ≤ size p * logScale p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hL)]
  refine ⟨?_, hlo, hhi, ?_⟩
  · have hpos : (0 : ℝ) < rounds p := hX.trans_le hlo
    exact_mod_cast hpos
  · change (⌈(2 : ℝ) ^ 30 * size p * logScale p⌉₊ : ℝ) ≤ _
    nlinarith

lemma rounds_log_bound (p : Public) (hp : spec.valid p) :
    Real.log (2 * rounds p) ≤ 36 * logScale p := by
  have hN := rounds_bounds p hp
  have hQ := (size_bounds p hp).1
  have hQhi := (size_bounds p hp).2
  have hL := (logScale_bounds p hp).1
  have hLS := (logScale_bounds p hp).2.1
  have hS := (scale_pos p hp).2.2
  have hNp : (0 : ℝ) < rounds p := by exact_mod_cast hN.1
  have hlogQ : Real.log (size p) ≤ 2 + Real.log (totalScale p) := by
    have h := Real.log_le_log (by positivity : 0 < size p) hQhi
    rw [Real.log_mul (by norm_num) (by linarith : totalScale p ≠ 0)] at h
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogL := Real.log_le_self (by linarith : 0 ≤ logScale p)
  have hnum : 2 * (rounds p : ℝ) ≤ (2 : ℝ) ^ 32 * size p * logScale p := by
    nlinarith [hN.2.2.2]
  have h := Real.log_le_log (by positivity : 0 < 2 * (rounds p : ℝ)) hnum
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 32 * size p ≠ 0) (by positivity),
    Real.log_mul (by positivity : (2 : ℝ) ^ 32 ≠ 0) (by positivity), Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_lt_d9]

lemma rounds_finished (p : Public) (hp : spec.valid p) {f : Point p → ℝ} {g : Point p → Point p}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (p.L0 + p.L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (xstar : Point p) (hmin : IsMinOn f univ xstar) (hval : f xstar = p.fstar)
    (hprior : ∑ i, |p.x0 i - xstar i| ≤ p.R) :
    (trajectory p f g (rounds p)).finished = true := by
  cases hf : (trajectory p f g (rounds p)).finished with
  | true => rfl
  | false =>
    have hQ := (size_bounds p hp).1
    have hL := (logScale_bounds p hp).1
    have hb := rounds_bounds p hp
    have h := unfinished_bound p hp hconv hgrad hg hgs xstar hmin hval hprior (rounds p) hb.1 hf
    have hlog := rounds_log_bound p hp
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 128 * size p by positivity)
    have hprod : 0 < size p * logScale p := by positivity
    nlinarith [hb.2.1]

lemma lineCalls_bound (p : Public) (hp : spec.valid p) : (lineCalls p : ℝ) ≤ 40 * logScale p := by
  let C := 1 + 32 * aScale p + 4 * bScale p
  let X := 128 * C ^ 2
  have hA := (scale_pos p hp).1
  have hB := (scale_pos p hp).2.1
  have hS := (scale_pos p hp).2.2
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC' : C ≤ 32 * totalScale p := by dsimp only [C, totalScale]; linarith
  have hX : 128 ≤ X := by dsimp only [X]; nlinarith
  have hceil := Nat.le_ceil X
  have hceilhi := (Nat.ceil_lt_add_one (show 0 ≤ X by linarith)).le
  have hceilpos : (0 : ℝ) < (⌈X⌉₊ : ℝ) := by linarith
  have hceilpos' : 0 < ⌈X⌉₊ := by exact_mod_cast hceilpos
  have hceil2 : (⌈X⌉₊ : ℝ) ≤ 2 * X := by linarith
  have hXhi : X ≤ (2 : ℝ) ^ 17 * totalScale p ^ 2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ C by linarith) hC' 2
    dsimp only [X]
    nlinarith only [h]
  have hceilhi' : (⌈X⌉₊ : ℝ) ≤ (2 : ℝ) ^ 18 * totalScale p ^ 2 := by nlinarith only [hceil2, hXhi]
  have hl := Real.log_le_log hceilpos hceilhi'
  rw [Real.log_mul (by positivity : (2 : ℝ) ^ 18 ≠ 0) (by positivity), Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have hnat := natLog_bound ⌈X⌉₊ hceilpos'
  have hcost : (lineCalls p : ℝ) = 3 + (Nat.log 2 ⌈X⌉₊ : ℝ) := by
    have hx : 128 * (1 + 32 * p.L0 * p.R ^ 2 / p.ε + 4 * p.L1 * p.R) ^ 2 = X := by
      dsimp only [X, C, aScale, bScale]
      ring
    simp only [lineCalls, midpointCount, hx, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hcost]
  have hLS := (logScale_bounds p hp).2.1
  have hlogS := (logScale_bounds p hp).2.2.2
  linarith [Real.log_two_lt_d9]

lemma budget_covers_blocks (p : Public) (hp : spec.valid p) :
    rounds p * lineCalls p ≤ ⌈(2 : ℝ) ^ 36 * size p * logScale p ^ 2⌉₊ := by
  have hN := (rounds_bounds p hp).2.2.1
  have hC := lineCalls_bound p hp
  have hQ := (size_bounds p hp).1
  have hL := (logScale_bounds p hp).1
  have hQL : 1 ≤ size p * logScale p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sub_nonneg.mpr hL)]
  have hL' : logScale p ≤ size p * logScale p ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hQL) (show 0 ≤ logScale p by linarith)]
  have h := mul_le_mul hN hC (Nat.cast_nonneg (lineCalls p)) (by positivity)
  have hh : (rounds p : ℝ) * lineCalls p ≤ (2 : ℝ) ^ 36 * size p * logScale p ^ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 30 * size p * logScale p + 1) * (40 * logScale p) := h
      _ = 40 * (2 : ℝ) ^ 30 * size p * logScale p ^ 2 + 40 * logScale p := by ring
      _ ≤ 40 * (2 : ℝ) ^ 30 * size p * logScale p ^ 2 + 40 * (size p * logScale p ^ 2) := by gcongr
      _ ≤ (2 : ℝ) ^ 36 * size p * logScale p ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ size p by linarith) (sq_nonneg (logScale p))]
  have hh' := hh.trans (Nat.le_ceil ((2 : ℝ) ^ 36 * size p * logScale p ^ 2))
  exact_mod_cast hh'

end LongTails.Proofs.KnownValueNondualBudget
