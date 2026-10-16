import LongTails.Proofs.OnlineMetricMain
import LongTails.Proofs.Execution
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

open LongTails.Setups.DiagonalSmoothStronglyConvex

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)}

noncomputable def secantBox (f : EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : ℝ :=
  1 / (gradient f (x0 + EuclideanSpace.single i 1) i - gradient f x0 i)

noncomputable def initState (f : EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (j : ℕ) : Core d :=
  { initialCore x0 with
    stage := j
    fs := if j = 0 then 0 else f x0
    b := fun i => if i.val < j then secantBox f x0 i else 1 }

lemma initState_zero (f : EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) :
    initState f x0 0 = initialCore x0 := by
  simp [initState, initialCore]

lemma macro_init [NeZero d] {j : ℕ} (hj : j < d) :
    macroStep fstar x0 f (initState f x0 j) = initState f x0 (j + 1) := by
  have hs : (initState f x0 j).stage < d := hj
  simp only [macroStep, resolve, firstQuery, secondQuery, hs, ↓reduceIte, ↓reduceDIte]
  simp only [initResolve, initState, initialCore]
  congr 1
  funext i
  by_cases h1 : i.val = j
  · have hi : i = ⟨j, hj⟩ := Fin.ext h1
    subst hi
    simp [secantBox]
  · by_cases h2 : i.val < j
    · have h3 : i.val < j + 1 := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ i.val < j + 1 := by omega
      simp [h1, h2, h3]

lemma iterate_init [NeZero d] {j : ℕ} (hj : j ≤ d) :
    (macroStep fstar x0 f)^[j] (initialCore x0) = initState f x0 j := by
  induction j with
  | zero => simp [initState_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), macro_init (by omega)]

lemma secant_mem (H : Hyp f w μ fstar xstar) (i : Fin d) :
    1 / w i ≤ secantBox f x0 i ∧ secantBox f x0 i ≤ 1 / (μ * w i) := by
  obtain ⟨h1, h2⟩ := secant_bounds H.smooth H.sc x0 i
  have hw := H.w_pos i
  have hμ := H.μ_pos
  have hpos : 0 < gradient f (x0 + EuclideanSpace.single i 1) i - gradient f x0 i :=
    lt_of_lt_of_le (by positivity) h1
  unfold secantBox
  exact ⟨one_div_le_one_div_of_le hpos h2, one_div_le_one_div_of_le (by positivity) h1⟩

lemma inv_init [NeZero d] (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ)) :
    Inv f w μ fstar x0 (secantBox f x0) (initState f x0 d) 0 := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hb : (initState f x0 d).b = secantBox f x0 := by
    funext i; simp [initState]
  have hfs : (initState f x0 d).fs = f x0 := by simp [initState, hd0]
  refine ⟨rfl, ?_, ?_, ⟨fun i => fresh_band hd i, le_rfl⟩, ⟨fun i => fresh_band hd i, le_rfl⟩,
    ?_, hfs, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact fun i => (secant_mem H i).1
  · refine ⟨fun _ => 0, fun i => by rw [hb]; simp, by simp [initState, initialCore]⟩
  · show (freshLearner d).φ = (learnerFor _ 0).φ
    unfold learnerFor; simp [initState, initialCore]
  · show (initState f x0 d).fs - fstar ≤ (f x0 - fstar) / 2 ^ 0
    rw [hfs]; simp
  · intro u
    simp [initState, initialCore]
  · show stepScale (initState f x0 d) * (((0 : ℕ) : ℝ) * ((0 : ℕ) + 1)) / 4 ≤ 0
    simp
  · intro h; simp [initState, initialCore] at h
  · intro a ha; simp [initState, initialCore] at ha
  · show 1 / stepScale (initState f x0 d) ≤ (bestCut [] _).1
    simp [stepScale, bestCut, initState, initialCore]
  · show PrevOK f w μ fstar (initState f x0 d)
    simp [PrevOK, initState, initialCore]
  · refine ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, ?_, ?_, ?_, ?_, fresh_ledger _ _ _ _,
      fresh_ledger _ _ _ _, ?_⟩ <;> simp [initState, initialCore, prevSeg, prevSteps]

lemma logTwo_eq (hd : 1 ≤ (d : ℝ)) : logTwo d = 1 + Real.logb 2 d := by
  unfold logTwo
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]

lemma logTwo_le (hd : 1 ≤ (d : ℝ)) : logTwo d ≤ 2 * (1 + Real.log (2 * d)) ^ 2 := by
  unfold logTwo Real.logb
  have hl2 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma seg_le (H : Hyp f w μ fstar xstar) {b0 : Fin d → ℝ} (hb0 : ∀ i, b0 i ≤ 1 / (μ * w i))
    {s : Core d} {n : ℕ} (I : Inv f w μ fstar x0 b0 s n) :
    s.seg ≤ d * ⌈Real.logb 2 (1 / μ)⌉₊ := by
  obtain ⟨m, hm, hseg⟩ := I.box_pow
  rw [hseg]
  have hμ := H.μ_pos
  have hmi : ∀ i, m i ≤ ⌈Real.logb 2 (1 / μ)⌉₊ := by
    intro i
    have hw := H.w_pos i
    have h1 := I.box_ge i
    rw [hm i] at h1
    have h2 : (2 : ℝ) ^ m i ≤ 1 / μ := by
      have hb := hb0 i
      have hpow : (0 : ℝ) < 2 ^ m i := by positivity
      rw [le_div_iff₀ hpow] at h1
      have : 1 / w i * 2 ^ m i ≤ 1 / (μ * w i) := le_trans h1 hb
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hw (by positivity)] at this
      rw [le_div_iff₀ hμ]; nlinarith
    have h3 : (m i : ℝ) ≤ Real.logb 2 (1 / μ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      exact_mod_cast h2
    exact Nat.cast_le.mp ((h3.trans (Nat.le_ceil _)))
  calc ∑ i, m i ≤ ∑ _i : Fin d, ⌈Real.logb 2 (1 / μ)⌉₊ := Finset.sum_le_sum fun i _ => hmi i
    _ = d * ⌈Real.logb 2 (1 / μ)⌉₊ := by simp

lemma cap_bound {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hd : 1 ≤ (d : ℝ)) :
    9 / 2 * bandWidth d ^ 2 * lossCap d μ + 2 * (runCap d μ + 2 + logTwo d) ≤
      110 * d ^ 2 * (1 + Real.log (2 * d)) ^ 2 * Real.sqrt (1 / μ) := by
  have hr : 1 ≤ Real.sqrt (1 / μ) := kappaRoot_ge_one hμ hμ1
  have hl : 0 ≤ Real.log (2 * d) := Real.log_nonneg (by linarith)
  have hlt := logTwo_le hd
  set r := Real.sqrt (1 / μ)
  set ℓ := Real.log (2 * d)
  set q := (1 + ℓ) ^ 2
  have hq : 1 ≤ q := by nlinarith
  have hℓq : ℓ ^ 2 ≤ q := by nlinarith
  have hd2 : (d : ℝ) ≤ d ^ 2 := by nlinarith
  have hw2 : bandWidth d ^ 2 = d * ℓ ^ 2 := by
    unfold bandWidth; rw [mul_pow, Real.sq_sqrt (by linarith)]
  set P := (d : ℝ) ^ 2 * q * r
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ d ^ 2 := by nlinarith
    have h1 : (1 : ℝ) ≤ d ^ 2 * q := by nlinarith
    nlinarith
  have t1 : 9 / 2 * bandWidth d ^ 2 * lossCap d μ ≤ 153 / 2 * P := by
    rw [hw2]
    unfold lossCap kappaRoot
    have : (d : ℝ) ^ 2 * ℓ ^ 2 * r ≤ d ^ 2 * q * r := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hℓq (by positivity)
    have e : 9 / 2 * (d * ℓ ^ 2) * (17 * d * r) = 153 / 2 * (d ^ 2 * ℓ ^ 2 * r) := by ring
    rw [e]; simp only [P]; linarith
  have t2 : runCap d μ ≤ 8 * P := by
    unfold runCap kappaRoot
    have : (d : ℝ) * r ≤ d ^ 2 * q * r := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      nlinarith
    simp only [P]; linarith
  have t3 : logTwo d ≤ 2 * P := by
    have : q ≤ P := by
      have : (1 : ℝ) ≤ d ^ 2 * r := by nlinarith
      simp only [P]; nlinarith
    linarith
  have hfinal : 9 / 2 * bandWidth d ^ 2 * lossCap d μ + 2 * (runCap d μ + 2 + logTwo d) ≤
      110 * P := by linarith
  simp only [P] at hfinal
  linarith

lemma count_bound (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    {b0 : Fin d → ℝ} (hb0 : ∀ i, b0 i ≤ 1 / (μ * w i)) {s : Core d} {n J : ℕ}
    (I : Inv f w μ fstar x0 b0 s n) (hJ : s.ep < J) :
    (n : ℝ) ≤ J * (24 * Real.sqrt (1 / μ) + Real.logb 2 d + 2) +
      ((d * ⌈Real.logb 2 (1 / μ)⌉₊ : ℕ) + 1 : ℝ) *
        (110 * d ^ 2 * (1 + Real.log (2 * d)) ^ 2 * Real.sqrt (1 / μ)) := by
  obtain ⟨Xc, X0, X0', X1, X1', nc, n0, n1, ndrop, hep, hd1, hd2, hXc, hL0, hL1, hn⟩ := I.ledger
  have hμ := H.μ_pos
  have hD := bandWidth_pos hd
  have hF := lossCap_nonneg (d := d) hμ
  have hc0 := ledger_close hD hF hL0
  have hc1 := ledger_close hD hF hL1
  have hk := I.k_le H hd
  have hcl := I.cuts_len hd
  have hlg := logTwo_nonneg hd
  have hrc := runCap_nonneg (d := d) hμ
  have hps : (prevSteps s : ℝ) ≤ runCap d μ + 1 + logTwo d := by
    have hp := I.prev
    unfold PrevOK at hp
    unfold prevSteps
    cases hR : s.prev with
    | none => simp; linarith
    | some R => rw [hR] at hp; exact hp.2.2.2.2.2.2.2.2.2
  have hfedN : nc + n0 + n1 + 1 ≤ J := by
    have : nc + n0 + n1 ≤ s.ep := by rw [hep]; split_ifs <;> omega
    omega
  have hfed : (nc : ℝ) + n0 + n1 + 1 ≤ J := by exact_mod_cast hfedN
  have hdrop : (ndrop : ℝ) ≤ s.seg := by exact_mod_cast hd1.trans hd2
  have hsegN := seg_le H hb0 I
  have hsegK : (s.seg : ℝ) ≤ ((d * ⌈Real.logb 2 (1 / μ)⌉₊ : ℕ) : ℝ) := by exact_mod_cast hsegN
  have hcap := cap_bound hμ H.μ_le hd
  set Y := 9 / 2 * bandWidth d ^ 2 * lossCap d μ + 2 * (runCap d μ + 2 + logTwo d) with hYdef
  set Z := 110 * (d : ℝ) ^ 2 * (1 + Real.log (2 * d)) ^ 2 * Real.sqrt (1 / μ)
  set X := 24 * Real.sqrt (1 / μ) + Real.logb 2 d + 2
  have hX : 1 + logTwo d + 24 * kappaRoot μ = X := by
    rw [logTwo_eq hd]; simp only [X, kappaRoot]; ring
  have hYnn : 0 ≤ Y := by
    have := runCap_nonneg (d := d) hμ
    rw [hYdef]; positivity
  have hXnn : 0 ≤ X := by
    have := Real.logb_nonneg (b := 2) (by norm_num) hd
    simp only [X]; positivity
  have hnd : (ndrop : ℝ) * (runCap d μ + 1 + logTwo d) ≤
      s.seg * (runCap d μ + 1 + logTwo d) := mul_le_mul_of_nonneg_right hdrop (by linarith)
  have hmain : (n : ℝ) ≤ (nc + n0 + n1) * X + (s.seg + 1) * Y := by
    rw [← hX, hYdef]
    linarith
  have h1 : ((nc : ℝ) + n0 + n1) * X ≤ J * X :=
    mul_le_mul_of_nonneg_right (by linarith) hXnn
  have h2 : ((s.seg : ℝ) + 1) * Y ≤ (((d * ⌈Real.logb 2 (1 / μ)⌉₊ : ℕ) : ℝ) + 1) * Y :=
    mul_le_mul_of_nonneg_right (by linarith) hYnn
  have h3 : (((d * ⌈Real.logb 2 (1 / μ)⌉₊ : ℕ) : ℝ) + 1) * Y ≤
      (((d * ⌈Real.logb 2 (1 / μ)⌉₊ : ℕ) : ℝ) + 1) * Z :=
    mul_le_mul_of_nonneg_left hcap (by positivity)
  linarith

end OracleTemplate.OnlineMetricAccelerated
