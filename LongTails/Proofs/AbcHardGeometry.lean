import LongTails.Proofs.AbcHardFunction

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardGeometry

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.AbcChain
open LongTails.Proofs.AbcChainProperties LongTails.Proofs.AbcChainMask
open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.AbcHardFunction

variable {d n : ℕ}

lemma sqrt_bounds (n : ℕ) : 1 ≤ Real.sqrt (n + 1) ∧ Real.sqrt (n + 1) ≤ n + 1 := by
  refine ⟨?_, sqrt_le_self_succ n⟩
  rw [Real.one_le_sqrt]
  have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith

lemma hardGrad_lipschitz_near (π : Fin (n + 1) ↪ Fin d) (x y : Space d)
    (hx : ‖x‖ ≤ 3 * radius n) (hy : ‖y‖ ≤ 3 * radius n) :
    ‖hardGrad π x - hardGrad π y‖ ≤ 1024 * ‖x - y‖ := by
  have hR := radius_pos n
  have hs := sqrt_bounds n
  let M := 27 * Real.sqrt (n + 1) + 6
  have hf : ‖(sel π).adjoint (field (sel π x)) - (sel π).adjoint (field (sel π y))‖ ≤
      1000 * ‖x - y‖ := by
    rw [← map_sub]
    refine (adjoint_norm π _).trans ((field_lipschitz _ _).trans ?_)
    rw [← map_sub]
    exact mul_le_mul_of_nonneg_left (sel_norm π _) (by norm_num)
  have hg : ‖wallGrad n x - wallGrad n y‖ ≤ 1000 * ‖x - y‖ := by
    refine (wallGrad_lipschitz n x y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    unfold radius
    rw [div_le_iff₀ (by positivity)]
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  have hv : |chain (sel π x) - chain (sel π y)| + |wallFn n x - wallFn n y| ≤ M * ‖x - y‖ := by
    have h1 := chainSel_value_lipschitz π x y
    have h2 := wall_value_lipschitz n (3 * radius n) x y hx hy
    have he : 2 * (3 * radius n) / radius n = 6 := by rw [div_eq_iff hR.ne']; ring
    rw [he] at h2
    dsimp only [M]
    nlinarith [norm_nonneg (x - y)]
  have hn : ‖(sel π).adjoint (field (sel π y))‖ + ‖wallGrad n y‖ ≤ M := by
    have h1 := (adjoint_norm π _).trans (field_norm (sel π y))
    have h2 : ‖wallGrad n y‖ ≤ 6 := by
      rw [wallGrad_norm, div_le_iff₀ hR]; linarith
    dsimp only [M]; linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have h := smoothMax_field_lipschitz (width n) M 1000 (width_pos n) hM
    (fun z => chain (sel π z)) (wallFn n) (fun z => (sel π).adjoint (field (sel π z)))
    (wallGrad n) x y hf hg hv hn
  have hMw : M ^ 2 / width n ≤ 24 := by
    rw [div_le_iff₀ (width_pos n)]
    dsimp only [M, width]
    have hq : Real.sqrt (n + 1) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

lemma hardGrad_lipschitz_far (π : Fin (n + 1) ↪ Fin d) (x y : Space d)
    (hy : 3 * radius n < ‖y‖) : ‖hardGrad π x - hardGrad π y‖ ≤ 1024 * ‖x - y‖ := by
  have hR := radius_pos n
  have hs := sqrt_bounds n
  rw [hardGrad_outside π y (by linarith)]
  by_cases hx : 2 * radius n ≤ ‖x‖
  · rw [hardGrad_outside π x hx]
    refine (wallGrad_lipschitz n x y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    unfold radius
    rw [div_le_iff₀ (by positivity)]
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  · push Not at hx
    have hd : radius n ≤ ‖x - y‖ := by
      have h := norm_sub_norm_le y x
      rw [norm_sub_rev] at h
      linarith
    let t := weight (width n) (chain (sel π x)) (wallFn n x)
    have ht : 0 ≤ t := weight_nonneg _ _ _
    have ht' : t ≤ 1 := weight_le_one _ _ _
    have he : hardGrad π x - wallGrad n y =
        t • ((sel π).adjoint (field (sel π x)) - wallGrad n x) + (wallGrad n x - wallGrad n y) := by
      simp only [hardGrad, t]
      module
    rw [he]
    have h1 : ‖(sel π).adjoint (field (sel π x)) - wallGrad n x‖ ≤ radius n := by
      have ha := (adjoint_norm π _).trans (field_norm (sel π x))
      have hw : ‖wallGrad n x‖ ≤ 4 := by
        rw [wallGrad_norm, div_le_iff₀ hR]; linarith
      have hb : 27 * Real.sqrt (n + 1) + 4 ≤ radius n := by
        unfold radius; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); nlinarith
      exact (norm_sub_le _ _).trans (by linarith)
    have h2 := wallGrad_lipschitz n x y
    have h3 : 2 / radius n ≤ 1 := by
      unfold radius
      rw [div_le_iff₀ (by positivity)]
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith
    calc _ ≤ ‖t • ((sel π).adjoint (field (sel π x)) - wallGrad n x)‖ +
          ‖wallGrad n x - wallGrad n y‖ := norm_add_le _ _
      _ ≤ 1 * radius n + 1 * ‖x - y‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht]
          gcongr
          · exact h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
      _ ≤ 1024 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]

lemma hardGrad_lipschitz (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    ‖hardGrad π x - hardGrad π y‖ ≤ 1024 * ‖x - y‖ := by
  by_cases hx : ‖x‖ ≤ 3 * radius n
  · by_cases hy : ‖y‖ ≤ 3 * radius n
    · exact hardGrad_lipschitz_near π x y hx hy
    · exact hardGrad_lipschitz_far π x y (lt_of_not_ge hy)
  · have h := hardGrad_lipschitz_far π y x (lt_of_not_ge hx)
    rwa [norm_sub_rev, norm_sub_rev y x] at h

lemma abs_apply_le_norm (x : Space d) (j : Fin d) : |x j| ≤ ‖x‖ := by
  have h : x j ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i))
      (Finset.mem_univ j)
  rw [← sq_abs] at h
  nlinarith [abs_nonneg (x j), norm_nonneg x]

lemma hardGrad_lower (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (hu : |sel π w (Fin.last n)| < 1) : 1 / 20 ≤ ‖hardGrad π w‖ := by
  have hR := radius_pos n
  obtain ⟨k, hk⟩ := field_large_coordinate (sel π w) hu
  let t := weight (width n) (chain (sel π w)) (wallFn n w)
  have ht : 0 ≤ t := weight_nonneg _ _ _
  have ht' : t ≤ 1 := weight_le_one _ _ _
  have hcoord : hardGrad π w (π k) = t * field (sel π w) k + (1 - t) * wallGrad n w (π k) := by
    simp only [hardGrad, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, adjoint_apply_emb, t]
  by_cases h1 : ‖w‖ ≤ radius n / 2
  · have ht1 : t = 1 := (weight_one_inside π 0 w h1).2.1
    have hc := abs_apply_le_norm (hardGrad π w) (π k)
    rw [hcoord, ht1] at hc
    simp only [one_mul, sub_self, zero_mul, add_zero] at hc
    have : 1 ≤ |field (sel π w) k| := by rw [abs_of_neg (by linarith)]; linarith
    linarith
  · push Not at h1
    by_cases h2 : 2 * radius n ≤ ‖w‖
    · rw [hardGrad_outside π w h2, wallGrad_norm]
      rw [le_div_iff₀ hR]
      linarith
    · push Not at h2
      have hgw : ‖wallGrad n w‖ ≤ 4 := by rw [wallGrad_norm, div_le_iff₀ hR]; linarith
      have ha : t - 4 * (1 - t) ≤ ‖hardGrad π w‖ := by
        have hc := abs_apply_le_norm (hardGrad π w) (π k)
        rw [hcoord] at hc
        have hw1 := (abs_apply_le_norm (wallGrad n w) (π k)).trans hgw
        have hb : |(1 - t) * wallGrad n w (π k)| ≤ 4 * (1 - t) := by
          rw [abs_mul, abs_of_nonneg (by linarith)]; nlinarith
        have hf1 : |t * field (sel π w) k| ≥ t := by
          rw [abs_mul, abs_of_nonneg ht, abs_of_neg (by linarith)]; nlinarith
        have := abs_sub_abs_le_abs_sub (t * field (sel π w) k) (-((1 - t) * wallGrad n w (π k)))
        rw [abs_neg, sub_neg_eq_add] at this
        linarith
      have hb : (1 - t) - 108 * ((n : ℝ) + 1) / radius n ≤ ‖hardGrad π w‖ := by
        have hwpos : 0 < ‖w‖ := by linarith
        have hin : ⟪hardGrad π w, w⟫ ≤ ‖hardGrad π w‖ * ‖w‖ := real_inner_le_norm _ _
        have hval : ⟪hardGrad π w, w⟫ = t * ⟪field (sel π w), sel π w⟫ +
            (1 - t) * (2 / radius n * ‖w‖ ^ 2) := by
          simp only [hardGrad, wallGrad, inner_add_left, real_inner_smul_left, t,
            ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
        have hf := inner_field_self (sel π w)
        rw [hval] at hin
        have hk1 : t * ⟪field (sel π w), sel π w⟫ ≥ -54 * ((n : ℝ) + 1) := by
          have := mul_le_mul_of_nonneg_left hf ht
          have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
          nlinarith
        have hk2 : (1 - t) * (2 / radius n * ‖w‖ ^ 2) ≥ (1 - t) * ‖w‖ := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_mul_eq_mul_div, le_div_iff₀ hR]
          nlinarith
        have hdiv : 54 * ((n : ℝ) + 1) ≤ 108 * ((n : ℝ) + 1) / radius n * ‖w‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hR]
          nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        nlinarith
      have hr : 108 * ((n : ℝ) + 1) / radius n = 108 / 2048 := by
        unfold radius
        rw [div_eq_div_iff (by positivity) (by norm_num)]
        ring
      rw [hr] at hb
      by_cases h3 : 3 / 20 ≤ 1 - t
      · linarith
      · push Not at h3; linarith

lemma secret_bound (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |sel π w i| ≤ 1 / 4) :
    ‖hardGrad π w - knownGrad π m w‖ ≤ 29 := by
  have hR := radius_pos n
  by_cases hout : 2 * radius n ≤ ‖w‖
  · rw [hardGrad_outside π w hout, knownGrad_outside π m w hout, sub_self, norm_zero]
    norm_num
  · push Not at hout
    let t := weight (width n) (chain (sel π w)) (wallFn n w)
    let s := weight (width n) (chain (trunc m (sel π w))) (wallFn n w)
    have ht : 0 ≤ t := weight_nonneg _ _ _
    have ht' : t ≤ 1 := weight_le_one _ _ _
    have he : hardGrad π w - knownGrad π m w =
        t • (sel π).adjoint (field (sel π w) - knownField m (sel π w)) +
          (t - s) • ((sel π).adjoint (knownField m (sel π w)) - wallGrad n w) := by
      simp only [hardGrad, knownGrad, map_sub, t, s]
      module
    rw [he]
    have h1 : ‖t • (sel π).adjoint (field (sel π w) - knownField m (sel π w))‖ ≤ 28 := by
      rw [norm_smul, Real.norm_of_nonneg ht]
      have := (adjoint_norm π _).trans (secret_field_bound m (sel π w) hs)
      nlinarith [norm_nonneg ((sel π).adjoint (field (sel π w) - knownField m (sel π w)))]
    have hts : |t - s| ≤ 1 / 2 / width n := by
      have h := weight_lipschitz (width n) (chain (sel π w)) (wallFn n w)
        (chain (trunc m (sel π w))) (wallFn n w) (width_pos n)
      rw [sub_self, abs_zero, add_zero] at h
      exact h.trans (div_le_div_of_nonneg_right (chain_trunc_close m _ hs) (width_pos n).le)
    have hk : ‖(sel π).adjoint (knownField m (sel π w)) - wallGrad n w‖ ≤
        27 * Real.sqrt (n + 1) + 4 := by
      have ha := ((adjoint_norm π _).trans (knownField_norm_le m _)).trans (field_norm (sel π w))
      have hw : ‖wallGrad n w‖ ≤ 4 := by rw [wallGrad_norm, div_le_iff₀ hR]; linarith
      exact (norm_sub_le _ _).trans (by linarith)
    have h2 : ‖(t - s) • ((sel π).adjoint (knownField m (sel π w)) - wallGrad n w)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hsq := sqrt_bounds n
      have hb : 1 / 2 / width n * (27 * Real.sqrt (n + 1) + 4) ≤ 1 := by
        unfold width
        rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        nlinarith
      calc _ ≤ 1 / 2 / width n * (27 * Real.sqrt (n + 1) + 4) :=
            mul_le_mul hts hk (norm_nonneg _) (by have := width_pos n; positivity)
        _ ≤ 1 := hb
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ 29 := by linarith

lemma hardValue_gap (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (w : Space d)
    (hs : ∀ i : Fin (n + 1), m ≤ i.val → |sel π w i| ≤ 1 / 4) :
    3 * ((n : ℝ) - m) ≤ hardValue π w - -3 * ((n : ℝ) + 1) := by
  have h := (chain_gap (sel π w) m hs).trans (hardValue_ge π w)
  linarith

end LongTails.Proofs.AbcHardGeometry
