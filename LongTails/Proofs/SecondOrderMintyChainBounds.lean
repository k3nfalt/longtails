import LongTails.Proofs.SecondOrderMintyChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SecondOrderMintyChain

open SecondOrderMintyProfile LocalizedMonotoneConstruction ContinuousLinearMap

lemma coordinate_sum_le {d m : ℕ} (π : Fin m ↪ Fin d) (z : Space d) :
    ∑ j : Fin m, z (π j) ^ 2 ≤ ‖z‖ ^ 2 := by
  have hcoord := pow_le_pow_left₀
    (norm_nonneg (FiniteSumNondualLowerComponents.coordinateMap π z))
    (FiniteSumNondualLowerComponents.coordinateMap_norm π z) 2
  rw [EuclideanSpace.real_norm_sq_eq] at hcoord
  exact hcoord

lemma coordinate_le {d : ℕ} (x : Space d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i

lemma castSucc_sum_le {n : ℕ} (f : Fin (n + 1) → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ j : Fin n, f j.castSucc ≤ ∑ i : Fin (n + 1), f i := by
  rw [Fin.sum_univ_castSucc]
  linarith [hf (Fin.last n)]

lemma succ_sum_le {n : ℕ} (f : Fin (n + 1) → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ j : Fin n, f j.succ ≤ ∑ i : Fin (n + 1), f i := by
  rw [Fin.sum_univ_succ]
  linarith [hf 0]

lemma sq_le_of_abs_le {a b : ℝ} (h : |a| ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have := pow_le_pow_left₀ (abs_nonneg a) h 2
  rwa [sq_abs] at this

lemma bidiagonal_norm_le {d n : ℕ} (π : Fin (n + 1) ↪ Fin d) (M : Space d →L[ℝ] Space d)
    (h0 : ℝ) (p q : Fin n → ℝ)
    (hM0 : ∀ z, M z (π 0) = h0 * z (π 0))
    (hMs : ∀ z j, M z (π j.succ) = p j * z (π j.castSucc) + q j * z (π j.succ))
    (hMo : ∀ z i, (∀ j, i ≠ π j) → M z i = 0)
    {A B C K : ℝ} (hA : |h0| ≤ A) (hB : ∀ j, |p j| ≤ B) (hC : ∀ j, |q j| ≤ C) (hK : 0 ≤ K)
    (hABC : A ^ 2 + 2 * B ^ 2 + 2 * C ^ 2 ≤ K ^ 2) : ‖M‖ ≤ K := by
  apply M.opNorm_le_bound hK
  intro z
  set S := ∑ i : Fin (n + 1), z (π i) ^ 2 with hSdef
  have hS : S ≤ ‖z‖ ^ 2 := coordinate_sum_le π z
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsq : ‖M z‖ ^ 2 ≤ K ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_sq_supported π _ (hMo z), Fin.sum_univ_succ]
    simp only [hM0, hMs]
    have hz0 : z (π 0) ^ 2 ≤ S := by
      rw [hSdef, Fin.sum_univ_succ]
      have : 0 ≤ ∑ j : Fin n, z (π j.succ) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      linarith
    have hc := castSucc_sum_le (fun i => z (π i) ^ 2) (fun i => sq_nonneg _)
    have hs := succ_sum_le (fun i => z (π i) ^ 2) (fun i => sq_nonneg _)
    have hterm : ∀ j : Fin n, (p j * z (π j.castSucc) + q j * z (π j.succ)) ^ 2 ≤
        2 * B ^ 2 * z (π j.castSucc) ^ 2 + 2 * C ^ 2 * z (π j.succ) ^ 2 := by
      intro j
      have hp := sq_le_of_abs_le (hB j)
      have hq := sq_le_of_abs_le (hC j)
      have h1 := mul_le_mul_of_nonneg_right hp (sq_nonneg (z (π j.castSucc)))
      have h2 := mul_le_mul_of_nonneg_right hq (sq_nonneg (z (π j.succ)))
      nlinarith [sq_nonneg (p j * z (π j.castSucc) - q j * z (π j.succ))]
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hh0 : (h0 * z (π 0)) ^ 2 ≤ A ^ 2 * S := by
      have := sq_le_of_abs_le hA
      rw [mul_pow]
      exact (mul_le_mul_of_nonneg_right this (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hz0 (sq_nonneg _))
    have hB2 : 0 ≤ 2 * B ^ 2 := by positivity
    have hC2 : 0 ≤ 2 * C ^ 2 := by positivity
    calc
      _ ≤ A ^ 2 * S + (2 * B ^ 2 * S + 2 * C ^ 2 * S) := by
        have e1 := mul_le_mul_of_nonneg_left hc hB2
        have e2 := mul_le_mul_of_nonneg_left hs hC2
        linarith
      _ = (A ^ 2 + 2 * B ^ 2 + 2 * C ^ 2) * S := by ring
      _ ≤ K ^ 2 * ‖z‖ ^ 2 := mul_le_mul hABC hS hS0 (sq_nonneg K)
  have hn : 0 ≤ K * ‖z‖ := by positivity
  nlinarith [norm_nonneg (M z)]

lemma mul_sub_mul_abs (a b c e : ℝ) : |a * b - c * e| ≤ |a - c| * |b| + |c| * |b - e| := by
  have he : a * b - c * e = (a - c) * b + c * (b - e) := by ring
  rw [he, ← abs_mul, ← abs_mul]
  exact abs_add_le _ _

lemma headSlope_abs (κ r t : ℝ) (hκ : 0 ≤ κ) : |headSlope κ r t| ≤ 2 * κ := by
  have h := satSlope_bounds (t / r - 1)
  rw [headSlope, abs_mul, abs_of_nonneg hκ, abs_of_nonneg h.1]
  nlinarith

lemma linkIn_abs (κ r s t : ℝ) (hκ : 0 ≤ κ) : |linkIn κ r s t| ≤ 8 * κ := by
  have h := gateSlope_bounds (s / r)
  have h2 := sat_bounds (t / r - 1)
  rw [linkIn, abs_mul, abs_of_nonneg hκ, abs_mul, abs_of_nonneg h.1]
  have : gateSlope (s / r) * |sat (t / r - 1)| ≤ 8 := by nlinarith [abs_nonneg (sat (t / r - 1))]
  nlinarith

lemma linkOut_abs (κ r s t : ℝ) (hκ : 0 ≤ κ) : |linkOut κ r s t| ≤ 2 * κ := by
  have h := gate_bounds (s / r)
  have h2 := satSlope_bounds (t / r - 1)
  rw [linkOut, abs_mul, abs_of_nonneg hκ, abs_mul, abs_of_nonneg h.1, abs_of_nonneg h2.1]
  have : gate (s / r) * satSlope (t / r - 1) ≤ 2 := by nlinarith
  nlinarith

lemma chainJacobian_norm {d n : ℕ} (κ r : ℝ) (hκ : 0 ≤ κ) (π : Fin (n + 1) ↪ Fin d)
    (x : Space d) : ‖chainJacobian κ r π x‖ ≤ 12 * κ := by
  apply bidiagonal_norm_le π _ (headSlope κ r (x (π 0)))
    (fun j => linkIn κ r (x (π j.castSucc)) (x (π j.succ)))
    (fun j => linkOut κ r (x (π j.castSucc)) (x (π j.succ)))
    (chainJacobian_zero κ r π x) (chainJacobian_succ κ r π x)
    (chainJacobian_outside κ r π x) (headSlope_abs κ r _ hκ)
    (fun j => linkIn_abs κ r _ _ hκ) (fun j => linkOut_abs κ r _ _ hκ) (by positivity)
  nlinarith

lemma scaled_abs (r a b : ℝ) (hr : 0 < r) : |a / r - b / r| = |a - b| / r := by
  rw [← sub_div, abs_div, abs_of_pos hr]

lemma headSlope_difference (κ r s t : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) :
    |headSlope κ r s - headSlope κ r t| ≤ 4 * κ / r * |s - t| := by
  have h := satSlope_lipschitz (s / r - 1) (t / r - 1)
  have he : s / r - 1 - (t / r - 1) = s / r - t / r := by ring
  rw [he, scaled_abs r s t hr] at h
  have hd : headSlope κ r s - headSlope κ r t =
      κ * (satSlope (s / r - 1) - satSlope (t / r - 1)) := by simp only [headSlope]; ring
  rw [hd, abs_mul, abs_of_nonneg hκ]
  calc
    κ * |satSlope (s / r - 1) - satSlope (t / r - 1)| ≤ κ * (4 * (|s - t| / r)) :=
      mul_le_mul_of_nonneg_left h hκ
    _ = 4 * κ / r * |s - t| := by ring

lemma linkIn_difference (κ r s t s' t' : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) :
    |linkIn κ r s t - linkIn κ r s' t'| ≤ κ / r * (128 * |s - s'| + 16 * |t - t'|) := by
  have hg := gateSlope_lipschitz (s / r) (s' / r)
  rw [scaled_abs r s s' hr] at hg
  have hs := sat_difference (t / r - 1) (t' / r - 1)
  have he : t / r - 1 - (t' / r - 1) = t / r - t' / r := by ring
  rw [he, scaled_abs r t t' hr] at hs
  have hb := sat_bounds (t / r - 1)
  have hgb := gateSlope_bounds (s' / r)
  have hm := mul_sub_mul_abs (gateSlope (s / r)) (sat (t / r - 1)) (gateSlope (s' / r))
    (sat (t' / r - 1))
  have hd : linkIn κ r s t - linkIn κ r s' t' =
      κ * (gateSlope (s / r) * sat (t / r - 1) - gateSlope (s' / r) * sat (t' / r - 1)) := by
    simp only [linkIn]; ring
  rw [hd, abs_mul, abs_of_nonneg hκ]
  have h1 : |gateSlope (s / r) - gateSlope (s' / r)| * |sat (t / r - 1)| ≤ 128 * (|s - s'| / r) := by
    have := mul_le_mul hg hb (abs_nonneg _) (by positivity)
    linarith
  have h2 : gateSlope (s' / r) * |sat (t / r - 1) - sat (t' / r - 1)| ≤ 8 * (2 * (|t - t'| / r)) :=
    mul_le_mul hgb.2 hs (abs_nonneg _) (by norm_num)
  have hfin : κ * (128 * (|s - s'| / r) + 8 * (2 * (|t - t'| / r))) =
      κ / r * (128 * |s - s'| + 16 * |t - t'|) := by ring
  rw [← hfin]
  apply mul_le_mul_of_nonneg_left _ hκ
  rw [abs_of_nonneg hgb.1] at hm
  linarith

lemma linkOut_difference (κ r s t s' t' : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) :
    |linkOut κ r s t - linkOut κ r s' t'| ≤ κ / r * (16 * |s - s'| + 4 * |t - t'|) := by
  have hg := gate_difference (s / r) (s' / r)
  rw [scaled_abs r s s' hr] at hg
  have hs := satSlope_lipschitz (t / r - 1) (t' / r - 1)
  have he : t / r - 1 - (t' / r - 1) = t / r - t' / r := by ring
  rw [he, scaled_abs r t t' hr] at hs
  have hb := satSlope_bounds (t / r - 1)
  have hgb := gate_bounds (s' / r)
  have hm := mul_sub_mul_abs (gate (s / r)) (satSlope (t / r - 1)) (gate (s' / r))
    (satSlope (t' / r - 1))
  have hd : linkOut κ r s t - linkOut κ r s' t' =
      κ * (gate (s / r) * satSlope (t / r - 1) - gate (s' / r) * satSlope (t' / r - 1)) := by
    simp only [linkOut]; ring
  rw [hd, abs_mul, abs_of_nonneg hκ]
  rw [abs_of_nonneg hgb.1, abs_of_nonneg hb.1] at hm
  have h1 : |gate (s / r) - gate (s' / r)| * satSlope (t / r - 1) ≤ 8 * (|s - s'| / r) * 2 :=
    mul_le_mul hg hb.2 hb.1 (by positivity)
  have h2 : gate (s' / r) * |satSlope (t / r - 1) - satSlope (t' / r - 1)| ≤ 1 * (4 * (|t - t'| / r)) :=
    mul_le_mul hgb.2 hs (abs_nonneg _) (by norm_num)
  have hfin : κ * (8 * (|s - s'| / r) * 2 + 1 * (4 * (|t - t'| / r))) =
      κ / r * (16 * |s - s'| + 4 * |t - t'|) := by ring
  rw [← hfin]
  apply mul_le_mul_of_nonneg_left _ hκ
  linarith

lemma chainJacobian_difference {d n : ℕ} (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    ‖chainJacobian κ r π x - chainJacobian κ r π y‖ ≤ 256 * κ / r * ‖x - y‖ := by
  set Δ := ‖x - y‖ with hΔ
  have hc : ∀ i : Fin d, |x i - y i| ≤ Δ := fun i => by
    simpa only [PiLp.sub_apply] using coordinate_le (x - y) i
  have hcr : 0 ≤ κ / r := by positivity
  apply bidiagonal_norm_le π _
    (headSlope κ r (x (π 0)) - headSlope κ r (y (π 0)))
    (fun j => linkIn κ r (x (π j.castSucc)) (x (π j.succ)) -
      linkIn κ r (y (π j.castSucc)) (y (π j.succ)))
    (fun j => linkOut κ r (x (π j.castSucc)) (x (π j.succ)) -
      linkOut κ r (y (π j.castSucc)) (y (π j.succ)))
    (fun z => by simp only [sub_apply, PiLp.sub_apply, chainJacobian_zero]; ring)
    (fun z j => by simp only [sub_apply, PiLp.sub_apply, chainJacobian_succ]; ring)
    (fun z i hi => by
      simp only [sub_apply, PiLp.sub_apply, chainJacobian_outside κ r π x z i hi,
        chainJacobian_outside κ r π y z i hi, sub_self])
    (A := 4 * κ / r * Δ) (B := 144 * κ / r * Δ) (C := 20 * κ / r * Δ)
  · exact (headSlope_difference κ r _ _ hκ hr).trans
      (mul_le_mul_of_nonneg_left (hc _) (by positivity))
  · intro j
    refine (linkIn_difference κ r _ _ _ _ hκ hr).trans ?_
    have h1 := hc (π j.castSucc)
    have h2 := hc (π j.succ)
    have : κ / r * (128 * |x (π j.castSucc) - y (π j.castSucc)| +
        16 * |x (π j.succ) - y (π j.succ)|) ≤ κ / r * (144 * Δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hcr
    have e : κ / r * (144 * Δ) = 144 * κ / r * Δ := by ring
    linarith
  · intro j
    refine (linkOut_difference κ r _ _ _ _ hκ hr).trans ?_
    have h1 := hc (π j.castSucc)
    have h2 := hc (π j.succ)
    have : κ / r * (16 * |x (π j.castSucc) - y (π j.castSucc)| +
        4 * |x (π j.succ) - y (π j.succ)|) ≤ κ / r * (20 * Δ) :=
      mul_le_mul_of_nonneg_left (by linarith) hcr
    have e : κ / r * (20 * Δ) = 20 * κ / r * Δ := by ring
    linarith
  · positivity
  · have hΔ0 : 0 ≤ Δ := norm_nonneg _
    have : 0 ≤ (κ / r * Δ) ^ 2 := sq_nonneg _
    have e : (4 * κ / r * Δ) ^ 2 + 2 * (144 * κ / r * Δ) ^ 2 + 2 * (20 * κ / r * Δ) ^ 2 =
        42288 * (κ / r * Δ) ^ 2 := by ring
    have e2 : (256 * κ / r * Δ) ^ 2 = 65536 * (κ / r * Δ) ^ 2 := by ring
    rw [e, e2]
    nlinarith

lemma chain_lipschitz {d n : ℕ} (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    ‖chain κ r π x - chain κ r π y‖ ≤ 12 * κ * ‖x - y‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Space d))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (chain_hasFDerivAt κ r hr π z).hasFDerivWithinAt)
    (fun z _ => chainJacobian_norm κ r hκ π z) (Set.mem_univ y) (Set.mem_univ x)
  simpa only using h

lemma head_abs (κ r t : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) : |head κ r t| ≤ κ * r := by
  have h := sat_bounds (t / r - 1)
  rw [head, abs_mul, abs_of_nonneg (by positivity : 0 ≤ κ * r)]
  nlinarith [mul_nonneg hκ hr.le]

lemma link_abs (κ r s t : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) : |link κ r s t| ≤ κ * r := by
  have h := sat_bounds (t / r - 1)
  have hg := gate_bounds (s / r)
  rw [link, abs_mul, abs_of_nonneg (by positivity : 0 ≤ κ * r), abs_mul, abs_of_nonneg hg.1]
  have : gate (s / r) * |sat (t / r - 1)| ≤ 1 := by nlinarith [abs_nonneg (sat (t / r - 1))]
  nlinarith [mul_nonneg hκ hr.le]

lemma chain_norm_sq {d n : ℕ} (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    ‖chain κ r π x‖ ^ 2 ≤ (n + 1) * (κ * r) ^ 2 := by
  rw [norm_sq_supported π _ (fun i hi => chain_outside κ r π x i hi), Fin.sum_univ_succ]
  simp only [chain_zero, chain_succ]
  have h0 := sq_le_of_abs_le (head_abs κ r (x (π 0)) hκ hr)
  have hs : ∑ j : Fin n, link κ r (x (π j.castSucc)) (x (π j.succ)) ^ 2 ≤
      ∑ _j : Fin n, (κ * r) ^ 2 :=
    Finset.sum_le_sum (fun j _ => sq_le_of_abs_le (link_abs κ r _ _ hκ hr))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  linarith

noncomputable def target {d n : ℕ} (r : ℝ) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  ∑ j : Fin (n + 1), r • axis (π j)

lemma target_coordinate {d n : ℕ} (r : ℝ) (π : Fin (n + 1) ↪ Fin d) (j : Fin (n + 1)) :
    target r π (π j) = r := by
  classical
  simp only [target, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  simp [axis, π.injective.eq_iff]

lemma target_outside {d n : ℕ} (r : ℝ) (π : Fin (n + 1) ↪ Fin d) (i : Fin d)
    (hi : ∀ j, i ≠ π j) : target r π i = 0 := by
  classical
  simp only [target, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  simp [axis, hi]

lemma target_norm_sq {d n : ℕ} (r : ℝ) (π : Fin (n + 1) ↪ Fin d) :
    ‖target r π‖ ^ 2 = (n + 1) * r ^ 2 := by
  rw [norm_sq_supported π _ (fun i hi => target_outside r π i hi)]
  simp [target_coordinate]

lemma chain_target {d n : ℕ} (κ r : ℝ) (π : Fin (n + 1) ↪ Fin d) :
    chain κ r π (target r π) = 0 := by
  have hr : ∀ j, target r π (π j) / r - 1 = 0 ∨ r = 0 := by
    intro j
    rw [target_coordinate]
    by_cases h : r = 0
    · exact Or.inr h
    · left; field_simp; ring
  ext i
  by_cases hi : ∃ j, i = π j
  · obtain ⟨j, rfl⟩ := hi
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [chain_zero]
      rcases hr 0 with h | h
      · simp [head, h, sat_zero]
      · simp [head, h]
    · rw [chain_succ]
      rcases hr k.succ with h | h
      · simp [link, h, sat_zero]
      · simp [link, h]
  · push Not at hi
    simp [chain_outside κ r π _ i (fun j h => hi j h)]

lemma inner_supported {d m : ℕ} (π : Fin m ↪ Fin d) (u w : Space d)
    (hu : ∀ i, (∀ j, i ≠ π j) → u i = 0) :
    ⟪u, w⟫ = ∑ j : Fin m, u (π j) * w (π j) := by
  classical
  rw [PiLp.inner_apply]
  symm
  calc
    _ = ∑ i ∈ Finset.univ.map π, u i * w i := by simp
    _ = _ := by
      rw [Finset.sum_subset (Finset.subset_univ _)]
      · apply Finset.sum_congr rfl
        intro i _
        simp [mul_comm]
      · intro i _ hi
        have hui : u i = 0 := hu i (by
          intro j hij
          apply hi
          exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hij.symm⟩)
        simp [hui]

lemma head_minty (κ r t : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) : 0 ≤ head κ r t * (t - r) := by
  have h := sat_mul_nonneg (t / r - 1)
  have he : head κ r t * (t - r) = κ * r ^ 2 * ((t / r - 1) * sat (t / r - 1)) := by
    simp only [head]; field_simp
  rw [he]
  positivity

lemma link_minty (κ r s t : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) : 0 ≤ link κ r s t * (t - r) := by
  have h := sat_mul_nonneg (t / r - 1)
  have hg := (gate_bounds (s / r)).1
  have he : link κ r s t * (t - r) =
      κ * r ^ 2 * gate (s / r) * ((t / r - 1) * sat (t / r - 1)) := by
    simp only [link]; field_simp
  rw [he]
  positivity

lemma chain_minty {d n : ℕ} (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (x : Space d) :
    0 ≤ ⟪chain κ r π x, x - target r π⟫ := by
  rw [inner_supported π _ _ (fun i hi => chain_outside κ r π x i hi), Fin.sum_univ_succ]
  simp only [PiLp.sub_apply, target_coordinate, chain_zero, chain_succ]
  have h0 := head_minty κ r (x (π 0)) hκ hr
  have hs : 0 ≤ ∑ j : Fin n, link κ r (x (π j.castSucc)) (x (π j.succ)) * (x (π j.succ) - r) :=
    Finset.sum_nonneg (fun j _ => link_minty κ r _ _ hκ hr)
  linarith

lemma chain_floor {d n : ℕ} (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (π : Fin (n + 1) ↪ Fin d) (x : Space d) (i : Fin (n + 1)) (hi : x (π i) ≤ r / 2) :
    3 / 4 * (κ * r) ≤ ‖chain κ r π x‖ := by
  have hkr : 0 ≤ κ * r := by positivity
  have hlow : ∀ t : ℝ, t ≤ r / 2 → 3 / 4 ≤ |sat (t / r - 1)| := by
    intro t ht
    have h1 : t / r ≤ 1 / 2 := by rw [div_le_iff₀ hr]; linarith
    have h2 := sat_low (t / r - 1) (by linarith)
    rw [abs_of_neg (by linarith)]
    linarith
  induction i using Fin.induction with
  | zero =>
    have hc := coordinate_le (chain κ r π x) (π 0)
    rw [chain_zero, head, abs_mul, abs_of_nonneg hkr] at hc
    have := mul_le_mul_of_nonneg_left (hlow _ hi) hkr
    linarith
  | succ j ih =>
    by_cases hp : x (π j.castSucc) ≤ r / 2
    · exact ih hp
    · have hg : gate (x (π j.castSucc) / r) = 1 := by
        apply gate_top
        rw [le_div_iff₀ hr]
        linarith
      have hc := coordinate_le (chain κ r π x) (π j.succ)
      rw [chain_succ, link, hg, one_mul, abs_mul, abs_of_nonneg hkr] at hc
      have := mul_le_mul_of_nonneg_left (hlow _ hi) hkr
      linarith

noncomputable def partialChain {d n : ℕ} (κ r : ℝ) (k : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (x : Space d) : Space d :=
  head κ r (x (π 0)) • axis (π 0) +
    ∑ j : Fin n, if j.val < k then link κ r (x (π j.castSucc)) (x (π j.succ)) • axis (π j.succ)
      else 0

noncomputable def partialJacobian {d n : ℕ} (κ r : ℝ) (k : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (x : Space d) : Space d →L[ℝ] Space d :=
  headSlope κ r (x (π 0)) • InnerProductSpace.rankOne ℝ (axis (π 0)) (axis (π 0)) +
    ∑ j : Fin n, if j.val < k then (linkIn κ r (x (π j.castSucc)) (x (π j.succ)) •
        InnerProductSpace.rankOne ℝ (axis (π j.succ)) (axis (π j.castSucc)) +
      linkOut κ r (x (π j.castSucc)) (x (π j.succ)) •
        InnerProductSpace.rankOne ℝ (axis (π j.succ)) (axis (π j.succ))) else 0

lemma flat_coefficients (κ r s t : ℝ) (hr : 0 < r) (hs : |s| ≤ r / 4) :
    link κ r s t = 0 ∧ linkIn κ r s t = 0 ∧ linkOut κ r s t = 0 := by
  have h : s / r ≤ 1 / 4 := by
    rw [div_le_iff₀ hr]
    linarith [(abs_le.mp hs).2]
  have hg := gate_flat (s / r) h
  simp [link, linkIn, linkOut, hg.1, hg.2]

lemma chain_eq_partial {d n k : ℕ} (κ r : ℝ) (hr : 0 < r) (π : Fin (n + 1) ↪ Fin d)
    (x : Space d) (hx : ∀ i : Fin (n + 1), k ≤ i.val → |x (π i)| ≤ r / 4) :
    chain κ r π x = partialChain κ r k π x := by
  simp only [chain, partialChain]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · simp only [hj, ite_true]
  · have hf := flat_coefficients κ r _ (x (π j.succ)) hr
      (hx j.castSucc (by simpa using Nat.le_of_not_gt hj))
    simp only [hj, ite_false, hf.1, zero_smul]

lemma jacobian_eq_partial {d n k : ℕ} (κ r : ℝ) (hr : 0 < r) (π : Fin (n + 1) ↪ Fin d)
    (x : Space d) (hx : ∀ i : Fin (n + 1), k ≤ i.val → |x (π i)| ≤ r / 4) :
    chainJacobian κ r π x = partialJacobian κ r k π x := by
  simp only [chainJacobian, partialJacobian]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · simp only [hj, ite_true]
  · have hf := flat_coefficients κ r _ (x (π j.succ)) hr
      (hx j.castSucc (by simpa using Nat.le_of_not_gt hj))
    simp only [hj, ite_false, hf.2.1, hf.2.2, zero_smul, add_zero]

lemma partialChain_prefix {d n k : ℕ} (κ r : ℝ) (π τ : Fin (n + 1) ↪ Fin d) (x : Space d)
    (h : ∀ i : Fin (n + 1), i.val < k + 1 → π i = τ i) :
    partialChain κ r k π x = partialChain κ r k τ x := by
  have h0 : π 0 = τ 0 := h 0 (by simp)
  simp only [partialChain, h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · rw [ite_eq_left hj, ite_eq_left hj, h j.succ (by simpa using Nat.succ_lt_succ hj),
      h j.castSucc (by simp only [Fin.val_castSucc]; omega)]
  · simp only [hj, ite_false]

lemma partialJacobian_prefix {d n k : ℕ} (κ r : ℝ) (π τ : Fin (n + 1) ↪ Fin d) (x : Space d)
    (h : ∀ i : Fin (n + 1), i.val < k + 1 → π i = τ i) :
    partialJacobian κ r k π x = partialJacobian κ r k τ x := by
  have h0 : π 0 = τ 0 := h 0 (by simp)
  simp only [partialJacobian, h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k
  · rw [ite_eq_left hj, ite_eq_left hj, h j.succ (by simpa using Nat.succ_lt_succ hj),
      h j.castSucc (by simp only [Fin.val_castSucc]; omega)]
  · simp only [hj, ite_false]

end LongTails.Proofs.SecondOrderMintyChain
