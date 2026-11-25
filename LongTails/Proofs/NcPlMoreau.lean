import LongTails.Proofs.NcPlPL
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcPlMoreau

open LongTails.Proofs.AbcChainProfiles LongTails.Proofs.NcPlCalc LongTails.Proofs.NcPlSchedule
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChain
open LongTails.Proofs.NcPlChainPL LongTails.Proofs.NcPlFlat LongTails.Proofs.NcPlCut
open LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlLipschitz LongTails.Proofs.NcPlPL
open LongTails.Proofs.NcPlProfiles
open LongTails.Proofs.AbcChain (Chain)
open LongTails.Proofs.AbcHardFunction (Space sel sel_apply sel_norm)
open LongTails.Proofs.MintyChainGeometry (ball ball_of_le)

lemma prox_slope {E : Type*} [NormedAddCommGroup E] (Φ : E → ℝ) {L γ C t0 : ℝ} (hL : 0 < L)
    (hC : 0 ≤ C) (ht0 : 0 < t0) (z xb : E)
    (hprox : ∀ x', Φ xb + L * ‖xb - z‖ ^ 2 ≤ Φ x' + L * ‖x' - z‖ ^ 2)
    (hdesc : ∀ t, 0 < t → t ≤ t0 → ∃ x', ‖x' - xb‖ ≤ t ∧ Φ x' ≤ Φ xb - γ * t + C * t ^ 2) :
    γ ≤ 2 * L * ‖xb - z‖ := by
  by_contra hcon
  have hgap : 0 < γ - 2 * L * ‖xb - z‖ := by linarith [not_le.mp hcon]
  have hden : 0 < 2 * (C + L) := by positivity
  obtain ⟨t, ht⟩ : ∃ t, t = min t0 ((γ - 2 * L * ‖xb - z‖) / (2 * (C + L))) := ⟨_, rfl⟩
  have htpos : 0 < t := by
    rw [ht]
    exact lt_min ht0 (div_pos hgap hden)
  have htle : t ≤ t0 := by
    rw [ht]
    exact min_le_left _ _
  have htle2 : t * (2 * (C + L)) ≤ γ - 2 * L * ‖xb - z‖ := by
    have : t ≤ (γ - 2 * L * ‖xb - z‖) / (2 * (C + L)) := by
      rw [ht]
      exact min_le_right _ _
    rwa [le_div_iff₀ hden] at this
  obtain ⟨x', hx1, hx2⟩ := hdesc t htpos htle
  have hp := hprox x'
  have htri : ‖x' - z‖ ≤ ‖xb - z‖ + t := by
    have e : x' - z = (x' - xb) + (xb - z) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith)
  have hsq : ‖x' - z‖ ^ 2 ≤ (‖xb - z‖ + t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h1 := mul_le_mul_of_nonneg_left hsq hL.le
  have hn := norm_nonneg (xb - z)
  have h2 := mul_le_mul_of_nonneg_left htle2 htpos.le
  have h3 : 0 < (C + L) * (t * t) := mul_pos (by positivity) (mul_pos htpos htpos)
  nlinarith

section Flat

variable {m n : ℕ} {r : ℕ → ℝ}

lemma theta_sum (a b : ℕ → ℝ) (c : ℝ) :
    theta m n r a b c = ∑ k ∈ Finset.range (m + 1),
      (c * blockU n r (prevRead (uOf n a) k) (uOf n a k) (wOf n b k) -
        compU n (prevRead (uOf n a) k)) := by
  unfold theta rF cF rhat csum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem theta_update {c : ℝ} (hc1 : c ≤ 1) (a a' b : ℕ → ℝ) {i : ℕ} (hi : i ≤ m)
    {t : ℝ} (ht : 0 ≤ t)
    (hu : ∀ j, j ≤ m → uOf n a' j = if j = i then uOf n a i + t else uOf n a j) :
    theta m n r a' b c - theta m n r a b c ≤
      c * (rwd n r (sig n (prevRead (uOf n a) i)) (uOf n a i + t) (wOf n b i) -
        rwd n r (sig n (prevRead (uOf n a) i)) (uOf n a i) (wOf n b i)) := by
  have hprev : ∀ k, k ≤ m → prevRead (uOf n a') k =
      if k = i + 1 then uOf n a i + t else prevRead (uOf n a) k := by
    intro k hk
    unfold prevRead
    by_cases h0 : k = 0
    · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_right (by omega)]
    · rw [ite_eq_right h0, ite_eq_right h0, hu (k - 1) (by omega)]
      by_cases h1 : k = i + 1
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [theta_sum, theta_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (c * blockU n r (prevRead (uOf n a') k) (uOf n a' k) (wOf n b k) -
        compU n (prevRead (uOf n a') k)) -
      (c * blockU n r (prevRead (uOf n a) k) (uOf n a k) (wOf n b k) -
        compU n (prevRead (uOf n a) k)) ≤
      if k = i then c * (rwd n r (sig n (prevRead (uOf n a) i)) (uOf n a i + t) (wOf n b i) -
        rwd n r (sig n (prevRead (uOf n a) i)) (uOf n a i) (wOf n b i)) else 0 := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hprev k hkm, hu k hkm]
    by_cases h1 : k = i
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega), h1]
      unfold blockU
      linarith
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : k = i + 1
      · rw [ite_eq_left h2]
        have hpr : prevRead (uOf n a) k = uOf n a i := by
          rw [h2]
          exact prevRead_succ _ _
        rw [hpr]
        have hm := mono_front (n := n) (r := r) hc1 (uOf n a k) (wOf n b k)
          (sig_mono (n := n) (by linarith : uOf n a i ≤ uOf n a i + t))
        unfold blockU compU
        linarith
      · rw [ite_eq_right h2]
        linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.mpr (by omega))]

lemma pos_lt {i j : ℕ} (hi : i ≤ m) (hj : j < n + 2) : i * (n + 2) + j < (m + 1) * (n + 2) := by
  have h1 : i * (n + 2) + j < i * (n + 2) + (n + 2) := Nat.add_lt_add_left hj _
  have h2 : i * (n + 2) + (n + 2) = (i + 1) * (n + 2) := by ring
  have h3 : (i + 1) * (n + 2) ≤ (m + 1) * (n + 2) := Nat.mul_le_mul_right _ (by omega)
  omega

end Flat

variable (G : Geo) {d : ℕ} (π : Fin (G.k + 1) ↪ Fin d)

noncomputable def ymax (x : Space d) : Space d := Classical.choose (hardF_attain G π x)

lemma ymax_spec (x y : Space d) : hardF G π x y ≤ hardF G π x (ymax G π x) :=
  Classical.choose_spec (hardF_attain G π x) y

noncomputable def Phi (x : Space d) : ℝ := hardF G π x (ymax G π x)

lemma ymax_grad (x : Space d) : hardGy G π x (ymax G π x) = 0 := by
  have hloc : IsLocalMax (fun y => hardF G π x y) (ymax G π x) :=
    Filter.Eventually.of_forall (ymax_spec G π x)
  have h := hloc.hasFDerivAt_eq_zero (hardF_hasGradientAt_y G π x (ymax G π x)).hasFDerivAt
  exact (InnerProductSpace.toDual ℝ (Space d)).map_eq_zero_iff.mp h

lemma ymax_inside (x : Space d) : ‖ymax G π x‖ ≤ G.By := by
  by_contra hcon
  have hy : G.By < ‖ymax G π x‖ := not_le.mp hcon
  have hin := hardGy_inner G π x (ymax G π x)
  rw [ymax_grad, inner_zero_left] at hin
  have hlam := lamOf_pos G.n
  have hlB := lam_By G
  have hN2 : G.By ^ 2 < ‖ymax G π x‖ ^ 2 := pow_lt_pow_left₀ hy G.hBy.le two_ne_zero
  have hP : 0 ≤ ∑ j, pos (-ymax G π x j - G.ρ / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm0 : (0 : ℝ) ≤ (G.m : ℝ) + 1 := by positivity
  nlinarith

lemma upos_lt {i : ℕ} (hi : i ≤ G.m) : i * (G.n + 2) + (G.n + 1) < G.k + 1 := by
  rw [G.hk]
  exact pos_lt hi (Nat.lt_succ_self _)

lemma wpos_lt {i j : ℕ} (hi : i ≤ G.m) (hj : j ≤ G.n) : i * (G.n + 2) + j < G.k + 1 := by
  rw [G.hk]
  exact pos_lt hi (by omega)

lemma chA_inside (x : Space d) (hx : ‖x‖ ≤ G.Bx) : chA G π x = sel π x := by
  unfold chA
  rw [cutv_of_le G.hBx hx, one_smul]

lemma uOf_sel (x : Space d) {i : ℕ} (hi : i ≤ G.m) :
    uOf G.n (seq (sel π x)) i = x (π ⟨i * (G.n + 2) + (G.n + 1), upos_lt G hi⟩) := by
  unfold uOf
  rw [seq_lt _ (upos_lt G hi), sel_apply]

theorem descent_coord (xb : Space d) (hxb : ‖xb‖ ≤ G.Bx - 1) {i : ℕ} (hi : i ≤ G.m)
    (hprev : 1 ≤ prevRead (uOf G.n (seq (sel π xb))) i)
    (hui : uOf G.n (seq (sel π xb)) i < 1) :
    ∀ t, 0 < t → t ≤ min 1 (1 - uOf G.n (seq (sel π xb)) i) →
      ∃ x', ‖x' - xb‖ ≤ t ∧ Phi G π x' ≤ Phi G π xb - 1 / 16 * t + 1 / 32 * t ^ 2 := by
  intro t ht htle
  have ht1 : t ≤ 1 := htle.trans (min_le_left _ _)
  have ht2 : t ≤ 1 - uOf G.n (seq (sel π xb)) i := htle.trans (min_le_right _ _)
  obtain ⟨q, hq⟩ : ∃ q, q = π ⟨i * (G.n + 2) + (G.n + 1), upos_lt G hi⟩ := ⟨_, rfl⟩
  obtain ⟨x', hx'⟩ : ∃ x' : Space d, x' = WithLp.toLp 2 (fun j => xb j + if j = q then t else 0) :=
    ⟨_, rfl⟩
  have hx'j : ∀ j, x' j = xb j + if j = q then t else 0 := fun j => by rw [hx']
  have hdsq : ‖x' - xb‖ ^ 2 = t ^ 2 := by
    rw [norm_sub_sq_eq]
    have e : ∀ j ∈ (Finset.univ : Finset (Fin d)), (x' j - xb j) ^ 2 = if j = q then t ^ 2 else 0 := by
      intro j _
      rw [hx'j j, add_sub_cancel_left]
      split_ifs
      · rfl
      · norm_num
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ q)]
  have hd : ‖x' - xb‖ = t := (pow_left_inj₀ (norm_nonneg _) ht.le two_ne_zero).mp hdsq
  have hnsq : ‖x'‖ ^ 2 = ‖xb‖ ^ 2 + (2 * t * xb q + t ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have e : ∀ j ∈ (Finset.univ : Finset (Fin d)), x' j ^ 2 =
        xb j ^ 2 + if j = q then 2 * t * xb j + t ^ 2 else 0 := by
      intro j _
      rw [hx'j j]
      split_ifs
      · ring
      · ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ q)]
  have hxbB : ‖xb‖ ≤ G.Bx := by linarith
  have hx'B : ‖x'‖ ≤ G.Bx := by
    have e : x' = xb + (x' - xb) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [hd]
    linarith
  have hu : ∀ j, j ≤ G.m → uOf G.n (seq (sel π x')) j =
      if j = i then uOf G.n (seq (sel π xb)) i + t else uOf G.n (seq (sel π xb)) j := by
    intro j hj
    rw [uOf_sel G π x' hj, hx'j]
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl, uOf_sel G π xb hj, ← hq, ite_eq_left rfl]
    · rw [ite_eq_right hji, uOf_sel G π xb hj]
      have hne : π ⟨j * (G.n + 2) + (G.n + 1), upos_lt G hj⟩ ≠ q := by
        rw [hq]
        intro h
        have h2 := Fin.mk.inj (π.injective h)
        exact hji (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) (Nat.add_right_cancel h2))
      rw [ite_eq_right hne, add_zero]
  have hui_eq : uOf G.n (seq (sel π xb)) i = xb q := by
    rw [uOf_sel G π xb hi, hq]
  obtain ⟨yt, hyt⟩ : ∃ yt, yt = ymax G π x' := ⟨_, rfl⟩
  have hyin : ‖yt‖ ≤ G.By := by
    rw [hyt]
    exact ymax_inside G π x'
  have hcy : cutv G.By yt = 1 := cutv_of_le G.hBy hyin
  have hprev' : prevRead (uOf G.n (seq (sel π x'))) i = prevRead (uOf G.n (seq (sel π xb))) i := by
    unfold prevRead
    by_cases h0 : i = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
    · rw [ite_eq_right h0, ite_eq_right h0, hu (i - 1) (by omega), ite_eq_right (by omega)]
  have hgate : gate (wOf G.n (seq (sel π yt)) i G.n / G.r G.n) = 1 := by
    apply block_open_chain G.scales hprev (uOf G.n (seq (sel π xb)) i + t)
    intro k hk
    have hg := hardGy_dual G π x' yt hyin ⟨i * (G.n + 2) + k, wpos_lt G hi hk⟩
    have hz : hardGy G π x' yt = 0 := by
      rw [hyt]
      exact ymax_grad G π x'
    rw [hz] at hg
    rw [chA_inside G π x' hx'B] at hg
    unfold gB at hg
    rw [pos_mod G.n i (by omega), ite_eq_right (by omega), pos_div G.n i (by omega)] at hg
    unfold gW at hg
    rw [hprev', hu i hi, ite_eq_left rfl] at hg
    unfold bgrad
    exact hg.symm
  have hstep : hardF G π x' yt - hardF G π xb yt =
      (‖x'‖ ^ 2 - ‖xb‖ ^ 2) / 32 +
        (theta G.m G.n G.r (seq (sel π x')) (seq (sel π yt)) 1 -
          theta G.m G.n G.r (seq (sel π xb)) (seq (sel π yt)) 1) := by
    unfold hardF
    rw [chA_inside G π x' hx'B, chA_inside G π xb hxbB, hcy]
    ring
  have hθ := theta_update (m := G.m) (n := G.n) (r := G.r) (c := 1) le_rfl
    (seq (sel π xb)) (seq (sel π x')) (seq (sel π yt)) hi ht.le hu
  rw [rw_sub_t, sig_of_ge hprev, ampT_full le_rfl, hgate, one_mul, one_mul, one_mul] at hθ
  have hmax1 : Phi G π x' = hardF G π x' yt := by
    rw [hyt]
    rfl
  have hmax2 : hardF G π xb yt ≤ Phi G π xb := ymax_spec G π xb yt
  have hafun : afun (uOf G.n (seq (sel π xb)) i + t) - afun (uOf G.n (seq (sel π xb)) i) ≤ -t ∨
      (afun (uOf G.n (seq (sel π xb)) i + t) - afun (uOf G.n (seq (sel π xb)) i) ≤ 0 ∧
        uOf G.n (seq (sel π xb)) i < -1) := by
    by_cases hneg : -1 ≤ uOf G.n (seq (sel π xb)) i
    · left
      unfold afun
      rw [phi_of_mem (by linarith) (by linarith), phi_of_mem hneg hui.le]
      linarith
    · right
      refine ⟨?_, not_le.mp hneg⟩
      unfold afun
      have := phi_mono (by linarith : uOf G.n (seq (sel π xb)) i ≤ uOf G.n (seq (sel π xb)) i + t)
      linarith
  refine ⟨x', hd.le, ?_⟩
  rw [hmax1]
  rw [← hui_eq] at hnsq
  rcases hafun with h | ⟨h, hlt⟩
  · have hprod : t * uOf G.n (seq (sel π xb)) i ≤ t := by nlinarith
    linarith
  · have hprod : t * uOf G.n (seq (sel π xb)) i ≤ -t := by nlinarith
    linarith

theorem descent_radial (xb : Space d) (hxb : G.Bx - 1 < ‖xb‖) :
    ∀ t, 0 < t → t ≤ 1 →
      ∃ x', ‖x' - xb‖ ≤ t ∧ Phi G π x' ≤ Phi G π xb - 1 / 16 * t + 1 / 32 * t ^ 2 := by
  intro t ht ht1
  have hB4 := geo_Bx_ge G
  have hn : 3 < ‖xb‖ := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = 1 - t / ‖xb‖ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by
    rw [hs, sub_nonneg, div_le_one (by linarith)]
    linarith
  have hsn : s * ‖xb‖ = ‖xb‖ - t := by
    rw [hs]
    field_simp
  have hd : ‖s • xb - xb‖ = t := by
    have e : s • xb - xb = (s - 1) • xb := by rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs]
    have e2 : s - 1 = -(t / ‖xb‖) := by rw [hs]; ring
    rw [e2, abs_neg, abs_of_nonneg (by positivity), div_mul_cancel₀ _ (by linarith : ‖xb‖ ≠ 0)]
  have hnorm : ‖s • xb‖ = ‖xb‖ - t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, hsn]
  obtain ⟨yt, hyt⟩ : ∃ yt, yt = ymax G π (s • xb) := ⟨_, rfl⟩
  have hlip := thetaA_lip_Bx G (seq (sel π yt)) (cutv_nonneg G.By yt) (cutv_le_one G.By yt)
    (chA G π xb) (chA G π (s • xb))
  have hch := chA_lip G π xb (s • xb)
  rw [hd] at hch
  have hstep : hardF G π (s • xb) yt - hardF G π xb yt =
      (‖s • xb‖ ^ 2 - ‖xb‖ ^ 2) / 32 +
        (theta G.m G.n G.r (seq (chA G π (s • xb))) (seq (sel π yt)) (cutv G.By yt) -
          theta G.m G.n G.r (seq (chA G π xb)) (seq (sel π yt)) (cutv G.By yt)) := by
    unfold hardF
    ring
  have hmax1 : Phi G π (s • xb) = hardF G π (s • xb) yt := by
    rw [hyt]
    rfl
  have hmax2 : hardF G π xb yt ≤ Phi G π xb := ymax_spec G π xb yt
  have hθ := (abs_le.mp hlip).2
  have hBpos := G.hBx
  have h17 : G.Bx / 2 ^ 12 * ‖chA G π (s • xb) - chA G π xb‖ ≤ G.Bx / 2 ^ 12 * (17 * t) :=
    mul_le_mul_of_nonneg_left hch (by positivity)
  refine ⟨s • xb, hd.le, ?_⟩
  rw [hmax1]
  rw [hnorm] at hstep
  have e : G.Bx / 2 ^ 12 * (17 * t) = 17 / 4096 * (G.Bx * t) := by ring
  nlinarith [mul_nonneg hBpos.le ht.le, mul_pos ht (by linarith : (0 : ℝ) < ‖xb‖ - (G.Bx - 1))]

theorem moreau_lower (z xb : Space d)
    (hprox : ∀ x', Phi G π xb + 2 ^ 26 * ‖xb - z‖ ^ 2 ≤ Phi G π x' + 2 ^ 26 * ‖x' - z‖ ^ 2)
    (hsmall : |ball (2 * G.Bx) z (π ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩)| ≤ 1 / 4) :
    1 / 16 ≤ 2 * 2 ^ 26 * ‖xb - z‖ := by
  by_cases hI : ‖xb‖ ≤ G.Bx - 1
  · by_cases hex : ∃ i, i ≤ G.m ∧ uOf G.n (seq (sel π xb)) i < 1
    · classical
      have hi := Nat.find_spec hex
      have hmin : ∀ j, j < Nat.find hex → 1 ≤ uOf G.n (seq (sel π xb)) j := by
        intro j hj
        by_contra hne
        exact Nat.find_min hex hj ⟨by omega, not_le.mp hne⟩
      have hprev : 1 ≤ prevRead (uOf G.n (seq (sel π xb))) (Nat.find hex) := by
        unfold prevRead
        by_cases h0 : Nat.find hex = 0
        · rw [ite_eq_left h0]
          norm_num
        · rw [ite_eq_right h0]
          exact hmin _ (by omega)
      exact prox_slope (Phi G π) (by norm_num) (by norm_num)
        (lt_min one_pos (by linarith [hi.2])) z xb hprox
        (descent_coord G π xb hI hi.1 hprev hi.2)
    · have hall : 1 ≤ uOf G.n (seq (sel π xb)) G.m := by
        by_contra hne
        exact hex ⟨G.m, le_rfl, not_le.mp hne⟩
      rw [uOf_sel G π xb le_rfl] at hall
      rcases le_or_gt ‖z‖ (2 * G.Bx) with hzn | hzn
      · rw [ball_of_le _ _ hzn] at hsmall
        have hc := PiLp.norm_apply_le (xb - z)
          (π ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩)
        rw [Real.norm_eq_abs] at hc
        have hc2 : xb (π ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩) -
            z (π ⟨G.m * (G.n + 2) + (G.n + 1), upos_lt G le_rfl⟩) ≤ ‖xb - z‖ :=
          (le_abs_self _).trans hc
        have hz := (abs_le.mp hsmall).2
        linarith
      · have h1 := norm_sub_norm_le z xb
        rw [norm_sub_rev] at h1
        have hB4 := geo_Bx_ge G
        linarith
  · exact prox_slope (Phi G π) (by norm_num) (by norm_num) one_pos z xb hprox
      (descent_radial G π xb (not_le.mp hI))

end LongTails.Proofs.NcPlMoreau
