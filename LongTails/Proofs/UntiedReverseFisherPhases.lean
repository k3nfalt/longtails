import LongTails.Proofs.UntiedReverseFisherDynamics
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherPhases

open LongTails.Proofs.UntiedReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory
open LongTails.Proofs.SymmetricReverseFisherGeometry
open LongTails.Proofs.SymmetricReverseFisherContraction

lemma pow_le_inv_of_log {t Z : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hZ : 0 < Z) {n : ℕ}
    (hn : Real.log Z / t ≤ n) : (1 - t) ^ n ≤ 1 / Z := by
  have h1 := one_sub_pow_le_exp ht.le ht1 n
  have h2 : Real.log Z ≤ t * n := by rwa [div_le_iff₀ ht, mul_comm] at hn
  calc
    _ ≤ Real.exp (-t * n) := h1
    _ ≤ Real.exp (-Real.log Z) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Z := by rw [Real.exp_neg, Real.exp_log hZ, one_div]

lemma one_div_one_add_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 1 / (1 + x) ≤ 1 - x / 2 := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma one_sub_le_one_div_one_add {x : ℝ} (hx : 0 ≤ x) : 1 - x ≤ 1 / (1 + x) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg x]

lemma growth_of_log {x Z : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hZ : 0 < Z) {n : ℕ}
    (hn : Real.log Z / (x / 2) ≤ n) : Z ≤ (1 + x) ^ n := by
  have h := pow_le_inv_of_log (t := x / 2) (by positivity) (by linarith) hZ hn
  have hprod : 1 ≤ (1 + x) * (1 - x / 2) := by nlinarith
  have hpos : 0 < (1 - x / 2) ^ n := pow_pos (by linarith) n
  have hp : 1 ≤ (1 + x) ^ n * (1 - x / 2) ^ n := by
    rw [← mul_pow]; exact one_le_pow₀ hprod
  rw [le_div_iff₀ hZ] at h
  nlinarith

lemma snd_inner_gd {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (x : SSpace q × SSpace q) :
    ⟪(pairStep (a • e) x).2, e⟫ = ⟪gdStep (a • e) (stepSize / 2) x.2, e⟫ +
      stepSize / 4 * shiftDefect a (a * ⟪x.1, e⟫) (a * ⟪x.2, e⟫) * a := by
  rw [snd_eq_gdStep, inner_add_left, norm_axis e he ha, inner_axis, inner_axis, inner_smul_left,
    inner_smul_left]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [conj_trivial, hee]
  ring

noncomputable def centreThreshold : ℝ := 1 / 10 ^ 7

noncomputable def contractionFactor : ℝ := 1 - 7 * stepSize / 16

lemma stepSize_half : stepSize / 2 = 1 / 64 := by norm_num [stepSize]

lemma strength_pos {a : ℝ} (ha : 0 < a) : 0 < signalStrength a := (strength_bounds ha).1

lemma strength_le {a : ℝ} (ha : 0 < a) : signalStrength a ≤ a ^ 2 ∧ signalStrength a ≤ 1 := by
  have h := (strength_bounds ha).2
  exact ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩

lemma centre_small {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    32 * a ^ 3 * centreThreshold ≤ signalStrength a / 4 := by
  unfold signalStrength centreThreshold
  rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have h2 := pow_pos ha 2
  nlinarith [mul_le_mul_of_nonneg_left ha1 (le_of_lt h2), mul_pos h2 h2]

noncomputable def ratioRate (a : ℝ) : ℝ := 1 / (1 + 3 * (1 / 64) * signalStrength a / 4)

noncomputable def floorLevel (a u1 P : ℝ) : ℝ :=
  min u1 (Real.sqrt (signalStrength a) / (6 * (1 + P)))

noncomputable def phaseOne (a P : ℝ) : ℕ :=
  ⌈8 / (3 * (1 / 64) * signalStrength a) * Real.log P⌉₊

noncomputable def phaseTwo (a u1 P : ℝ) : ℕ :=
  ⌈8 / ((1 / 64) * signalStrength a) *
    Real.log (Real.sqrt (signalStrength a) / (8 * floorLevel a u1 P))⌉₊

noncomputable def phaseThree (a ε : ℝ) : ℕ :=
  ⌈960 / ((1 / 64) * signalStrength a) *
    Real.log (300 * (1 + 600 * a) / (signalStrength a * Real.sqrt ε))⌉₊

noncomputable def postIterations (a ε u1 P : ℝ) : ℕ :=
  phaseOne a P + phaseTwo a u1 P + phaseThree a ε

noncomputable def ucoord {q : SParams} (e : SSpace q) (z : ℕ → SSpace q × SSpace q) (j : ℕ) : ℝ :=
  ⟪(z j).2, e⟫

noncomputable def tcoord {q : SParams} (e : SSpace q) (z : ℕ → SSpace q × SSpace q) (j : ℕ) : ℝ :=
  ‖transverse e (z j).2‖

lemma ratioRate_bounds {a : ℝ} (ha : 0 < a) :
    0 < ratioRate a ∧ ratioRate a ≤ 1 - 3 * (1 / 64) * signalStrength a / 8 ∧
      contractionFactor ≤ ratioRate a ∧ ratioRate a ≤ 1 := by
  have hm := strength_pos ha
  have hm1 := (strength_le ha).2
  set x := 3 * (1 / 64) * signalStrength a / 4
  have hx : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by dsimp [x]; nlinarith
  refine ⟨by unfold ratioRate; positivity, ?_, ?_, ?_⟩
  · have := one_div_one_add_le hx hx1
    unfold ratioRate; dsimp [x] at this; linarith
  · have := one_sub_le_one_div_one_add hx
    unfold ratioRate contractionFactor stepSize; dsimp [x] at this; nlinarith
  · unfold ratioRate
    rw [div_le_one (by positivity)]
    linarith

section Post

variable {q : SParams} {e : SSpace q} {a : ℝ} {z : ℕ → SSpace q × SSpace q} {u1 P : ℝ}

noncomputable def postBeta (e : SSpace q) (a : ℝ) (z : ℕ → SSpace q × SSpace q) (j : ℕ) : ℝ :=
  beta a (a * ucoord e z j) * a ^ 2 - 32 * a ^ 3 * ‖(z j).1‖ + signalStrength a / 4

lemma post_hyps (he : ‖e‖ = 1) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hz : ∀ j, z (j + 1) = pairStep (a • e) (z j)) (hball0 : ‖(z 0).2‖ ≤ 1 + 600 * a)
    (hW : ∀ j, ‖(z j).1‖ ≤ centreThreshold * contractionFactor ^ j) :
    (∀ j, 0 < ucoord e z j → signalStrength a ≤ postBeta e a z j) ∧
    (∀ j, 0 < ucoord e z j → (1 - 1 / 64 * alpha ‖(z j).2‖ +
        1 / 64 * (postBeta e a z j - signalStrength a / 4)) * ucoord e z j ≤ ucoord e z (j + 1)) ∧
    (∀ j, tcoord e z (j + 1) = (1 - 1 / 64 * alpha ‖(z j).2‖) * tcoord e z j) := by
  have hc0 : 0 ≤ contractionFactor := by unfold contractionFactor stepSize; norm_num
  have hθ0 : 0 ≤ centreThreshold := by unfold centreThreshold; norm_num
  have hcs := centre_small ha ha1
  have hWθ : ∀ j, ‖(z j).1‖ ≤ centreThreshold := fun j =>
    (hW j).trans (mul_le_of_le_one_right hθ0
      (pow_le_one₀ hc0 (by unfold contractionFactor stepSize; norm_num)))
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have h1 := strength_on_ball e (z j).2 he ha.le hj.le (traj_ball he ha.le hz hball0 j)
    have h2 : 32 * a ^ 3 * ‖(z j).1‖ ≤ signalStrength a / 4 :=
      (mul_le_mul_of_nonneg_left (hWθ j) (by positivity)).trans hcs
    unfold postBeta ucoord at *
    linarith
  · intro j hj
    have h := traj_perturbed he ha.le ha1 hz j hj.le
    rw [stepSize_half] at h
    unfold postBeta ucoord at *
    convert h using 2
    ring
  · intro j
    have h := traj_transverse he ha.le hz j
    rw [stepSize_half] at h
    exact h

lemma post_core (he : ‖e‖ = 1) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hz : ∀ j, z (j + 1) = pairStep (a • e) (z j)) (hball0 : ‖(z 0).2‖ ≤ 1 + 600 * a)
    (hW : ∀ j, ‖(z j).1‖ ≤ centreThreshold * contractionFactor ^ j)
    (hu1 : 0 < u1) (hU0 : u1 ≤ ucoord e z 0) (hP : 1 ≤ P)
    (hT0 : tcoord e z 0 ≤ P * ucoord e z 0) :
    (∀ j, 0 < ucoord e z j) ∧ (∀ j, tcoord e z j ≤ P * ratioRate a ^ j * ucoord e z j) ∧
      (∀ j, floorLevel a u1 P ≤ ucoord e z j) := by
  obtain ⟨hBm, hUstep, hTstep⟩ := post_hyps he ha ha1 hz hball0 hW
  have hm := strength_pos ha
  have hAb : ∀ j, 0 ≤ alpha ‖(z j).2‖ ∧ alpha ‖(z j).2‖ ≤ 4 * ‖(z j).2‖ ^ 2 ∧
      alpha ‖(z j).2‖ ≤ 4 := fun j => traj_alpha (y := z) j
  have hA4 : ∀ j, 0 ≤ alpha ‖(z j).2‖ ∧ alpha ‖(z j).2‖ ≤ 4 := fun j => ⟨(hAb j).1, (hAb j).2.2⟩
  have h0 : 0 < ucoord e z 0 := lt_of_lt_of_le hu1 hU0
  have hTnn : ∀ j, 0 ≤ tcoord e z j := fun j => norm_nonneg _
  have hpos := post_positive (U := ucoord e z) (A := fun j => alpha ‖(z j).2‖)
    (B := postBeta e a z) (by norm_num) le_rfl hm.le hA4 hBm hUstep h0
  have hratio : ∀ j, tcoord e z j ≤ P * ratioRate a ^ j * ucoord e z j := by
    intro j
    have h := post_ratio (U := ucoord e z) (T := tcoord e z) (A := fun j => alpha ‖(z j).2‖)
      (B := postBeta e a z) (by norm_num) le_rfl hm.le hA4 hBm hUstep hTstep hTnn h0 hT0 j
    unfold ratioRate
    convert h using 4
  refine ⟨hpos, hratio, ?_⟩
  have hR2 : ∀ j, ‖(z j).2‖ ^ 2 = ucoord e z j ^ 2 + tcoord e z j ^ 2 :=
    fun j => coordinate_norm e (z j).2 he
  have hRle : ∀ j, ‖(z j).2‖ ≤ ucoord e z j + tcoord e z j := by
    intro j
    have h1 := hR2 j
    have h2 := hpos j
    have h3 := hTnn j
    nlinarith [norm_nonneg (z j).2, sq_nonneg (‖(z j).2‖ - (ucoord e z j + tcoord e z j)),
      mul_nonneg h2.le h3]
  have hb0 := (ratioRate_bounds ha).1
  have hb1 := (ratioRate_bounds ha).2.2.2
  have hcone : ∀ j, tcoord e z j ≤ P * ucoord e z j := by
    intro j
    have h := hratio j
    have hbj : ratioRate a ^ j ≤ 1 := pow_le_one₀ hb0.le hb1
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbj (show 0 ≤ P by linarith))
      (hpos j).le
    linarith
  have hsq : Real.sqrt (signalStrength a) ^ 2 = signalStrength a := Real.sq_sqrt hm.le
  intro j
  have h := post_floor (U := ucoord e z) (T := tcoord e z) (R := fun j => ‖(z j).2‖)
    (A := fun j => alpha ‖(z j).2‖) (B := postBeta e a z) (by norm_num) le_rfl hm.le
    (show 0 ≤ P by linarith) (fun j => ⟨(hAb j).1, (hAb j).2.1⟩) (fun j => (hAb j).2.2) hBm
    hUstep hRle (fun j => norm_nonneg _) hcone h0 (ϱ := Real.sqrt (signalStrength a) / 3)
    (by positivity) (by rw [div_pow, hsq]; nlinarith) j
  unfold floorLevel
  refine le_trans ?_ h
  rw [show Real.sqrt (signalStrength a) / 3 / (2 * (1 + P)) =
    Real.sqrt (signalStrength a) / (6 * (1 + P)) by field_simp; ring]
  exact min_le_min_right _ hU0

lemma phaseOne_spec (ha : 0 < a) (hP : 1 ≤ P) {j : ℕ} (hj : phaseOne a P ≤ j) :
    P * ratioRate a ^ j ≤ 1 := by
  have hm := strength_pos ha
  have hm1 := (strength_le ha).2
  obtain ⟨hb0, hbup, -, hb1⟩ := ratioRate_bounds ha
  have ht : 0 < 3 * (1 / 64) * signalStrength a / 8 := by positivity
  have hn : Real.log P / (3 * (1 / 64) * signalStrength a / 8) ≤ (phaseOne a P : ℝ) := by
    have := Nat.le_ceil (8 / (3 * (1 / 64) * signalStrength a) * Real.log P)
    calc Real.log P / (3 * (1 / 64) * signalStrength a / 8) =
        8 / (3 * (1 / 64) * signalStrength a) * Real.log P := by field_simp
      _ ≤ _ := this
  have h1 := pow_le_inv_of_log ht (by nlinarith) (by linarith) hn
  have h2 : ratioRate a ^ j ≤ ratioRate a ^ phaseOne a P := pow_le_pow_of_le_one hb0.le hb1 hj
  have h3 : ratioRate a ^ phaseOne a P ≤ (1 - 3 * (1 / 64) * signalStrength a / 8) ^ phaseOne a P :=
    pow_le_pow_left₀ hb0.le hbup _
  rw [le_div_iff₀ (by linarith)] at h1
  have := mul_le_mul_of_nonneg_left (h2.trans h3) (show 0 ≤ P by linarith)
  linarith

lemma post_escaped (he : ‖e‖ = 1) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hz : ∀ j, z (j + 1) = pairStep (a • e) (z j)) (hball0 : ‖(z 0).2‖ ≤ 1 + 600 * a)
    (hW : ∀ j, ‖(z j).1‖ ≤ centreThreshold * contractionFactor ^ j)
    (hu1 : 0 < u1) (hU0 : u1 ≤ ucoord e z 0) (hP : 1 ≤ P)
    (hT0 : tcoord e z 0 ≤ P * ucoord e z 0) {k : ℕ} (hk : phaseTwo a u1 P ≤ k) :
    Real.sqrt (signalStrength a) / 8 ≤ ucoord e z (phaseOne a P + k) := by
  obtain ⟨hBm, hUstep, -⟩ := post_hyps he ha ha1 hz hball0 hW
  obtain ⟨hpos, hratio, hfloor⟩ := post_core he ha ha1 hz hball0 hW hu1 hU0 hP hT0
  have hm := strength_pos ha
  have hm1 := (strength_le ha).2
  have hsqm : 0 < Real.sqrt (signalStrength a) := Real.sqrt_pos.mpr hm
  have hsq : Real.sqrt (signalStrength a) ^ 2 = signalStrength a := Real.sq_sqrt hm.le
  set n1 := phaseOne a P
  have hesc : ∀ k, min ((1 + 1 / 64 * signalStrength a / 4) * ucoord e z (n1 + k))
      (Real.sqrt (signalStrength a) / 8) ≤ ucoord e z (n1 + k + 1) := by
    intro k
    have hPb := phaseOne_spec ha hP (j := n1 + k) (by omega)
    have h1 := hratio (n1 + k)
    have hTU : tcoord e z (n1 + k) ≤ ucoord e z (n1 + k) := by
      have := mul_le_mul_of_nonneg_right hPb (hpos (n1 + k)).le
      linarith
    have hR2k : ‖(z (n1 + k)).2‖ ^ 2 ≤ 2 * ucoord e z (n1 + k) ^ 2 := by
      have h := coordinate_norm e (z (n1 + k)).2 he
      change ‖(z (n1 + k)).2‖ ^ 2 = ucoord e z (n1 + k) ^ 2 + tcoord e z (n1 + k) ^ 2 at h
      have ht0 : 0 ≤ tcoord e z (n1 + k) := norm_nonneg _
      nlinarith [mul_le_mul hTU hTU ht0 (hpos (n1 + k)).le]
    have hA := traj_alpha (y := z) (n1 + k)
    exact post_escape_step (U := ucoord e z) (R := fun j => ‖(z j).2‖)
      (A := fun j => alpha ‖(z j).2‖) (B := postBeta e a z) (by norm_num) le_rfl hm.le
      hsqm.le hsq (n1 + k) ⟨hA.1, hA.2.1⟩ hA.2.2 (hBm _ (hpos _)) (hpos _) (hUstep _ (hpos _)) hR2k
  have hgrow := capped_growth (fun k => ucoord e z (n1 + k)) (g := 1 + 1 / 64 * signalStrength a / 4)
    (ell := Real.sqrt (signalStrength a) / 8) (by nlinarith) (by positivity)
    (fun k => by simpa [add_assoc] using hesc k)
  have hL0 : 0 < floorLevel a u1 P := by unfold floorLevel; positivity
  have hZ : 0 < Real.sqrt (signalStrength a) / (8 * floorLevel a u1 P) := by positivity
  have hn : Real.log (Real.sqrt (signalStrength a) / (8 * floorLevel a u1 P)) /
      (1 / 64 * signalStrength a / 4 / 2) ≤ (phaseTwo a u1 P : ℝ) := by
    have := Nat.le_ceil (8 / ((1 / 64) * signalStrength a) *
      Real.log (Real.sqrt (signalStrength a) / (8 * floorLevel a u1 P)))
    calc _ = 8 / ((1 / 64) * signalStrength a) *
          Real.log (Real.sqrt (signalStrength a) / (8 * floorLevel a u1 P)) := by field_simp; ring
      _ ≤ _ := this
  have h1 := growth_of_log (x := 1 / 64 * signalStrength a / 4) (by positivity) (by nlinarith) hZ hn
  have hg1 : 1 ≤ 1 + 1 / 64 * signalStrength a / 4 := by nlinarith
  have h2 := pow_le_pow_right₀ hg1 hk
  have h3 := hgrow k
  have h5 : Real.sqrt (signalStrength a) / 8 ≤
      (1 + 1 / 64 * signalStrength a / 4) ^ phaseTwo a u1 P * floorLevel a u1 P := by
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  have h6 := hfloor (n1 + 0)
  have h4 : Real.sqrt (signalStrength a) / 8 ≤
      (1 + 1 / 64 * signalStrength a / 4) ^ k * ucoord e z (n1 + 0) := by
    have hpk : 0 ≤ (1 + 1 / 64 * signalStrength a / 4) ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h6 hpk, mul_le_mul_of_nonneg_right h2 hL0.le]
  rw [min_eq_right h4] at h3
  exact h3

lemma post_step_error (he : ‖e‖ = 1) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hz : ∀ j, z (j + 1) = pairStep (a • e) (z j)) (j : ℕ)
    (hu : Real.sqrt (signalStrength a) / 8 ≤ ucoord e z j) :
    |ucoord e z (j + 1) - a| ≤ (1 - 1 / 64 * signalStrength a / 960) * |ucoord e z j - a| +
      1 / 64 * (48 * tcoord e z j + 32 * a ^ 3 * (‖(z j).1‖ * |ucoord e z j|)) := by
  have hm := strength_pos ha
  have hma := (strength_le ha).1
  have hm1 := (strength_le ha).2
  have hsqm : 0 < Real.sqrt (signalStrength a) := Real.sqrt_pos.mpr hm
  have hsq : Real.sqrt (signalStrength a) ^ 2 = signalStrength a := Real.sq_sqrt hm.le
  have hq1 : Real.sqrt (signalStrength a) ≤ 1 := by rw [Real.sqrt_le_one]; exact hm1
  have hqa : Real.sqrt (signalStrength a) ≤ a := by rw [Real.sqrt_le_left ha.le]; exact hma
  have hηL : stepSize / 2 * (48 + 20 * a) ≤ 1 := by rw [stepSize_half]; nlinarith
  have hc := projected_step_contraction e (z j).2 (a := a) (η := stepSize / 2)
    (q := Real.sqrt (signalStrength a)) he ha.le (by rw [stepSize_half]; norm_num) hηL hsqm hq1
    hqa hu
  have hd := defect_bound e he ha.le ha1 (z j)
  have hin := snd_inner_gd e he ha.le (z j)
  rw [← hz j] at hin
  rw [hsq] at hc
  set G := ⟪gdStep (a • e) (stepSize / 2) (z j).2, e⟫
  set δ := stepSize / 4 * shiftDefect a (a * ⟪(z j).1, e⟫) (a * ⟪(z j).2, e⟫) * a
  have htri := abs_add_le (G - a) δ
  unfold ucoord tcoord
  rw [hin, show G + δ - a = (G - a) + δ by ring]
  rw [stepSize_half] at hc hd
  have e1 : 1 / 64 * (signalStrength a / 960) = 1 / 64 * signalStrength a / 960 := by ring
  rw [e1] at hc
  nlinarith [htri, hc, hd]

set_option maxHeartbeats 1000000 in
theorem post_branch (he : ‖e‖ = 1) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hz : ∀ j, z (j + 1) = pairStep (a • e) (z j)) (hball0 : ‖(z 0).2‖ ≤ 1 + 600 * a)
    (hW : ∀ j, ‖(z j).1‖ ≤ centreThreshold * contractionFactor ^ j)
    (hu1 : 0 < u1) (hU0 : u1 ≤ ucoord e z 0) (hP : 1 ≤ P)
    (hT0 : tcoord e z 0 ≤ P * ucoord e z 0) {ε : ℝ} (hε : 0 < ε)
    {i : ℕ} (hi : postIterations a ε u1 P ≤ i) :
    ‖(z i).2 - a • e‖ ^ 2 ≤ ε / 4 := by
  obtain ⟨hpos, hratio, -⟩ := post_core he ha ha1 hz hball0 hW hu1 hU0 hP hT0
  have hm := strength_pos ha
  have hm1 := (strength_le ha).2
  obtain ⟨hb0, hbup, hcb, hb1⟩ := ratioRate_bounds ha
  have hc0 : 0 ≤ contractionFactor := by unfold contractionFactor stepSize; norm_num
  have hc1 : contractionFactor ≤ 1 := by unfold contractionFactor stepSize; norm_num
  have hθ0 : 0 ≤ centreThreshold := by unfold centreThreshold; norm_num
  have hcs := centre_small ha ha1
  have hball := traj_ball he ha.le hz hball0
  unfold postIterations at hi
  set n1 := phaseOne a P
  set n2 := phaseTwo a u1 P
  set n3 := phaseThree a ε
  set N2 := n1 + n2 with hN2
  set Rb := 1 + 600 * a with hRb
  have hRb1 : 1 ≤ Rb := by rw [hRb]; linarith
  set m := signalStrength a with hmd
  set b := ratioRate a with hbd
  set Ac := 1 - 1 / 64 * m / 960 with hAc
  set F := 1 / 64 * (48 + 32 * a ^ 3 * centreThreshold) * Rb with hF
  have hgap : b < Ac := by rw [hAc]; nlinarith [hbup]
  have hgap3 : 1 / 64 * m / 3 ≤ Ac - b := by rw [hAc]; nlinarith [hbup]
  have hFnn : 0 ≤ F := by rw [hF]; positivity
  have hθ1 : 32 * a ^ 3 * centreThreshold ≤ 1 := by nlinarith
  have hUR : ∀ j, |ucoord e z j| ≤ Rb := by
    intro j
    have := abs_real_inner_le_norm (z j).2 e
    rw [he, mul_one] at this
    exact this.trans (hball j)
  have hTb : ∀ k, tcoord e z (N2 + k) ≤ b ^ k * Rb := by
    intro k
    have h1 := hratio (N2 + k)
    have hPb := phaseOne_spec ha hP (j := n1) le_rfl
    have hb2 : b ^ n2 ≤ 1 := pow_le_one₀ hb0.le hb1
    have hbk : 0 ≤ b ^ k := pow_nonneg hb0.le k
    have hbn1 : 0 ≤ b ^ n1 := pow_nonneg hb0.le n1
    have h2 : P * b ^ (N2 + k) ≤ b ^ k := by
      rw [hN2, pow_add, pow_add]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2
        (show 0 ≤ P * b ^ n1 by positivity)) hbk
      nlinarith
    have hU := hUR (N2 + k)
    rw [abs_of_pos (hpos _)] at hU
    calc tcoord e z (N2 + k) ≤ P * b ^ (N2 + k) * ucoord e z (N2 + k) := h1
      _ ≤ b ^ k * ucoord e z (N2 + k) := mul_le_mul_of_nonneg_right h2 (hpos _).le
      _ ≤ b ^ k * Rb := mul_le_mul_of_nonneg_left hU hbk
  have hWb : ∀ k, ‖(z (N2 + k)).1‖ * |ucoord e z (N2 + k)| ≤ centreThreshold * b ^ k * Rb := by
    intro k
    have h1 := hW (N2 + k)
    have h2 : contractionFactor ^ (N2 + k) ≤ b ^ k :=
      (pow_le_pow_of_le_one hc0 hc1 (by omega : k ≤ N2 + k)).trans (pow_le_pow_left₀ hc0 hcb k)
    calc ‖(z (N2 + k)).1‖ * |ucoord e z (N2 + k)| ≤ (centreThreshold * b ^ k) * Rb :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hθ0)) (hUR _) (abs_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hEstep : ∀ k, |ucoord e z (N2 + (k + 1)) - a| ≤
      Ac * |ucoord e z (N2 + k) - a| + F * b ^ k := by
    intro k
    have hesc := post_escaped he ha ha1 hz hball0 hW hu1 hU0 hP hT0 (k := n2 + k) (by omega)
    rw [show n1 + (n2 + k) = N2 + k by omega] at hesc
    have h := post_step_error he ha ha1 hz (N2 + k) hesc
    rw [show N2 + (k + 1) = N2 + k + 1 by omega]
    have hT := hTb k
    have hW' := hWb k
    rw [hAc, hF]
    nlinarith [mul_le_mul_of_nonneg_left hW' (show (0:ℝ) ≤ 1 / 64 * (32 * a ^ 3) by positivity),
      mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ 1 / 64 * 48 by norm_num)]
  have hEbound := perturbed_geometric_recurrence (fun k => |ucoord e z (N2 + k) - a|)
    (A := Ac) (b := b) (F := F) (by rw [hAc]; nlinarith) hb0.le hgap hFnn hEstep
  obtain ⟨k, rfl⟩ : ∃ k, i = N2 + k := ⟨i - N2, by omega⟩
  have hk3 : n3 ≤ k := by omega
  have hnorm := norm_error_coordinates e (z (N2 + k)).2 a he
  have hE0 : |ucoord e z (N2 + 0) - a| ≤ 2 * Rb := by
    have h3 := abs_sub (ucoord e z (N2 + 0)) a
    rw [abs_of_pos ha] at h3
    linarith [hUR (N2 + 0)]
  have hFA : F / (Ac - b) ≤ 147 * Rb / m := by
    rw [div_le_div_iff₀ (by linarith) hm]
    have h1 : F ≤ 1 / 64 * 49 * Rb := by
      rw [hF]; nlinarith
    have h2 := mul_le_mul_of_nonneg_left hgap3 (show 0 ≤ 147 * Rb by positivity)
    have h3 := mul_le_mul_of_nonneg_right h1 hm.le
    nlinarith
  have hsε := Real.sqrt_pos.mpr hε
  have hAk : Ac ^ k ≤ m * Real.sqrt ε / (300 * Rb) := by
    have hZ : 0 < 300 * Rb / (m * Real.sqrt ε) := by positivity
    have hn : Real.log (300 * Rb / (m * Real.sqrt ε)) / (1 / 64 * m / 960) ≤ (k : ℝ) := by
      have := Nat.le_ceil (960 / ((1 / 64) * m) * Real.log (300 * Rb / (m * Real.sqrt ε)))
      calc Real.log (300 * Rb / (m * Real.sqrt ε)) / (1 / 64 * m / 960) =
          960 / ((1 / 64) * m) * Real.log (300 * Rb / (m * Real.sqrt ε)) := by field_simp
        _ ≤ (n3 : ℝ) := this
        _ ≤ k := by exact_mod_cast hk3
    have h := pow_le_inv_of_log (t := 1 / 64 * m / 960) (by positivity) (by nlinarith) hZ hn
    rw [hAc]
    calc (1 - 1 / 64 * m / 960) ^ k ≤ 1 / (300 * Rb / (m * Real.sqrt ε)) := h
      _ = m * Real.sqrt ε / (300 * Rb) := by field_simp
  have hbA : b ^ k ≤ Ac ^ k := pow_le_pow_left₀ hb0.le hgap.le k
  have hAk0 : 0 ≤ Ac ^ k := pow_nonneg (by rw [hAc]; nlinarith) k
  have h1 := hEbound k
  have h3 : |ucoord e z (N2 + k) - a| ≤ Ac ^ k * (2 * Rb + 147 * Rb / m) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hAk0)
  have hRm : Rb ≤ Rb / m := by rw [le_div_iff₀ hm]; nlinarith
  have h5 : tcoord e z (N2 + k) ≤ Ac ^ k * Rb :=
    (hTb k).trans (mul_le_mul_of_nonneg_right hbA (by linarith))
  have h6 : Ac ^ k * (2 * Rb + 147 * Rb / m) + Ac ^ k * Rb ≤ Ac ^ k * (150 * Rb / m) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hAk0
    have : 150 * Rb / m = 3 * (Rb / m) + 147 * Rb / m := by ring
    nlinarith
  have hfinal : ‖(z (N2 + k)).2 - a • e‖ ≤ Real.sqrt ε / 2 := by
    have h7 : ‖(z (N2 + k)).2 - a • e‖ ≤ Ac ^ k * (150 * Rb / m) := by
      refine hnorm.trans ?_
      change |ucoord e z (N2 + k) - a| + tcoord e z (N2 + k) ≤ _
      linarith
    calc _ ≤ Ac ^ k * (150 * Rb / m) := h7
      _ ≤ m * Real.sqrt ε / (300 * Rb) * (150 * Rb / m) :=
        mul_le_mul_of_nonneg_right hAk (by positivity)
      _ = Real.sqrt ε / 2 := by field_simp; ring
  have hn0 := norm_nonneg ((z (N2 + k)).2 - a • e)
  have hsqe := Real.sq_sqrt hε.le
  nlinarith [mul_le_mul hfinal hfinal hn0 (by positivity)]

end Post

end LongTails.Proofs.UntiedReverseFisherPhases
