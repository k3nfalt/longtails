import LongTails.Proofs.NearestSetEnergy

open Set Metric
open scoped RealInnerProductSpace

namespace OracleTemplate.NearestSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma energy_control {M : Set E} {F : E → ℝ} {a s B : ℝ} {x v p : E}
    (ha : 0 < a) (hs : 0 ≤ s) (hq : a * s ≤ 1 / 2)
    (hB : 0 ≤ B) (hp : p ∈ M)
    (hnear : infDist (x + s • v) M = ‖x + s • v - p‖)
    (hgrowth : a ^ 2 / 2 * infDist x M ^ 2 ≤ F x)
    (henergy : energy M F a s x v p ≤ B ^ 2 / 2) :
    ‖v‖ ≤ 4 * B ∧ a * infDist (x + s • v) M ≤ 3 * B := by
  have hD := divergence_nonneg hp hnear x
  have hDterm : 0 ≤ (a / s) * divergence M p x (x + s • v) := by positivity
  have hFx : 0 ≤ F x := le_trans (by positivity) hgrowth
  have hFxB := (energy_nonneg ha.le hs hp hnear).trans henergy
  have hdx : a * infDist x M ≤ B := by
    nlinarith [infDist_nonneg (x := x) (s := M)]
  have hw : ‖v + a • (x + s • v - p)‖ ≤ B := by
    unfold energy at henergy
    nlinarith [norm_nonneg (v + a • (x + s • v - p))]
  have hv : ‖v‖ ≤ B + a * infDist (x + s • v) M := by
    have h := norm_sub_le (v + a • (x + s • v - p)) (a • (x + s • v - p))
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha, ← hnear] at h
    linarith
  have hd : infDist (x + s • v) M ≤ infDist x M + s * ‖v‖ := by
    have h : infDist (x + s • v) M ≤ infDist x M + dist (x + s • v) x :=
      infDist_le_infDist_add_dist
    simpa [dist_eq_norm, norm_smul, abs_of_nonneg hs] using h
  have hd' := mul_le_mul_of_nonneg_left hd ha.le
  have hq' := mul_le_mul_of_nonneg_right hq (norm_nonneg v)
  constructor <;> nlinarith only [hv, hd', hq', hdx]

lemma step_containment {M : Set E} {a s L r B : ℝ} {x v g : E}
    (ha : 0 < a) (hs : 0 < s) (hr : 0 < r)
    (hq : a * s ≤ 1 / 2) (hstep : s ^ 2 * L ≤ 1 / 4)
    (hB : B ≤ a * r / 8) (hv : ‖v‖ ≤ 4 * B)
    (hd : a * infDist (x + s • v) M ≤ 3 * B)
    (hg : ‖g‖ ≤ L * infDist (x + s • v) M) :
    let y := x + s • v
    let z := y - s ^ 2 • g
    let w := ((1 - a * s) / (1 + a * s)) • (v - s • g)
    (∀ t ∈ Icc (0 : ℝ) 1, infDist (y - (t * s ^ 2) • g) M < r) ∧
      infDist z M < r ∧ infDist (z + s • w) M < r := by
  let y := x + s • v
  let z := y - s ^ 2 • g
  let w := ((1 - a * s) / (1 + a * s)) • (v - s • g)
  have hdy : infDist y M ≤ 3 * r / 8 := by
    dsimp [y]
    nlinarith
  have hsv : s * ‖v‖ ≤ r / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hv hs.le
    have h2 := mul_le_mul_of_nonneg_left hB hs.le
    have h3 := mul_le_mul_of_nonneg_right hq hr.le
    nlinarith only [h1, h2, h3]
  have hsg : s ^ 2 * ‖g‖ ≤ 3 * r / 32 := by
    have h1 := mul_le_mul_of_nonneg_left hg (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_right hstep (infDist_nonneg (x := y) (s := M))
    change ‖g‖ ≤ L * infDist y M at hg
    nlinarith only [h1, h2, hdy]
  have hbeta0 : 0 ≤ (1 - a * s) / (1 + a * s) :=
    div_nonneg (by linarith) (by positivity)
  have hbeta1 : (1 - a * s) / (1 + a * s) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    nlinarith [mul_nonneg ha.le hs.le]
  have hw : ‖w‖ ≤ ‖v‖ + s * ‖g‖ := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta0]
    calc
      _ ≤ ‖v - s • g‖ := mul_le_of_le_one_left (norm_nonneg _) hbeta1
      _ ≤ ‖v‖ + ‖s • g‖ := norm_sub_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have htube : ∀ t ∈ Icc (0 : ℝ) 1,
      infDist (y - (t * s ^ 2) • g) M ≤ 15 * r / 32 := by
    intro t ht
    have h : infDist (y - (t * s ^ 2) • g) M ≤ infDist y M +
        dist (y - (t * s ^ 2) • g) y := infDist_le_infDist_add_dist
    have he : y - (t * s ^ 2) • g - y = -((t * s ^ 2) • g) := by module
    rw [dist_eq_norm, he, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht.1 (sq_nonneg s))] at h
    have h1 := mul_le_mul_of_nonneg_right ht.2
      (mul_nonneg (sq_nonneg s) (norm_nonneg g))
    nlinarith only [h, h1, hdy, hsg]
  have hz : infDist z M ≤ 15 * r / 32 := by
    simpa [z] using htube 1 (by simp)
  have hY : infDist (z + s • w) M ≤ 13 * r / 16 := by
    have h : infDist (z + s • w) M ≤ infDist z M + dist (z + s • w) z :=
      infDist_le_infDist_add_dist
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs] at h
    have h1 := mul_le_mul_of_nonneg_left hw hs.le
    nlinarith only [h, h1, hz, hsv, hsg]
  dsimp only
  change (∀ t ∈ Icc (0 : ℝ) 1, infDist (y - (t * s ^ 2) • g) M < r) ∧
    infDist z M < r ∧ infDist (z + s • w) M < r
  exact ⟨fun t ht => (htube t ht).trans_lt (by linarith),
    hz.trans_lt (by linarith), hY.trans_lt (by linarith)⟩

end OracleTemplate.NearestSet
