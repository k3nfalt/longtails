import LongTails.Algorithms.RelativeGeneralizedAcceleration
import LongTails.Proofs.RelativeGeneralizedLocal
import LongTails.Proofs.RelativeGeneralizedEnergy
import LongTails.Proofs.RelativeGeneralizedTuning

open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeGeneralized

open LongTails.Setups.RelativeGeneralizedSmoothConvex

lemma projection_feasible (p : Public) (hR : 0 ≤ p.R) (w : p.E) :
    ‖projectBall p w - p.x0‖ ≤ 2 * p.R := by
  simpa [projectBall] using norm_clip_le (by positivity : 0 ≤ 2 * p.R) (w - p.x0)

lemma projection_distance (p : Public) (hR : 0 ≤ p.R) {u : p.E}
    (hu : ‖u - p.x0‖ ≤ 2 * p.R) (w : p.E) :
    ‖projectBall p w - u‖ ≤ ‖w - u‖ := by
  have h := norm_clip_sub_le (by positivity : 0 ≤ 2 * p.R) hu (w - p.x0)
  have h1 : projectBall p w - u = clip (2 * p.R) (w - p.x0) - (u - p.x0) := by
    unfold projectBall; abel
  have h2 : w - p.x0 - (u - p.x0) = w - u := by abel
  rw [h1]
  rw [h2] at h
  exact h

lemma projection_normal (p : Public) (hR : 0 ≤ p.R) (w : p.E) {u : p.E}
    (hu : ‖u - p.x0‖ ≤ 2 * p.R) :
    ⟪w - projectBall p w, u - projectBall p w⟫ ≤ 0 := by
  have h := inner_clip_residual_nonpos (by positivity : 0 ≤ 2 * p.R) hu (w - p.x0)
  convert h using 1
  unfold projectBall
  congr 1 <;> abel

lemma mixing_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A a : ℝ} (hs : A + a ≠ 0) (x z : E) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    A • (y - x) + a • (y - z) = 0 := by
  dsimp only
  match_scalars <;> (field_simp; ring)

lemma mixing_distance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A a R : ℝ} {c x z : E} (hA : 0 < A) (ha : 0 < a)
    (hx : ‖x - c‖ ≤ 2 * R) (hz : ‖z - c‖ ≤ 2 * R) :
    let y := (A / (A + a)) • x + (a / (A + a)) • z
    ‖y - c‖ ≤ 2 * R ∧ ‖y - x‖ ≤ 4 * R * a / (A + a) := by
  have hs : A + a ≠ 0 := by positivity
  have hadd : A / (A + a) + a / (A + a) = 1 := by field_simp
  dsimp only
  constructor
  · have heq : (A / (A + a)) • x + (a / (A + a)) • z - c =
        (A / (A + a)) • (x - c) + (a / (A + a)) • (z - c) := by
      match_scalars
      all_goals field_simp
      all_goals ring
    rw [heq]
    calc
      _ ≤ ‖(A / (A + a)) • (x - c)‖ + ‖(a / (A + a)) • (z - c)‖ := norm_add_le _ _
      _ = A / (A + a) * ‖x - c‖ + a / (A + a) * ‖z - c‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (by positivity), abs_of_pos (by positivity)]
      _ ≤ A / (A + a) * (2 * R) + a / (A + a) * (2 * R) := by gcongr
      _ = 2 * R := by rw [← add_mul, hadd, one_mul]
  · have heq : (A / (A + a)) • x + (a / (A + a)) • z - x =
        (a / (A + a)) • (z - x) := by
      match_scalars
      all_goals field_simp
      all_goals ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hd : ‖z - x‖ ≤ 4 * R := by
      have h := norm_sub_le_norm_sub_add_norm_sub z c x
      rw [norm_sub_rev c x] at h
      linarith
    have h := mul_le_mul_of_nonneg_left hd (show 0 ≤ a / (A + a) by positivity)
    convert h using 1; ring

lemma advance_potential (p : Public) (N : ℕ) (I : Instance p) {u : p.E}
    (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1) (hR : 0 < p.R)
    (hα : 0 ≤ p.α) (hαmax : p.α ≤ 1 / 100)
    (hf : ConvexOn ℝ Set.univ I.f) (hg : ∀ w, HasGradientAt I.f (I.grad w) w)
    (hcont : Continuous I.grad)
    (hs : CompositeGeneralized.SymmetricSmooth I.grad p.L0 p.L1)
    (hm : IsMinOn I.f Set.univ u) (hu : ‖u - p.x0‖ ≤ p.R)
    (s : State p.E) (hA : 0 < s.A)
    (hx : ‖s.x - p.x0‖ ≤ 2 * p.R) (hz : ‖s.z - p.x0‖ ≤ 2 * p.R)
    (hgap : I.f s.x - I.f u ≤ noiseBudget p N * p.R ^ 2 / s.A)
    (reply : p.E) (herr : ‖reply - I.grad (queryPoint p N s)‖ ≤
      p.α * ‖I.grad (queryPoint p N s)‖) :
    (advance p N s reply).A * (I.f (advance p N s reply).x - I.f u) +
      1 / 2 * ‖(advance p N s reply).z - u‖ ^ 2 ≤
    s.A * (I.f s.x - I.f u) + 1 / 2 * ‖s.z - u‖ ^ 2 + p.α ^ 2 * p.R ^ 2 := by
  let a := weight p N s
  let η := stepSize p N s
  let y := queryPoint p N s
  let x := projectBall p (y - η • reply)
  let D := noiseBudget p N * p.R ^ 2 / s.A
  have hB : 1 ≤ noiseBudget p N := by
    unfold noiseBudget
    nlinarith [mul_nonneg (sq_nonneg p.α) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have ht := tuning_bounds hA hB hR h0 h1
  change 0 < a ∧ 0 < η ∧ η * (p.L0 + p.L1 ^ 2 * D) = 1 / 1024 ∧
    p.L1 * (4 * p.R * a / (s.A + a)) ≤ 1 / 2 ∧
    p.L0 * (4 * p.R * a / (s.A + a)) ≤ Real.sqrt (p.L0 * D) / 2 ∧
    1024 * a ^ 2 ≤ η * (s.A + a) at ht
  obtain ⟨ha, hη, hηeq, hr, hd, hw⟩ := ht
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmix := mixing_distance hA ha hx hz
  change ‖y - p.x0‖ ≤ 2 * p.R ∧ ‖y - s.x‖ ≤ 4 * p.R * a / (s.A + a) at hmix
  have hG := query_gradient_bound h0 h1 hD hg hcont hs hm hgap
    ((mul_le_mul_of_nonneg_left hmix.2 h1).trans hr)
    ((mul_le_mul_of_nonneg_left hmix.2 h0.le).trans hd)
  let v := η⁻¹ • (y - x)
  let e := reply - I.grad y
  let n := v - reply
  have hxy : y - x = η • v := by dsimp [v]; rw [smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
  have hv : v = I.grad y + e + n := by dsimp [e, n]; abel
  have hnorm : ∀ w : p.E, ‖w - p.x0‖ ≤ 2 * p.R → ⟪n, w - x⟫ ≤ 0 := by
    intro w hfw
    have hp := projection_normal p hR.le (y - η • reply) hfw
    have heq : y - η • reply - x = η • n := by
      dsimp [n]; rw [smul_sub, ← hxy]; abel
    change ⟪y - η • reply - x, w - x⟫ ≤ 0 at hp
    rw [heq, real_inner_smul_left] at hp
    nlinarith
  have hx' := projection_feasible p hR.le (y - η • reply)
  have hmon : 0 ≤ ⟪I.grad x, x - u⟫ := by
    have hc := Gradient.convex_support hf hg x u
    have hmin := hm (Set.mem_univ x)
    change I.f u ≤ I.f x at hmin
    have heq : u - x = -(x - u) := by abel
    rw [heq, inner_neg_right] at hc
    linarith
  have hdist : ‖x - y‖ ≤ 2 * η * ‖I.grad y‖ := by
    have hp := projection_distance p hR.le hmix.1 (y - η • reply)
    have heq : y - η • reply - y = -(η • reply) := by abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hp
    have ht : ‖reply‖ ≤ 2 * ‖I.grad y‖ := by
      have hh := norm_sub_norm_le reply (I.grad y)
      have he : ‖reply - I.grad y‖ ≤ p.α * ‖I.grad y‖ := herr
      have hmul := mul_le_mul_of_nonneg_right hαmax (norm_nonneg (I.grad y))
      nlinarith [norm_nonneg (I.grad y)]
    have hmul := mul_le_mul_of_nonneg_left ht hη.le
    exact hp.trans (by nlinarith)
  have hdesc := local_projected_descent hR hαmax hη h0.le h1 hD hg hcont hs
    hu hx' hmix.1 hnorm hmon herr hv hxy hdist hG hηeq
  have hmirror : ‖projectBall p (s.z - a • reply) - u‖ ^ 2 ≤
      ‖s.z - a • (I.grad y + e) - u‖ ^ 2 := by
    have hh := projection_distance p hR.le (hu.trans (by linarith)) (s.z - a • reply)
    have heq : I.grad y + e = reply := by dsimp [e]; abel
    rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hc := mixing_identity (show s.A + a ≠ 0 by positivity) s.x s.z
  exact energy_step hf hg hA.le ha.le hα (by linarith) hu hz herr hw hc hdesc hmirror

end OracleTemplate.RelativeGeneralized
