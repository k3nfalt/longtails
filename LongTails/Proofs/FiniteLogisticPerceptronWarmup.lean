import LongTails.Proofs.FiniteLogisticTwoTapExecution
import LongTails.Proofs.FiniteLogisticTwoTapSpectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteLogisticPerceptronWarmup

lemma sigmoid_offset (s : ℝ) : |Real.sigmoid s - 1 / 2| ≤ |s| / 4 := by
  have H {x y : ℝ} (h : x ≤ y) : Real.sigmoid y - Real.sigmoid x ≤ 1 / 4 * (y - x) := by
    apply image_sub_le_mul_sub_of_deriv_le (fun t => (Real.hasDerivAt_sigmoid t).differentiableAt) _ h
    intro t
    rw [Real.deriv_sigmoid]
    nlinarith [sq_nonneg (Real.sigmoid t - 1 / 2)]
  rcases le_total 0 s with h | h
  · have hm := Real.sigmoid_strictMono.monotone h
    have hs := H h
    rw [Real.sigmoid_zero] at hs hm
    rw [abs_of_nonneg h, abs_of_nonneg (by linarith : 0 ≤ Real.sigmoid s - 1 / 2)]
    linarith
  · have hm := Real.sigmoid_strictMono.monotone h
    have hs := H h
    rw [Real.sigmoid_zero] at hs hm
    rw [abs_of_nonpos h, abs_of_nonpos (by linarith : Real.sigmoid s - 1 / 2 ≤ 0)]
    linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma component_remainder (A : E →L[ℝ] E) (x : E) :
    ‖(Real.sigmoid (-⟪A x, x⟫ / 2) - 1 / 2) • A x‖ ≤ ‖A‖ ^ 2 * ‖x‖ ^ 3 / 8 := by
  rw [norm_smul, Real.norm_eq_abs]
  have h := sigmoid_offset (-⟪A x, x⟫ / 2)
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  have h₁ := abs_real_inner_le_norm (A x) x
  have h₂ := A.le_opNorm x
  calc
    _ ≤ (‖A‖ * ‖x‖ * ‖x‖ / 8) * (‖A‖ * ‖x‖) := by
      apply mul_le_mul _ h₂ (norm_nonneg _) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right h₂ (norm_nonneg x)]
    _ = _ := by ring

lemma batch_remainder (A B : E →L[ℝ] E) (η : ℝ) (hη : 0 ≤ η) (x : E) :
    ‖(x + (η / 2) • (Real.sigmoid (-⟪A x, x⟫ / 2) • A x +
        Real.sigmoid (-⟪B x, x⟫ / 2) • B x)) -
      (x + (η / 4) • (A x + B x))‖ ≤
        η * (‖A‖ ^ 2 + ‖B‖ ^ 2) / 16 * ‖x‖ ^ 3 := by
  have he (a b : ℝ) (u v : E) :
      (x + (η / 2) • (a • u + b • v)) - (x + (η / 4) • (u + v)) =
      (η / 2) • ((a - 1 / 2) • u + (b - 1 / 2) • v) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ η / 2)]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)) ?_
  nlinarith [mul_le_mul_of_nonneg_left (component_remainder A x) hη,
    mul_le_mul_of_nonneg_left (component_remainder B x) hη]

omit [InnerProductSpace ℝ E] in
lemma trajectory_error {q C r K : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hs : 8 * C * r ^ 3 ≤ K * (q ^ 3 - q))
    (x y : ℕ → E) (h₀ : x 0 = y 0)
    (hy : ∀ t, ‖y t‖ ≤ r * q ^ t)
    (hstep : ∀ t, ‖x (t+1) - y (t+1)‖ ≤ q * ‖x t - y t‖ + C * ‖x t‖ ^ 3)
    (t : ℕ) (hsize : K * (q ^ t) ^ 2 ≤ r) :
    ‖x t - y t‖ ≤ K * q ^ t * ((q ^ t) ^ 2 - 1) := by
  induction t with
  | zero => simp [h₀]
  | succ t ih =>
    have hq₀ := zero_le_one.trans hq
    have hp : 0 ≤ q ^ t := pow_nonneg hq₀ _
    have ht : K * (q ^ t) ^ 2 ≤ r := by
      refine le_trans ?_ hsize
      gcongr
      exact Nat.le_succ t
    have he := ih ht
    have he' : ‖x t - y t‖ ≤ r * q ^ t := by
      nlinarith [mul_le_mul_of_nonneg_right ht hp, mul_nonneg hK hp]
    have hx : ‖x t‖ ≤ 2 * (r * q ^ t) := by linarith [norm_sub_norm_le (x t) (y t), hy t]
    have hcube := pow_le_pow_left₀ (norm_nonneg _) hx 3
    have H := hstep t
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left he hq₀, mul_le_mul_of_nonneg_left hcube hC,
      mul_le_mul_of_nonneg_right hs (pow_nonneg hp 3)]

open LongTails.Setups.FiniteLogisticTwoTap
open LongTails.Proofs.FiniteLogisticTwoTapExecution
open LongTails.Proofs.FiniteLogisticTwoTapSpectrum

lemma iterate_alignment {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i)
    (w : Weights d) (μ η r K : ℝ) (hμ : 0 ≤ μ) (hη : 0 ≤ η) (hw : ‖w‖ ≤ r)
    (hK : 0 ≤ K) (n : ℕ) :
    let s := η * μ / 4
    let A := sampleMatrix (signedInput μ i false)
    let B := sampleMatrix (signedInput μ i true)
    s ≤ 1 → 8 * (η * (‖A‖ ^ 2 + ‖B‖ ^ 2) / 16) * r ^ 3 ≤ K * ((1 + s) ^ 3 - (1 + s)) →
    K * ((1 + s) ^ n) ^ 2 ≤ r →
    ‖(step μ η i)^[n] w - (1 + s) ^ n • growingPart i w‖ ≤
      3 * r + K * (1 + s) ^ n * (((1 + s) ^ n) ^ 2 - 1) := by
  intro s A B hs hcoef hsize
  let M := sampleMatrix (EuclideanSpace.single i 1)
  let L := fun x : Weights d => x - s • M x
  have hg (x : Weights d) : L x = x + (η / 4) • (A x + B x) := by
    change x - s • M x = x + (η / 4) • ((A + B) x)
    dsimp only [A, B, M, s]
    rw [sum_matrices, smul_apply]
    module
  have hL (x : Weights d) : ‖L x‖ ≤ (1+s) * ‖x‖ := by
    rw [hg]
    exact linear_growth i hi hμ hη x
  have hdiff (x y : Weights d) : L x - L y = L (x - y) := by
    simp only [L, map_sub, smul_sub]
    abel
  have hs₀ : 0 ≤ s := by dsimp [s]; positivity
  have hn (t : ℕ) : ‖L^[t] w‖ ≤ r * (1+s)^t := by
    induction t with
    | zero => simpa
    | succ t ih =>
      rw [Function.iterate_succ_apply', pow_succ]
      nlinarith [hL (L^[t] w), mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+s by linarith)]
  have hb (x : Weights d) : ‖step μ η i x - L x‖ ≤ η * (‖A‖^2 + ‖B‖^2) / 16 * ‖x‖^3 := by
    rw [hg]
    simpa only [step, answer, neg_div, A, B] using batch_remainder A B η hη x
  have he := trajectory_error (q := 1+s) (C := η * (‖A‖^2 + ‖B‖^2) / 16)
    (by linarith) (by positivity) hK hcoef (fun t => (step μ η i)^[t] w)
    (fun t => L^[t] w) rfl hn (fun t => by
      simp only [Function.iterate_succ_apply']
      grw [norm_sub_le_norm_sub_add_norm_sub _ (L ((step μ η i)^[t] w)) _, hb, hdiff, hL]
      linarith) n hsize
  have hl := linear_residual i hi hs₀ hs w n
  change ‖L^[n] w - _‖ ≤ _ at hl
  linarith [norm_sub_le_norm_sub_add_norm_sub ((step μ η i)^[n] w) (L^[n] w)
    ((1 + s)^n • growingPart i w)]

lemma finite_radius_alignment {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i) (w : Weights d)
    {μ η r : ℝ} (hμ : 0 < μ) (hμ' : μ ≤ 1) (hη : 0 ≤ η) (hw : ‖w‖ ≤ r) (n : ℕ) :
    let q := 1 + η * μ / 4
    let K := 80 * (d : ℝ) * r ^ 3 / μ
    η * μ / 4 ≤ 1 → K * (q ^ n) ^ 2 ≤ r →
    ‖(step μ η i)^[n] w - q ^ n • growingPart i w‖ ≤ 3 * r + K * (q ^ n) ^ 3 := by
  intro q K hs hsize
  have hr := (norm_nonneg w).trans hw
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcoeff := signed_norms i hμ.le hμ'
  have hkμ : K * μ = 80 * (d : ℝ) * r ^ 3 := div_mul_cancel₀ _ hμ.ne'
  have hbound : 2 * (η * μ / 4) ≤ q ^ 3 - q := by
    dsimp [q]
    nlinarith [pow_nonneg (show 0 ≤ η*μ by positivity) 3, sq_nonneg (η*μ)]
  have he := iterate_alignment i hi w μ η r K hμ.le hη hw hK n hs (by
    change _ ≤ K * (q ^ 3 - q)
    have h₁ := mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ η * r ^ 3 by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hbound hK, congrArg (fun z => η * z) hkμ]) hsize
  change ‖_ - q ^ n • _‖ ≤ 3 * r + K * q ^ n * ((q ^ n) ^ 2 - 1) at he
  nlinarith [mul_nonneg hK (pow_nonneg hq n)]

lemma entry_error {D μ ρ r M : ℝ} (hD : 1 ≤ D) (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ' : ρ ≤ 1) (hr : 0 ≤ r)
    (hr' : r ^ 2 * D ^ 4 ≤ μ * ρ ^ 3 / 2 ^ 48)
    (hlo : 16384 * D ≤ M * ρ) (hhi : M * ρ ≤ 32768 * D) :
    let K := 80 * D * r ^ 3 / μ
    K * M ^ 2 ≤ r ∧ 3 * r + K * M ^ 3 ≤ r * M * ρ / (1024 * D) := by
  have hD₀ : 0 < D := by linarith
  have hM : 0 ≤ M := by
    by_contra! h
    linarith [mul_neg_of_neg_of_pos h hρ]
  have hMsq := pow_le_pow_left₀ (mul_nonneg hM hρ.le) hhi 2
  have haux : 163840 * D ^ 2 * r ^ 2 * M ^ 2 ≤ μ * ρ := by
    apply le_of_mul_le_mul_right (a := ρ ^ 2) _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hMsq (show 0 ≤ D ^ 2 * r ^ 2 by positivity),
      mul_nonneg hμ.le (pow_nonneg hρ.le 3)]
  let K := 80 * D * r ^ 3 / μ
  have hk : K * M ^ 2 * (2048 * D) ≤ r * ρ := by
    have he : K * μ = 80 * D * r ^ 3 := div_mul_cancel₀ _ hμ.ne'
    apply le_of_mul_le_mul_right (a := μ) _ hμ
    nlinarith [mul_le_mul_of_nonneg_right haux hr,
      congrArg (fun z : ℝ => z * (M^2 * D)) he]
  change K * M ^ 2 ≤ r ∧ _
  constructor
  · apply le_of_mul_le_mul_right (a := 2048 * D) _ (by positivity)
    exact hk.trans (mul_le_mul_of_nonneg_left (by linarith) hr)
  · apply (le_div_iff₀ (by positivity : 0 < 1024 * D)).mpr
    change (3 * r + K * M ^ 3) * (1024 * D) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hk hM, mul_le_mul_of_nonneg_left hlo hr]

lemma warmup_horizon {q M : ℝ} (hq : 1 < q) (hq' : q ≤ 2) (hM : 1 ≤ M) :
    let n := ⌈Real.log M / Real.log q⌉₊
    M ≤ q ^ n ∧ q ^ n ≤ 2 * M := by
  intro n
  have hq₀ : 0 < q := by linarith
  have hM₀ : 0 < M := by linarith
  have hl := Real.log_pos hq
  have hratio := div_nonneg (Real.log_nonneg hM) hl.le
  have hlo : Real.log M ≤ n * Real.log q :=
    (div_le_iff₀ hl).mp (Nat.le_ceil _)
  have hhi : (n : ℝ) ≤ Real.log M / Real.log q + 1 := (Nat.ceil_lt_add_one hratio).le
  have hlog : Real.log (q ^ n) ≤ Real.log (q * M) := by
    rw [Real.log_pow, Real.log_mul hq₀.ne' hM₀.ne']
    have H := mul_le_mul_of_nonneg_right hhi hl.le
    rw [add_mul, div_mul_cancel₀ _ hl.ne'] at H
    linarith
  refine ⟨(Real.log_le_log_iff hM₀ (pow_pos hq₀ _)).mp (by rwa [Real.log_pow]), ?_⟩
  exact ((Real.log_le_log_iff (pow_pos hq₀ _) (mul_pos hq₀ hM₀)).mp hlog).trans
    (mul_le_mul_of_nonneg_right hq' hM₀.le)

lemma warmup_at_scale (p : Params) (hp : spec.valid p) (i : Fin p.d)
    (hi : finRotate p.d i ≠ i) {η : ℝ} (hη : 0 < η) (hs : η * p.μ / 4 ≤ 1)
    (w : Weights p.d) (hw : ‖w‖ ≤ p.r) :
    let q := 1 + η * p.μ / 4
    let n := ⌈Real.log (16384 * (p.d : ℝ) / p.ρ) / Real.log q⌉₊
    ‖(step p.μ η i)^[n] w - q ^ n • growingPart i w‖ ≤
      p.r * q ^ n * p.ρ / (1024 * (p.d : ℝ)) := by
  obtain ⟨hd, hμ, hμ', hρ, hρ', hr, hcap⟩ := hp
  have hD : (1 : ℝ) ≤ p.d := by exact_mod_cast (show 1 ≤ p.d by omega)
  have hD₀ : (0 : ℝ) < p.d := by linarith
  intro q n
  have hq : 1 < q := by dsimp [q]; linarith [mul_pos hη hμ]
  have hM : 1 ≤ 16384 * (p.d : ℝ) / p.ρ := by
    apply (le_div_iff₀ hρ).mpr
    linarith
  obtain ⟨hlo,hhi⟩ := warmup_horizon hq (by dsimp [q]; linarith) hM
  change _ ≤ q ^ n at hlo
  change q ^ n ≤ _ at hhi
  have hhi' : q ^ n ≤ 32768 * (p.d : ℝ) / p.ρ := by
    calc
      _ ≤ _ := hhi
      _ = _ := by ring
  have hR := (le_div_iff₀ (by positivity : 0 < 2 ^ 24 * (p.d : ℝ) ^ 2)).mp hcap
  have hR₂ := pow_le_pow_left₀ (show 0 ≤ p.r * (2^24 * (p.d : ℝ)^2) by positivity) hR 2
  have hsq := Real.sq_sqrt (mul_nonneg hμ.le hρ.le)
  have hc := entry_error hD hμ hρ hρ'.le hr.le (by
    nlinarith [congrArg (fun z : ℝ => z * p.ρ^2) hsq])
    ((div_le_iff₀ hρ).mp hlo) ((le_div_iff₀ hρ).mp hhi')
  exact (finite_radius_alignment i hi w hμ (by linarith) hη.le hw n hs hc.1).trans hc.2

end LongTails.Proofs.FiniteLogisticPerceptronWarmup
