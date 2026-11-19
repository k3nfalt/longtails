import LongTails.Proofs.AdditiveCubeAnchoringExecution
import LongTails.Proofs.SmoothBanachAnchoring

open LongTails.Setups.AdditiveCubeFixedPoint LongTails.Algorithms.AdditiveCubeAnchoring

namespace LongTails.Proofs.AdditiveCubeAnchoringRate

open AdditiveCubeAnchoringExecution SmoothBanachAnchoring

variable {p : Params}

lemma mean_ne {T : Cube p → Cube p} (hT : LipschitzWith 1 T) (x y : Point p) :
    ‖mean T x - mean T y‖ ≤ ‖x-y‖ := by
  have h := (hT.comp (project_lipschitz p)).dist_le_mul x y
  simpa only [Function.comp_apply, one_mul, NNReal.coe_one, Subtype.dist_eq, dist_eq_norm, mean] using h

lemma root_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E)
    (hF : ∀ x y, ‖F x - F y‖ ≤ ‖x-y‖) {a : ℝ} (ha : 0 < a) (b u z v : E)
    (hu : (1+a) • u - F u - b = 0) (hv : (1+8*a) • v - F v - (b + (7*a) • z) = 0) :
    ‖z-v‖ ≤ 2 * ‖z-u‖ ∧ ‖v-F v‖ ≤ ‖u-F u‖ + 14*a*‖z-u‖ := by
  have eq := sub_eq_zero.mp hu
  have eqv := sub_eq_zero.mp hv
  have hid : (1+8*a) • u - F u - (b+(7*a) • z) = (7*a) • (u-z) := by rw [← eq]; module
  have h := anchored_inverse_bound F hF (8*a) (by positivity) (b+(7*a) • z) u v hv
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), norm_sub_rev u z] at h
  have hmove : ‖u-v‖ ≤ ‖z-u‖ := by
    apply le_of_mul_le_mul_left (a := a) _ ha
    nlinarith [mul_nonneg ha.le (norm_nonneg (z-u))]
  have hres : (v-F v) - (u-F u) = (7*a) • (z-u) + (8*a) • (u-v) := by
    have hFu : F u = (1+a) • u-b := by rw [← eq]; abel
    have hFv : F v = (1+8*a) • v-(b+(7*a) • z) := by rw [← eqv]; abel
    rw [hFu,hFv]
    module
  have htriangle := norm_add_le ((7*a) • (z-u)) ((8*a) • (u-v))
  rw [← hres, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity), abs_of_pos (by positivity)] at htriangle
  constructor
  · linarith [norm_sub_le_norm_sub_add_norm_sub z u v]
  · have ht := norm_sub_le_norm_sub_add_norm_sub (v-F v) (u-F u) 0
    simp only [sub_zero] at ht
    linarith

lemma picard_distance {T : Cube p → Cube p} (hT : LipschitzWith 1 T)
    (M : ℕ) (hM : 0 < M) (b u x noise : Point p)
    (hu : (1 + (M : ℝ)⁻¹) • u - mean T u - b = 0) :
    ‖picard T M b x noise-u‖ ≤ (1 + (M : ℝ)⁻¹)⁻¹ * ‖x-u‖ + ‖noise‖ := by
  let a := (M : ℝ)⁻¹
  let q := (1+a)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' : q ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hr : (1+a) • u = b + mean T u := by
    have hh := sub_eq_zero.mp hu
    rw [sub_eq_iff_eq_add] at hh
    exact hh
  have hid : picard T M b x noise - u = q • ((mean T x-mean T u)+noise) := by
    have he : q • ((1+a) • u) = u := by rw [smul_smul, inv_mul_cancel₀ (by linarith : 1+a ≠ 0), one_smul]
    calc picard T M b x noise - u = q • (b+(mean T x+noise)) - q • ((1+a) • u) := by rw [he]; rfl
         _ = _ := by rw [hr, ← smul_sub]; congr 1; abel
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  have ht := (norm_add_le (mean T x-mean T u) noise).trans (add_le_add (mean_ne hT x u) le_rfl)
  nlinarith [mul_le_mul_of_nonneg_left ht hq, mul_le_mul_of_nonneg_right hq' (norm_nonneg noise)]

lemma decay {M : ℕ} (hM : 0 < M) : ((1 + (M : ℝ)⁻¹)⁻¹)^(6*M) ≤ 1/64 := by
  have hp : 0 < (M : ℝ) := by exact_mod_cast hM
  have h := one_add_mul_le_pow (show -2 ≤ (M : ℝ)⁻¹ by linarith [inv_nonneg.mpr hp.le]) M
  rw [mul_inv_cancel₀ hp.ne'] at h
  rw [Nat.mul_comm, pow_mul, inv_pow, inv_pow, one_div]
  apply (inv_le_inv₀ (by positivity) (by norm_num : 0 < (64:ℝ))).mpr
  exact (by norm_num : (64:ℝ) = (1+1)^6).le.trans (pow_le_pow_left₀ (by norm_num) h 6)

noncomputable def noiseSum (ξ : ℕ → Point p) (off n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ‖blockSum ξ (off+j*n) n‖ / n

lemma iter_distance {T : Cube p → Cube p} (hT : LipschitzWith 1 T) (ξ : ℕ → Point p)
    (off M n : ℕ) (hM : 0 < M) (b x u : Point p)
    (hu : (1+(M : ℝ)⁻¹) • u - mean T u - b = 0) (k : ℕ) :
    ‖iter T ξ off M n b x k-u‖ ≤ ((1+(M : ℝ)⁻¹)⁻¹)^k * ‖x-u‖ + noiseSum ξ off n k := by
  let q := (1+(M : ℝ)⁻¹)⁻¹
  have ha : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' : q ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  induction k with
  | zero => simp [iter, noiseSum]
  | succ k ih =>
    rw [iter]
    apply (picard_distance hT M hM _ _ _ _ hu).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := mul_le_mul_of_nonneg_left ih hq
    have hn : 0 ≤ noiseSum ξ off n k := Finset.sum_nonneg (fun _ _ => by positivity)
    have hh := mul_le_mul_of_nonneg_right hq' hn
    simp only [noiseSum, Finset.sum_range_succ, pow_succ] at *
    dsimp only [q] at *
    linarith only [hb, hh, show (n : ℝ)⁻¹ * ‖blockSum ξ (off+k*n) n‖ = ‖blockSum ξ (off+k*n) n‖/n by ring]

noncomputable def totalNoise (ξ : ℕ → Point p) : ℕ → ℕ → ℕ → ℝ
  | 0, n, off => noiseSum ξ off n 6
  | m+1, n, off =>
    let M : ℕ := 8^(m+1)
    (M : ℝ)⁻¹ * noiseSum ξ off n (6*M) + totalNoise ξ m (4*n) (off+6*M*n)

lemma terminal_residual {T : Cube p → Cube p} (hT : LipschitzWith 1 T) (ξ : ℕ → Point p)
    (m n off : ℕ) (hn : 0 < n) (x b u : Point p)
    (hu : (1+((8^m : ℕ) : ℝ)⁻¹) • u - mean T u - b = 0) :
    let y := (run T ξ (program m n) off (x,b,0)).1
    ‖y - mean T y‖ ≤ ‖u - mean T u‖ + ((8^m : ℕ) : ℝ)⁻¹ * ‖x-u‖ + 30 * totalNoise ξ m n off := by
  induction m generalizing off n b x u with
  | zero =>
    let M : ℕ := 8^0
    let a := ((M : ℕ) : ℝ)⁻¹
    let z := iter T ξ off M n b x (6*M)
    have hM : 0 < M := by dsimp [M]; positivity
    have ha : 0 < a := by dsimp [a]; positivity
    have hstage := run_stage T ξ off M n hM hn b x
    have hd : ‖z-u‖ ≤ 1/64 * ‖x-u‖ + noiseSum ξ off n (6*M) :=
      (iter_distance hT ξ off M n hM b x u hu _).trans
        (add_le_add (mul_le_mul_of_nonneg_right (decay hM) (norm_nonneg _)) le_rfl)
    have hnoise : 0 ≤ noiseSum ξ off n (6*M) := Finset.sum_nonneg (fun _ _ => by positivity)
    dsimp only [program]
    change run T ξ (stage 1 n) off (x,b,0) = _ at hstage
    rw [hstage]
    have hres := norm_sub_le_norm_sub_add_norm_sub z u (mean T z)
    have hres' := norm_sub_le_norm_sub_add_norm_sub u (mean T u) (mean T z)
    rw [norm_sub_rev (mean T u) (mean T z)] at hres'
    have hmean := mean_ne hT z u
    change ‖z-mean T z‖ ≤ ‖u-mean T u‖ + (↑(8^0 : ℕ) : ℝ)⁻¹ * ‖x-u‖ + 30 * noiseSum ξ off n 6
    norm_num only [pow_zero, Nat.cast_one, inv_one, one_mul]
    change 0 ≤ noiseSum ξ off n 6 at hnoise
    change ‖z-u‖ ≤ 1/64 * ‖x-u‖ + noiseSum ξ off n 6 at hd
    linarith [norm_nonneg (x-u)]
  | succ m ih =>
    let M : ℕ := 8^(m+1)
    let a := ((M : ℕ) : ℝ)⁻¹
    let z := iter T ξ off M n b x (6*M)
    have hM : 0 < M := by dsimp [M]; positivity
    have ha : 0 < a := by dsimp [a]; positivity
    have hstage := run_stage T ξ off M n hM hn b x
    have hd : ‖z-u‖ ≤ 1/64 * ‖x-u‖ + noiseSum ξ off n (6*M) :=
      (iter_distance hT ξ off M n hM b x u hu _).trans
        (add_le_add (mul_le_mul_of_nonneg_right (decay hM) (norm_nonneg _)) le_rfl)
    have hnoise : 0 ≤ noiseSum ξ off n (6*M) := Finset.sum_nonneg (fun _ _ => by positivity)
    let b' := b + (7*a) • z
    have ha' : ((8^m : ℕ) : ℝ)⁻¹ = 8*a := by
      dsimp [a, M]
      push_cast
      rw [pow_succ, mul_inv]
      ring
    obtain ⟨v,hv⟩ := exists_anchored_root (mean T) (mean_ne hT) (8*a) (by positivity) b'
    have hroot := root_step (mean T) (mean_ne hT) ha b u z v hu hv
    rw [← ha'] at hv
    have hnext := ih (4*n) (off+6*M*n) (by omega) z b' v hv
    dsimp only [program]
    rw [run_append, stage_length _ _ hM hn, hstage]
    apply hnext.trans
    change ‖v-mean T v‖ + ((8^m : ℕ) : ℝ)⁻¹ * ‖z-v‖ + _ ≤
      ‖u-mean T u‖ + a * ‖x-u‖ + 30 * (a * noiseSum ξ off n (6*M) + totalNoise ξ m (4*n) (off+6*M*n))
    rw [ha']
    have hdist := mul_le_mul_of_nonneg_left hroot.1 ha.le
    have hsum := mul_le_mul_of_nonneg_left hd ha.le
    nlinarith only [hroot.2, hdist, hsum, mul_nonneg ha.le (norm_nonneg (x-u))]

end LongTails.Proofs.AdditiveCubeAnchoringRate
