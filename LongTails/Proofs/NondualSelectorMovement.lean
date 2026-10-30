import LongTails.Proofs.NondualProjection
import LongTails.Proofs.NondualSphericalMoments
import LongTails.Proofs.AdamNormalizedMoments
import LongTails.Proofs.AdaptiveHistoryTracking

open Set MeasureTheory Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.NondualSelectorMovement

open NondualProjection NondualSphericalMoments OracleTemplate.ZerothOrder
open LongTails.Algorithms.NondualSelector

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : E) 1
local notation "Q" => (sphereLaw E : Measure S)

omit [NeZero d] in
lemma inner_le_l1 {x u : E} {C R : ℝ} (hC : 0 ≤ C)
    (hx : ∀ i, |x i| ≤ C) (hu : ∑ i, |u i| ≤ R) : |⟪x, u⟫| ≤ C * R := by
  rw [PiLp.inner_apply]
  calc
    |∑ i, ⟪x i, u i⟫| ≤ ∑ i, |⟪x i, u i⟫| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| * |u i| := by simp [abs_mul, mul_comm]
    _ ≤ ∑ i, C * |u i| := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = C * ∑ i, |u i| := (Finset.mul_sum _ _ _).symm
    _ ≤ C * R := mul_le_mul_of_nonneg_left hu hC

omit [NeZero d] in
lemma potential_total_bound (K : ℕ → Set E) (T : ℕ)
    (hne : ∀ t ≤ T, (K t).Nonempty) (hco : ∀ t ≤ T, IsCompact (K t))
    (hcv : ∀ t ≤ T, Convex ℝ (K t))
    {R C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hl1 : ∀ t ≤ T, ∀ u ∈ K t, ∑ i, |u i| ≤ R)
    (x : E) (hx : ∀ i, |x i| ≤ C) :
    (∑ t ∈ Finset.range T, (value (K (t + 1)) (r • x) - value (K t) (r • x))) ≤
      R ^ 2 / 2 + 2 * r * C * R := by
  have hb (t : ℕ) (ht : t ≤ T) := value_bounds (hne t ht) (hco t ht) (hcv t ht)
    (r • x) (R := R) (B := r * C * R)
    (fun u hu => (AdamNormalizedMoments.norm_le_coordinate_sum u).trans (hl1 t ht u hu))
    (fun u hu => inner_le_l1 (mul_nonneg hr hC)
      (fun i => by simpa [abs_mul, abs_of_nonneg hr] using mul_le_mul_of_nonneg_left (hx i) hr)
      (hl1 t ht u hu))
  rw [Finset.sum_range_sub (fun t => value (K t) (r • x)) T]
  have h0 := (hb 0 (Nat.zero_le T)).1
  have hT := (hb T le_rfl).2
  linarith

omit [NeZero d] in
lemma potential_increment_nonneg {K L : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (hneL : L.Nonempty) (hcoL : IsCompact L)
    (hcvL : Convex ℝ L) (hLK : L ⊆ K) (x : E) :
    0 ≤ value L x - value K x :=
  sub_nonneg.mpr (value_mono hne hco hcv hneL hcoL hcvL hLK x)

lemma sum_inner_integral_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → E) (Δ : ι → E → ℝ) (hc : ∀ i ∈ s, Continuous (Δ i))
    (hΔ : ∀ i ∈ s, ∀ x, 0 ≤ Δ i x) :
    (∑ i ∈ s, ∫ u : S, ⟪a i, (u : E)⟫ * Δ i u ∂Q) ≤
      Real.sqrt (∫ u : S, maximumSquare s hs a u ∂Q) *
        Real.sqrt (∫ u : S, (∑ i ∈ s, Δ i u) ^ 2 ∂Q) := by
  let b : E → ℝ := fun x => Real.sqrt (maximumSquare s hs a x)
  let F : E → ℝ := fun x => ∑ i ∈ s, Δ i x
  have hb : Continuous b := (maximumSquare_continuous s hs a).sqrt
  have hF : Continuous F := continuous_finsetSum s hc
  have hb0 (x : E) : 0 ≤ b x := Real.sqrt_nonneg _
  have hF0 (x : E) : 0 ≤ F x := Finset.sum_nonneg fun i hi => hΔ i hi x
  have hbi : MemLp (fun u : S => b u) 2 Q :=
    (memLp_two_iff_integrable_sq (hb.comp continuous_subtype_val).aestronglyMeasurable).mpr
      (sphere_integrable_continuous (hb.pow 2))
  have hFi : MemLp (fun u : S => F u) 2 Q :=
    (memLp_two_iff_integrable_sq (hF.comp continuous_subtype_val).aestronglyMeasurable).mpr
      (sphere_integrable_continuous (hF.pow 2))
  have hint (i : ι) (hi : i ∈ s) :
      Integrable (fun u : S => ⟪a i, (u : E)⟫ * Δ i u) Q :=
    sphere_integrable_continuous (f := fun x : E => ⟪a i, x⟫ * Δ i x)
      (Continuous.mul (by fun_prop) (hc i hi))
  have hp (u : S) : (∑ i ∈ s, ⟪a i, (u : E)⟫ * Δ i u) ≤ b u * F u := by
    dsimp [F]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hΔ i hi u)
    exact (le_abs_self _).trans (inner_abs_le_maximumSquare_sqrt s hs a u hi)
  have hj := integral_mono (integrable_finsetSum s hint)
    (sphere_integrable_continuous (hb.mul hF)) hp
  rw [integral_finsetSum s hint] at hj
  have hcs := AdaptiveHistoryTracking.integral_mul_le_square_moments hbi hFi
    (fun u => hb0 u) (fun u => hF0 u)
  have he : (fun u : S => b u ^ 2) = fun u : S => maximumSquare s hs a u := by
    funext u
    exact Real.sq_sqrt (maximumSquare_nonneg s hs a u)
  rw [he] at hcs
  exact hj.trans hcs

lemma exists_norming_unit (w : E) : ∃ a : E, ‖a‖ = 1 ∧ ⟪a, w⟫ = ‖w‖ := by
  by_cases hw : w = 0
  · refine ⟨EuclideanSpace.single ⟨0, NeZero.pos d⟩ 1, by simp, ?_⟩
    simp [hw]
  · refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · simp [norm_smul, hw]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp

lemma sum_norm_integral_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Δ : ι → E → ℝ) (hc : ∀ i ∈ s, Continuous (Δ i))
    (hΔ : ∀ i ∈ s, ∀ x, 0 ≤ Δ i x) :
    ∃ a : ι → E, (∀ i, ‖a i‖ = 1) ∧
      (∑ i ∈ s, ‖∫ u : S, Δ i u • (u : E) ∂Q‖) ≤
        Real.sqrt (∫ u : S, maximumSquare s hs a u ∂Q) *
          Real.sqrt (∫ u : S, (∑ i ∈ s, Δ i u) ^ 2 ∂Q) := by
  choose a ha he using fun i => exists_norming_unit (∫ u : S, Δ i u • (u : E) ∂Q)
  refine ⟨a, ha, ?_⟩
  have hint (i : ι) (hi : i ∈ s) :
      Integrable (fun u : S => Δ i u • (u : E)) Q :=
    sphere_integrable_continuous_map (f := fun x : E => Δ i x • x)
      ((hc i hi).smul continuous_id)
  have hid (i : ι) (hi : i ∈ s) :
      ‖∫ u : S, Δ i u • (u : E) ∂Q‖ = ∫ u : S, ⟪a i, (u : E)⟫ * Δ i u ∂Q := by
    rw [← he i, ← integral_inner (hint i hi)]
    apply integral_congr_ae
    filter_upwards [] with u
    simp [real_inner_smul_right, mul_comm]
  simp_rw [Finset.sum_congr rfl hid]
  exact sum_inner_integral_le s hs a Δ hc hΔ

lemma sum_norm_integral_sq_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Δ : ι → E → ℝ) (hc : ∀ i ∈ s, Continuous (Δ i))
    (hΔ : ∀ i ∈ s, ∀ x, 0 ≤ Δ i x)
    (k : ℕ) (hk : k ≠ 0) (hcard : s.card ≤ 2 ^ k) :
    (d : ℝ) * (∑ i ∈ s, ‖∫ u : S, Δ i u • (u : E) ∂Q‖) ^ 2 ≤
      4 * k * (∫ u : S, (∑ i ∈ s, Δ i u) ^ 2 ∂Q) := by
  obtain ⟨a, ha, hM⟩ := sum_norm_integral_le s hs Δ hc hΔ
  have hU : 0 ≤ ∫ u : S, maximumSquare s hs a u ∂Q :=
    integral_nonneg fun u => maximumSquare_nonneg s hs a u
  have hV : 0 ≤ ∫ u : S, (∑ i ∈ s, Δ i u) ^ 2 ∂Q :=
    integral_nonneg fun u => sq_nonneg _
  have hM0 : 0 ≤ ∑ i ∈ s, ‖∫ u : S, Δ i u • (u : E) ∂Q‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hM2 := pow_le_pow_left₀ hM0 hM 2
  rw [mul_pow, Real.sq_sqrt hU, Real.sq_sqrt hV] at hM2
  have hmom := maximumSquare_integral_le s hs a (fun i _ => ha i) k hk hcard
  calc
    (d : ℝ) * (∑ i ∈ s, ‖∫ u : S, Δ i u • (u : E) ∂Q‖) ^ 2 ≤
        (d : ℝ) * ((∫ u : S, maximumSquare s hs a u ∂Q) *
          (∫ u : S, (∑ i ∈ s, Δ i u) ^ 2 ∂Q)) :=
      mul_le_mul_of_nonneg_left hM2 (by positivity)
    _ = ((d : ℝ) * (∫ u : S, maximumSquare s hs a u ∂Q)) *
        (∫ u : S, (∑ i ∈ s, Δ i u) ^ 2 ∂Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmom hV

noncomputable def coordinateMaximum (x : E) : ℝ :=
  Real.sqrt (maximumSquare Finset.univ Finset.univ_nonempty
    (fun i : Fin d => EuclideanSpace.single i 1) x)

lemma coordinateMaximum_continuous : Continuous (coordinateMaximum (d := d)) :=
  (maximumSquare_continuous _ _ _).sqrt

lemma coordinateMaximum_nonneg (x : E) : 0 ≤ coordinateMaximum x := Real.sqrt_nonneg _

lemma coordinate_abs_le (x : E) (i : Fin d) : |x i| ≤ coordinateMaximum x := by
  simpa [PiLp.inner_apply, coordinateMaximum] using
    inner_abs_le_maximumSquare_sqrt Finset.univ Finset.univ_nonempty
      (fun j : Fin d => EuclideanSpace.single j 1) x (Finset.mem_univ i)

lemma coordinateMaximum_moment (k : ℕ) (hk : k ≠ 0) (hd : d ≤ 2 ^ k) :
    (d : ℝ) * (∫ u : S, coordinateMaximum (u : E) ^ 2 ∂Q) ≤ 4 * k := by
  have he (u : S) : coordinateMaximum (u : E) ^ 2 =
      maximumSquare Finset.univ Finset.univ_nonempty
        (fun i : Fin d => EuclideanSpace.single i 1) u :=
    Real.sq_sqrt (maximumSquare_nonneg _ _ _ _)
  simp_rw [he]
  exact maximumSquare_integral_le Finset.univ Finset.univ_nonempty _
    (by intro i hi; simp) k hk (by simpa using hd)

lemma potential_total_square_integral (K : ℕ → Set E) (T : ℕ)
    (hne : ∀ t ≤ T, (K t).Nonempty) (hco : ∀ t ≤ T, IsCompact (K t))
    (hcv : ∀ t ≤ T, Convex ℝ (K t)) (hnest : ∀ t < T, K (t + 1) ⊆ K t)
    {R r : ℝ} (hr : 0 ≤ r)
    (hl1 : ∀ t ≤ T, ∀ u ∈ K t, ∑ i, |u i| ≤ R)
    (k : ℕ) (hk : k ≠ 0) (hd : d ≤ 2 ^ k) :
    (d : ℝ) * (∫ u : S,
      (∑ t ∈ Finset.range T, (value (K (t + 1)) (r • (u : E)) -
        value (K t) (r • (u : E)))) ^ 2 ∂Q) ≤
      (d : ℝ) * R ^ 4 / 2 + 32 * r ^ 2 * R ^ 2 * k := by
  let F : E → ℝ := fun x => ∑ t ∈ Finset.range T,
    (value (K (t + 1)) (r • x) - value (K t) (r • x))
  have hv (t : ℕ) (ht : t ≤ T) : Continuous (value (K t)) :=
    value_continuous (hne t ht) (hco t ht) (hcv t ht)
  have hrx : Continuous (fun x : E => r • x) := by fun_prop
  have hF : Continuous F := by
    exact continuous_finsetSum (Finset.range T) (fun t ht =>
      ((hv (t + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp ht))).comp hrx).sub
        ((hv t (Nat.le_of_lt (Finset.mem_range.mp ht))).comp hrx))
  have hF0 (x : E) : 0 ≤ F x := by
    apply Finset.sum_nonneg
    intro t ht
    have ht' := Finset.mem_range.mp ht
    exact potential_increment_nonneg (hne t (by omega)) (hco t (by omega))
      (hcv t (by omega)) (hne (t + 1) (by omega)) (hco (t + 1) (by omega))
      (hcv (t + 1) (by omega)) (hnest t ht') _
  have hFb (x : E) : F x ≤ R ^ 2 / 2 + 2 * r * coordinateMaximum x * R :=
    potential_total_bound K T hne hco hcv (coordinateMaximum_nonneg x) hr hl1 x
      (coordinate_abs_le x)
  have hp (x : E) : F x ^ 2 ≤ R ^ 4 / 2 + 8 * r ^ 2 * R ^ 2 * coordinateMaximum x ^ 2 := by
    have h := pow_le_pow_left₀ (hF0 x) (hFb x) 2
    nlinarith [sq_nonneg (R ^ 2 / 2 - 2 * r * coordinateMaximum x * R)]
  have hiC : Integrable (fun u : S => coordinateMaximum (u : E) ^ 2) Q :=
    sphere_integrable_continuous (coordinateMaximum_continuous.pow 2)
  have hi := integral_mono (sphere_integrable_continuous (hF.pow 2))
    (integrable_const (R ^ 4 / 2) |>.add (hiC.const_mul (8 * r ^ 2 * R ^ 2)))
    (fun u => hp u)
  change (∫ u : S, F u ^ 2 ∂Q) ≤
    ∫ u : S, R ^ 4 / 2 + 8 * r ^ 2 * R ^ 2 * coordinateMaximum (u : E) ^ 2 ∂Q at hi
  rw [integral_add (integrable_const _) (hiC.const_mul _), integral_const,
    integral_const_mul] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul] at hi
  have hm := coordinateMaximum_moment k hk hd
  have hi' := mul_le_mul_of_nonneg_left hi (show 0 ≤ (d : ℝ) by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8 * r ^ 2 * R ^ 2 by positivity)
  change (d : ℝ) * (∫ u : S, F u ^ 2 ∂Q) ≤ _
  nlinarith

lemma center_step_norm {K L : Set E} (hne : K.Nonempty) (hco : IsCompact K)
    (hcv : Convex ℝ K) (hneL : L.Nonempty) (hcoL : IsCompact L)
    (hcvL : Convex ℝ L) {r : ℝ} (hr : 0 < r) :
    ‖center L r - center K r‖ = (d : ℝ) / r *
      ‖∫ u : S, (value L (r • (u : E)) - value K (r • (u : E))) • (u : E) ∂Q‖ := by
  rw [center_difference hne hco hcv hneL hcoL hcvL hr.ne', norm_neg]
  simp_rw [← smul_smul]
  rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma nested_movement_square (K : ℕ → Set E) (T : ℕ)
    (hne : ∀ t ≤ T, (K t).Nonempty) (hco : ∀ t ≤ T, IsCompact (K t))
    (hcv : ∀ t ≤ T, Convex ℝ (K t)) (hnest : ∀ t < T, K (t + 1) ⊆ K t)
    {R r : ℝ} (hr : 0 < r)
    (hl1 : ∀ t ≤ T, ∀ u ∈ K t, ∑ i, |u i| ≤ R)
    (kd kt : ℕ) (hkd : kd ≠ 0) (hkt : kt ≠ 0)
    (hd : d ≤ 2 ^ kd) (ht : T ≤ 2 ^ kt) :
    r ^ 2 * (∑ t ∈ Finset.range T, ‖center (K (t + 1)) r - center (K t) r‖) ^ 2 ≤
      2 * d * R ^ 4 * kt + 128 * r ^ 2 * R ^ 2 * kd * kt := by
  by_cases hT : T = 0
  · simp only [hT, Finset.range_zero, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]
    positivity
  let Δ : ℕ → E → ℝ := fun t x => value (K (t + 1)) (r • x) - value (K t) (r • x)
  have hv (t : ℕ) (ht : t ≤ T) : Continuous (value (K t)) :=
    value_continuous (hne t ht) (hco t ht) (hcv t ht)
  have hrx : Continuous (fun x : E => r • x) := by fun_prop
  have hc (t : ℕ) (ht : t ∈ Finset.range T) : Continuous (Δ t) :=
    ((hv (t + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp ht))).comp hrx).sub
      ((hv t (Nat.le_of_lt (Finset.mem_range.mp ht))).comp hrx)
  have hΔ (t : ℕ) (ht : t ∈ Finset.range T) (x : E) : 0 ≤ Δ t x := by
    have ht' := Finset.mem_range.mp ht
    exact potential_increment_nonneg (hne t (by omega)) (hco t (by omega))
      (hcv t (by omega)) (hne (t + 1) (by omega)) (hco (t + 1) (by omega))
      (hcv (t + 1) (by omega)) (hnest t ht') _
  have hI := sum_norm_integral_sq_le (Finset.range T)
    (Finset.nonempty_range_iff.mpr hT) Δ hc hΔ kt hkt (by simpa using ht)
  have hP := potential_total_square_integral K T hne hco hcv hnest hr.le hl1 kd hkd hd
  have he : (∑ t ∈ Finset.range T, ‖center (K (t + 1)) r - center (K t) r‖) =
      (d : ℝ) / r * (∑ t ∈ Finset.range T, ‖∫ u : S, Δ t u • (u : E) ∂Q‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    exact center_step_norm (hne t (by omega)) (hco t (by omega)) (hcv t (by omega))
      (hne (t + 1) (by omega)) (hco (t + 1) (by omega)) (hcv (t + 1) (by omega)) hr
  rw [he]
  have hI' := mul_le_mul_of_nonneg_left hI (show 0 ≤ (d : ℝ) by positivity)
  have hP' := mul_le_mul_of_nonneg_left hP (show 0 ≤ 4 * (kt : ℝ) by positivity)
  change (d : ℝ) * (∫ u : S, (∑ t ∈ Finset.range T, Δ t u) ^ 2 ∂Q) ≤ _ at hP
  change 4 * (kt : ℝ) * ((d : ℝ) *
    (∫ u : S, (∑ t ∈ Finset.range T, Δ t u) ^ 2 ∂Q)) ≤ _ at hP'
  have heq (w : ℝ) : r ^ 2 * ((d : ℝ) / r * w) ^ 2 = (d : ℝ) ^ 2 * w ^ 2 := by
    field_simp [hr.ne']
  rw [heq]
  nlinarith only [hI', hP']

lemma nested_movement_bound (K : ℕ → Set E) (T : ℕ)
    (hne : ∀ t ≤ T, (K t).Nonempty) (hco : ∀ t ≤ T, IsCompact (K t))
    (hcv : ∀ t ≤ T, Convex ℝ (K t)) (hnest : ∀ t < T, K (t + 1) ⊆ K t)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hl1 : ∀ t ≤ T, ∀ u ∈ K t, ∑ i, |u i| ≤ R)
    (kd kt : ℕ) (hkd : kd ≠ 0) (hkt : kt ≠ 0)
    (hd : d ≤ 2 ^ kd) (ht : T ≤ 2 ^ kt)
    (hscale : r ^ 2 * kd = R ^ 2 * d) :
    (∑ t ∈ Finset.range T, ‖center (K (t + 1)) r - center (K t) r‖) ≤
      12 * R * Real.sqrt ((kd : ℝ) * kt) := by
  have h := nested_movement_square K T hne hco hcv hnest hr hl1 kd kt hkd hkt hd ht
  have he := congrArg (fun x : ℝ => 2 * R ^ 2 * kt * x) hscale
  have hb : (∑ t ∈ Finset.range T, ‖center (K (t + 1)) r - center (K t) r‖) ^ 2 ≤
      130 * R ^ 2 * kd * kt := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
    nlinarith only [h, he]
  have hm : 0 ≤ ∑ t ∈ Finset.range T, ‖center (K (t + 1)) r - center (K t) r‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hs := Real.sq_sqrt (show 0 ≤ (kd : ℝ) * kt by positivity)
  have hrhs : 0 ≤ 12 * R * Real.sqrt ((kd : ℝ) * kt) := by positivity
  apply (sq_le_sq₀ hm hrhs).mp
  calc
    _ ≤ 130 * R ^ 2 * kd * kt := hb
    _ ≤ 144 * R ^ 2 * kd * kt := by gcongr; norm_num
    _ = (12 * R * Real.sqrt ((kd : ℝ) * kt)) ^ 2 := by rw [mul_pow, mul_pow, hs]; ring

end LongTails.Proofs.NondualSelectorMovement
