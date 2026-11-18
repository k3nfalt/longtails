import LongTails.Proofs.TailEntropyDual
import LongTails.Proofs.GeneralizedSmoothHardDualSegments

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set Finset
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.TailEntropySegments

open TailEntropyCurvature TailEntropyDual CompactConjugate
open GeneralizedSmoothHardDual (radial radial_derivative radial_second_derivative nonnegative_norm_le_sum feasible)
open GeneralizedSmoothHardDualSegments (path path_nonnegative path_norm path_sum_positive)

noncomputable def slopeN (m : ℕ) (z u : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range m, (u k * (Real.log (z k / tail z m k) + 1) - z k / tail z m k * tail u m k)

noncomputable def curvN (m : ℕ) (z u : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range m, TailEntropyCurvature.residual m z u k ^ 2 / z k

lemma tail_line (m k : ℕ) (a u : ℕ → ℝ) (t : ℝ) :
    tail (fun i => a i + t * u i) m k = tail a m k + t * tail u m k := by
  simp [tail, Finset.sum_add_distrib, Finset.mul_sum]

lemma tail_hasDerivAt (m k : ℕ) (a u : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (fun t => tail a m k + t * tail u m k) (tail u m k) x := by
  simpa using ((hasDerivAt_id x).mul_const (tail u m k)).const_add (tail a m k)

lemma coord_hasDerivAt (a u : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t => a k + t * u k) (u k) x := by
  simpa using ((hasDerivAt_id x).mul_const (u k)).const_add (a k)

section

variable (m : ℕ) (a u : ℕ → ℝ) (x : ℝ)
  (hnn : ∀ k < m, 0 ≤ a k + x * u k)
  (hcase : ∀ k < m, 0 < a k + x * u k ∨ (a k = 0 ∧ u k = 0))

include hnn hcase

omit hcase in
lemma tail_pos_of_pos {k : ℕ} (hk : k < m) (hp : 0 < a k + x * u k) :
    0 < tail a m k + x * tail u m k := by
  have h := tail_le (fun i => a i + x * u i) hk hnn
  rw [tail_line] at h
  linarith

lemma term_hasDerivAt {k : ℕ} (hk : k < m) :
    HasDerivAt (fun t => entropyTerm (a k + t * u k) (tail a m k + t * tail u m k))
      (u k * (Real.log ((a k + x * u k) / (tail a m k + x * tail u m k)) + 1) -
        (a k + x * u k) / (tail a m k + x * tail u m k) * tail u m k) x := by
  rcases hcase k hk with hp | ⟨ha, hu⟩
  · have hT := tail_pos_of_pos m a u x hnn hk hp
    have hz := coord_hasDerivAt a u k x
    have hTd := tail_hasDerivAt m k a u x
    set T := tail a m k + x * tail u m k with hTdef
    set U := tail u m k
    set w := a k + x * u k with hwdef
    have hq : HasDerivAt (fun t => (a k + t * u k) / (tail a m k + t * tail u m k))
        ((u k * T - w * U) / T ^ 2) x := hz.div hTd hT.ne'
    have hqpos : 0 < w / T := div_pos hp hT
    have hl : HasDerivAt (fun t => Real.log ((a k + t * u k) / (tail a m k + t * tail u m k)))
        ((u k * T - w * U) / T ^ 2 / (w / T)) x := hq.log hqpos.ne'
    have hm : HasDerivAt (fun t => (a k + t * u k) *
        Real.log ((a k + t * u k) / (tail a m k + t * tail u m k)))
        (u k * Real.log (w / T) + w * ((u k * T - w * U) / T ^ 2 / (w / T))) x := hz.mul hl
    have key : w * ((u k * T - w * U) / T ^ 2 / (w / T)) = u k - w / T * U := by
      field_simp
    unfold entropyTerm
    rw [key] at hm
    convert hm using 1
    ring
  · have hconst : (fun t => entropyTerm (a k + t * u k) (tail a m k + t * tail u m k)) =
        fun _ => 0 := by
      funext t; simp [entropyTerm, ha, hu]
    rw [hconst, ha, hu]
    simpa using hasDerivAt_const x (0 : ℝ)

lemma slopeTerm_hasDerivAt {k : ℕ} (hk : k < m) :
    HasDerivAt (fun t => u k * (Real.log ((a k + t * u k) / (tail a m k + t * tail u m k)) + 1) -
        (a k + t * u k) / (tail a m k + t * tail u m k) * tail u m k)
      ((u k - (a k + x * u k) * ((tail u m k) / (tail a m k + x * tail u m k))) ^ 2 /
        (a k + x * u k)) x := by
  rcases hcase k hk with hp | ⟨ha, hu⟩
  · have hT := tail_pos_of_pos m a u x hnn hk hp
    have hz := coord_hasDerivAt a u k x
    have hTd := tail_hasDerivAt m k a u x
    set T := tail a m k + x * tail u m k with hTdef
    set U := tail u m k
    set w := a k + x * u k with hwdef
    have hq : HasDerivAt (fun t => (a k + t * u k) / (tail a m k + t * tail u m k))
        ((u k * T - w * U) / T ^ 2) x := hz.div hTd hT.ne'
    have hqpos : 0 < w / T := div_pos hp hT
    have hl : HasDerivAt (fun t => Real.log ((a k + t * u k) / (tail a m k + t * tail u m k)))
        ((u k * T - w * U) / T ^ 2 / (w / T)) x := hq.log hqpos.ne'
    have hd : HasDerivAt (fun t => u k * (Real.log ((a k + t * u k) / (tail a m k + t * tail u m k)) + 1) -
        (a k + t * u k) / (tail a m k + t * tail u m k) * U)
        (u k * ((u k * T - w * U) / T ^ 2 / (w / T)) - (u k * T - w * U) / T ^ 2 * U) x :=
      ((hl.add_const 1).const_mul (u k)).sub (hq.mul_const U)
    have key : u k * ((u k * T - w * U) / T ^ 2 / (w / T)) - (u k * T - w * U) / T ^ 2 * U =
        (u k - w * (U / T)) ^ 2 / w := by
      field_simp
    rw [key] at hd
    exact hd
  · have hconst : (fun t => u k * (Real.log ((a k + t * u k) / (tail a m k + t * tail u m k)) + 1) -
        (a k + t * u k) / (tail a m k + t * tail u m k) * tail u m k) = fun _ => 0 := by
      funext t; simp [ha, hu]
    rw [hconst, ha, hu]
    simpa using hasDerivAt_const x (0 : ℝ)

lemma entropy_hasDerivAt :
    HasDerivAt (fun t => ∑ k ∈ range m, entropyTerm (a k + t * u k) (tail a m k + t * tail u m k))
      (slopeN m (fun k => a k + x * u k) u) x := by
  have h := HasDerivAt.fun_sum (u := range m) (fun k hk => term_hasDerivAt m a u x hnn hcase
    (Finset.mem_range.mp hk))
  unfold slopeN
  simp only [tail_line] at h ⊢
  exact h

lemma slope_hasDerivAt :
    HasDerivAt (fun t => slopeN m (fun k => a k + t * u k) u)
      (curvN m (fun k => a k + x * u k) u) x := by
  have h := HasDerivAt.fun_sum (u := range m) (fun k hk => slopeTerm_hasDerivAt m a u x hnn hcase
    (Finset.mem_range.mp hk))
  unfold slopeN curvN TailEntropyCurvature.residual ratio
  simp only [tail_line]
  exact h

end

noncomputable def dualSlope {m : ℕ} (L₀ L₁ : ℝ) (z w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  2 * (∑ i, w i) * (Real.log (1 + L₁ * (∑ i, z i) / L₀) / L₁) +
    28 / L₁ * (slopeN m (ext z) (ext w) + Real.log m * ∑ i, w i)

noncomputable def dualCurvature {m : ℕ} (L₀ L₁ : ℝ) (z w : EuclideanSpace ℝ (Fin m)) : ℝ :=
  2 * (∑ i, w i) ^ 2 / (L₀ + L₁ * ∑ i, z i) + 28 / L₁ * curvN m (ext z) (ext w)

lemma ext_path {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (t : ℝ) (k : ℕ) :
    ext (path x y t) k = ext x k + t * ext (y - x) k := by
  simp only [path, ext_add, ext_smul, ext_sub]
  ring

lemma sum_path {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    ∑ i, path x y t i = ∑ i, x i + t * ∑ i, (y - x) i := by
  simp only [path, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma tailEntropy_path {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    tailEntropy (path x y t) = ∑ k ∈ range m,
      entropyTerm (ext x k + t * ext (y - x) k) (tail (ext x) m k + t * tail (ext (y - x)) m k) := by
  unfold tailEntropy
  apply Finset.sum_congr rfl
  intro k _
  have he : ext (path x y t) = fun i => ext x i + t * ext (y - x) i := funext (ext_path x y t)
  rw [he, tail_line]

section

variable {m : ℕ} (L₀ L₁ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (x y : EuclideanSpace ℝ (Fin m))
  (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)

include hL₀ hL₁ hx hy

omit hL₀ hL₁ in
lemma path_cases (s : ℝ) (hs : s ∈ Set.Ioo 0 1) (k : ℕ) (_hk : k < m) :
    0 < ext x k + s * ext (y - x) k ∨ (ext x k = 0 ∧ ext (y - x) k = 0) := by
  have hxk := ext_nonneg x hx k
  have hyk := ext_nonneg y hy k
  rw [ext_sub]
  by_cases h0 : ext x k = 0 ∧ ext y k = 0
  · right; rw [h0.1, h0.2]; simp
  · left
    have he : ext x k + s * (ext y k - ext x k) = (1 - s) * ext x k + s * ext y k := by ring
    rw [he]
    rcases not_and_or.mp h0 with h | h
    · have : 0 < ext x k := lt_of_le_of_ne hxk (Ne.symm h)
      nlinarith [hs.1, hs.2]
    · have : 0 < ext y k := lt_of_le_of_ne hyk (Ne.symm h)
      nlinarith [hs.1, hs.2]

omit hL₀ hL₁ in
lemma path_ext_nonneg (s : ℝ) (hs : s ∈ Set.Icc 0 1) (k : ℕ) :
    0 ≤ ext x k + s * ext (y - x) k := by
  rw [← ext_path]
  exact ext_nonneg _ (path_nonnegative x y hx hy s hs) k

lemma dual_path_hasDerivAt (s : ℝ) (hs : s ∈ Set.Ioo 0 1) :
    HasDerivAt (fun t => dual L₀ L₁ (path x y t)) (dualSlope L₀ L₁ (path x y s) (y - x)) s := by
  have hcases := path_cases x y hx hy s hs
  have hnn (k : ℕ) (_ : k < m) := path_ext_nonneg x y hx hy s ⟨hs.1.le, hs.2.le⟩ k
  have hent := entropy_hasDerivAt m (ext x) (ext (y - x)) s hnn hcases
  have hZ : 0 ≤ ∑ i, path x y s i := Finset.sum_nonneg (fun i _ =>
    path_nonnegative x y hx hy s ⟨hs.1.le, hs.2.le⟩ i)
  have hlin : HasDerivAt (fun t => ∑ i, x i + t * ∑ i, (y - x) i) (∑ i, (y - x) i) s := by
    simpa using ((hasDerivAt_id s).mul_const (∑ i, (y - x) i)).const_add (∑ i, x i)
  have hZs : ∑ i, x i + s * ∑ i, (y - x) i = ∑ i, path x y s i := (sum_path x y s).symm
  have hr := ((radial_derivative L₀ L₁ _ hL₀ hL₁ (hZs ▸ hZ)).comp s hlin).const_mul 2
  have hh := hr.add (((hent.add (hlin.const_mul (Real.log m)))).const_mul (28 / L₁))
  have hfun : (fun t => dual L₀ L₁ (path x y t)) = fun t =>
      2 * radial L₀ L₁ (∑ i, x i + t * ∑ i, (y - x) i) +
        28 / L₁ * (∑ k ∈ range m, entropyTerm (ext x k + t * ext (y - x) k)
          (tail (ext x) m k + t * tail (ext (y - x)) m k) +
          Real.log m * (∑ i, x i + t * ∑ i, (y - x) i)) := by
    funext t
    unfold dual
    rw [tailEntropy_path, sum_path]
  rw [hfun]
  convert hh using 1
  · rfl
  unfold dualSlope
  have he : ext (path x y s) = fun k => ext x k + s * ext (y - x) k := funext (ext_path x y s)
  rw [he, ← hZs]
  ring

lemma dualSlope_path_hasDerivAt (s : ℝ) (hs : s ∈ Set.Ioo 0 1) :
    HasDerivAt (fun t => dualSlope L₀ L₁ (path x y t) (y - x))
      (dualCurvature L₀ L₁ (path x y s) (y - x)) s := by
  have hcases := path_cases x y hx hy s hs
  have hnn (k : ℕ) (_ : k < m) := path_ext_nonneg x y hx hy s ⟨hs.1.le, hs.2.le⟩ k
  have hsl := slope_hasDerivAt m (ext x) (ext (y - x)) s hnn hcases
  have hZ : 0 ≤ ∑ i, path x y s i := Finset.sum_nonneg (fun i _ =>
    path_nonnegative x y hx hy s ⟨hs.1.le, hs.2.le⟩ i)
  have hlin : HasDerivAt (fun t => ∑ i, x i + t * ∑ i, (y - x) i) (∑ i, (y - x) i) s := by
    simpa using ((hasDerivAt_id s).mul_const (∑ i, (y - x) i)).const_add (∑ i, x i)
  have hZs : ∑ i, x i + s * ∑ i, (y - x) i = ∑ i, path x y s i := (sum_path x y s).symm
  have hr := ((radial_second_derivative L₀ L₁ _ hL₀ hL₁ (hZs ▸ hZ)).comp s hlin).const_mul
    (2 * ∑ i, (y - x) i)
  have hh := hr.add ((hsl.add_const (Real.log m * ∑ i, (y - x) i)).const_mul (28 / L₁))
  have hfun : (fun t => dualSlope L₀ L₁ (path x y t) (y - x)) = fun t =>
      2 * (∑ i, (y - x) i) * (Real.log (1 + L₁ * (∑ i, x i + t * ∑ i, (y - x) i) / L₀) / L₁) +
        28 / L₁ * (slopeN m (fun k => ext x k + t * ext (y - x) k) (ext (y - x)) +
          Real.log m * ∑ i, (y - x) i) := by
    funext t
    unfold dualSlope
    have he : ext (path x y t) = fun k => ext x k + t * ext (y - x) k := funext (ext_path x y t)
    rw [he, sum_path]
  rw [hfun]
  convert hh using 1
  · rfl
  unfold dualCurvature
  have he : ext (path x y s) = fun k => ext x k + s * ext (y - x) k := funext (ext_path x y s)
  rw [he, ← hZs]
  field_simp

lemma dualCurvature_lower (s : ℝ) (hs : s ∈ Set.Ioo 0 1) (hne : x ≠ y) :
    ‖y - x‖ ^ 2 / (L₀ + L₁ * max ‖x‖ ‖y‖) ≤ dualCurvature L₀ L₁ (path x y s) (y - x) := by
  set z := path x y s with hzdef
  have hz : ∀ i, 0 ≤ z i := path_nonnegative x y hx hy s ⟨hs.1.le, hs.2.le⟩
  have hZ : 0 < ∑ i, z i := path_sum_positive x y hx hy hne s hs
  set Z := ∑ i, z i with hZdef
  set U := ∑ i, (y - x) i with hUdef
  set N := max ‖x‖ ‖y‖
  have hzN : ‖z‖ ≤ N := path_norm x y s ⟨hs.1.le, hs.2.le⟩
  have hzZ : ‖z‖ ≤ Z := nonnegative_norm_le_sum z hz
  have hnz := norm_nonneg z
  have hD : 0 < L₀ + L₁ * N := by have := norm_nonneg x; positivity
  have hcases := path_cases x y hx hy s hs
  have hzu : ∀ k < m, ext z k = 0 → ext (y - x) k = 0 := by
    intro k hk h0
    rcases hcases k hk with hp | hp
    · rw [hzdef, ext_path] at h0; linarith
    · exact hp.2
  have hbound := curvature_bound m (ext z) (ext (y - x)) ‖z‖ (fun k _ => ext_nonneg z hz k) hzu
    (fun k _ => ext_le_norm z k)
  have hTz : tail (ext z) m 0 = Z := (sum_eq_tail z).symm
  have hTu : tail (ext (y - x)) m 0 = U := (sum_eq_tail (y - x)).symm
  have hcurv0 : 0 ≤ curvN m (ext z) (ext (y - x)) := by
    unfold curvN
    exact Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (ext_nonneg z hz k))
  have hnorm : ‖y - x‖ ^ 2 ≤ 2 * (U / Z) ^ 2 * ‖z‖ ^ 2 +
      2 * (14 * ‖z‖ * curvN m (ext z) (ext (y - x))) := by
    rw [norm_sq_eq (y - x), norm_sq_eq z]
    have hpt (k : ℕ) : ext (y - x) k ^ 2 ≤ 2 * ((U / Z) ^ 2 * ext z k ^ 2) +
        2 * (ext (y - x) k - ratio m (ext z) (ext (y - x)) 0 * ext z k) ^ 2 := by
      have hr : ratio m (ext z) (ext (y - x)) 0 = U / Z := by
        unfold ratio; rw [hTz, hTu]
      rw [hr]
      nlinarith [sq_nonneg (ext (y - x) k - 2 * (U / Z) * ext z k)]
    have hs := Finset.sum_le_sum (fun k (_ : k ∈ range m) => hpt k)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    unfold curvN
    rw [← Finset.mul_sum] at hs
    have h14 := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  have hfirst : 2 * (U / Z) ^ 2 * ‖z‖ ^ 2 / (L₀ + L₁ * N) ≤ 2 * U ^ 2 / (L₀ + L₁ * Z) := by
    rw [div_le_div_iff₀ hD (by positivity)]
    have hk : ‖z‖ ^ 2 * (L₀ + L₁ * Z) ≤ Z ^ 2 * (L₀ + L₁ * N) := by
      have h1 : ‖z‖ ^ 2 ≤ Z ^ 2 := pow_le_pow_left₀ hnz hzZ 2
      have h2 : ‖z‖ ^ 2 * Z ≤ Z ^ 2 * N := by
        have h3 : ‖z‖ * ‖z‖ ≤ Z * N := mul_le_mul hzZ hzN hnz hZ.le
        nlinarith [mul_le_mul_of_nonneg_right h3 hZ.le]
      nlinarith
    have hU := sq_nonneg U
    have hZ2 : 0 < Z ^ 2 := by positivity
    have he : 2 * (U / Z) ^ 2 * ‖z‖ ^ 2 * (L₀ + L₁ * Z) = 2 * U ^ 2 * (‖z‖ ^ 2 * (L₀ + L₁ * Z)) / Z ^ 2 := by
      field_simp
    rw [he, div_le_iff₀ hZ2]
    nlinarith [mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * U ^ 2 by positivity)]
  have hsecond : 2 * (14 * ‖z‖ * curvN m (ext z) (ext (y - x))) / (L₀ + L₁ * N) ≤
      28 / L₁ * curvN m (ext z) (ext (y - x)) := by
    rw [div_le_iff₀ hD]
    have : 28 * ‖z‖ ≤ 28 / L₁ * (L₀ + L₁ * N) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL₁]
      nlinarith
    nlinarith
  unfold dualCurvature
  rw [← hZdef, ← hUdef]
  have hsplit := div_le_div_of_nonneg_right hnorm hD.le
  rw [add_div] at hsplit
  linarith

lemma dual_segment_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    dual L₀ L₁ (path x y t) ≤ (1 - t) * dual L₀ L₁ x + t * dual L₀ L₁ y -
      (‖y - x‖ ^ 2 / (L₀ + L₁ * max ‖x‖ ‖y‖)) / 2 * t * (1 - t) := by
  by_cases he : x = y
  · subst y
    have hh : path x x t = x := by simp [path, ← add_smul]
    rw [hh]
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, sub_zero]
    nlinarith
  · have hc : Continuous (path x y) := by unfold path; fun_prop
    have hF : ContinuousOn (fun s => dual L₀ L₁ (path x y s)) (Set.Icc 0 1) :=
      (dual_continuousOn_nonnegative L₀ L₁ hL₀ hL₁).comp hc.continuousOn
        (fun s hs => path_nonnegative x y hx hy s hs)
    have hh := strong_segment_of_second_derivative _ _ _ _ hF
      (fun s hs => dual_path_hasDerivAt L₀ L₁ hL₀ hL₁ x y hx hy s hs)
      (fun s hs => dualSlope_path_hasDerivAt L₀ L₁ hL₀ hL₁ x y hx hy s hs)
      (fun s hs => dualCurvature_lower L₀ L₁ hL₀ hL₁ x y hx hy s hs he) t ht
    simpa only [path, sub_zero, sub_self, zero_smul, one_smul, zero_add, add_zero] using hh

end

end LongTails.Proofs.TailEntropySegments
