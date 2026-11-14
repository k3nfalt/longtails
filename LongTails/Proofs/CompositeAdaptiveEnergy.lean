import LongTails.Proofs.CompositeGeneralizedStep
import LongTails.Proofs.CompositeCubicAcceleration

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeAdaptive

open OracleTemplate.CompositeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma coupling_energy_surplus {f ψ : E → ℝ} {g : E → E} {Q : Set E} (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ)
    {A a M : ℝ} (hA : 0 < A) (ha : 0 < a) (hstep : 4 * M * a ^ 2 ≤ A + a)
    {x z p xs : E} (hx : x ∈ Q) (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun u => ‖u - z‖ ^ 2 / (2 * a) + ⟪g (mixPoint A a x z), u - z⟫ + ψ u)
      Q p)
    (hdesc : f (mixPoint A a x p) ≤ f (mixPoint A a x z) +
      ⟪g (mixPoint A a x z), mixPoint A a x p - mixPoint A a x z⟫ +
        M * ‖mixPoint A a x p - mixPoint A a x z‖ ^ 2) :
    (A + a) * (f (mixPoint A a x p) + ψ (mixPoint A a x p) - (f xs + ψ xs)) +
        ‖p - xs‖ ^ 2 / 2 + ‖p - z‖ ^ 2 / 4 +
        a * (f xs - f (mixPoint A a x z) - ⟪g (mixPoint A a x z), xs - mixPoint A a x z⟫) ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 := by
  have hS : 0 < A + a := by positivity
  set y := mixPoint A a x z
  set x' := mixPoint A a x p
  set gy := g y
  set l := A / (A + a)
  set m := a / (A + a)
  have hlm : l + m = 1 := by simp only [l, m]; field_simp
  have hl0 : 0 ≤ l := by positivity
  have hm0 : 0 ≤ m := by positivity
  have e1 : x' - y = m • (p - z) := mix_sub_mix A a x z p
  have e2 : x' - y = l • (x - y) + m • (p - y) := by
    have h : l • (x - y) + m • (p - y) = (l • x + m • p) - (l + m) • y := by module
    rw [h, hlm, one_smul]
    rfl
  have i1 : ⟪gy, x' - y⟫ = l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, p - xs⟫) := by
    rw [e2, inner_add_right, inner_smul_right, inner_smul_right,
      show p - y = (xs - y) + (p - xs) by abel, inner_add_right]
  have n1 : ‖x' - y‖ ^ 2 = m ^ 2 * ‖p - z‖ ^ 2 := by
    rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have c1 := Gradient.convex_support hc hf y x
  have c2 := Gradient.convex_support hc hf y xs
  have hψx' : ψ x' ≤ l * ψ x + m * ψ p := by
    have h := hψ.2 hx hp hl0 hm0 hlm
    simp only [smul_eq_mul] at h
    exact h
  have tp := prox_three_point hQ hψ ha hp hmin hxs
  have hq : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) ≤ ‖p - z‖ ^ 2 / 4 := by
    have e : (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) =
        (4 * M * a ^ 2) / (A + a) * (‖p - z‖ ^ 2 / 4) := by
      simp only [m]; field_simp
    rw [e]
    have hfrac : (4 * M * a ^ 2) / (A + a) ≤ 1 := (div_le_one hS).mpr hstep
    have hn : 0 ≤ ‖p - z‖ ^ 2 / 4 := by positivity
    nlinarith
  have hd := mul_le_mul_of_nonneg_left hdesc hS.le
  rw [i1, n1] at hd
  have ex1 : (A + a) * (f y + (l * ⟪gy, x - y⟫ + m * (⟪gy, xs - y⟫ + ⟪gy, p - xs⟫)) +
      M * (m ^ 2 * ‖p - z‖ ^ 2)) =
      (A + a) * f y + A * ⟪gy, x - y⟫ + a * ⟪gy, xs - y⟫ + a * ⟪gy, p - xs⟫ +
        (A + a) * (M * (m ^ 2 * ‖p - z‖ ^ 2)) := by
    simp only [l, m]; field_simp; ring
  rw [ex1] at hd
  have hψ' := mul_le_mul_of_nonneg_left hψx' hS.le
  have ex2 : (A + a) * (l * ψ x + m * ψ p) = A * ψ x + a * ψ p := by
    simp only [l, m]; field_simp
  rw [ex2] at hψ'
  have k1 := mul_le_mul_of_nonneg_left c1 hA.le
  have k2 := mul_le_mul_of_nonneg_left c2 ha.le
  nlinarith

lemma accepted_energy_surplus {f ψ : E → ℝ} {g : E → E} {Q : Set E}
    {prox : ℝ → E → E → E} {L0 L1 : ℝ}
    (h : Hyp f ψ g Q prox L0 L1) {A a : ℝ} (hA : 0 < A) (ha : 0 < a)
    {x z xs : E} (hx : x ∈ Q) (hxs : xs ∈ Q)
    (hc : 4 * (L0 + L1 * ‖g (mixPoint A a x z)‖) * a ^ 2 ≤ A + a)
    (hd : L1 * ‖mixPoint A a x (prox a z (g (mixPoint A a x z))) -
      mixPoint A a x z‖ ≤ 1 / 2) :
    (A + a) * (f (mixPoint A a x (prox a z (g (mixPoint A a x z)))) +
      ψ (mixPoint A a x (prox a z (g (mixPoint A a x z)))) - (f xs + ψ xs)) +
      ‖prox a z (g (mixPoint A a x z)) - xs‖ ^ 2 / 2 +
      ‖prox a z (g (mixPoint A a x z)) - z‖ ^ 2 / 4 +
      a * (f xs - f (mixPoint A a x z) - ⟪g (mixPoint A a x z), xs - mixPoint A a x z⟫) ≤
      A * (f x + ψ x - (f xs + ψ xs)) + ‖z - xs‖ ^ 2 / 2 := by
  have hp := h.proxSpec a ha z (g (mixPoint A a x z))
  apply coupling_energy_surplus h.convex h.grad h.setConvex h.regConvex hA ha hc hx hp.1 hxs hp.2
  exact ball_upper h.hL0.le h.hL1 h.grad h.cont h.smooth hd
    (by simp) le_rfl

lemma high_curvature_algebra {L0 L1 G q d B : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hG : 0 ≤ G) (hq : 0 ≤ q)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hqd : q ≤ d + G) (hdq : d ≤ q + G)
    (hhigh : 2 * (L0 + L1 * G) ≤ L1 * q)
    (hcoc : d ^ 2 ≤ 8 * (L0 + L1 * G + L1 * d) * B) :
    L0 + L1 * q ≤ 128 * L1 ^ 2 * B := by
  have hqpos : 0 < q := by nlinarith
  have hGq : 2 * G ≤ q := by nlinarith
  have hqd' : q ≤ 2 * d := by linarith
  have hc : L0 + L1 * G + L1 * d ≤ 2 * L1 * q := by nlinarith
  have hcB := mul_le_mul_of_nonneg_right hc hB
  have hdB : d ^ 2 ≤ 16 * L1 * q * B := by nlinarith
  have hsq : q ^ 2 ≤ 4 * d ^ 2 := by nlinarith [sq_nonneg (2 * d - q)]
  have hqB : q ≤ 64 * L1 * B := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hqB hL1.le
  nlinarith [mul_nonneg (sq_nonneg L1) hB]

lemma high_gradient_surplus {f : E → ℝ} {g : E → E} {L0 L1 G : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hc : ConvexOn ℝ univ f)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    (hs : SymmetricSmooth g L0 L1) (xs y : E) (hG : ‖g xs‖ ≤ G)
    (hhigh : 2 * (L0 + L1 * G) ≤ L1 * ‖g y‖) :
    L0 + L1 * ‖g y‖ ≤ 128 * L1 ^ 2 * (f xs - f y - ⟪g y, xs - y⟫) := by
  have hco := shifted_cocoercive hL0 hL1.le hc hf hg hs y xs
  have hB : 0 ≤ f xs - f y - ⟪g y, xs - y⟫ := by
    linarith [Gradient.convex_support hc hf y xs]
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hqd : ‖g y‖ ≤ ‖g xs - g y‖ + G := by
    have hh := norm_sub_norm_le (g y) (g xs)
    rw [norm_sub_rev] at hh
    linarith
  have hdq : ‖g xs - g y‖ ≤ ‖g y‖ + G := by
    have hh := norm_sub_le (g xs) (g y)
    linarith
  apply high_curvature_algebra hL0 hL1 hG0 (norm_nonneg _) (norm_nonneg _) hB hqd hdq hhigh
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hL1.le) hB
  nlinarith

omit [CompleteSpace E] in
lemma prox_variational {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q)
    (hψ : ConvexOn ℝ Q ψ) {a : ℝ} (ha : 0 < a) {z g p u : E}
    (hp : p ∈ Q) (hu : u ∈ Q)
    (hmin : IsMinOn (fun w => ‖w - z‖ ^ 2 / (2 * a) + ⟪g, w - z⟫ + ψ w) Q p) :
    ⟪p - z + a • g, p - u⟫ + a * (ψ p - ψ u) ≤ 0 := by
  have ht := prox_three_point hQ hψ ha hp hmin hu
  have hn : ‖z - u‖ ^ 2 = ‖p - u‖ ^ 2 + ‖p - z‖ ^ 2 -
      2 * ⟪p - z, p - u⟫ := by
    rw [show z - u = (p - u) - (p - z) by abel, norm_sub_sq_real,
      real_inner_comm (p - u) (p - z)]
    ring
  rw [inner_add_left, real_inner_smul_left]
  nlinarith

omit [CompleteSpace E] in
lemma prox_parameter_sensitivity {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q)
    (hψ : ConvexOn ℝ Q ψ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z g h p q : E} (hp : p ∈ Q) (hq : q ∈ Q)
    (hpa : IsMinOn (fun w => ‖w - z‖ ^ 2 / (2 * a) + ⟪g, w - z⟫ + ψ w) Q p)
    (hqb : IsMinOn (fun w => ‖w - z‖ ^ 2 / (2 * b) + ⟪h, w - z⟫ + ψ w) Q q) :
    ‖q - p‖ ≤ |b / a - 1| * ‖p - z‖ + b * ‖g - h‖ := by
  have hpv := prox_variational hQ hψ ha hp hq hpa
  have hqv := prox_variational hQ hψ hb hq hp hqb
  have hmul := mul_le_mul_of_nonneg_left hpv (div_nonneg hb.le ha.le)
  have hba : b / a * a = b := div_mul_cancel₀ b ha.ne'
  let w := (b / a - 1) • (p - z) + b • (g - h)
  have hi : ⟪q - z + b • h, q - p⟫ +
      b / a * ⟪p - z + a • g, p - q⟫ = ‖q - p‖ ^ 2 - ⟪w, q - p⟫ := by
    have he : q - z + b • h - (b / a) • (p - z + a • g) = q - p - w := by
      dsimp only [w]
      rw [smul_add, smul_smul, hba]
      module
    have hh := congrArg (fun v => ⟪v, q - p⟫) he
    rw [inner_sub_left, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hh
    rw [show p - q = -(q - p) by abel, inner_neg_right]
    simpa only [mul_neg, sub_eq_add_neg] using hh
  have hs : ‖q - p‖ ^ 2 ≤ ⟪w, q - p⟫ := by
    simp only [mul_add, ← mul_assoc, hba, mul_zero] at hmul
    linarith
  have hn : ‖w‖ ≤ |b / a - 1| * ‖p - z‖ + b * ‖g - h‖ := by
    calc
      ‖w‖ ≤ ‖(b / a - 1) • (p - z)‖ + ‖b • (g - h)‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb]
  have hc := real_inner_le_norm w (q - p)
  have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg (q - p))
  by_cases hz : ‖q - p‖ = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖q - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

lemma high_curvature_count {ι : Type*} (s : Finset ι) (A a S D : ι → ℝ)
    {L1 R H : ℝ} (hA : ∀ i ∈ s, 0 < A i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hD : ∀ i ∈ s, 0 ≤ D i)
    (hcurv : ∀ i ∈ s, A i ≤ 64 * a i ^ 2 * S i)
    (hhigh : ∀ i ∈ s, S i ≤ 128 * L1 ^ 2 * D i)
    (henergy : (∑ i ∈ s, a i * D i) ≤ 3 * R ^ 2)
    (hlog : (∑ i ∈ s, a i / A i) ≤ H) :
    (s.card : ℝ) ^ 2 ≤ 24576 * (L1 * R) ^ 2 * H := by
  have hu : ∀ i ∈ s, 0 ≤ a i * D i := fun i hi => mul_nonneg (ha i hi) (hD i hi)
  have hv : ∀ i ∈ s, 0 ≤ 8192 * L1 ^ 2 * (a i / A i) := by
    intro i hi
    exact mul_nonneg (by positivity) (div_nonneg (ha i hi) (hA i hi).le)
  have hp : ∀ i ∈ s, (1 : ℝ) ^ 2 ≤ (a i * D i) * (8192 * L1 ^ 2 * (a i / A i)) := by
    intro i hi
    have hm := mul_le_mul_of_nonneg_left (hhigh i hi) (by positivity : 0 ≤ 64 * a i ^ 2)
    have hb : A i ≤ 8192 * L1 ^ 2 * a i ^ 2 * D i := by nlinarith [hcurv i hi]
    have he : (a i * D i) * (8192 * L1 ^ 2 * (a i / A i)) =
        (8192 * L1 ^ 2 * a i ^ 2 * D i) / A i := by ring
    rw [he, one_pow]
    exact (one_le_div (hA i hi)).mpr hb
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hu hv hp
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have he : (∑ i ∈ s, 8192 * L1 ^ 2 * (a i / A i)) =
      8192 * L1 ^ 2 * ∑ i ∈ s, a i / A i := by rw [Finset.mul_sum]
  rw [he] at hc
  have hv0 : 0 ≤ 8192 * L1 ^ 2 * ∑ i ∈ s, a i / A i := by
    rw [← he]
    exact Finset.sum_nonneg hv
  have hvH := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 8192 * L1 ^ 2)
  calc
    (s.card : ℝ) ^ 2 ≤ (∑ i ∈ s, a i * D i) * (8192 * L1 ^ 2 * ∑ i ∈ s, a i / A i) := hc
    _ ≤ (3 * R ^ 2) * (8192 * L1 ^ 2 * H) :=
      mul_le_mul henergy hvH hv0 (by positivity)
    _ = _ := by ring

lemma displacement_count {ι : Type*} (s : Finset ι) (A a d : ι → ℝ)
    {L1 R H : ℝ} (hL1 : 0 ≤ L1) (hA : ∀ i ∈ s, 0 < A i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hd : ∀ i ∈ s, 0 ≤ d i)
    (hboundary : ∀ i ∈ s, A i ≤ 64 * L1 * a i * d i)
    (henergy : (∑ i ∈ s, d i ^ 2) ≤ 12 * R ^ 2)
    (hlog : (∑ i ∈ s, a i / A i) ≤ H) :
    (s.card : ℝ) ^ 3 ≤ 49152 * (L1 * R) ^ 2 * H ^ 2 := by
  have hu : ∀ i ∈ s, 0 ≤ a i / A i := fun i hi => div_nonneg (ha i hi) (hA i hi).le
  have hv : ∀ i ∈ s, 0 ≤ 64 * L1 * d i := fun i hi => by
    exact mul_nonneg (mul_nonneg (by norm_num) hL1) (hd i hi)
  have hp : ∀ i ∈ s, (1 : ℝ) ≤ (a i / A i) * (64 * L1 * d i) := by
    intro i hi
    have he : (a i / A i) * (64 * L1 * d i) = (64 * L1 * a i * d i) / A i := by ring
    rw [he]
    exact (one_le_div (hA i hi)).mpr (hboundary i hi)
  have hc := LongTails.Proofs.CompositeCubicAcceleration.bucket_count_cube s
    (fun i => a i / A i) (fun i => 64 * L1 * d i) (by norm_num : (0 : ℝ) ≤ 1) hu hv hp
  simp only [one_pow, mul_one] at hc
  have he : (∑ i ∈ s, (64 * L1 * d i) ^ 2) = 4096 * L1 ^ 2 * ∑ i ∈ s, d i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hvB : (∑ i ∈ s, (64 * L1 * d i) ^ 2) ≤ 49152 * (L1 * R) ^ 2 := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 4096 * L1 ^ 2)
    nlinarith
  have huH := pow_le_pow_left₀ (Finset.sum_nonneg hu) hlog 2
  calc
    (s.card : ℝ) ^ 3 ≤ (∑ i ∈ s, a i / A i) ^ 2 * (∑ i ∈ s, (64 * L1 * d i) ^ 2) := hc
    _ ≤ H ^ 2 * (49152 * (L1 * R) ^ 2) := mul_le_mul huH hvB (by positivity) (sq_nonneg H)
    _ = _ := by ring

omit [CompleteSpace E] in
lemma prox_distance_sharp {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q)
    (hψ : ConvexOn ℝ Q ψ) {a : ℝ} (ha : 0 < a) {z g p xs gs : E}
    (hp : p ∈ Q) (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun w => ‖w - z‖ ^ 2 / (2 * a) + ⟪g, w - z⟫ + ψ w) Q p)
    (hopt : ψ xs - ψ p ≤ ⟪gs, p - xs⟫) :
    ‖p - xs‖ ≤ ‖z - xs‖ + a * ‖g - gs‖ := by
  have hv := prox_variational hQ hψ ha hp hxs hmin
  have ho := mul_le_mul_of_nonneg_left hopt ha.le
  let w := z - xs - a • (g - gs)
  have hi : ⟪p - z + a • g, p - xs⟫ - a * ⟪gs, p - xs⟫ =
      ‖p - xs‖ ^ 2 - ⟪w, p - xs⟫ := by
    dsimp only [w]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    have hh : ⟪p, p - xs⟫ - ⟪xs, p - xs⟫ = ‖p - xs‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  have hb : ‖p - xs‖ ^ 2 ≤ ⟪w, p - xs⟫ := by linarith
  have hn : ‖w‖ ≤ ‖z - xs‖ + a * ‖g - gs‖ := by
    calc
      ‖w‖ ≤ ‖z - xs‖ + ‖a • (g - gs)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hc := real_inner_le_norm w (p - xs)
  have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg (p - xs))
  by_cases hz : ‖p - xs‖ = 0
  · rw [hz]
    positivity
  · have hpos : 0 < ‖p - xs‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

omit [CompleteSpace E] in
lemma prox_displacement_from_previous {ψ : E → ℝ} {Q : Set E}
    (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z v p g h : E} (hv : v ∈ Q) (hp : p ∈ Q)
    (hold : IsMinOn (fun w => ‖w - z‖ ^ 2 / (2 * a) + ⟪g, w - z⟫ + ψ w) Q v)
    (hnew : IsMinOn (fun w => ‖w - v‖ ^ 2 / (2 * b) + ⟪h, w - v⟫ + ψ w) Q p) :
    ‖p - v‖ ≤ b * (‖h - g‖ + ‖v - z‖ / a) := by
  have hvi := prox_variational hQ hψ ha hv hp hold
  have hopt : ψ v - ψ p ≤ ⟪g + (1 / a) • (v - z), p - v⟫ := by
    have he : ⟪v - z + a • g, v - p⟫ =
        -a * ⟪g + (1 / a) • (v - z), p - v⟫ := by
      rw [show v - p = -(p - v) by abel]
      simp only [inner_add_left, real_inner_smul_left, inner_neg_right]
      field_simp
      ring
    rw [he] at hvi
    nlinarith
  have hd := prox_distance_sharp hQ hψ hb hp hv hnew hopt
  simp only [sub_self, norm_zero, zero_add] at hd
  have hn : ‖h - (g + (1 / a) • (v - z))‖ ≤ ‖h - g‖ + ‖v - z‖ / a := by
    rw [show h - (g + (1 / a) • (v - z)) = (h - g) - (1 / a) • (v - z) by abel]
    have hh := norm_sub_le (h - g) ((1 / a) • (v - z))
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr ha),
      one_div_mul_eq_div] using hh
  exact hd.trans (mul_le_mul_of_nonneg_left hn hb.le)

end OracleTemplate.CompositeAdaptive
