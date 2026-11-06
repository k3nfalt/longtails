import LongTails.Proofs.GradientOnlyQuasarEnergy
import LongTails.Proofs.ConstrainedRegularization
import LongTails.Proofs.StochasticQuasarProx
import LongTails.Proofs.ComponentEnvelopeGeometry

open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma squared_distance_change (v z u : E) :
    |(‖v - u‖ ^ 2 - ‖z - u‖ ^ 2) / 2| ≤
      ‖v - z‖ * ‖z - u‖ + ‖v - z‖ ^ 2 / 2 := by
  have he : v - u = (v - z) + (z - u) := by abel
  have hi := abs_real_inner_le_norm (v - z) (z - u)
  rw [abs_le] at hi ⊢
  rw [he, norm_add_sq_real]
  constructor <;> nlinarith [sq_nonneg ‖v - z‖]

lemma projected_displacement {Q : Set E} {P : E → E} (hP : ConstrainedMonotone.Proj Q P)
    {z h : E} {c : ℝ} (hz : z ∈ Q) (hc : 0 ≤ c) :
    ‖P (z - c • h) - z‖ ≤ c * ‖h‖ := by
  have hh := hP.lipschitz.dist_le_mul (z - c • h) z
  rw [hP.fixed hz] at hh
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, sub_sub_cancel_left, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] using hh

lemma projected_distance_change {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {z h u : E} {c : ℝ}
    (hz : z ∈ Q) (hc : 0 ≤ c) :
    |(‖P (z - c • h) - u‖ ^ 2 - ‖z - u‖ ^ 2) / 2| ≤
      c * ‖h‖ * ‖z - u‖ + c ^ 2 * ‖h‖ ^ 2 / 2 := by
  have hd := projected_displacement hP hz hc (h := h)
  have h1 := mul_le_mul_of_nonneg_right hd (norm_nonneg (z - u))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  exact (squared_distance_change (P (z - c • h)) z u).trans (by nlinarith)

lemma projected_energy_jump_upper {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {u x z g h : E}
    {A η c L : ℝ} (hu : u ∈ Q) (hA : 0 ≤ A)
    (hf : f (x - η • h) ≤ f x - η * ⟪g, h⟫ + L * η ^ 2 * ‖h‖ ^ 2 / 2) :
    GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
      GradientOnlyQuasar.weightedEnergy f u A x z ≤
      -A * η * ⟪g, h⟫ - c * ⟪h, z - u⟫ + (A * L * η ^ 2 + c ^ 2) * ‖h‖ ^ 2 / 2 := by
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hP.dist_le (z - c • h) hu) 2
  have he : z - c • h - u = (z - u) - c • h := by abel
  rw [he, norm_sub_sq_real (z - u) (c • h), real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, ← real_inner_comm (z - u) h] at hp
  have hh := mul_le_mul_of_nonneg_left hf hA
  unfold GradientOnlyQuasar.weightedEnergy
  nlinarith

lemma smooth_absolute_increment [CompleteSpace E] {f : E → ℝ} {G : E → E} {L : ℝ}
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    |f y - f x| ≤ ‖G x‖ * ‖y - x‖ + L / 2 * ‖y - x‖ ^ 2 := by
  have hu := Gradient.smooth_upper_bound hG hlip x y
  have hn : ∀ x y, ‖-G x - -G y‖ ≤ L * ‖x - y‖ := by
    intro x y
    rw [neg_sub_neg, norm_sub_rev]
    exact hlip x y
  have hd := Gradient.smooth_upper_bound (fun x => TwoSidedPL.hasGradientAt_neg' (hG x)) hn x y
  simp only [inner_neg_left] at hd
  have hi := abs_real_inner_le_norm (G x) (y - x)
  rw [abs_le] at hi ⊢
  constructor <;> linarith

lemma projected_energy_jump_absolute [CompleteSpace E] {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {G : E → E} {u x z h : E}
    {A η c L : ℝ} (hz : z ∈ Q) (hA : 0 ≤ A) (hη : 0 ≤ η) (hc : 0 ≤ c)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    |GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
      GradientOnlyQuasar.weightedEnergy f u A x z| ≤
      A * η * ‖G x‖ * ‖h‖ + c * ‖h‖ * ‖z - u‖ +
        (A * L * η ^ 2 + c ^ 2) * ‖h‖ ^ 2 / 2 := by
  have hf := smooth_absolute_increment hG hlip x (x - η • h)
  simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hη, mul_pow] at hf
  have hp := projected_distance_change (u := u) hP hz hc (h := h)
  have he : GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
      GradientOnlyQuasar.weightedEnergy f u A x z =
      A * (f (x - η • h) - f x) +
        (‖P (z - c • h) - u‖ ^ 2 - ‖z - u‖ ^ 2) / 2 := by
    unfold GradientOnlyQuasar.weightedEnergy
    ring
  rw [he]
  have hh := abs_add_le (A * (f (x - η • h) - f x))
    ((‖P (z - c • h) - u‖ ^ 2 - ‖z - u‖ ^ 2) / 2)
  rw [abs_mul, abs_of_nonneg hA] at hh
  have hf' := mul_le_mul_of_nonneg_left hf hA
  nlinarith

lemma projected_update_difference {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) (z h k : E) {c : ℝ} (hc : 0 ≤ c) :
    ‖P (z - c • h) - P (z - c • k)‖ ≤ c * ‖h - k‖ := by
  have hh := hP.lipschitz.dist_le_mul (z - c • h) (z - c • k)
  have he : (z - c • h) - (z - c • k) = -(c • (h - k)) := by module
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, he, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] using hh

lemma projected_energy_jump_difference [CompleteSpace E] {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {G : E → E} {u x z h k : E}
    {A η c L : ℝ} (hu : u ∈ Q) (hA : 0 ≤ A) (hη : 0 ≤ η) (hc : 0 ≤ c)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    |GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
      GradientOnlyQuasar.weightedEnergy f u A (x - η • k) (P (z - c • k))| ≤
      (A * η * (‖G x‖ + L * η * ‖k‖) + c * (‖z - u‖ + c * ‖k‖)) * ‖h - k‖ +
        (A * L * η ^ 2 + c ^ 2) * ‖h - k‖ ^ 2 / 2 := by
  have hdiff : (x - η • h) - (x - η • k) = -(η • (h - k)) := by module
  have hnorm : ‖(x - η • h) - (x - η • k)‖ = η * ‖h - k‖ := by
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  have hkg := hlip (x - η • k) x
  simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hη] at hkg
  have hg : ‖G (x - η • k)‖ ≤ ‖G x‖ + L * η * ‖k‖ := by
    have ht := norm_sub_norm_le (G (x - η • k)) (G x)
    nlinarith
  have hf := smooth_absolute_increment hG hlip (x - η • k) (x - η • h)
  rw [hnorm] at hf
  have hg' := mul_le_mul_of_nonneg_right hg (by positivity : 0 ≤ η * ‖h - k‖)
  have hf' : |f (x - η • h) - f (x - η • k)| ≤
      η * (‖G x‖ + L * η * ‖k‖) * ‖h - k‖ + L * η ^ 2 * ‖h - k‖ ^ 2 / 2 := by
    nlinarith
  have hd := projected_update_difference hP z h k hc
  have hbase := hP.dist_le (z - c • k) hu
  have hbase' : ‖P (z - c • k) - u‖ ≤ ‖z - u‖ + c * ‖k‖ := by
    have he : z - c • k - u = (z - u) - c • k := by abel
    have hh := norm_sub_le (z - u) (c • k)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at hh
    rw [he] at hbase
    exact hbase.trans hh
  have hs := squared_distance_change (P (z - c • h)) (P (z - c • k)) u
  have hm := mul_le_mul hd hbase' (norm_nonneg _) (by positivity : 0 ≤ c * ‖h - k‖)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hs' : |(‖P (z - c • h) - u‖ ^ 2 - ‖P (z - c • k) - u‖ ^ 2) / 2| ≤
      c * (‖z - u‖ + c * ‖k‖) * ‖h - k‖ + c ^ 2 * ‖h - k‖ ^ 2 / 2 := by
    nlinarith
  have he : GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
      GradientOnlyQuasar.weightedEnergy f u A (x - η • k) (P (z - c • k)) =
      A * (f (x - η • h) - f (x - η • k)) +
        (‖P (z - c • h) - u‖ ^ 2 - ‖P (z - c • k) - u‖ ^ 2) / 2 := by
    unfold GradientOnlyQuasar.weightedEnergy
    ring
  rw [he]
  have hh := abs_add_le (A * (f (x - η • h) - f (x - η • k)))
    ((‖P (z - c • h) - u‖ ^ 2 - ‖P (z - c • k) - u‖ ^ 2) / 2)
  rw [abs_mul, abs_of_nonneg hA] at hh
  have hf'' := mul_le_mul_of_nonneg_left hf' hA
  nlinarith

lemma energy_perturbation_coefficient {a q B c g z : ℝ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hB : 0 ≤ B) (hg0 : 0 ≤ g)
    (hqcap : q ≤ 1 / 4) (hc : c ^ 2 ≤ a * q)
    (hg : a * g ^ 2 ≤ 2 * q * B) (hz : z ^ 2 ≤ 2 * B) :
    (a * (1 + q) + c ^ 2) * g + c * z ≤ 4 * Real.sqrt (q * a * B) := by
  have hf : (a * (1 + q) + c ^ 2) * g + c * z ≤ a * (1 + 2 * q) * g + c * z := by
    have hh := mul_le_mul_of_nonneg_right hc hg0
    nlinarith
  have hs1 := mul_le_mul_of_nonneg_left hg ha
  have hs2 : (1 + 2 * q) ^ 2 ≤ 9 / 4 := by nlinarith
  have hs3 := mul_le_mul hs2 hs1 (by positivity : 0 ≤ a * (a * g ^ 2)) (by norm_num : (0 : ℝ) ≤ 9 / 4)
  have hs : (a * (1 + 2 * q) * g) ^ 2 ≤ (9 / 2 : ℝ) * q * a * B := by
    nlinarith
  have ht1 := mul_le_mul_of_nonneg_right hc (sq_nonneg z)
  have ht2 := mul_le_mul_of_nonneg_left hz (mul_nonneg ha hq)
  have ht : (c * z) ^ 2 ≤ 2 * q * a * B := by nlinarith
  have hj : (a * (1 + 2 * q) * g + c * z) ^ 2 ≤ 13 * q * a * B := by
    nlinarith [sq_nonneg (a * (1 + 2 * q) * g - c * z)]
  have hr := Real.sq_sqrt (by positivity : 0 ≤ q * a * B)
  have hr0 := Real.sqrt_nonneg (q * a * B)
  apply hf.trans
  nlinarith [sq_nonneg (a * (1 + 2 * q) * g + c * z - 4 * Real.sqrt (q * a * B))]

lemma energy_perturbation_second {a q B p e d : ℝ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hB : 0 ≤ B) (hp : 0 < p)
    (hcap : p * a * e ^ 2 ≤ 4 * B) (hqp : 8 * q ≤ p)
    (hd : |d| ≤ 4 * Real.sqrt (q * a * B) * e + q * a * e ^ 2) :
    d ^ 2 ≤ 33 * q * a * B * e ^ 2 := by
  have hr := Real.sq_sqrt (by positivity : 0 ≤ q * a * B)
  have hs := pow_le_pow_left₀ (abs_nonneg d) hd 2
  rw [sq_abs] at hs
  have hab := sq_nonneg (4 * Real.sqrt (q * a * B) * e - q * a * e ^ 2)
  have hroot : (4 * Real.sqrt (q * a * B) * e) ^ 2 = 16 * q * a * B * e ^ 2 := by
    calc
      _ = 16 * (Real.sqrt (q * a * B)) ^ 2 * e ^ 2 := by ring
      _ = _ := by rw [hr]; ring
  have hh := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 2 * q ^ 2 * a * e ^ 2)
  have hq' := mul_le_mul_of_nonneg_right hqp (by positivity : 0 ≤ q * a * B * e ^ 2)
  have hsq : p * (q * a * e ^ 2) ^ 2 * 2 ≤ p * q * a * B * e ^ 2 := by
    nlinarith
  have hrem : 2 * (q * a * e ^ 2) ^ 2 ≤ q * a * B * e ^ 2 := by
    apply le_of_mul_le_mul_left (a := p) _ hp
    nlinarith
  nlinarith

lemma energy_localization [CompleteSpace E] {f : E → ℝ} {G : E → E}
    {u x z : E} {A L B : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B) :
    ‖z - u‖ ^ 2 ≤ 2 * B ∧ A * ‖G x‖ ^ 2 ≤ 2 * L * B := by
  have hgap : 0 ≤ f x - f u := sub_nonneg.mpr (hmin x)
  have hg := ComponentEnvelope.smooth_gradient_gap hL hG hlip hmin x
  have hh := mul_le_mul_of_nonneg_left hg hA
  unfold GradientOnlyQuasar.weightedEnergy at henergy
  have hp := mul_nonneg hA hgap
  constructor
  · nlinarith
  · have hscaled := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 2 * L)
    nlinarith [mul_nonneg hL.le (sq_nonneg ‖z - u‖)]

lemma exact_energy_jump_square {q B d t J : ℝ} (hq : 0 ≤ q) (hd : 0 ≤ d)
    (hqcap : q ≤ 1 / 16) (hdb : d ≤ 2 * q * B) (ht : t ^ 2 ≤ 2 * q * B * d)
    (hJ : |J| ≤ (1 + q) * d + t) : J ^ 2 ≤ 9 * q * B * d := by
  have hq2 : (1 + q) ^ 2 ≤ 5 / 4 := by nlinarith
  have hd2 := mul_le_mul_of_nonneg_right hdb hd
  have hsd := mul_le_mul hq2 hd2 (by positivity : 0 ≤ d * d) (by norm_num : (0 : ℝ) ≤ 5 / 4)
  have hs : ((1 + q) * d) ^ 2 ≤ (5 / 2 : ℝ) * q * B * d := by nlinarith
  have hh := pow_le_pow_left₀ (abs_nonneg J) hJ 2
  rw [sq_abs] at hh
  nlinarith [sq_nonneg ((1 + q) * d - t)]

lemma small_energy_linear_term {p q B t : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (hsmall : 32 * p * q ≤ 1) (ht : p * t ^ 2 ≤ 2 * q * B ^ 2) :
    t ≤ B / (4 * p) := by
  have h1 := mul_le_mul_of_nonneg_left ht hp.le
  have h2 := mul_le_mul_of_nonneg_right hsmall (sq_nonneg B)
  have hab : |4 * p * t| ≤ B := by
    apply (sq_le_sq₀ (abs_nonneg _) hB).mp
    rw [sq_abs]
    nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 4 * p)).mpr
  nlinarith [le_abs_self (4 * p * t)]

lemma clipped_energy_jump_cap {a q B c g z H p J : ℝ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hB : 0 ≤ B) (hp : 0 < p)
    (hsmall : 32 * p * q ≤ 1) (hqcap : q ≤ 1 / 2)
    (hbalance : p * a * H ^ 2 = B) (hc : c ^ 2 ≤ a * q)
    (hg : a * g ^ 2 ≤ 2 * q * B) (hz : z ^ 2 ≤ 2 * B)
    (hJ : |J| ≤ a * g * H + c * H * z + a * q * H ^ 2) :
    |J| ≤ B / p := by
  have ht1 : p * (a * g * H) ^ 2 ≤ 2 * q * B ^ 2 := by
    calc
      _ = (p * a * H ^ 2) * (a * g ^ 2) := by ring
      _ = B * (a * g ^ 2) := by rw [hbalance]
      _ ≤ B * (2 * q * B) := mul_le_mul_of_nonneg_left hg hB
      _ = _ := by ring
  have ht2 : p * (c * H * z) ^ 2 ≤ 2 * q * B ^ 2 := by
    have hh := mul_le_mul hc hz (sq_nonneg z) (mul_nonneg ha hq)
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ p * H ^ 2)
    calc
      _ ≤ (p * a * H ^ 2) * (2 * q * B) := by nlinarith
      _ = _ := by rw [hbalance]; ring
  have h1 := small_energy_linear_term hp hB hsmall ht1
  have h2 := small_energy_linear_term hp hB hsmall ht2
  have h3 : a * q * H ^ 2 ≤ B / (2 * p) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * p)).mpr
    have hh := mul_le_mul_of_nonneg_right hqcap hB
    nlinarith [show 2 * p * (a * q * H ^ 2) = 2 * q * B by rw [← hbalance]; ring]
  have he : B / (4 * p) + B / (4 * p) + B / (2 * p) = B / p := by ring
  linarith

lemma clipping_contains_gradient {a q B g H p : ℝ} (ha : 0 < a)
    (hH : 0 ≤ H) (hsmall : 8 * p * q ≤ 1) (hbalance : p * a * H ^ 2 = B)
    (hg : a * g ^ 2 ≤ 2 * q * B) : g ≤ H / 2 := by
  have hh := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ a * H ^ 2)
  have he : 8 * p * q * (a * H ^ 2) = 8 * q * B := by rw [← hbalance]; ring
  rw [he] at hh
  have hs : 4 * g ^ 2 ≤ H ^ 2 := by
    apply le_of_mul_le_mul_left (a := a) _ ha
    nlinarith
  nlinarith [sq_nonneg (2 * g - H)]

lemma localized_clipped_jump [CompleteSpace E] {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {G : E → E} {u x z h : E}
    {A η c L q B H p : ℝ} (hz : z ∈ Q) (hA : 0 < A) (hη : 0 < η)
    (hc0 : 0 ≤ c) (hL : 0 < L) (hq : 0 ≤ q) (hB : 0 ≤ B) (hH : 0 ≤ H) (hp : 0 < p)
    (hLη : L * η = q) (hc : c ^ 2 ≤ A * η * q)
    (hsmall : 32 * p * q ≤ 1) (hqcap : q ≤ 1 / 2)
    (hbalance : p * (A * η) * H ^ 2 = B) (hh : ‖h‖ ≤ H)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B) :
    ‖G x‖ ≤ H / 2 ∧
      |GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
        GradientOnlyQuasar.weightedEnergy f u A x z| ≤ B / p := by
  have hloc := energy_localization hA.le hL hG hlip hmin henergy
  have hg : (A * η) * ‖G x‖ ^ 2 ≤ 2 * q * B := by
    have ht := mul_le_mul_of_nonneg_left hloc.2 hη.le
    have he : η * (2 * L * B) = 2 * q * B := by rw [← hLη]; ring
    rw [he] at ht
    nlinarith
  have hsmall' : 8 * p * q ≤ 1 := by nlinarith [mul_nonneg hp.le hq]
  refine ⟨clipping_contains_gradient (mul_pos hA hη) hH hsmall' hbalance hg, ?_⟩
  apply clipped_energy_jump_cap (mul_nonneg hA.le hη.le) hq hB hp hsmall hqcap hbalance hc hg hloc.1
  have hb := projected_energy_jump_absolute (u := u) (x := x) hP hz hA.le hη.le hc0 hG hlip (h := h)
  have h1 := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ A * η * ‖G x‖)
  have h2 := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ c * ‖z - u‖)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  have h3 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (A * L * η ^ 2 + c ^ 2) / 2)
  have h4 := mul_le_mul_of_nonneg_right hc (sq_nonneg H)
  have he : A * L * η ^ 2 = A * η * q := by rw [← hLη]; ring
  rw [he] at hb h3
  nlinarith

lemma localized_exact_jump_square [CompleteSpace E] {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {G : E → E} {u x z : E}
    {A η c L q B : ℝ} (hz : z ∈ Q) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hc0 : 0 ≤ c) (hL : 0 < L) (hq : 0 ≤ q) (hLη : L * η = q)
    (hc : c ^ 2 ≤ A * η * q) (hqcap : q ≤ 1 / 16)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B) :
    (GradientOnlyQuasar.weightedEnergy f u A (x - η • G x) (P (z - c • G x)) -
      GradientOnlyQuasar.weightedEnergy f u A x z) ^ 2 ≤
      9 * q * B * (A * η * ‖G x‖ ^ 2) := by
  have hloc := energy_localization hA hL hG hlip hmin henergy
  have hg : (A * η) * ‖G x‖ ^ 2 ≤ 2 * q * B := by
    have ht := mul_le_mul_of_nonneg_left hloc.2 hη
    have he : η * (2 * L * B) = 2 * q * B := by rw [← hLη]; ring
    rw [he] at ht
    nlinarith
  have ht : (c * ‖G x‖ * ‖z - u‖) ^ 2 ≤ 2 * q * B * (A * η * ‖G x‖ ^ 2) := by
    have hh := mul_le_mul hc hloc.1 (sq_nonneg _) (by positivity : 0 ≤ A * η * q)
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖G x‖)
    nlinarith
  apply exact_energy_jump_square hq (by positivity : 0 ≤ A * η * ‖G x‖ ^ 2) hqcap hg ht
  have hb := projected_energy_jump_absolute (u := u) (x := x) hP hz hA hη hc0 hG hlip (h := G x)
  have he : A * L * η ^ 2 = A * η * q := by rw [← hLη]; ring
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖G x‖)
  nlinarith

lemma localized_jump_difference [CompleteSpace E] {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {G : E → E} {u x z h : E}
    {A η c L q B : ℝ} (hu : u ∈ Q) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hc0 : 0 ≤ c) (hL : 0 < L) (hq : 0 ≤ q) (hB : 0 ≤ B) (hLη : L * η = q)
    (hc : c ^ 2 ≤ A * η * q) (hqcap : q ≤ 1 / 4)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hmin : ∀ x, f u ≤ f x) (henergy : GradientOnlyQuasar.weightedEnergy f u A x z ≤ B) :
    |GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
      GradientOnlyQuasar.weightedEnergy f u A (x - η • G x) (P (z - c • G x))| ≤
      4 * Real.sqrt (q * (A * η) * B) * ‖h - G x‖ + q * (A * η) * ‖h - G x‖ ^ 2 := by
  have hloc := energy_localization hA hL hG hlip hmin henergy
  have hg : (A * η) * ‖G x‖ ^ 2 ≤ 2 * q * B := by
    have ht := mul_le_mul_of_nonneg_left hloc.2 hη
    have he : η * (2 * L * B) = 2 * q * B := by rw [← hLη]; ring
    rw [he] at ht
    nlinarith
  have hcoef := energy_perturbation_coefficient (mul_nonneg hA hη) hq hB
    (norm_nonneg (G x)) hqcap hc hg hloc.1
  have hd := projected_energy_jump_difference (x := x) (z := z) (h := h) (k := G x)
    (A := A) (η := η) (c := c) hP hu hA hη hc0 hG hlip
  have hecoef : A * η * (‖G x‖ + L * η * ‖G x‖) + c * (‖z - u‖ + c * ‖G x‖) =
      (A * η * (1 + q) + c ^ 2) * ‖G x‖ + c * ‖z - u‖ := by rw [← hLη]; ring
  have hequad : A * L * η ^ 2 = A * η * q := by rw [← hLη]; ring
  rw [hecoef, hequad] at hd
  have h1 := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (h - G x))
  have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖h - G x‖)
  nlinarith

lemma projected_noisy_energy_drift [CompleteSpace E] {Q : Set E} {P : E → E}
    (hP : ConstrainedMonotone.Proj Q P) {f : E → ℝ} {G : E → E} {u x z h : E}
    {A η c L q γ : ℝ} (hu : u ∈ Q) (hA : 0 ≤ A) (hc0 : 0 ≤ c)
    (hLη : L * η = q) (hc : c ^ 2 ≤ A * η * q)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hquasar : γ * (f x - f u) ≤ ⟪G x, x - u⟫) :
    γ * c * (f x - f u) + c * ⟪G x, z - x⟫ +
      (GradientOnlyQuasar.weightedEnergy f u A (x - η • h) (P (z - c • h)) -
        GradientOnlyQuasar.weightedEnergy f u A x z) ≤
      -(1 - q) * (A * η * ‖G x‖ ^ 2) +
        ⟪h - G x, ((2 * q - 1) * (A * η)) • G x - c • (z - u)⟫ +
        q * (A * η) * ‖h - G x‖ ^ 2 := by
  have hf := Gradient.smooth_upper_bound hG hlip x (x - η • h)
  simp only [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right,
    norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hf
  have hf' : f (x - η • h) ≤ f x - η * ⟪G x, h⟫ + L * η ^ 2 * ‖h‖ ^ 2 / 2 := by
    nlinarith
  have hj := projected_energy_jump_upper (u := u) (z := z) (c := c) hP hu hA hf'
  have hflow := GradientOnlyQuasar.weightedEnergy_flow_bound (z := z) hc0 hquasar
  have he : A * L * η ^ 2 = A * η * q := by rw [← hLη]; ring
  rw [he] at hj
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖h‖)
  have hi : ⟪h, G x⟫ = ⟪G x, h⟫ := real_inner_comm (G x) h
  simp only [inner_sub_right, real_inner_smul_right, inner_sub_left,
    real_inner_self_eq_norm_sq, norm_sub_sq_real, hi] at hj hflow ⊢
  nlinarith

lemma noisy_drift_coefficient {a q B c : ℝ} {g z : E}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hB : 0 ≤ B) (hqcap : q ≤ 1 / 2)
    (hc : c ^ 2 ≤ a * q) (hg : a * ‖g‖ ^ 2 ≤ 2 * q * B) (hz : ‖z‖ ^ 2 ≤ 2 * B) :
    ‖((2 * q - 1) * a) • g - c • z‖ ≤ 3 * Real.sqrt (q * a * B) := by
  have hqabs : |2 * q - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs := norm_sub_le (((2 * q - 1) * a) • g) (c • z)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg ha] at hs
  have hs1 := mul_le_mul_of_nonneg_right hqabs (by positivity : 0 ≤ a * ‖g‖)
  have hs2 : ‖((2 * q - 1) * a) • g - c • z‖ ≤ a * ‖g‖ + |c| * ‖z‖ := by
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hg ha
  have h2 := mul_le_mul hc hz (sq_nonneg _) (mul_nonneg ha hq)
  have hsq : (a * ‖g‖ + |c| * ‖z‖) ^ 2 ≤ 8 * q * a * B := by
    nlinarith [sq_abs c, sq_nonneg (a * ‖g‖ - |c| * ‖z‖)]
  have hr := Real.sq_sqrt (by positivity : 0 ≤ q * a * B)
  have hr0 := Real.sqrt_nonneg (q * a * B)
  apply hs2.trans
  nlinarith [sq_nonneg (a * ‖g‖ + |c| * ‖z‖ - 3 * Real.sqrt (q * a * B))]

lemma clipping_noise_absorption {a q B H p : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hqcap : q ≤ 1 / 2)
    (hsmall : 144 * p * q ≤ 1) (hbalance : p * a * H ^ 2 = B) :
    6 * Real.sqrt (q * a * B) ≤ (1 - q) * a * H := by
  have hq2 : 36 * p * q ≤ (1 - q) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hq2 (by positivity : 0 ≤ a ^ 2 * H ^ 2)
  have hr := Real.sq_sqrt (by positivity : 0 ≤ q * a * B)
  apply (sq_le_sq₀ (by positivity : 0 ≤ 6 * Real.sqrt (q * a * B))
    (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - q) ha) hH)).mp
  have he : 36 * p * q * (a ^ 2 * H ^ 2) = 36 * q * a * B := by rw [← hbalance]; ring
  rw [he] at hh
  nlinarith

end OracleTemplate.StochasticQuasar
