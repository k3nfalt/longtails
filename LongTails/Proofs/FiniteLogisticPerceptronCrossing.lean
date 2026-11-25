import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sigmoid

namespace LongTails.Proofs.FiniteLogisticPerceptronCrossing

lemma first_crossing_separates {L₁ L₂ η p p' q q' D D' : ℝ}
    (hL : 0 < L₁) (hL₂ : L₁ ≤ L₂) (hη : 0 ≤ η) (hp : 0 < p) (hp' : 0 < p')
    (hq : q ≤ 0) (hq' : 0 < q') (hD : 0 < D) (hD' : D / 2 ≤ D')
    (hstep : q' = q + η * (L₁ * Real.sigmoid (-(L₁ * p * q)) -
      L₂ * Real.sigmoid (L₂ * p * q - D)) * p)
    (hstable : η * L₁ * (L₁ + L₂) * p ^ 2 ≤ 4)
    (hscale : η * L₁ * L₂ * p * p' ≤ 1) :
    0 < L₁ * p' * q' ∧ 0 < D' - L₂ * p' * q' := by
  have hL₂' := hL.trans_le hL₂
  let a := Real.sigmoid (-(L₁ * p * q))
  let b := Real.sigmoid (L₂ * p * q - D)
  change q' = q + η * (L₁ * a - L₂ * b) * p at hstep
  have hb : 0 ≤ b := Real.sigmoid_nonneg _
  have hgap : a - b ≤ (D - (L₁ + L₂) * p * q) / 4 := by
    have hder : ∀ x, deriv Real.sigmoid x ≤ 1 / 4 := fun x => by
      rw [Real.deriv_sigmoid]
      nlinarith [sq_nonneg (Real.sigmoid x - 1 / 2)]
    have hneg := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (add_nonneg hL.le hL₂'.le) hp.le) hq
    have hxy : L₂ * p * q - D ≤ -(L₁ * p * q) := by nlinarith only [hneg, hD]
    have H := image_sub_le_mul_sub_of_deriv_le
      (fun x => (Real.hasDerivAt_sigmoid x).differentiableAt) hder hxy
    dsimp [a, b]
    linarith
  have hweight : L₁ * a - L₂ * b ≤ L₁ * (a - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL₂) hb]
  have hbound : q' ≤ η * L₁ * p * D / 4 := by
    rw [hstep]
    have h₁ := mul_le_mul_of_nonneg_left hweight (mul_nonneg hη hp.le)
    have h₂ := mul_le_mul_of_nonneg_left hgap (show 0 ≤ η * L₁ * p by positivity)
    nlinarith [mul_nonneg (neg_nonneg.mpr hq) (sub_nonneg.mpr hstable)]
  have hprod := mul_le_mul_of_nonneg_left hbound (show 0 ≤ L₂ * p' by positivity)
  exact ⟨by positivity, by nlinarith [mul_le_mul_of_nonneg_right hscale hD.le]⟩

lemma sigmoid_drift {t D x y : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/30)
    (hD : 256*t ≤ D) (hx : 0 ≤ x) (hy : y ≤ -D) :
    12*t ≤ Real.sigmoid x - (1+t)*Real.sigmoid y := by
  have ha := Real.sigmoid_le hx
  rw [Real.sigmoid_zero] at ha
  have hD₀ : 0 ≤ D := by linarith
  have hden : 0 < 2+D := by linarith
  have hb : Real.sigmoid y ≤ 1/(2+D) := by
    rw [Real.sigmoid_def, ← one_div]
    apply one_div_le_one_div_of_le hden
    linarith [Real.add_one_le_exp (-y)]
  have hfrac : (1+t)/(2+D) ≤ 1/2-12*t := by
    apply (div_le_iff₀ hden).mpr
    have h := mul_nonneg (show 0 ≤ 1/2-12*t by linarith) (sub_nonneg.mpr hD)
    have H := mul_nonneg ht (show 0 ≤ 1/30-t by linarith)
    nlinarith
  rw [div_eq_mul_one_div] at hfrac
  linarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+t by linarith)]

lemma sigmoid_growth_cases {t x y : ℝ} (ht : t ≤ 1/30) (hx : 0 ≤ x) :
    1/4 ≤ Real.sigmoid y ∨ 1/5 ≤ Real.sigmoid x - (1+t)*Real.sigmoid y := by
  by_cases h : 1/4 ≤ Real.sigmoid y
  · exact Or.inl h
  · have ha := Real.sigmoid_le hx
    rw [Real.sigmoid_zero] at ha
    right
    nlinarith [mul_le_mul_of_nonneg_right ht (Real.sigmoid_nonneg y)]

lemma angle_constants {k B : ℝ} (hk : 0 < k) (hk₂ : 3*k^2 ≤ 1) (hB : 0 < B)
    (hB₂ : B^2 = 1 - 2*k^2) :
    let a := min (19/20 : ℝ) (4*k)
    let c := Real.sqrt 2*k/B
    0 ≤ a ∧ a ≤ 19/20 ∧ c ≤ 10/7 ∧ c*(1-a^2) ≤ a/2 := by
  intro a c
  have hf := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  have hc₀ : 0 ≤ c := by dsimp [c]; positivity
  have h₁ : c ≤ 10/7 := by
    apply (div_le_iff₀ hB).mpr
    by_contra! ht
    nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < Real.sqrt 2*k + 10/7*B by positivity),
      congrArg (fun z => z*k^2) hf]
  refine ⟨le_min (by norm_num) (by positivity), min_le_left _ _, h₁, ?_⟩
  by_cases hl : 19/20 ≤ 4*k
  · change c*(1-(min _ _)^2) ≤ min _ _ / 2
    rw [min_eq_left hl]
    linarith
  · change c*(1-(min _ _)^2) ≤ min _ _ / 2
    rw [min_eq_right (le_of_not_ge hl)]
    have hprod := mul_pos (show 0 < 1/4-k by linarith) (show 0 < 1/4+k by positivity)
    have hb : 3/4 ≤ B := by nlinarith
    have hf' : Real.sqrt 2 ≤ 3/2 := by nlinarith
    have hlow : c ≤ 2*k := (div_le_iff₀ hB).mpr (by
      nlinarith [mul_le_mul_of_nonneg_right hf' hk.le, mul_le_mul_of_nonneg_left hb hk.le])
    nlinarith [mul_nonneg hc₀ (sq_nonneg (4*k))]

lemma enters_cone {k B P p q u e : ℝ} (hk : 0 < k) (hk₂ : 3*k^2 ≤ 1)
    (hB : 0 < B) (hB₂ : B^2 = 1-2*k^2) (hP : 0 < P) (he : e ≤ k*P/20)
    (ep : |p-P| ≤ e) (eq : |q+Real.sqrt 2*k*P| ≤ e) (eu : |u-B*P| ≤ e) :
    0 < p+q ∧ q ≤ 0 ∧ -(min (19/20 : ℝ) (4*k))*p ≤ q ∧ p/2 ≤ u ∧ u ≤ 50*(p+q) := by
  obtain ⟨ep₁,ep₂⟩ := abs_le.mp ep
  obtain ⟨eq₁,eq₂⟩ := abs_le.mp eq
  obtain ⟨eu₁,eu₂⟩ := abs_le.mp eu
  have hF := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hF₀ := Real.sqrt_nonneg (2:ℝ)
  have hF' : Real.sqrt 2 ≤ 3/2 := by nlinarith
  have hF'' : 1 ≤ Real.sqrt 2 := by nlinarith
  have hk' : k ≤ 7/12 := by nlinarith
  have hB' : 4/7 ≤ B := by nlinarith
  have hB'' : B ≤ 1 := by nlinarith [sq_nonneg k]
  have hkP := mul_le_mul_of_nonneg_right hk' hP.le
  have hkp := mul_nonneg hk.le hP.le
  have hfP := mul_le_mul_of_nonneg_right hF' hkp
  have hfQ := mul_le_mul_of_nonneg_right hF'' hkp
  have hbP := mul_le_mul_of_nonneg_right hB' hP.le
  have hbQ := mul_le_mul_of_nonneg_right hB'' hP.le
  have hp : 9*P/10 ≤ p := by linarith
  have hqp : -19/20*p ≤ q := by linarith
  refine ⟨by linarith, by nlinarith only [eq₂, he, hfQ, hkp], ?_, by linarith, by linarith⟩
  by_cases h : 19/20 ≤ 4*k
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith only [mul_le_mul_of_nonneg_left hp hk.le, hfP, eq₁, he, hkp]

lemma preserves_cone {a c h j p q u : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 19 / 20)
    (hc : c ≤ 10 / 7) (hslope : c * (1 - a ^ 2) ≤ a / 2)
    (hh : -(1 / 2 : ℝ) ≤ h) (hh' : h ≤ 1 / 2) (hj : 0 ≤ j) (hj' : j ≤ 1)
    (hdrift : -c * j ≤ h) (hpos : 0 < p + q) (hq : q ≤ 0)
    (hangle : -a * p ≤ q) (hu : p / 2 ≤ u) (hu' : u ≤ 50 * (p + q)) :
    let P := p + h*q + j*u
    let Q := q + h*p
    let U := u + j*p
    0 < P + Q ∧ 0 < P - Q ∧ -a*P ≤ Q ∧ P/2 ≤ U ∧ U ≤ 50*(P+Q) ∧
      p+q+u + j*(p+u)/21 ≤ P+Q+U := by
  dsimp only
  have hp : 0 < p := by linarith
  have hu₀ : 0 ≤ u := by linarith
  have hjp := mul_nonneg hj hp.le
  have hju := mul_nonneg hj hu₀
  have hJ := mul_le_mul_of_nonneg_left hu hj
  have hlow : -(10/7)*j ≤ h := by linarith [mul_le_mul_of_nonneg_right hc hj]
  have h₁ := mul_pos (show 0 < 1+h by linarith) hpos
  have h₂ := mul_pos (show 0 < 1-h by linarith) (show 0 < p-q by linarith)
  have ha₂ : 0 ≤ 1-a^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-a by linarith)
      (show 0 ≤ 1+a by linarith)]
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · have hx := mul_nonneg (show 0 ≤ 1+a*h by nlinarith [mul_le_mul_of_nonneg_left hh ha])
        (show 0 ≤ q+a*p by linarith)
    have hy := mul_le_mul_of_nonneg_right hdrift (mul_nonneg ha₂ hp.le)
    have hz := mul_le_mul_of_nonneg_right hslope hjp
    nlinarith [mul_le_mul_of_nonneg_left hJ ha]
  · have hx := mul_nonneg (show 0 ≤ 1-j/2 by linarith) (show 0 ≤ u-p/2 by linarith)
    have hy := mul_le_mul_of_nonpos_right hlow hq
    nlinarith [mul_nonneg hj hpos.le]
  · have hx := mul_nonneg (show 0 ≤ 1+h by linarith) (show 0 ≤ 50*(p+q)-u by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hlow hu₀]
  · nlinarith [mul_le_mul_of_nonneg_right hlow hpos.le, mul_nonpos_of_nonneg_of_nonpos hj hq]

lemma coefficients {η L t μ B x y : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hscale : η*L ≤ 1/2) (ht : 0 ≤ t) (ht' : t ≤ 1/30) (hμ : 0 < μ)
    (hμ' : 10*μ ≤ L) (hB : 1/2 ≤ B) (hB' : B ≤ 1) (hx : 0 ≤ x) (hy : y ≤ 0) :
    let a := Real.sigmoid x
    let b := Real.sigmoid y
    let h := η/2*L*(a-(1+t)*b)
    let j := η/2*μ*B*b;
    -(1/2 : ℝ) ≤ h ∧ h ≤ 1/2 ∧ 0 ≤ j ∧ j ≤ 1/2 ∧ -(L*t/(μ*B))*j ≤ h ∧
      (η*μ/16 ≤ j ∨ η*μ ≤ h) := by
  intro a b h j
  have ha : 1/2 ≤ a := by simpa [a] using Real.sigmoid_le hx
  have hb : b ≤ 1/2 := by simpa [b] using Real.sigmoid_le hy
  have ha' : a ≤ 1 := Real.sigmoid_le_one _
  have hb₀ : 0 ≤ b := Real.sigmoid_nonneg _
  have hB₀ : 0 < B := by linarith
  have h₁ : h ≤ 1/2 := by
    have hz : a-(1+t)*b ≤ 1 := by nlinarith [mul_nonneg ht hb₀]
    dsimp [h]
    nlinarith [mul_le_mul_of_nonneg_left hz (mul_nonneg hη.le hL.le)]
  have h₂ : -(1/2:ℝ) ≤ h := by
    have hz : -1 ≤ a-(1+t)*b := by nlinarith [mul_le_mul_of_nonneg_right ht' hb₀]
    dsimp [h]
    nlinarith [mul_le_mul_of_nonneg_left hz (mul_nonneg hη.le hL.le)]
  have hημ : η*μ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hμ' hη.le]
  have hBmul : B*b ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hB' hb₀]
  refine ⟨h₂,h₁,by dsimp [j]; positivity,?_,?_,?_⟩
  · dsimp [j]
    nlinarith [mul_le_mul_of_nonneg_left hBmul (mul_nonneg hη.le hμ.le)]
  · dsimp [j,h]
    field_simp [hB₀.ne',hμ.ne']
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hη.le hL.le) hμ.le) hB₀.le)
      (show 0 ≤ a-b by linarith)]
  · rcases sigmoid_growth_cases ht' hx (y := y) with H|H
    · left
      change 1/4 ≤ b at H
      dsimp [j]
      have hz : 1/8 ≤ B*b := by nlinarith [mul_le_mul_of_nonneg_right hB hb₀]
      nlinarith [mul_le_mul_of_nonneg_left hz (mul_nonneg hη.le hμ.le)]
    · right
      change 1/5 ≤ a-(1+t)*b at H
      dsimp [h]
      nlinarith [mul_le_mul_of_nonneg_left H (mul_nonneg hη.le hL.le),
        mul_le_mul_of_nonneg_left hμ' hη.le]

lemma phase_growth {p q u h j δ : ℝ} (hq : q ≤ 0) (hP : 0 < p+q)
    (hu : p/2 ≤ u) (hu' : u ≤ 50*(p+q)) (hj : 0 ≤ j) (hδ : 0 ≤ δ)
    (hcases : δ/16 ≤ j ∨ δ ≤ h)
    (hinc : p+q+u+j*(p+u)/21 ≤
      (p+h*q+j*u)+(q+h*p)+(u+j*p)) :
    (1+δ/336)*(p+q+u) ≤ (p+h*q+j*u)+(q+h*p)+(u+j*p) := by
  have hp : 0 ≤ p := by linarith
  have hu₀ : 0 ≤ u := by linarith
  obtain h|h := hcases
  · nlinarith [mul_le_mul_of_nonneg_right h (add_nonneg hp hu₀),
      mul_nonpos_of_nonneg_of_nonpos hδ hq]
  · nlinarith [mul_le_mul_of_nonneg_right h hP.le, mul_le_mul_of_nonneg_left hu' hδ,
      mul_nonneg hj (add_nonneg hp hu₀)]

lemma phase_size {p q u h j : ℝ} (hq : q ≤ 0) (hP : 0 < p+q) (hu : p/2 ≤ u)
    (hh : h ≤ 1/2) (hj : j ≤ 1/2) :
    (p+h*q+j*u)+(q+h*p)+(u+j*p) ≤ 3*(p+q+u) := by
  have hp : 0 ≤ p := by linarith
  have hu₀ : 0 ≤ u := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hh hP.le, mul_le_mul_of_nonneg_right hj (add_nonneg hp hu₀)]

lemma high_drift {η L t μ B x y D p u k : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hp : 0 ≤ p) (hu : p/2 ≤ u) (ht : 4*t ≤ D)
    (hD : μ*B*p*u ≤ D) (hx : 0 ≤ x) (hy : y ≤ -D) (hscale : 84*k ≤ L*p^2)
    (hk : 0 ≤ k) :
    let a := Real.sigmoid x
    let b := Real.sigmoid y
    let h := η/2*L*(a-(1+t)*b)
    let j := η/2*μ*B*b
    7*k*j*(p+u) ≤ h*p := by
  intro a b h j
  have hb : 0 < b := Real.sigmoid_pos _
  have ha : 1/2 ≤ a := by simpa [a] using Real.sigmoid_le hx
  have hbD : b*(2+D) ≤ 1 := by
    dsimp only [b, Real.sigmoid_def]
    rw [inv_mul_eq_div, div_le_one (by positivity)]
    linarith [Real.add_one_le_exp (-y)]
  have hgap : b*D/4 ≤ a-(1+t)*b := by nlinarith [mul_le_mul_of_nonneg_left ht hb.le]
  have hstep : j*L*p*u/4 ≤ h := by
    dsimp [h,j]
    nlinarith only [mul_le_mul_of_nonneg_left hgap (mul_nonneg hη hL),
      mul_le_mul_of_nonneg_left hD (mul_nonneg (mul_nonneg hη hL) hb.le)]
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hu₀ : 0 ≤ u := by linarith
  have hh₁ := mul_le_mul_of_nonneg_right hstep hp
  have hh₂ := mul_le_mul_of_nonneg_right hscale (mul_nonneg hj hu₀)
  have hh₃ := mul_le_mul_of_nonneg_left hu (mul_nonneg hk hj)
  nlinarith only [hh₁,hh₂,hh₃]

lemma size_barrier {k p q u P Q U : ℝ} (hk : 0 < k) (hU : 0 ≤ U) (ha : -(4*k)*P ≤ Q) (hsize : P+U ≤ 2*(p+u))
    (hG : p+u ≤ 3*(p+q+u)) (hsmall : p+q+u ≤ 4096*k) :
    7*k*(P+U)-Q ≤ 270336*k^2 := by
  nlinarith [mul_le_mul_of_nonneg_left hsize hk.le, mul_le_mul_of_nonneg_left hG hk.le,
    mul_le_mul_of_nonneg_left hsmall hk.le, mul_nonneg hk.le hU]

lemma high_drift_size {p q u h j k : ℝ} (hq : q ≤ 0) (hh : 0 ≤ h) (hk : 0 < k) (hw : 7*k*j*(p+u) ≤ h*p) :
    7*k*((p+h*q+j*u)+(u+j*p)-(p+u)) ≤ (q+h*p)-q := by
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hk.le hh) hq]

end LongTails.Proofs.FiniteLogisticPerceptronCrossing
