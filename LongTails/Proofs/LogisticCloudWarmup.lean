import LongTails.Proofs.LogisticCloudModel

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCoordinates
open LongTails.Proofs.LogisticCloudAlignment
open LongTails.Proofs.LogisticCloudAverages
open LongTails.Proofs.LogisticCloudDispersion
open LongTails.Proofs.LogisticCloudModel

namespace LongTails.Proofs.LogisticCloudWarmup

variable {p : Params} {D : Data p} (G : Geometry p D)

lemma mean_action (w : Weights p.d) :
    (p.n : ℝ)⁻¹ • ∑ i, action (zcol G i) (ycol G i) w =
      action G.e 0 w - p.μ • action (axis G) G.v w := by
  obtain ⟨C,hC⟩ := action_columns w
  simp_rw [← hC]
  rw [← map_sum,← C.map_smul,← C.map_smul,← map_sub]
  apply congrArg C
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
  ext1
  · simp [Prod.fst_sum,zcol,Finset.sum_add_distrib,G.centered_z,← Nat.cast_smul_eq_nsmul ℝ,
      smul_sub,smul_smul,hn]
  · simp [Prod.snd_sum,ycol,Finset.sum_add_distrib,G.centered_y,← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul,hn]

lemma weight_error {d : ℕ} (a b : Features d) (w : Weights d) (z : ℝ)
    (hz : |z| = |score a b w|) (h : ‖a‖+‖b‖ ≤ 8) :
    ‖(Real.sigmoid z - 1/2) • action a b w‖ ≤ 8*‖w‖^3 := by
  obtain ⟨t,⟨ht,ht'⟩,he⟩ := sigmoid_secant z 0
  simp only [Real.sigmoid_zero,sub_zero] at he
  have H := (norm_action a b w).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  have H' := abs_real_inner_le_norm (action a b w) w
  have hz' : |z| ≤ 4*‖w‖^2 := by
    rw [hz,score_inner,abs_div]
    norm_num
    nlinarith [mul_le_mul_of_nonneg_right H (norm_nonneg w)]
  rw [one_div,he,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg ht]
  have hcoeff := mul_le_mul ht' hz' (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
  nlinarith only [mul_le_mul hcoeff H (norm_nonneg _) (by positivity : 0 ≤ (1/4:ℝ)*(4*‖w‖^2))]

lemma linear_error (η : ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ p.μ) (hμ' : p.μ ≤ 1)
    (ha : 0 ≤ p.a) (ha' : p.a ≤ 1) (w : Weights p.d) :
    ‖gradientStep G η w - linear (axis G) G.v (η*p.μ/4) w‖ ≤ 8*η*‖w‖^3 := by
  let P := action G.e 0 w
  let N := fun i => action (zcol G i) (ycol G i) w
  let A := Real.sigmoid (-score G.e 0 w)
  let B := bweight G w
  have HP : ‖(A-1/2) • P‖ ≤ 8*‖w‖^3 :=
    weight_error G.e 0 w _ (abs_neg _) (by simp [G.norm_e])
  have HN (i : Fin p.n) : ‖(B i-1/2) • N i‖ ≤ 8*‖w‖^3 := by
    apply weight_error _ _ _ _ rfl
    have h₁ := norm_add_le (G.e-p.μ • axis G) (G.z i)
    have h₂ := norm_sub_le G.e (p.μ • axis G)
    have h₃ := norm_add_le (-(p.μ • G.v)) (G.y i)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hμ,G.norm_e,G.norm_v,
      axis_unit G ha ha',norm_neg,mul_one] at h₁ h₂ h₃
    dsimp [zcol,ycol]
    linarith [G.bound_z i,G.bound_y i]
  have Hc : (p.μ : ℝ) • action (axis G) G.v w = P-(p.n : ℝ)⁻¹ • ∑ i, N i := by
    have hh := mean_action G w
    change _ = P-_ at hh
    rw [hh]
    abel
  have He : gradientStep G η w - linear (axis G) G.v (η*p.μ/4) w =
      (η/2) • ((A-1/2) • P - (p.n : ℝ)⁻¹ • ∑ i, (B i-1/2) • N i) := by
    change (w + (η/2) • (A • P-(p.n : ℝ)⁻¹ • ∑ i, B i • N i)) -
      (w+(η*p.μ/4) • action (axis G) G.v w) = _
    rw [show η*p.μ/4 = (η/4)*p.μ by ring,mul_smul,Hc]
    simp_rw [sub_smul,Finset.sum_sub_distrib,← Finset.smul_sum]
    module
  rw [He,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have H := norm_sub_le ((A-1/2) • P) ((p.n : ℝ)⁻¹ • ∑ i, (B i-1/2) • N i)
  have H' := mean_norm_le _ _ HN
  simp only [Fintype.card_fin] at H'
  nlinarith [mul_le_mul_of_nonneg_left (H.trans (add_le_add HP H')) hη]

lemma aligned (η r : ℝ) (hη : 0 < η) (hr : 0 ≤ r) (hμ : 0 < p.μ) (hμ' : p.μ ≤ 1)
    (ha : 0 ≤ p.a) (ha' : p.a ≤ 1) (w : Weights p.d) (hw : ‖w‖ ≤ r) (k : ℕ)
    (hδ : η*p.μ/4 ≤ 1)
    (hs : (256*r^3/p.μ)*((1+η*p.μ/4)^k)^2 ≤ r) :
    let g := 1+η*p.μ/4
    ‖(gradientStep G η)^[k] w - g^k • growing (axis G) G.v w‖ ≤
      8*r+(256*r^3/p.μ)*(g^k)^3 := by
  let δ := η*p.μ/4
  let g := 1+δ
  let C := 8*η
  let K := 256*r^3/p.μ
  let x := fun n => (gradientStep G η)^[n] w
  let y := fun n => (linear (axis G) G.v δ)^[n] w
  have hδ₀ : 0 ≤ δ := by dsimp [δ]; positivity
  have hg : 1 ≤ g := by dsimp [g]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq (n : ℕ) : ‖y n‖ ≤ r*g^n := by
    induction n with
    | zero => simpa [y] using hw
    | succ n ih =>
      change ‖(linear _ _ _)^[n+1] w‖ ≤ _
      rw [Function.iterate_succ_apply',pow_succ]
      have H := linear_norm _ _ (axis_unit G ha ha') G.norm_v (axis_ortho G) hδ₀ (y n)
      nlinarith only [H,mul_le_mul_of_nonneg_right ih (show 0 ≤ g by linarith)]
  have hstep (n : ℕ) : ‖x (n+1)-y (n+1)‖ ≤ g*‖x n-y n‖+C*‖x n‖^3 := by
    let L := linear (axis G) G.v δ
    have eq : L (x n) - L (y n) = L (x n-y n) := by
      dsimp [L,linear]; rw [action_sub,smul_sub]; abel
    have hh := norm_sub_le_norm_sub_add_norm_sub (gradientStep G η (x n)) (L (x n)) (L (y n))
    rw [eq] at hh
    have H := linear_norm _ _ (axis_unit G ha ha') G.norm_v (axis_ortho G) hδ₀ (x n-y n)
    have e := linear_error G η hη.le hμ.le hμ' ha ha' (x n)
    change ‖(gradientStep G η)^[n+1] w - (linear _ _ _)^[n+1] w‖ ≤ _
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact hh.trans (by linarith only [H,e])
  have hcoef : 8*C*r^3 ≤ K*(g^3-g) := by
    have hk : K*p.μ = 256*r^3 := div_mul_cancel₀ _ hμ.ne'
    have H : 2*δ ≤ g^3-g := by dsimp [g]; nlinarith [sq_nonneg δ,pow_nonneg hδ₀ 3]
    have H' := mul_le_mul_of_nonneg_left H hK
    dsimp only [C,δ] at *
    nlinarith only [H',congrArg (fun a => a*η) hk,mul_nonneg hη.le (pow_nonneg hr 3)]
  have H := cubic_tracking hg (by dsimp [C]; positivity) hK hcoef x y rfl hq hstep k hs
  obtain ⟨hf,hn⟩ := bounded_modes _ _ (axis_unit G ha ha') G.norm_v (axis_ortho G) w
  have Hpath := linear_path _ _ (axis_unit G ha ha') G.norm_v (axis_ortho G) δ w k
  change y k = g^k • _ + _ + _ at Hpath
  have hbound : ‖y k-g^k • growing (axis G) G.v w‖ ≤ 8*r := by
    rw [Hpath,show ∀ x y z : Weights p.d, x+y+z-x = y+z by intros; abel]
    refine (norm_add_le ..).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by dsimp [δ]; linarith) _)]
    have ht := pow_le_one₀ (n := k) (show 0 ≤ 1-δ by dsimp [δ]; linarith) (by linarith : 1-δ ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_right ht (norm_nonneg (falling (axis G) G.v w))]
  have HH := norm_sub_le_norm_sub_add_norm_sub (x k) (y k) (g^k • growing (axis G) G.v w)
  change ‖x k - g^k • growing (axis G) G.v w‖ ≤ 8*r+K*(g^k)^3
  nlinarith only [H,HH,hbound,mul_nonneg hK (pow_nonneg (by linarith : 0 ≤ g) k)]

end LongTails.Proofs.LogisticCloudWarmup
