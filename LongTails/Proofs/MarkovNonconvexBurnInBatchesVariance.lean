import LongTails.Proofs.MarkovNonconvexBurnInBatchesCovariance
import LongTails.Proofs.MarkovNormalizedAlignment

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient

private lemma decay_sum {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∑ i ∈ Finset.range k, Real.exp (((i : ℝ)-k)/c) ≤ c := by
  let f := fun i : ℕ => Real.exp (((i:ℝ)-k)/c)
  have step i : f i ≤ c*(f (i+1)-f i) := by
    have eq : f (i+1) = f i * Real.exp (1/c) := by
      dsimp only [f]; rw [← Real.exp_add, Nat.cast_add, Nat.cast_one]; congr 1; ring
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1/c)) (Real.exp_pos (((i:ℝ)-k)/c)).le
    rw [eq]
    rw [mul_comm c, ← div_le_iff₀ hc]
    change f i*(1/c+1) ≤ _ at h
    linarith [show f i*(1/c+1) = f i/c + f i by ring]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => step i)
  rw [← Finset.mul_sum, Finset.sum_range_sub] at hs
  have hk : f k = 1 := by simp [f]
  rw [hk] at hs
  exact hs.trans (by nlinarith [mul_nonneg hc.le (show 0 ≤ f 0 from (Real.exp_pos _).le)])

variable {Z E : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option maxHeartbeats 1000000 in
lemma stationary_sum (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) {τ : ℝ} (hτ : 1 ≤ τ)
    (hd : ∀ t z, mixingDistance κ π t z ≤ 2*Real.exp (-(t:ℝ)/τ))
    {h : Z → E} (hm : Measurable h) (hi : Integrable h (π : Measure Z))
    (hz : (∫ z, h z ∂(π : Measure Z)) = 0)
    (hq : Integrable (fun z => ‖h z‖^2) (π : Measure Z)) (s n : ℕ) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    let S := fun ξ : ℕ → Z => ‖∑ i ∈ Finset.range n, h (ξ (s+i))‖^2
    Integrable S P ∧ (∫ ξ, S ξ ∂P) ≤ n*(13*τ)*(∫ z, ‖h z‖^2 ∂(π : Measure Z)) := by
  let P : Measure (ℕ → Z) := pathLaw κ π
  let X := fun i (ξ : ℕ → Z) => h (ξ (s+i))
  let m := ∫ z, ‖h z‖^2 ∂(π : Measure Z)
  have hm0 : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have law i : MeasurePreserving (fun ξ : ℕ → Z => ξ (s+i)) P (π : Measure Z) :=
    ⟨measurable_pi_apply _, pathLaw_stationary_marginal κ π hinv _⟩
  have mi i : Measurable (X i) := hm.comp (measurable_pi_apply _)
  have qi i : Integrable (fun ξ => ‖X i ξ‖^2) P := (law i).integrable_comp_of_integrable (g := fun z => ‖h z‖^2) hq
  have ii i j := integrable_pair (mi i) (mi j) (qi i) (qi j)
  induction n with
  | zero => simp
  | succ k ih =>
    dsimp only at ih ⊢
    let C := fun i (ξ : ℕ → Z) => ⟪X i ξ,X k ξ⟫
    have ci := integrable_finsetSum (Finset.range k) (fun i _ => ii i k)
    let R := fun i : ℕ => Real.exp (((i:ℝ)-k)/(2*τ))
    have cross (i) (hik : i ∈ Finset.range k) : (∫ ξ, C i ξ ∂P) ≤ R i*(3*m) := by
      have hi' := Finset.mem_range.mp hik
      have hh := lag_covariance κ π hinv (s+i) (k-i) (hd _) hm hi hz hq
      dsimp only at hh
      rw [show s+i+(k-i) = s+k by omega, Nat.cast_sub hi'.le, neg_sub] at hh
      exact hh.trans_eq (by dsimp [R,m]; ring)
    have hs := Finset.sum_le_sum cross
    rw [← Finset.sum_mul] at hs
    have hb := hs.trans (mul_le_mul_of_nonneg_right (decay_sum (show 0 < 2*τ by linarith) k)
      (show 0 ≤ 3*m by positivity))
    have diag : (∫ ξ, ‖X k ξ‖^2 ∂P) = m := by
      have e := integral_map (μ := P) (measurable_pi_apply (s+k)).aemeasurable
        (f := fun z => ‖h z‖^2) (hm.norm.pow_const 2).aestronglyMeasurable
      rw [(law k).map_eq] at e
      exact e.symm
    change Integrable (fun ξ => ‖∑ i ∈ Finset.range (k+1), X i ξ‖^2) P ∧ _
    simp_rw [Finset.sum_range_succ, norm_add_sq_real, sum_inner]
    refine ⟨(ih.1.add (ci.const_mul 2)).add (qi k), ?_⟩
    erw [integral_add (ih.1.add (ci.const_mul 2)) (qi k), integral_add ih.1 (ci.const_mul 2),
      integral_const_mul, integral_finsetSum _ (fun i _ => ii i k), diag, Nat.cast_succ]
    change (∫ ξ, ‖∑ i ∈ Finset.range k, X i ξ‖^2 ∂P) + 2*(∑ i ∈ Finset.range k, ∫ ξ, C i ξ ∂P) + m ≤ _
    have prev := ih.2
    change _ ≤ (k:ℝ)*(13*τ)*m at prev
    nlinarith [ih.2, mul_le_mul_of_nonneg_right hτ hm0]

lemma stationary_alignment (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) {τ σ ε : ℝ} (hτ : 1 ≤ τ) (hε : 0 < ε)
    (hd : ∀ t z, mixingDistance κ π t z ≤ 2*Real.exp (-(t:ℝ)/τ))
    {g : Z → E} (hm : Measurable g) (hi : Integrable g (π : Measure Z)) (u : E)
    (hz : (∫ z, g z ∂(π : Measure Z)) = u)
    (hq : Integrable (fun z => ‖g z-u‖^2) (π : Measure Z))
    (hv : (∫ z, ‖g z-u‖^2 ∂(π : Measure Z)) ≤ σ^2) (s n : ℕ) (hn : 0 < n)
    (hs : 1024*τ*σ^2 ≤ n*ε^2) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    ‖u‖-ε/4 ≤ ∫ ξ, let v := ∑ i ∈ Finset.range n, g (ξ (s+i))
      ⟪u, ‖v‖⁻¹ • v⟫ ∂P := by
  intro P
  let h := fun z => g z-u
  have mh : Measurable h := hm.sub measurable_const
  have hz' : (∫ z, h z ∂(π : Measure Z)) = 0 := by
    simp [h, integral_sub hi (integrable_const u), hz]
  have var := stationary_sum κ π hinv hτ hd mh (hi.sub (integrable_const u)) hz' hq s n
  let S := fun ξ : ℕ → Z => ∑ i ∈ Finset.range n, h (ξ (s+i))
  let V := fun ξ : ℕ → Z => ∑ i ∈ Finset.range n, g (ξ (s+i))
  let A := fun ξ => ⟪u, ‖V ξ‖⁻¹ • V ξ⟫
  have mV : Measurable V := Finset.measurable_sum _ (fun i _ => hm.comp (measurable_pi_apply _))
  have mS : Measurable S := Finset.measurable_sum _ (fun i _ => mh.comp (measurable_pi_apply _))
  have mA : Measurable A := by dsimp [A]; fun_prop
  have iA : Integrable A P := Integrable.of_bound mA.aestronglyMeasurable ‖u‖
    (.of_forall fun ξ => MarkovBatchContinuation.bound_normalized u (V ξ))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have cs := OracleTemplate.Scent.AnchorHyp.integral_mul_le_sqrt (μ := P) mS.norm
    (measurable_const (a := (1:ℝ))) (fun ξ => norm_nonneg (S ξ)) (fun _ => zero_le_one)
    var.1 (integrable_const _)
  simp only [mul_one, one_pow, integral_const, probReal_univ, one_smul, Real.sqrt_one] at cs
  have est : (∫ ξ, ‖S ξ‖ ∂P) ≤ n*ε/8 := by
    apply cs.trans
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, var.2.trans ?_⟩
    have hh := mul_le_mul_of_nonneg_left hv (show 0 ≤ (n:ℝ)*(13*τ) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hs hn'.le
    nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)*τ by positivity) (sq_nonneg σ)]
  have iS : Integrable (fun ξ => ‖S ξ‖) P :=
    ((memLp_two_iff_integrable_sq mS.norm.aestronglyMeasurable).2 var.1).integrable (by norm_num)
  have pt ξ : ‖u‖ - (2/(n:ℝ))*‖S ξ‖ ≤ A ξ := by
    have hh := MarkovNormalizedAlignment.alignment hn u (fun i : Fin n => g (ξ (s+i.val)))
    rw [OracleTemplate.RobustGradient.finite_mean_centered u n hn (fun i : Fin n => ξ (s+i.val)),
      norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 1/(n:ℝ)),
      Fin.sum_univ_eq_sum_range (fun i => h (ξ (s+i)))] at hh
    unfold Algorithms.MarkovNormalizedBatch.direction at hh
    rw [Fin.sum_univ_eq_sum_range (fun i => g (ξ (s+i)))] at hh
    exact (by dsimp [S,A,V]; convert hh using 1; ring)
  have bound := integral_mono ((integrable_const ‖u‖).sub (iS.const_mul (2/(n:ℝ)))) iA pt
  change (∫ ξ, ‖u‖ - (2/(n:ℝ))*‖S ξ‖ ∂P) ≤ _ at bound
  rw [integral_sub (integrable_const _) (iS.const_mul _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at bound
  apply le_trans _ bound
  have scaled := mul_le_mul_of_nonneg_left est (show 0 ≤ 2/(n:ℝ) by positivity)
  field_simp [hn'.ne'] at scaled ⊢
  linarith

end LongTails.Proofs.MarkovNonconvexBurnInBatches
