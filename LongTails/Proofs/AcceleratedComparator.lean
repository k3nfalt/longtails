import LongTails.Proofs.AcceleratedBiasedStochastic

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.BiasedStochasticGradient

open StochasticGradient HeavyTailedMarkovGradient
open LongTails.Setups.StochasticSmoothAndConvex LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma integrable_comparator_energy {H : Type*} [MeasurableSpace H]
    {P : Measure H} [IsProbabilityMeasure P] {s : H → E × E} (hs : Measurable s)
    {f : E → ℝ} (hf : Measurable f) {D R M : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R)
    {x0 u : E} (hu : ‖u-x0‖ ≤ R)
    (hgap : ∀ x, ‖x-x0‖ ≤ R → |f x-f u| ≤ M)
    (hb : ∀ h, ‖(s h).1-x0‖ ≤ R ∧ ‖(s h).2-x0‖ ≤ R) (k : ℕ) :
    Integrable (fun h => acceleratedEnergy f D u k (s h)) P := by
  apply Integrable.of_bound ((measurable_acceleratedEnergy hf D u k).comp hs).aestronglyMeasurable
    (acceleratedWeight k * M + 2*D*R^2)
  apply Filter.Eventually.of_forall
  intro h
  have hz : ‖(s h).2-u‖ ≤ 2*R := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (s h).2 x0 u
    rw [norm_sub_rev x0 u] at hh
    linarith [(hb h).2]
  have hz' : ‖(s h).2-u‖^2 ≤ (2*R)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz
  have h1 := mul_le_mul_of_nonneg_left (hgap _ (hb h).1) (acceleratedWeight_nonneg k)
  have h2 := mul_le_mul_of_nonneg_left hz' hD
  change ‖acceleratedEnergy f D u k (s h)‖ ≤ _
  rw [Real.norm_eq_abs]
  unfold acceleratedEnergy
  calc
    _ ≤ |acceleratedWeight k * (f (s h).1-f u)| + |D/2*‖(s h).2-u‖^2| := abs_add_le _ _
    _ = acceleratedWeight k * |f (s h).1-f u| + D/2*‖(s h).2-u‖^2 := by
      rw [abs_mul, abs_of_nonneg (acceleratedWeight_nonneg k), abs_of_nonneg (by positivity : 0 ≤ D/2*‖(s h).2-u‖^2)]
    _ ≤ _ := by nlinarith only [h1,h2]

variable {Ω : Type} [MeasurableSpace Ω]

lemma comparator_stochastic_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D R b v M : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry g)) (hGi : ∀ x, Integrable (g x) p)
    (hb : ∀ x, ‖gradient f x - ∫ ω, g x ω ∂p‖ ≤ b)
    (hvi : ∀ x, Integrable (fun ω => ‖gradient f x - g x ω‖ ^ 2) p)
    (hv : ∀ x, (∫ ω, ‖gradient f x - g x ω‖ ^ 2 ∂p) ≤ v)
    (x0 x z u : E) (hgap : ∀ t, ‖t-x0‖ ≤ R → |f t-f u| ≤ M)
    (hx : ‖x-x0‖ ≤ R) (hz : ‖z-x0‖ ≤ R) (hu : ‖u-x0‖ ≤ R) (k : ℕ) :
    let step := fun ω => projectedUpdate D R x0 k (x,z) (g (Gradient.acceleratedQuery (k,x,z)) ω)
    Integrable (fun ω => acceleratedEnergy f D u (k+1) (step ω)) p ∧
      (∫ ω, acceleratedEnergy f D u (k+1) (step ω) ∂p) ≤
        acceleratedEnergy f D u k (x,z) + 2 * R * (((k:ℝ)+1)/2) * b +
          4 * (((k:ℝ)+1)/2)^2 * v / D := by
  let a := ((k:ℝ)+1)/2
  let y := Gradient.acceleratedQuery (k,x,z)
  let e := fun ω => gradient f y - g y ω
  let step := fun ω => projectedUpdate D R x0 k (x,z) (g y ω)
  have heint : Integrable e p := (integrable_const _).sub (hGi y)
  have hsm : Measurable step := (measurable_projectedUpdate D R x0 k).comp
    (measurable_const.prodMk (hG.comp (measurable_const.prodMk measurable_id)))
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hFi := integrable_comparator_energy (P := p) hsm hf hD.le hR hu hgap
    (fun ω => projectedUpdate_ball hR hx k (g y ω)) (k+1)
  have hBi : Integrable (fun ω => acceleratedEnergy f D u k (x,z) +
      a * ⟪e ω,z-u⟫ + 4*a^2/D * ‖e ω‖^2) p :=
    ((integrable_const _).add ((heint.inner_const _).const_mul _)).add ((hvi y).const_mul _)
  have hstep : ∀ ω, acceleratedEnergy f D u (k+1) (step ω) ≤
      acceleratedEnergy f D u k (x,z) + a * ⟪e ω,z-u⟫ + 4*a^2/D * ‖e ω‖^2 := by
    intro ω
    have hs := accelerated_projected_step hL.le hD hLD hR (p := 2) (by norm_num) (by norm_num)
      hc hg hlip x0 x z u (g y ω) hz hu
      (A := (k:ℝ)*((k:ℝ)+1)/4) (a := a)
      (by positivity) (by dsimp [a]; positivity) (by dsimp [a]; positivity)
      (by dsimp [a]; nlinarith [Nat.cast_nonneg (α := ℝ) k])
    have hw : ((k:ℝ)+1)*((k:ℝ)+1+1)/4 = (k:ℝ)*((k:ℝ)+1)/4 + a := by dsimp [a]; ring
    have heq : (a * ‖e ω‖)^ (2:ℝ) * (2*R)^((2:ℝ)-2) / (D/4)^((2:ℝ)-1) = 4*a^2/D * ‖e ω‖^2 := by
      norm_num [Real.rpow_two]
      ring
    have hmin := min_le_left ((a * ‖e ω‖)^ (2:ℝ) * (2*R)^((2:ℝ)-2) / (D/4)^((2:ℝ)-1)) (2*R*a*‖e ω‖)
    have hs' := hs.trans (add_le_add (le_refl _) hmin)
    rw [heq] at hs'
    simpa only [acceleratedEnergy, acceleratedWeight, projectedUpdate, step,
      Gradient.acceleratedQuery, Nat.cast_add, Nat.cast_one, hw, a, y, e, div_div] using hs'
  have hzu : ‖z-u‖ ≤ 2*R := by
    have := norm_sub_le_norm_sub_add_norm_sub z x0 u
    rw [norm_sub_rev x0 u] at this
    linarith
  have hmean : (∫ ω, e ω ∂p) = gradient f y - ∫ ω, g y ω ∂p := by
    rw [show e = (fun ω => gradient f y - g y ω) from rfl,
      integral_sub (integrable_const _) (hGi y)]
    simp
  have hinner : (∫ ω, ⟪e ω,z-u⟫ ∂p) ≤ 2*R*b := by
    simp_rw [real_inner_comm (z-u)]
    rw [integral_inner heint, hmean]
    rw [real_inner_comm]
    have h1 := (real_inner_le_norm (gradient f y - ∫ ω, g y ω ∂p) (z-u)).trans
      (mul_le_mul (hb y) hzu (norm_nonneg _) (le_trans (norm_nonneg _) (hb y)))
    nlinarith only [h1]
  refine ⟨hFi, ?_⟩
  have hi := integral_mono hFi hBi hstep
  have hci : Integrable (fun ω => acceleratedEnergy f D u k (x,z) + a * ⟪e ω,z-u⟫) p :=
    (integrable_const _).add ((heint.inner_const _).const_mul _)
  have hqi : Integrable (fun ω => 4*a^2/D * ‖e ω‖^2) p := (hvi y).const_mul _
  rw [integral_add hci hqi,
    integral_add (integrable_const (acceleratedEnergy f D u k (x,z))) ((heint.inner_const (z-u)).const_mul a),
    integral_const_mul, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hb' := mul_le_mul_of_nonneg_left hinner (show 0 ≤ a by dsimp [a]; positivity)
  have hv' := mul_le_mul_of_nonneg_left (hv y) (show 0 ≤ 4*a^2/D by positivity)
  change _ ≤ acceleratedEnergy f D u k (x,z) + 2*R*a*b + 4*a^2*v/D
  dsimp [e, step, y] at hi hb' hv' ⊢
  calc
    _ ≤ acceleratedEnergy f D u k (x,z) + a * (2*R*b) + 4*a^2/D*v :=
      hi.trans (add_le_add (add_le_add (le_refl _) hb') hv')
    _ = _ := by ring


set_option maxHeartbeats 400000 in
lemma comparator_energy_bound {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D R b v M : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R) (hb0 : 0 ≤ b) (hv0 : 0 ≤ v)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry g)) (hGi : ∀ x, Integrable (g x) p)
    (hb : ∀ x, ‖gradient f x - ∫ ω, g x ω ∂p‖ ≤ b)
    (hvi : ∀ x, Integrable (fun ω => ‖gradient f x - g x ω‖ ^ 2) p)
    (hv : ∀ x, (∫ ω, ‖gradient f x - g x ω‖ ^ 2 ∂p) ≤ v)
    (x0 u : E) (hgap : ∀ t, ‖t-x0‖ ≤ R → |f t-f u| ≤ M) (hu : ‖u-x0‖ ≤ R)
    (K k : ℕ) (x z : E) (hx : ‖x-x0‖ ≤ R) (hz : ‖z-x0‖ ≤ R) :
    Integrable (fun ξ => acceleratedEnergy f D u (k+K) (projectedRun g D R x0 K k x z ξ))
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, acceleratedEnergy f D u (k+K) (projectedRun g D R x0 K k x z ξ)
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      acceleratedEnergy f D u k (x,z) + K * errorCost D R b v (k+K) := by
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hg x).continuousAt)).measurable
  induction K generalizing k x z with
  | zero => simp [projectedRun]
  | succ K ih =>
    let q := Measure.pi (fun _ : Fin K => p)
    let y := Gradient.acceleratedQuery (k,x,z)
    let step := fun ω => projectedUpdate D R x0 k (x,z) (g y ω)
    let C := (K:ℝ) * errorCost D R b v (k+(K+1))
    let B := fun ω => acceleratedEnergy f D u (k+1) (step ω) + C
    let F := fun w : Ω × (Fin K → Ω) => acceleratedEnergy f D u (k+(K+1))
      (projectedRun g D R x0 (K+1) k x z (Fin.cons w.1 w.2))
    have hmp : Measurable (fun ξ : Fin (K+1) → Ω => acceleratedEnergy f D u (k+(K+1))
        (projectedRun g D R x0 (K+1) k x z ξ)) :=
      (measurable_acceleratedEnergy hf D u _).comp
        ((measurable_projectedRun hG D R x0 (K+1) k).comp
          (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin (K+1) → Ω => ((x,z),ξ))))
    have hcons := cons_measurePreserving p K
    have hFm : Measurable F := hmp.comp hcons.measurable
    have hFeq (ω : Ω) : (fun ξ => F (ω,ξ)) = fun ξ => acceleratedEnergy f D u (k+1+K)
        (projectedRun g D R x0 K (k+1) (step ω).1 (step ω).2 ξ) := by
      funext ξ
      simp only [F,projectedRun,Fin.cons_zero,Fin.cons_succ,step,y]
      congr 1
      omega
    have hstep := comparator_stochastic_step hL hD hLD hR hc hg hlip hG hGi hb hvi hv
      x0 x z u hgap hx hz hu k
    have hstep' : (∫ ω, acceleratedEnergy f D u (k+1) (step ω) ∂p) ≤
        acceleratedEnergy f D u k (x,z) + errorCost D R b v (k+1) := by
      convert hstep.2 using 1; simp only [errorCost,Nat.cast_add,Nat.cast_one]; ring
    have hBint : Integrable B p := hstep.1.add (integrable_const C)
    have hsection : ∀ ω, Integrable (fun ξ => F (ω,ξ)) q := by
      intro ω
      rw [hFeq]
      have hs := projectedUpdate_ball (D := D) (z := z) hR hx k (g y ω)
      exact (ih (k+1) (step ω).1 (step ω).2 hs.1 hs.2).1
    have hbound : ∀ ω, (∫ ξ, F (ω,ξ) ∂q) ≤ B ω := by
      intro ω
      rw [hFeq]
      have hs := projectedUpdate_ball (D := D) (z := z) hR hx k (g y ω)
      simpa only [B,C,show k+1+K=k+(K+1) by omega] using
        (ih (k+1) (step ω).1 (step ω).2 hs.1 hs.2).2
    have hrun : Measurable (fun ξ : Fin (K+1) → Ω => projectedRun g D R x0 (K+1) k x z ξ) := by
      exact (measurable_projectedRun hG D R x0 (K+1) k).comp
        (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin (K+1) → Ω => ((x,z),ξ)))
    have hstate : Measurable (fun w : Ω × (Fin K → Ω) =>
        projectedRun g D R x0 (K+1) k x z (Fin.cons w.1 w.2)) :=
      hrun.comp hcons.measurable
    have hFi : Integrable F (p.prod q) := integrable_comparator_energy hstate hf hD.le hR hu hgap
      (fun w => projectedRun_ball g D hR x0 (K+1) k x z hx hz _) _
    have hi : Integrable (fun ξ => acceleratedEnergy f D u (k+(K+1))
        (projectedRun g D R x0 (K+1) k x z ξ)) (Measure.pi fun _ : Fin (K+1) => p) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp hFi
    refine ⟨hi,?_⟩
    calc
      _ = ∫ w, F w ∂p.prod q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable]
      _ = ∫ ω, ∫ ξ, F (ω,ξ) ∂q ∂p := integral_prod F hFi
      _ ≤ ∫ ω, B ω ∂p := integral_mono hFi.integral_prod_left hBint hbound
      _ = (∫ ω, acceleratedEnergy f D u (k+1) (step ω) ∂p) + C := by
        rw [integral_add hstep.1 (integrable_const C)]
        simp only [integral_const,probReal_univ,one_smul]
        rfl
      _ ≤ acceleratedEnergy f D u k (x,z) + errorCost D R b v (k+1) + C :=
        add_le_add hstep' (le_refl C)
      _ ≤ _ := by
        have hcost := errorCost_mono hD.le hR hb0 hv0 (show k+1 ≤ k+(K+1) by omega)
        dsimp [C]
        push_cast
        nlinarith only [hcost]


lemma comparator_expected_rate {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L D R b v M : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R) (hb0 : 0 ≤ b) (hv0 : 0 ≤ v)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hG : Measurable (Function.uncurry g)) (hGi : ∀ x, Integrable (g x) p)
    (hb : ∀ x, ‖gradient f x - ∫ ω, g x ω ∂p‖ ≤ b)
    (hvi : ∀ x, Integrable (fun ω => ‖gradient f x - g x ω‖ ^ 2) p)
    (hv : ∀ x, (∫ ω, ‖gradient f x - g x ω‖ ^ 2 ∂p) ≤ v)
    (x0 u : E) (hgap : ∀ t, ‖t-x0‖ ≤ R → |f t-f u| ≤ M) (hu : ‖u-x0‖ ≤ R) (K : ℕ) (hK : 0 < K) :
    Integrable (fun ξ => f (projectedRun g D R x0 K 0 x0 x0 ξ).1 - f u)
      (Measure.pi fun _ : Fin K => p) ∧
    (∫ ξ, f (projectedRun g D R x0 K 0 x0 x0 ξ).1 - f u
      ∂Measure.pi (fun _ : Fin K => p)) ≤
      2*D*R^2/((K:ℝ)*((K:ℝ)+1)) + 4*R*b + 4*(K:ℝ)*v/D := by
  have hKr : (0:ℝ) < K := Nat.cast_pos.mpr hK
  have hA : 0 < acceleratedWeight K := by unfold acceleratedWeight; positivity
  have hbnd := comparator_energy_bound hL hD hLD hR hb0 hv0 hc hg hlip hG hGi hb hvi hv
    x0 u hgap hu K 0 x0 x0 (by simpa) (by simpa)
  simp only [zero_add] at hbnd
  let V := fun ξ => acceleratedEnergy f D u K (projectedRun g D R x0 K 0 x0 x0 ξ)
  let F := fun ξ => f (projectedRun g D R x0 K 0 x0 x0 ξ).1 - f u
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hFm : Measurable F := (hf.comp (((measurable_projectedRun hG D R x0 K 0).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → Ω => ((x0,x0),ξ)))).fst)).sub_const _
  have hbound : ∀ ξ, F ξ ≤ (acceleratedWeight K)⁻¹ * V ξ := by
    intro ξ
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hA).mpr
    dsimp [F,V,acceleratedEnergy]
    have : 0 ≤ D/2 * ‖(projectedRun g D R x0 K 0 x0 x0 ξ).2-u‖^2 := by positivity
    nlinarith only [this]
  have hFi : Integrable F (Measure.pi fun _ : Fin K => p) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable M
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs]
    exact hgap _ (projectedRun_ball g D hR x0 K 0 x0 x0 (by simpa) (by simpa) ξ).1
  refine ⟨hFi,?_⟩
  calc
    _ ≤ ∫ ξ, (acceleratedWeight K)⁻¹ * V ξ ∂Measure.pi (fun _ : Fin K => p) :=
      integral_mono hFi (hbnd.1.const_mul _) hbound
    _ = (acceleratedWeight K)⁻¹ * ∫ ξ, V ξ ∂Measure.pi (fun _ : Fin K => p) := integral_const_mul _ _
    _ ≤ (acceleratedWeight K)⁻¹ * (acceleratedEnergy f D u 0 (x0,x0) + K*errorCost D R b v K) :=
      mul_le_mul_of_nonneg_left hbnd.2 (inv_nonneg.mpr hA.le)
    _ = 2*D*‖x0-u‖^2/((K:ℝ)*((K:ℝ)+1)) +
        4*(K:ℝ)*R*b/((K:ℝ)+1) + 4*(K:ℝ)^2*v/(((K:ℝ)+1)*D) := by
      simp only [acceleratedEnergy,acceleratedWeight,errorCost,Nat.cast_zero,zero_mul,zero_div,zero_add]
      field_simp
      ring
    _ ≤ _ := by
      have hnorm : ‖x0-u‖^2 ≤ R^2 := by
        rw [norm_sub_rev]
        exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hu
      have h1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm
        (show 0 ≤ 2*D by positivity)) (show 0 ≤ (K:ℝ)*((K:ℝ)+1) by positivity)
      have h2 : 4*(K:ℝ)*R*b/((K:ℝ)+1) ≤ 4*R*b := by
        apply (div_le_iff₀ (by positivity : 0 < (K:ℝ)+1)).mpr
        nlinarith [mul_nonneg hR hb0]
      have h3 : 4*(K:ℝ)^2*v/(((K:ℝ)+1)*D) ≤ 4*(K:ℝ)*v/D := by
        apply (div_le_iff₀ (by positivity : 0 < ((K:ℝ)+1)*D)).mpr
        have he : 4*(K:ℝ)*v/D*(((K:ℝ)+1)*D) = 4*(K:ℝ)*v*((K:ℝ)+1) := by field_simp
        rw [he]
        nlinarith [mul_nonneg hKr.le hv0]
      linarith


end OracleTemplate.BiasedStochasticGradient
