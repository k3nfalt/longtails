import LongTails.Proofs.InertialMonotoneStep
import LongTails.Proofs.InertialMonotoneTransport
import LongTails.Proofs.FiniteVarianceBatch
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_nonnegative_kernel {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {M : Measure A} {Q : Measure B} [SFinite Q] {f : A × B → ℝ} {u : A → ℝ}
    (hf : Measurable f) (hn : ∀ a b, 0 ≤ f (a, b))
    (hfi : ∀ a, Integrable (fun b => f (a, b)) Q) (hu : Integrable u M)
    (hb : ∀ a, (∫ b, f (a, b) ∂Q) ≤ u a) : Integrable f (M.prod Q) := by
  apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall hfi, ?_⟩
  have he (a : A) : (∫ b, ‖f (a, b)‖ ∂Q) = ∫ b, f (a, b) ∂Q := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun b => Real.norm_of_nonneg (hn a b))
  simp_rw [he]
  apply hu.mono' hf.aestronglyMeasurable.integral_prod_right'
  apply Filter.Eventually.of_forall
  intro a
  rw [Real.norm_of_nonneg (integral_nonneg (hn a))]
  exact hb a

omit [CompleteSpace E] in
lemma affine_sq_integrable {X : Ω → E} (hX : Measurable X)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (a : E) (c : ℝ) :
    Integrable (fun ω => ‖a - c • X ω‖ ^ 2) P := by
  have hx : MemLp X 2 P := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mpr hX2
  have hh : MemLp (fun ω => a - c • X ω) 2 P := (memLp_const a).sub (hx.const_smul c)
  exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh

lemma fresh_second_integral {η μ K v : ℝ} (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hcap : 2 * η * μ + 2 * η ^ 2 * K ^ 2 ≤ 1) (z p g q ξ : E)
    (hm : μ * ‖z - η • g - p‖ ^ 2 ≤ ⟪q, z - η • g - p⟫)
    (he : ‖q - g‖ ^ 2 ≤ 2 * K ^ 2 * ‖η • g‖ ^ 2 + 2 * ‖ξ‖ ^ 2)
    {ζ : Ω → E} (hζ : Measurable ζ) (hζi : Integrable ζ P)
    (hζ2 : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hmean : (∫ ω, ζ ω ∂P) = 0) (hv : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ v) :
    (∫ ω, ‖z - η • (q + ζ ω) - p‖ ^ 2 ∂P) ≤
      (1 - η * μ) * ‖z - p‖ ^ 2 + 2 * η ^ 2 * ‖ξ‖ ^ 2 + η ^ 2 * v := by
  let C := (1 - η * μ) * ‖z - p‖ ^ 2 + 2 * η ^ 2 * ‖ξ‖ ^ 2
  let a := z - η • q - p
  have hi : Integrable (fun ω => ‖z - η • (q + ζ ω) - p‖ ^ 2) P := by
    have heq (ω : Ω) : z - η • (q + ζ ω) - p = a - η • ζ ω := by
      dsimp [a]
      module
    simp_rw [heq]
    exact affine_sq_integrable hζ hζ2 a η
  have hz : (∫ ω, ⟪ζ ω, a⟫ ∂P) = 0 := by
    calc
      _ = ∫ ω, ⟪a, ζ ω⟫ ∂P := integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => (real_inner_comm (ζ ω) a).symm))
      _ = 0 := by rw [integral_inner hζi, hmean]; simp
  have hb : Integrable (fun ω => C + η ^ 2 * ‖ζ ω‖ ^ 2 -
      2 * η * ⟪ζ ω, a⟫) P :=
    ((integrable_const _).add (hζ2.const_mul _)).sub ((hζi.inner_const _).const_mul _)
  have hh := integral_mono hi hb (fun ω => extragradient_contract hη hμ hcap z p g q ξ
    (ζ ω) hm he)
  have hsub := integral_sub ((integrable_const C).add (hζ2.const_mul (η ^ 2)))
    ((hζi.inner_const a).const_mul (2 * η))
  have hadd := integral_add (integrable_const C) (hζ2.const_mul (η ^ 2))
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, integral_const_mul, hz] at hh
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero] at hh
  have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg η)
  change _ ≤ C + η ^ 2 * v
  linarith

lemma fresh_two_integral {η μ K v : ℝ} (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hcap : 2 * η * μ + 2 * η ^ 2 * K ^ 2 ≤ 1) (z p : E)
    {g q ξ : Ω → E} (hq : Measurable q)
    (hξ2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P)
    (hξv : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ v)
    (hm : ∀ ω, μ * ‖z - η • g ω - p‖ ^ 2 ≤ ⟪q ω, z - η • g ω - p⟫)
    (he : ∀ ω, ‖q ω - g ω‖ ^ 2 ≤ 2 * K ^ 2 * ‖η • g ω‖ ^ 2 + 2 * ‖ξ ω‖ ^ 2)
    {ζ : Ω × Ω → E} (hζ : Measurable ζ)
    (hζi : ∀ a, Integrable (fun b => ζ (a, b)) P)
    (hζ2 : ∀ a, Integrable (fun b => ‖ζ (a, b)‖ ^ 2) P)
    (hmean : ∀ a, (∫ b, ζ (a, b) ∂P) = 0)
    (hv : ∀ a, (∫ b, ‖ζ (a, b)‖ ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖z - η • (q ω.1 + ζ ω) - p‖ ^ 2) (P.prod P) ∧
    (∫ ω, ‖z - η • (q ω.1 + ζ ω) - p‖ ^ 2 ∂P.prod P) ≤
      (1 - η * μ) * ‖z - p‖ ^ 2 + 3 * η ^ 2 * v := by
  let f : Ω × Ω → ℝ := fun ω => ‖z - η • (q ω.1 + ζ ω) - p‖ ^ 2
  let C := (1 - η * μ) * ‖z - p‖ ^ 2
  let u : Ω → ℝ := fun ω => C + 2 * η ^ 2 * ‖ξ ω‖ ^ 2 + η ^ 2 * v
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hui : Integrable u P :=
    ((integrable_const C).add (hξ2.const_mul _)).add (integrable_const _)
  have hbound (a : Ω) : (∫ b, f (a, b) ∂P) ≤ u a :=
    fresh_second_integral hη hμ hcap z p (g a) (q a) (ξ a) (hm a) (he a)
      (hζ.comp measurable_prodMk_left) (hζi a) (hζ2 a) (hmean a) (hv a)
  have hfi (a : Ω) : Integrable (fun b => f (a, b)) P := by
    have heq (b : Ω) : z - η • (q a + ζ (a, b)) - p =
        (z - η • q a - p) - η • ζ (a, b) := by module
    dsimp [f]
    simp_rw [heq]
    exact affine_sq_integrable (hζ.comp measurable_prodMk_left) (hζ2 a) _ η
  have hi : Integrable f (P.prod P) := integrable_nonnegative_kernel hf
    (fun _ _ => sq_nonneg _) hfi hui hbound
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi.integral_prod_left hui hbound
  have ha := integral_add ((integrable_const C).add (hξ2.const_mul (2 * η ^ 2)))
    (integrable_const (η ^ 2 * v))
  have hb := integral_add (integrable_const C) (hξ2.const_mul (2 * η ^ 2))
  simp only [Pi.add_apply] at ha hb
  change (∫ a, ∫ b, f (a, b) ∂P ∂P) ≤ ∫ a, C + 2 * η ^ 2 * ‖ξ a‖ ^ 2 + η ^ 2 * v ∂P at hh
  rw [ha, hb] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  rw [integral_const_mul (2 * η ^ 2)] at hh
  change (∫ ω, f ω ∂P.prod P) ≤ C + 3 * η ^ 2 * v
  rw [integral_prod f hi]
  have hvar := mul_le_mul_of_nonneg_left hξv (show 0 ≤ 2 * η ^ 2 by positivity)
  linarith

lemma operator_two_integral {η μ K v : ℝ} (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hcap : 2 * η * μ + 2 * η ^ 2 * K ^ 2 ≤ 1)
    (H : E → E) (hH : Continuous H) (z p : E)
    (hm : ∀ y, μ * ‖y - p‖ ^ 2 ≤ ⟪H y, y - p⟫)
    (hlip : ∀ a b, ‖H a - H b‖ ≤ K * ‖a - b‖)
    {ξ : Ω → E} (hξ : Measurable ξ)
    (hξ2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P)
    (hξv : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ v)
    {ζ : E → Ω → E} (hζ : Measurable (Function.uncurry ζ))
    (hζi : ∀ y, Integrable (ζ y) P)
    (hζ2 : ∀ y, Integrable (fun ω => ‖ζ y ω‖ ^ 2) P)
    (hmean : ∀ y, (∫ ω, ζ y ω ∂P) = 0)
    (hv : ∀ y, (∫ ω, ‖ζ y ω‖ ^ 2 ∂P) ≤ v) :
    let y := fun ω => z - η • (H z + ξ ω)
    Integrable (fun ω => ‖z - η • (H (y ω.1) + ζ (y ω.1) ω.2) - p‖ ^ 2)
      (P.prod P) ∧
    (∫ ω, ‖z - η • (H (y ω.1) + ζ (y ω.1) ω.2) - p‖ ^ 2 ∂P.prod P) ≤
      (1 - η * μ) * ‖z - p‖ ^ 2 + 3 * η ^ 2 * v := by
  intro y
  have hy : Measurable y := by dsimp [y]; fun_prop
  have he (ω : Ω) : ‖H (y ω) - (H z + ξ ω)‖ ^ 2 ≤
      2 * K ^ 2 * ‖η • (H z + ξ ω)‖ ^ 2 + 2 * ‖ξ ω‖ ^ 2 := by
    apply extragradient_local_error
    have hd : ‖y ω - z‖ = ‖η • (H z + ξ ω)‖ := by
      rw [norm_sub_rev]
      congr 1
      dsimp [y]
      abel
    simpa only [hd] using hlip (y ω) z
  exact fresh_two_integral hη hμ hcap z p (hH.measurable.comp hy) hξ2 hξv
    (fun ω => hm (y ω)) he
    (hζ.comp ((hy.comp measurable_fst).prodMk measurable_snd))
    (fun a => hζi (y a)) (fun a => hζ2 (y a))
    (fun a => hmean (y a)) (fun a => hv (y a))

omit [CompleteSpace E] in
lemma integral_regularized_transport {F : E → E} (hF : Measurable F)
    {r μ : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hμ : 0 ≤ μ)
    (hmono : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (x p : E)
    (hp : F p = μ • (x - p)) {w q : Ω → E} (hw : Measurable w) (hq : Measurable q)
    (hw2 : Integrable (fun ω => ‖w ω - p‖ ^ 2) P)
    (hroot : ∀ ω, F (q ω) = (μ * (1 + r / 2)) •
      (x + (3 * r / (2 * (2 + r))) • (w ω - x) - q ω)) :
    let f := fun ω => ‖(μ * (1 + r / 2)) •
      (x + ((4 + 3 * r) / (2 * (2 + r))) • (w ω - x) - q ω)‖ ^ 2 + ‖F (q ω)‖ ^ 2
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤
      μ ^ 2 * (1 + r) ^ 2 * (∫ ω, ‖w ω - p‖ ^ 2 ∂P) + ‖F p‖ ^ 2 := by
  intro f
  let B := fun ω => μ ^ 2 * (1 + r) ^ 2 * ‖w ω - p‖ ^ 2 + ‖F p‖ ^ 2
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have hfn (ω : Ω) : 0 ≤ f ω := by dsimp [f]; positivity
  have hBi : Integrable B P := (hw2.const_mul _).add (integrable_const _)
  have hbound (ω : Ω) : f ω ≤ B ω := by
    have hh := regularized_transport hr hr2 hμ hmono x (w ω) p (q ω) hp (hroot ω)
    dsimp [f, B]
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using hh
  have hfi : Integrable f P := hBi.mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_of_nonneg (hfn ω)]
      exact hbound ω))
  refine ⟨hfi, ?_⟩
  have hh := integral_mono hfi hBi hbound
  have ha := integral_add (hw2.const_mul (μ ^ 2 * (1 + r) ^ 2)) (integrable_const (‖F p‖ ^ 2))
  change (∫ ω, f ω ∂P) ≤ ∫ ω, μ ^ 2 * (1 + r) ^ 2 * ‖w ω - p‖ ^ 2 + ‖F p‖ ^ 2 ∂P at hh
  rw [ha, integral_const_mul] at hh
  simpa only [integral_const, probReal_univ, one_smul] using hh

omit [CompleteSpace E] in
lemma integral_potential_step {F : E → E} (hF : Measurable F)
    {r μ η v : ℝ} (hr : 0 < r) (hrmax : r ≤ 1 / 16) (hμ : 0 < μ)
    (hv : 0 ≤ v) (hη : η = 2 * r / μ)
    (hmono : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (x z p : E)
    (hp : F p = μ • (x - p)) {w q : Ω → E} (hw : Measurable w) (hq : Measurable q)
    (hw2 : Integrable (fun ω => ‖w ω - p‖ ^ 2) P)
    (hstep : (∫ ω, ‖w ω - p‖ ^ 2 ∂P) ≤
      (1 - η * μ) * ‖z - p‖ ^ 2 + 3 * η ^ 2 * v)
    (hroot : ∀ ω, F (q ω) = (μ * (1 + r / 2)) •
      (x + (3 * r / (2 * (2 + r))) • (w ω - x) - q ω)) :
    let f := fun ω => ‖(μ * (1 + r / 2)) •
      (x + ((4 + 3 * r) / (2 * (2 + r))) • (w ω - x) - q ω)‖ ^ 2 + ‖F (q ω)‖ ^ 2
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤
      μ ^ 2 * ‖z - p‖ ^ 2 + ‖F p‖ ^ 2 + 14 * r ^ 2 * v := by
  intro f
  have ht := integral_regularized_transport hF hr (by linarith) hμ.le hmono x p hp hw hq hw2 hroot
  refine ⟨ht.1, ?_⟩
  have hs := mul_le_mul_of_nonneg_left hstep (sq_nonneg μ)
  have he : μ ^ 2 * ((1 - η * μ) * ‖z - p‖ ^ 2 + 3 * η ^ 2 * v) =
      (1 - 2 * r) * μ ^ 2 * ‖z - p‖ ^ 2 + 12 * r ^ 2 * v := by
    rw [hη]
    field_simp
    ring
  rw [he] at hs
  have hc := corrected_contraction hr.le hrmax hv (sq_nonneg ‖z - p‖) hs
  linarith [ht.2]

end OracleTemplate.InertialMonotone
