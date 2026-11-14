import LongTails.Setups.RipmGeneral
import LongTails.Proofs.RipmProxGeometry
import LongTails.Proofs.RipmSmoothGeometry
import LongTails.Proofs.RipmConditional
import LongTails.Proofs.RipmRegularity
import LongTails.Proofs.RipmVariance
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

open MeasureTheory
open LongTails.Setups.RipmGeneral

namespace LongTails.Proofs.RipmDescent

noncomputable section

lemma one_step {d : ℕ} (q phi f : Core.Vec d → ℝ)
    (H F : Core.Vec d → Core.Vec d) (L Lq tau delta : ℝ)
    (hL : 0 < L) (hLq : 0 ≤ Lq) (htau : 0 < tau) (hdelta : 0 < delta)
    (hq : ConvexOn ℝ Set.univ q)
    (hqLip : ∀ x y, |q x - q y| ≤ Lq * ‖x - y‖)
    (hphi : ConvexOn ℝ Set.univ phi)
    (hH : ∀ x, HasGradientAt phi (H x) x)
    (hHLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hF : ∀ x, HasGradientAt f (F x) x)
    (hFLip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (x z : Core.Vec d) :
    let y := Core.prox q tau (x - tau • H x)
    ‖y - z‖ ^ 2 - ‖x - z‖ ^ 2 ≤
      2 * tau * (phi z - phi x + q z - q y + f x - f y) +
      tau / delta * ‖H x - F x‖ ^ 2 +
      (tau * delta + tau * L - 1) * ‖x - y‖ ^ 2 := by
  let y := Core.prox q tau (x - tau • H x)
  change ‖y - z‖ ^ 2 - ‖x - z‖ ^ 2 ≤
    2 * tau * (phi z - phi x + q z - q y + f x - f y) +
      tau / delta * ‖H x - F x‖ ^ 2 +
      (tau * delta + tau * L - 1) * ‖x - y‖ ^ 2
  have hp := (LongTails.Proofs.RipmProxGeometry.prox_iff q tau Lq htau hLq hq hqLip
    (x - tau • H x) y).mp rfl z
  rw [show y - (x - tau • H x) = y - x + tau • H x by module,
    inner_add_left, real_inner_smul_left] at hp
  have hphiL : phi x + inner ℝ (H x) (z - x) ≤ phi z := by
    have hc := LongTails.Proofs.RipmSmoothGeometry.cocoercivity phi H L hL hH hHLip hphi z x
    have hb : 0 ≤ 2 * L * (phi z - phi x - inner ℝ (H x) (z - x)) :=
      (sq_nonneg ‖H z - H x‖).trans hc
    have hn := (mul_nonneg_iff_of_pos_left (show 0 < 2 * L by positivity)).mp hb
    linarith
  have hfU := LongTails.Proofs.RipmSmoothGeometry.smooth_upper f F L hL hF hFLip x y
  rw [norm_sub_rev y x] at hfU
  have hn : ‖y - z‖ ^ 2 - ‖x - z‖ ^ 2 =
      2 * inner ℝ (y - x) (y - z) - ‖x - y‖ ^ 2 := by
    rw [show x - z = (x - y) + (y - z) by module, norm_add_sq_real,
      show y - x = -(x - y) by module, inner_neg_left]
    ring
  have hY : 2 * inner ℝ (H x - F x) (x - y) ≤
      ‖H x - F x‖ ^ 2 / delta + delta * ‖x - y‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hdelta).mp
    have hd := div_mul_cancel₀ (‖H x - F x‖ ^ 2) hdelta.ne'
    have hc := mul_le_mul_of_nonneg_left
      (real_inner_le_norm (H x - F x) (x - y)) hdelta.le
    nlinarith [sq_nonneg (‖H x - F x‖ - delta * ‖x - y‖)]
  have hphiM := mul_le_mul_of_nonneg_left hphiL (by positivity : 0 ≤ 2 * tau)
  have hfM := mul_le_mul_of_nonneg_left hfU (by positivity : 0 ≤ 2 * tau)
  have hYM := mul_le_mul_of_nonneg_left hY htau.le
  have hpM := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  simp only [inner_sub_left, inner_sub_right] at hpM hphiM hfM hYM hn
  simp only [div_eq_mul_inv] at hYM ⊢
  nlinarith


lemma prox_decouple {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg tau : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (htau : 0 < tau)
    (hSamples : Core.Sampling I P tau x0 i j) (t : ℕ) (z : Ω → Core.Vec d)
    (hz : @Measurable Ω (Core.Vec d) (Core.iterateHistory I tau x0 i j t) _ z)
    (hzreg : ∀ k, Integrable (fun omega => I.regularizers k (z omega)) P.toMeasure) :
    (∀ᵐ omega ∂P.toMeasure,
      MeasureTheory.condExp (Core.iterateHistory I tau x0 i j t) P.toMeasure (fun omega => (m : ℝ) * (I.regularizers (j t omega) (z omega) - I.regularizers (j t omega) (Core.trajectory I tau x0 i j (t + 1) omega))) omega ≤
        MeasureTheory.condExp (Core.iterateHistory I tau x0 i j t) P.toMeasure (fun omega => Core.regularizer I (z omega) - Core.regularizer I (Core.trajectory I tau x0 i j (t + 1) omega) + 2 * m * Lg * ‖Core.trajectory I tau x0 i j t omega - Core.trajectory I tau x0 i j (t + 1) omega‖) omega) ∧
    2 * tau * (∫ omega, (m : ℝ) *
      (I.regularizers (j t omega) (z omega) - I.regularizers (j t omega) (Core.trajectory I tau x0 i j (t + 1) omega)) ∂P.toMeasure) ≤
      2 * tau * (∫ omega, Core.regularizer I (z omega) - Core.regularizer I (Core.trajectory I tau x0 i j (t + 1) omega) ∂P.toMeasure) +
      4 * tau * m * Lg * (∫ omega, ‖Core.trajectory I tau x0 i j t omega - Core.trajectory I tau x0 i j (t + 1) omega‖ ∂P.toMeasure) := by
  classical
  let mΩ : MeasurableSpace Ω := inferInstance
  let M := Core.iterateHistory I tau x0 i j t
  let : MeasurableSpace Ω := mΩ
  let x := Core.trajectory I tau x0 i j t
  let y := Core.trajectory I tau x0 i j (t + 1)
  have hM := (LongTails.Proofs.RipmRegularity.trajectory_adapted
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t).1
  have hxM := (LongTails.Proofs.RipmRegularity.trajectory_adapted
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t).2
  have hx : Measurable x := hxM.mono hM le_rfl
  have hy : Measurable y := LongTails.Proofs.RipmRegularity.trajectory_measurable
    I L Lg tau x0 xs sigmaSq i j hS htau hSamples.1.measurable
      (fun k => (hSamples.2 k).1) (t + 1)
  have hzA : Measurable z := hz.mono hM le_rfl
  have hx2 := LongTails.Proofs.RipmRegularity.trajectory_memLp
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t
  have hy2 := LongTails.Proofs.RipmRegularity.trajectory_memLp
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples (t + 1)
  have hgc (k : Fin m) : Continuous (I.regularizers k) :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ (hS.regularizerConvex k))
  have hreg (v : Ω → Core.Vec d) (hv : Measurable v) (hv2 : MemLp v 2 P.toMeasure)
      (k : Fin m) : Integrable (fun omega => I.regularizers k (v omega)) P.toMeasure := by
    have hn := (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hv2).norm
    apply ((integrable_const |I.regularizers k 0|).fun_add (hn.const_mul Lg)).mono'
      ((hgc k).measurable.comp hv).aestronglyMeasurable
    filter_upwards [] with omega
    have hl := hS.regularizerLipschitz k (v omega) 0
    rw [sub_zero] at hl
    have ha := abs_add_le (I.regularizers k (v omega) - I.regularizers k 0)
      (I.regularizers k 0)
    rw [sub_add_cancel] at ha
    change |I.regularizers k (v omega)| ≤ _
    linarith
  have hxreg := hreg x hx hx2
  have hyreg := hreg y hy hy2
  have hsum (v : Ω → Core.Vec d)
      (hv : ∀ k, Integrable (fun omega => I.regularizers k (v omega)) P.toMeasure) :
      Integrable (fun omega => Core.regularizer I (v omega)) P.toMeasure := by
    change Integrable (fun omega => ∑ k, I.regularizers k (v omega)) P.toMeasure
    exact integrable_finsetSum Finset.univ (fun k _ => hv k)
  have hsel (v : Ω → Core.Vec d) (hv : Measurable v)
      (hi : ∀ k, Integrable (fun omega => I.regularizers k (v omega)) P.toMeasure) :
      Integrable (fun omega => I.regularizers (j t omega) (v omega)) P.toMeasure := by
    have hm : Measurable (fun p : Core.Vec d × Fin m => I.regularizers p.2 p.1) :=
      measurable_from_prod_countable_left (fun k => (hgc k).measurable)
    have hb := integrable_finsetSum Finset.univ (fun k _ => (hi k).norm)
    apply hb.mono' (hm.comp (hv.prodMk (hSamples.2 t).1)).aestronglyMeasurable
    filter_upwards [] with omega
    exact Finset.single_le_sum (f := fun k : Fin m => ‖I.regularizers k (v omega)‖)
      (fun k _ => norm_nonneg _) (Finset.mem_univ (j t omega))
  have hmean (v : Ω → Core.Vec d) (hv : @Measurable Ω (Core.Vec d) M _ v)
      (hi : ∀ k, Integrable (fun omega => I.regularizers k (v omega)) P.toMeasure) :
      condExp M P.toMeasure (fun omega => (m : ℝ) * I.regularizers (j t omega) (v omega))
        =ᵐ[P.toMeasure] (fun omega => Core.regularizer I (v omega)) := by
    obtain ⟨hm, hlaw⟩ := (hSamples.2 t).2.2.2
    let nu := Core.uniformMeasure m hm
    have hav (v : Core.Vec d) :
        (∫ k, (m : ℝ) * I.regularizers k v ∂(nu : Measure (Fin m))) =
          Core.regularizer I v := by
      let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      change (∫ k, (m : ℝ) * I.regularizers k v
        ∂(PMF.uniformOfFintype (Fin m)).toMeasure) = ∑ k, I.regularizers k v
      rw [PMF.integral_eq_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [PMF.uniformOfFintype_apply]
      simp only [Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp [hm0]
    have hjoint := (hsel v (hv.mono hM le_rfl) hi).const_mul (m : ℝ)
    have havint : Integrable (fun omega =>
        ∫ k, (m : ℝ) * I.regularizers k (v omega) ∂(nu : Measure (Fin m))) P.toMeasure := by
      simp only [hav]
      exact hsum v hi
    have hk : Measurable (Function.uncurry (fun v k => (m : ℝ) * I.regularizers k v)) :=
      measurable_from_prod_countable_left (fun k => (hgc k).measurable.const_mul (m : ℝ))
    have hc := LongTails.Proofs.RipmConditional.conditional_kernel P nu M hM
      (j t) v (fun v k => (m : ℝ) * I.regularizers k v)
      (hSamples.2 t).1 hv hk (hSamples.2 t).2.2.1 hlaw hjoint havint
    simpa only [hav] using hc
  have hgmeas (v : Ω → Core.Vec d) (hv : @Measurable Ω (Core.Vec d) M _ v) :
      @Measurable Ω ℝ M _ (fun omega => Core.regularizer I (v omega)) := by
    change @Measurable Ω ℝ M _ (fun omega => ∑ k, I.regularizers k (v omega))
    exact Finset.measurable_fun_sum Finset.univ (fun k _ => (hgc k).measurable.comp hv)
  have hgz := hsum z hzreg
  have hgx := hsum x hxreg
  have hgy := hsum y hyreg
  have hsz := (hsel z hzA hzreg).const_mul (m : ℝ)
  have hsx := (hsel x hx hxreg).const_mul (m : ℝ)
  have hsy := (hsel y hy hyreg).const_mul (m : ℝ)
  let A := fun omega => (m : ℝ) *
    (I.regularizers (j t omega) (z omega) - I.regularizers (j t omega) (y omega))
  let B := fun omega => Core.regularizer I (z omega) - Core.regularizer I (y omega) +
    2 * m * Lg * ‖x omega - y omega‖
  let F := fun omega => ((m : ℝ) * I.regularizers (j t omega) (z omega) -
    Core.regularizer I (z omega)) - ((m : ℝ) * I.regularizers (j t omega) (x omega) -
    Core.regularizer I (x omega))
  have hA : Integrable A P.toMeasure := by
    simpa only [A, mul_sub] using hsz.sub' hsy
  have hN : Integrable (fun omega => ‖x omega - y omega‖) P.toMeasure := by
    simpa only [Pi.sub_apply] using
      (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hx2.sub hy2)).norm
  have hB : Integrable B P.toMeasure := (hgz.sub' hgy).fun_add (hN.const_mul (2 * m * Lg))
  have hF : Integrable F P.toMeasure := (hsz.sub' hgz).sub' (hsx.sub' hgx)
  have hzero : condExp M P.toMeasure F =ᵐ[P.toMeasure] (fun _ => 0) := by
    have hcz := hmean z hz hzreg
    have hcx := hmean x hxM hxreg
    have hzg := condExp_of_stronglyMeasurable hM (hgmeas z hz).stronglyMeasurable hgz
    have hxg := condExp_of_stronglyMeasurable hM (hgmeas x hxM).stronglyMeasurable hgx
    have hs1 := condExp_sub hsz hgz M
    have hs2 := condExp_sub hsx hgx M
    have hs3 := condExp_sub (hsz.sub' hgz) (hsx.sub' hgx) M
    have hsubeq (f g : Ω → ℝ) : f - g = (fun omega => f omega - g omega) := rfl
    simp only [hsubeq] at hs1 hs2 hs3
    filter_upwards [hcz, hcx, hs1, hs2, hs3] with omega hzv hxv hs1v hs2v hs3v
    change condExp M P.toMeasure
      (fun omega => ((m : ℝ) * I.regularizers (j t omega) (z omega) - Core.regularizer I (z omega)) -
        ((m : ℝ) * I.regularizers (j t omega) (x omega) - Core.regularizer I (x omega))) omega = 0
    rw [hs3v, hs1v, hs2v, hzv, hxv, hzg, hxg]
    simp only [sub_self]
  have hpoint : A ≤ᵐ[P.toMeasure] B + F := by
    filter_upwards [] with omega
    have hj := (abs_le.mp (hS.regularizerLipschitz (j t omega) (x omega) (y omega))).2
    have hjm := mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hg : -(m : ℝ) * Lg * ‖x omega - y omega‖ ≤
        Core.regularizer I (x omega) - Core.regularizer I (y omega) := by
      have hh := Finset.sum_le_sum (s := Finset.univ)
        (fun k _ => (abs_le.mp (hS.regularizerLipschitz k (x omega) (y omega))).1)
      change -(m : ℝ) * Lg * ‖x omega - y omega‖ ≤
        (∑ k, I.regularizers k (x omega)) - ∑ k, I.regularizers k (y omega)
      simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_neg, neg_mul, mul_assoc] using hh
    change A omega ≤ B omega + F omega
    dsimp [A, B, F]
    linarith
  have hce : condExp M P.toMeasure A ≤ᵐ[P.toMeasure] condExp M P.toMeasure B := by
    have hmono := condExp_mono (m := M) hA (hB.add hF) hpoint
    have hadd := condExp_add hB hF M
    filter_upwards [hmono, hadd, hzero] with omega hm ha hzv
    simpa only [ha, Pi.add_apply, hzv, add_zero] using hm
  constructor
  · exact hce
  · have hint := integral_mono_ae (integrable_condExp) (integrable_condExp) hce
    rw [integral_condExp hM, integral_condExp hM] at hint
    have hscaled := mul_le_mul_of_nonneg_left hint (show 0 ≤ 2 * tau by positivity)
    have hIB : (∫ omega, B omega ∂P.toMeasure) =
        (∫ omega, Core.regularizer I (z omega) - Core.regularizer I (y omega) ∂P.toMeasure) +
        (2 * m * Lg) * (∫ omega, ‖x omega - y omega‖ ∂P.toMeasure) := by
      change (∫ omega, (Core.regularizer I (z omega) - Core.regularizer I (y omega)) +
        (2 * m * Lg) * ‖x omega - y omega‖ ∂P.toMeasure) = _
      rw [integral_add (hgz.sub' hgy) (hN.const_mul (2 * m * Lg)), integral_const_mul]
    rw [hIB] at hscaled
    dsimp [A] at hscaled
    dsimp [x, y] at hscaled
    nlinarith


lemma conditional_descent {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg tau : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (htau : 0 < tau)
    (hSamples : Core.Sampling I P tau x0 i j) (t : ℕ) (z : Ω → Core.Vec d)
    (hz : @Measurable Ω (Core.Vec d) (Core.iterateHistory I tau x0 i j t) _ z)
    (hstep : tau * L < 1 / 4) (gamma : ℝ) (hgamma : 0 < gamma)
    (hobj : Integrable (fun omega => Core.objective I (z omega)) P.toMeasure)
    (hdist0 : Integrable (fun omega => ‖Core.trajectory I tau x0 i j t omega - z omega‖ ^ 2) P.toMeasure)
    (hdist1 : Integrable (fun omega => ‖Core.trajectory I tau x0 i j (t + 1) omega - z omega‖ ^ 2) P.toMeasure) :
    ∀ᵐ omega ∂P.toMeasure,
      MeasureTheory.condExp (Core.iterateHistory I tau x0 i j t) P.toMeasure (fun omega =>
        Core.objective I (Core.trajectory I tau x0 i j (t + 1) omega) - Core.objective I (z omega) -
          (2 * tau * L * (1 + gamma)) * Core.objective I (Core.trajectory I tau x0 i j t omega) +
          (2 * tau * L * (1 + gamma)) * Core.objective I xs) omega ≤
      1 / (2 * tau) * MeasureTheory.condExp (Core.iterateHistory I tau x0 i j t) P.toMeasure
        (fun omega => ‖Core.trajectory I tau x0 i j t omega - z omega‖ ^ 2 - ‖Core.trajectory I tau x0 i j (t + 1) omega - z omega‖ ^ 2) omega + (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2 := by
  classical
  let mΩ : MeasurableSpace Ω := inferInstance
  let M := Core.iterateHistory I tau x0 i j t
  let : MeasurableSpace Ω := mΩ
  let x := Core.trajectory I tau x0 i j t
  let y := Core.trajectory I tau x0 i j (t + 1)
  have hM := (LongTails.Proofs.RipmRegularity.trajectory_adapted
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t).1
  have hxM := (LongTails.Proofs.RipmRegularity.trajectory_adapted
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t).2
  have hx : Measurable x := hxM.mono hM le_rfl
  have hy : Measurable y := LongTails.Proofs.RipmRegularity.trajectory_measurable
    I L Lg tau x0 xs sigmaSq i j hS htau hSamples.1.measurable
      (fun k => (hSamples.2 k).1) (t + 1)
  have hzA : Measurable z := hz.mono hM le_rfl
  have hx2 : MemLp x 2 P.toMeasure := LongTails.Proofs.RipmRegularity.trajectory_memLp
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t
  have hy2 : MemLp y 2 P.toMeasure := LongTails.Proofs.RipmRegularity.trajectory_memLp
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples (t + 1)
  have hdiff2 : MemLp (fun omega => x omega - z omega) 2 P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm (hx.fun_sub hzA).aestronglyMeasurable).mpr hdist0
  have hz2 : MemLp z 2 P.toMeasure := by
    simpa only [Pi.sub_def, sub_sub_cancel] using hx2.sub hdiff2
  have hgc (k : Fin m) : Continuous (I.regularizers k) :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ (hS.regularizerConvex k))
  have hreg (v : Ω → Core.Vec d) (hv : Measurable v) (hv2 : MemLp v 2 P.toMeasure)
      (k : Fin m) : Integrable (fun omega => I.regularizers k (v omega)) P.toMeasure := by
    have hn := (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hv2).norm
    apply ((integrable_const |I.regularizers k 0|).fun_add (hn.const_mul Lg)).mono'
      ((hgc k).measurable.comp hv).aestronglyMeasurable
    filter_upwards [] with omega
    have hl := hS.regularizerLipschitz k (v omega) 0
    rw [sub_zero] at hl
    have ha := abs_add_le (I.regularizers k (v omega) - I.regularizers k 0)
      (I.regularizers k 0)
    rw [sub_add_cancel] at ha
    change |I.regularizers k (v omega)| ≤ _
    linarith
  have hsum (v : Ω → Core.Vec d)
      (hv : ∀ k, Integrable (fun omega => I.regularizers k (v omega)) P.toMeasure) :
      Integrable (fun omega => Core.regularizer I (v omega)) P.toMeasure := by
    change Integrable (fun omega => ∑ k, I.regularizers k (v omega)) P.toMeasure
    exact integrable_finsetSum Finset.univ (fun k _ => hv k)
  have hgx := hsum x (hreg x hx hx2)
  have hgy := hsum y (hreg y hy hy2)
  have hgz := hsum z (hreg z hzA hz2)
  have hhx : Integrable (fun omega => Core.objective I (x omega)) P.toMeasure := LongTails.Proofs.RipmRegularity.objective_integrable
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t
  have hhy : Integrable (fun omega => Core.objective I (y omega)) P.toMeasure := LongTails.Proofs.RipmRegularity.objective_integrable
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples (t + 1)
  have hfx : Integrable (fun omega => I.average (x omega)) P.toMeasure := by
    have h := hhx.sub' hgx
    change Integrable (fun omega =>
      (I.average (x omega) + Core.regularizer I (x omega)) -
        Core.regularizer I (x omega)) P.toMeasure at h
    simpa only [add_sub_cancel_right] using h
  have hfy : Integrable (fun omega => I.average (y omega)) P.toMeasure := by
    have h := hhy.sub' hgy
    change Integrable (fun omega =>
      (I.average (y omega) + Core.regularizer I (y omega)) -
        Core.regularizer I (y omega)) P.toMeasure at h
    simpa only [add_sub_cancel_right] using h
  have hfz : Integrable (fun omega => I.average (z omega)) P.toMeasure := by
    have h := hobj.sub' hgz
    change Integrable (fun omega =>
      (I.average (z omega) + Core.regularizer I (z omega)) -
        Core.regularizer I (z omega)) P.toMeasure at h
    simpa only [add_sub_cancel_right] using h
  have hrefz := LongTails.Proofs.RipmRegularity.reference_integrable
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t z hz hz2
  have hrefx := LongTails.Proofs.RipmRegularity.reference_integrable
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t x hxM hx2
  have hfc : Continuous I.average := continuous_iff_continuousAt.mpr
    (fun a => (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient
      I L Lg xs sigmaSq hS a).continuousAt)
  have hcomponent := LongTails.Proofs.RipmRegularity.component_measurable I L Lg xs sigmaSq hS
  have hmean (v : Ω → Core.Vec d) (hv : @Measurable Ω (Core.Vec d) M _ v)
      (hvI : Integrable (fun omega => I.component (i t omega) (v omega)) P.toMeasure)
      (hfI : Integrable (fun omega => I.average (v omega)) P.toMeasure) :
      condExp M P.toMeasure (fun omega => I.component (i t omega) (v omega)) =ᵐ[P.toMeasure]
        (fun omega => I.average (v omega)) := by
    have hAI : Integrable (fun omega => ∫ a, I.component a (v omega) ∂I.law.toMeasure)
        P.toMeasure := by simpa only [← hS.averageEq] using hfI
    have hc := LongTails.Proofs.RipmConditional.conditional_kernel P I.law M hM
      (i t) v (fun a s => I.component s a) (hSamples.1.measurable t) hv
      (hcomponent.comp measurable_swap) (hSamples.2 t).2.1
      (hSamples.1.marginal t) hvI hAI
    simpa only [← hS.averageEq] using hc
  have hsub {f g : Ω → ℝ} (hf : Integrable f P.toMeasure) (hg : Integrable g P.toMeasure) :
      condExp M P.toMeasure (fun omega => f omega - g omega) =ᵐ[P.toMeasure]
        (fun omega => condExp M P.toMeasure f omega - condExp M P.toMeasure g omega) := by
    simpa only [Pi.sub_def] using condExp_sub hf hg M
  have hadd {f g : Ω → ℝ} (hf : Integrable f P.toMeasure) (hg : Integrable g P.toMeasure) :
      condExp M P.toMeasure (fun omega => f omega + g omega) =ᵐ[P.toMeasure]
        (fun omega => condExp M P.toMeasure f omega + condExp M P.toMeasure g omega) := by
    simpa only [Pi.add_def] using condExp_add hf hg M
  let F := fun omega => (I.component (i t omega) (z omega) - I.component (i t omega) (x omega)) -
    (I.average (z omega) - I.average (x omega))
  have hFI : Integrable F P.toMeasure :=
    (hrefz.2.2.2.1.sub' hrefx.2.2.2.1).sub' (hfz.sub' hfx)
  have hFzero : condExp M P.toMeasure F =ᵐ[P.toMeasure] (fun _ => 0) := by
    have hzmean := hmean z hz hrefz.2.2.2.1 hfz
    have hxmean := hmean x hxM hrefx.2.2.2.1 hfx
    have h1 := hsub hrefz.2.2.2.1 hrefx.2.2.2.1
    have h2 := hsub hfz hfx
    have h3 := hsub (hrefz.2.2.2.1.sub' hrefx.2.2.2.1) (hfz.sub' hfx)
    have hzf := condExp_of_stronglyMeasurable hM (hfc.measurable.comp hz).stronglyMeasurable hfz
    have hxf := condExp_of_stronglyMeasurable hM (hfc.measurable.comp hxM).stronglyMeasurable hfx
    simp only [Function.comp_def] at hzf hxf
    filter_upwards [hzmean, hxmean, h1, h2, h3] with omega hzv hxv h1v h2v h3v
    change condExp M P.toMeasure
      (fun omega => (I.component (i t omega) (z omega) - I.component (i t omega) (x omega)) -
       (I.average (z omega) - I.average (x omega))) omega = 0
    rw [h3v, h1v, h2v, hzv, hxv, hzf, hxf]
    change (I.average (z omega) - I.average (x omega)) -
      (I.average (z omega) - I.average (x omega)) = 0
    exact sub_self _
  let B := fun omega => (m : ℝ) *
    (I.regularizers (j t omega) (z omega) - I.regularizers (j t omega) (y omega))
  let Bb := fun omega => Core.regularizer I (z omega) - Core.regularizer I (y omega) +
    2 * m * Lg * ‖x omega - y omega‖
  have hN := (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hx2.sub hy2)).norm
  have hBI : Integrable B P.toMeasure :=
    (hrefz.2.2.2.2.1.sub' hrefz.2.2.2.2.2).const_mul (m : ℝ)
  have hBbI : Integrable Bb P.toMeasure := (hgz.sub' hgy).fun_add (hN.const_mul (2 * m * Lg))
  have hBbound := (prox_decouple I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t z
    hz (hreg z hzA hz2)).1
  have hBnonpos : condExp M P.toMeasure (fun omega => B omega - Bb omega) ≤ᵐ[P.toMeasure] (fun _ => 0) := by
    have he := hsub hBI hBbI
    filter_upwards [he, hBbound] with omega he hb
    rw [he]
    exact sub_nonpos.mpr hb
  have hml : LipschitzWith (⟨L, hS.smoothPos.le⟩ : NNReal) (Core.meanGradient I) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [dist_eq_norm]
    change ‖Core.meanGradient I a - Core.meanGradient I b‖ ≤ L * ‖a - b‖
    exact LongTails.Proofs.RipmSmoothGeometry.mean_lipschitz I L Lg xs sigmaSq hS a b
  have hm2 : MemLp (fun omega => Core.meanGradient I (x omega)) 2 P.toMeasure := by
    apply ((hx2.norm.const_mul L).add (memLp_const ‖Core.meanGradient I 0‖)).mono'
      (hml.continuous.measurable.comp hx).aestronglyMeasurable
    filter_upwards [] with omega
    have hl := LongTails.Proofs.RipmSmoothGeometry.mean_lipschitz I L Lg xs sigmaSq hS (x omega) 0
    rw [sub_zero] at hl
    have hn := norm_add_le (Core.meanGradient I (x omega) - Core.meanGradient I 0)
      (Core.meanGradient I 0)
    rw [sub_add_cancel] at hn
    exact hn.trans (add_le_add hl le_rfl)
  have hgrad2 := LongTails.Proofs.RipmRegularity.gradient_memLp
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t
  let E := fun omega => ‖I.grad (i t omega) (x omega) - Core.meanGradient I (x omega)‖ ^ 2
  let V := fun omega => 2 * L * (1 + gamma) *
    (Core.objective I (x omega) - Core.objective I xs) + (1 + 1 / gamma) * sigmaSq
  have hEI : Integrable E P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm (hgrad2.sub hm2).aestronglyMeasurable).mp (hgrad2.sub hm2)
  have hVI : Integrable V P.toMeasure :=
    ((hhx.sub' (integrable_const (Core.objective I xs))).const_mul
      (2 * L * (1 + gamma))).fun_add (integrable_const ((1 + 1 / gamma) * sigmaSq))
  have hVM : @Measurable Ω ℝ M _ V := by
    have hc : Continuous (Core.objective I) := hfc.add
      (continuous_finsetSum Finset.univ (fun k _ => hgc k))
    exact Measurable.fun_add
      ((measurable_const_mul (2 * L * (1 + gamma))).comp
        ((hc.measurable.comp hxM).fun_sub measurable_const)) measurable_const
  let k := fun (a : Core.Vec d) (s : I.Sample) => ‖I.grad s a - Core.meanGradient I a‖ ^ 2
  have hk : Measurable (Function.uncurry k) :=
    (((hS.gradientMeasurable.comp measurable_swap).fun_sub
      (hml.continuous.measurable.comp measurable_fst)).norm).pow_const 2
  have havgM : Measurable (fun omega => ∫ s, k (x omega) s ∂I.law.toMeasure) :=
    hk.stronglyMeasurable.integral_prod_right.measurable.comp hx
  have havgBound (omega : Ω) :
      (∫ s, k (x omega) s ∂I.law.toMeasure) ≤ V omega :=
    (LongTails.Proofs.RipmVariance.variance_centered I L Lg xs sigmaSq hS (x omega)).2.trans
      (LongTails.Proofs.RipmVariance.variance_transfer I L Lg xs sigmaSq hS (x omega) gamma hgamma).2
  have havgI : Integrable (fun omega => ∫ s, k (x omega) s ∂I.law.toMeasure) P.toMeasure := by
    apply hVI.mono' havgM.aestronglyMeasurable
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun s => sq_nonneg _))]
    exact havgBound omega
  have hEbound : condExp M P.toMeasure E ≤ᵐ[P.toMeasure] V := by
    have he := LongTails.Proofs.RipmConditional.conditional_kernel P I.law M hM
      (i t) x k (hSamples.1.measurable t) hxM hk (hSamples.2 t).2.1
      (hSamples.1.marginal t) hEI havgI
    filter_upwards [he] with omega he
    rw [he]
    exact havgBound omega
  have hEnonpos : condExp M P.toMeasure (fun omega => E omega - V omega) ≤ᵐ[P.toMeasure] (fun _ => 0) := by
    have he := hsub hEI hVI
    have hv := condExp_of_stronglyMeasurable hM hVM.stronglyMeasurable hVI
    filter_upwards [he, hEbound] with omega he hb
    rw [he, hv]
    exact sub_nonpos.mpr hb
  let H := fun omega => Core.objective I (y omega) - Core.objective I (z omega) -
    (2 * tau * L * (1 + gamma)) * Core.objective I (x omega) +
    (2 * tau * L * (1 + gamma)) * Core.objective I xs
  let J := fun omega => ‖x omega - z omega‖ ^ 2 - ‖y omega - z omega‖ ^ 2
  let c := 2 * tau ^ 2 * (1 + 1 / gamma) * sigmaSq + 16 * tau ^ 2 * (m : ℝ) ^ 2 * Lg ^ 2
  have hHI : Integrable H P.toMeasure :=
    ((hhy.sub' hobj).sub' (hhx.const_mul (2 * tau * L * (1 + gamma)))).fun_add (integrable_const _)
  have hJI : Integrable J P.toMeasure := hdist0.sub' hdist1
  let D := 3 / (4 * tau) - L
  have hD : 0 < D := by
    dsimp [D]
    have hdiv : L < 1 / (4 * tau) := by
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith [hstep]
    have hpos : 0 < 1 / (4 * tau) := by positivity
    have hthree : 3 / (4 * tau) = 3 * (1 / (4 * tau)) := by ring
    linarith only [hdiv, hpos, hthree]
  have hcoef : tau * D + tau * L - 1 = -(1 / 4 : ℝ) := by
    dsimp [D]
    field_simp
    ring
  have hratio : tau / D ≤ 2 * tau ^ 2 := by
    apply (div_le_iff₀ hD).mpr
    have hprod : tau * D = 3 / 4 - tau * L := by
      dsimp [D]
      field_simp
    have hp := congrArg (fun a : ℝ => 2 * tau * a) hprod
    have hs := mul_lt_mul_of_pos_left hstep htau
    nlinarith
  have hpoint : (fun omega => 2 * tau * H omega - J omega) ≤ᵐ[P.toMeasure]
      (fun omega => 2 * tau * F omega + 2 * tau * (B omega - Bb omega) +
        2 * tau ^ 2 * (E omega - V omega) + c) := by
    filter_upwards [] with omega
    let q := fun a => (m : ℝ) * I.regularizers (j t omega) a
    have hm : 0 < (m : ℝ) := by exact_mod_cast hS.countPos
    have hq : ConvexOn ℝ Set.univ q := by
      refine ⟨convex_univ, ?_⟩
      intro a ha b hb s u hs hu hsu
      have hh := (hS.regularizerConvex (j t omega)).2 ha hb hs hu hsu
      simpa only [q, smul_eq_mul, mul_add, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hh hm.le
    have hqLip (a b : Core.Vec d) : |q a - q b| ≤ ((m : ℝ) * Lg) * ‖a - b‖ := by
      dsimp [q]
      rw [← mul_sub, abs_mul, abs_of_pos hm]
      exact (mul_le_mul_of_nonneg_left (hS.regularizerLipschitz (j t omega) a b) hm.le).trans_eq
        (mul_assoc _ _ _).symm
    let v := x omega - tau • I.grad (i t omega) (x omega)
    have hmin := LongTails.Proofs.RipmProxGeometry.prox_minimizes
      (I.regularizers (j t omega)) (tau * m) Lg (mul_pos htau hm) hS.regularizerNonneg
      (hS.regularizerConvex (j t omega)) (hS.regularizerLipschitz (j t omega)) v
    have hscale : Core.prox (I.regularizers (j t omega)) (tau * m) v = Core.prox q tau v := by
      apply LongTails.Proofs.RipmProxGeometry.prox_unique q tau ((m : ℝ) * Lg) htau
        (mul_nonneg hm.le hS.regularizerNonneg) hq hqLip v
      have he : Core.proxObjective q tau v =
          Core.proxObjective (I.regularizers (j t omega)) (tau * m) v := by
        funext a
        change tau * ((m : ℝ) * I.regularizers (j t omega) a) + ‖a - v‖ ^ 2 / 2 =
          (tau * m) * I.regularizers (j t omega) a + ‖a - v‖ ^ 2 / 2
        ring
      rw [he]
      exact hmin
    have hydef : y omega = Core.prox (I.regularizers (j t omega)) (tau * m) v := rfl
    have hs := one_step q (I.component (i t omega)) I.average
      (I.grad (i t omega)) (Core.meanGradient I) L ((m : ℝ) * Lg) tau D
      hS.smoothPos (mul_nonneg hm.le hS.regularizerNonneg) htau hD hq hqLip
      (hS.componentConvex (i t omega)) (hS.componentGradient (i t omega))
      (hS.componentSmooth (i t omega))
      (LongTails.Proofs.RipmSmoothGeometry.mean_hasGradient I L Lg xs sigmaSq hS)
      (LongTails.Proofs.RipmSmoothGeometry.mean_lipschitz I L Lg xs sigmaSq hS)
      (x omega) (z omega)
    change ‖Core.prox q tau v - z omega‖ ^ 2 - ‖x omega - z omega‖ ^ 2 ≤ _ at hs
    rw [← hscale, ← hydef, hcoef] at hs
    have hE := mul_le_mul_of_nonneg_right hratio
      (sq_nonneg ‖I.grad (i t omega) (x omega) - Core.meanGradient I (x omega)‖)
    have hcomplete := sq_nonneg (‖x omega - y omega‖ / 2 - 4 * tau * m * Lg)
    dsimp [q] at hs
    dsimp [H, J, F, B, Bb, E, V, c]
    change _ ≤ _ at hs
    delta Core.objective
    nlinarith only [hs, hE, hcomplete]
  have hmul (a : ℝ) (f : Ω → ℝ) :
      condExp M P.toMeasure (fun omega => a * f omega) =ᵐ[P.toMeasure]
        (fun omega => a * condExp M P.toMeasure f omega) := by
    simpa only [Pi.smul_def, smul_eq_mul] using condExp_smul a f M
  have hleft : condExp M P.toMeasure (fun omega => 2 * tau * H omega - J omega) =ᵐ[P.toMeasure]
      (fun omega => 2 * tau * condExp M P.toMeasure H omega - condExp M P.toMeasure J omega) := by
    have hs := hsub (hHI.const_mul (2 * tau)) hJI
    have hm := hmul (2 * tau) H
    filter_upwards [hs, hm] with omega hs hm
    rw [hs, hm]
  have hr1 := hFI.const_mul (2 * tau)
  have hr2 := (hBI.sub' hBbI).const_mul (2 * tau)
  have hr3 := (hEI.sub' hVI).const_mul (2 * tau ^ 2)
  have hright : condExp M P.toMeasure
      (fun omega => 2 * tau * F omega + 2 * tau * (B omega - Bb omega) +
        2 * tau ^ 2 * (E omega - V omega) + c) ≤ᵐ[P.toMeasure] (fun _ => c) := by
    have h1 := hadd hr1 hr2
    have h2 := hadd (hr1.fun_add hr2) hr3
    have h3 := hadd ((hr1.fun_add hr2).fun_add hr3) (integrable_const c)
    have hm1 := hmul (2 * tau) F
    have hm2 := hmul (2 * tau) (fun omega => B omega - Bb omega)
    have hm3 := hmul (2 * tau ^ 2) (fun omega => E omega - V omega)
    have hc := condExp_of_stronglyMeasurable hM stronglyMeasurable_const
      (integrable_const (μ := P.toMeasure) c)
    filter_upwards [h1, h2, h3, hm1, hm2, hm3, hFzero, hBnonpos, hEnonpos]
      with omega h1 h2 h3 hm1 hm2 hm3 hf hb he
    rw [h3, h2, h1, hm1, hm2, hm3, hc, hf]
    simp only [mul_zero, zero_add]
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * tau by positivity)
    have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * tau ^ 2 by positivity)
    linarith
  have hmono := condExp_mono (m := M) ((hHI.const_mul (2 * tau)).sub' hJI)
    (((hr1.fun_add hr2).fun_add hr3).fun_add (integrable_const c)) hpoint
  filter_upwards [hmono, hleft, hright] with omega hm hl hr
  rw [hl] at hm
  have hbound : 2 * tau * condExp M P.toMeasure H omega ≤
      condExp M P.toMeasure J omega + c := by linarith
  have hfinal := (le_div_iff₀ (show 0 < 2 * tau by positivity)).mpr
    (show condExp M P.toMeasure H omega * (2 * tau) ≤
      condExp M P.toMeasure J omega + c by nlinarith [hbound])
  change condExp M P.toMeasure H omega ≤
    1 / (2 * tau) * condExp M P.toMeasure J omega +
      (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2
  convert hfinal using 1
  dsimp [c]
  field_simp
  ring


lemma descent {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem d m) (P : ProbabilityMeasure Ω) (L Lg tau : ℝ)
    (x0 xs : Core.Vec d) (sigmaSq : ℝ)
    (i : ℕ → Ω → I.Sample) (j : ℕ → Ω → Fin m)
    (hS : Core.SourceAssumptions I L Lg xs sigmaSq) (htau : 0 < tau)
    (hSamples : Core.Sampling I P tau x0 i j) (t : ℕ) (z : Ω → Core.Vec d)
    (hz : @Measurable Ω (Core.Vec d) (Core.iterateHistory I tau x0 i j t) _ z)
    (hstep : tau * L < 1 / 4) (gamma : ℝ) (hgamma : 0 < gamma)
    (hobj : Integrable (fun omega => Core.objective I (z omega)) P.toMeasure)
    (hdist0 : Integrable (fun omega => ‖Core.trajectory I tau x0 i j t omega - z omega‖ ^ 2) P.toMeasure)
    (hdist1 : Integrable (fun omega => ‖Core.trajectory I tau x0 i j (t + 1) omega - z omega‖ ^ 2) P.toMeasure) :
    (∫ omega, Core.objective I (Core.trajectory I tau x0 i j (t + 1) omega) - Core.objective I (z omega) -
          (2 * tau * L * (1 + gamma)) * Core.objective I (Core.trajectory I tau x0 i j t omega) +
          (2 * tau * L * (1 + gamma)) * Core.objective I xs ∂P.toMeasure) ≤
      1 / (2 * tau) * (∫ omega, ‖Core.trajectory I tau x0 i j t omega - z omega‖ ^ 2 - ‖Core.trajectory I tau x0 i j (t + 1) omega - z omega‖ ^ 2 ∂P.toMeasure) + (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2 := by
  let mΩ : MeasurableSpace Ω := inferInstance
  let M := Core.iterateHistory I tau x0 i j t
  let : MeasurableSpace Ω := mΩ
  let f := fun omega =>
    Core.objective I (Core.trajectory I tau x0 i j (t + 1) omega) -
      Core.objective I (z omega) -
      (2 * tau * L * (1 + gamma)) * Core.objective I (Core.trajectory I tau x0 i j t omega) +
      (2 * tau * L * (1 + gamma)) * Core.objective I xs
  let g := fun omega => ‖Core.trajectory I tau x0 i j t omega - z omega‖ ^ 2 -
    ‖Core.trajectory I tau x0 i j (t + 1) omega - z omega‖ ^ 2
  let v := (1 + 1 / gamma) * sigmaSq * tau + 8 * tau * (m : ℝ) ^ 2 * Lg ^ 2
  have hM := (LongTails.Proofs.RipmRegularity.trajectory_adapted
    I P L Lg tau x0 xs sigmaSq i j hS htau hSamples t).1
  have hc := conditional_descent I P L Lg tau x0 xs sigmaSq i j hS htau hSamples
    t z hz hstep gamma hgamma hobj hdist0 hdist1
  have hf : Integrable (MeasureTheory.condExp M P.toMeasure f) P.toMeasure :=
    integrable_condExp
  have hg : Integrable (MeasureTheory.condExp M P.toMeasure g) P.toMeasure :=
    integrable_condExp
  have hc' : MeasureTheory.condExp M P.toMeasure f ≤ᵐ[P.toMeasure]
      (fun omega => 1 / (2 * tau) * MeasureTheory.condExp M P.toMeasure g omega + v) := by
    filter_upwards [hc] with omega h
    simpa only [f, g, M, v, add_assoc] using h
  have hb := integral_mono_ae hf
    ((hg.const_mul (1 / (2 * tau))).fun_add (integrable_const v)) hc'
  rw [integral_add (hg.const_mul (1 / (2 * tau))) (integrable_const v),
    integral_const_mul, integral_condExp hM, integral_condExp hM, integral_const] at hb
  simpa only [f, g, v, probReal_univ, one_smul, add_assoc] using hb


end

end LongTails.Proofs.RipmDescent
