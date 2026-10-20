import LongTails.Proofs.RiverValleyNoise
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

noncomputable def Vfun (K : Submodule ℝ E) [K.HasOrthogonalProjection] (h : E → ℝ) (gh : E → E)
    (φ : E → E) (Jφ : E → E →L[ℝ] E) (lam : ℝ) (x : E) : ℝ :=
  h (Kᗮ.starProjection x) + ⟪mr K gh Jφ (Kᗮ.starProjection x), wv K φ x⟫ + lam * ‖wv K φ x‖ ^ 2

noncomputable def Yv (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E) (φ : E → E)
    (Jφ : E → E →L[ℝ] E) (A : E →L[ℝ] E) (η : ℝ) (x : E) : E :=
  wv K φ x - η • (A (wv K φ x) + Jr K Jφ (Kᗮ.starProjection x)
    (ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x)))) +
    η • Jr K Jφ (Kᗮ.starProjection x) (ar K gh (Kᗮ.starProjection x))

noncomputable def d0v (K : Submodule ℝ E) [K.HasOrthogonalProjection] (gh : E → E) (φ : E → E)
    (Jφ : E → E →L[ℝ] E) (A : E →L[ℝ] E) (η : ℝ) (x : E) : E :=
  -(η • (ar K gh (Kᗮ.starProjection x) -
    ContinuousLinearMap.adjoint (Jr K Jφ (Kᗮ.starProjection x)) (A (wv K φ x))))


namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma h_lip (y y' : E) : |h y - h y'| ≤ G * ‖y - y'‖ := by
  have hg : ∀ z, HasFDerivAt h ((InnerProductSpace.toDual ℝ E (gh z)) : E →L[ℝ] ℝ) z :=
    fun z => (H.hgh z).hasFDerivAt
  have hdir : ∀ z, ‖((InnerProductSpace.toDual ℝ E (gh z)) : E →L[ℝ] ℝ) (y - y')‖ ≤
      G * ‖y - y'‖ := by
    intro z
    rw [InnerProductSpace.toDual_apply_apply, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (H.gh_bdd z)
      (norm_nonneg _))
  have := diff_le_of_dir hg y' (y - y') hdir
  rwa [add_sub_cancel, Real.norm_eq_abs] at this

omit [MeasurableSpace E] [BorelSpace E] in
lemma h_cont : Continuous h := continuous_iff_continuousAt.mpr fun y =>
  (H.hgh y).hasFDerivAt.continuousAt

omit [MeasurableSpace E] [BorelSpace E] in
lemma Vfun_cont (lam : ℝ) : Continuous (Vfun K h gh φ Jφ lam) := by
  have hQ : Continuous (Kᗮ.starProjection : E → E) := Kᗮ.starProjection.continuous
  have hw : Continuous (wv K φ) :=
    K.starProjection.continuous.sub (H.φ_cont.comp hQ)
  exact ((H.h_cont.comp hQ).add ((H.mr_cont.comp hQ).inner hw)).add
    (continuous_const.mul (hw.norm.pow 2))

set_option maxHeartbeats 1600000 in
lemma step_bound {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (hσu : 0 ≤ σu)
    (hσv : 0 ≤ σv) (x : E) (η lam : ℝ) (hlam : 0 ≤ lam) :
    let y := Kᗮ.starProjection x
    let a := ar K gh y
    let J := Jr K Jφ y
    let m := mr K gh Jφ y
    let d0 := d0v K gh φ Jφ A η x
    let Y := Yv K gh φ Jφ A η x
    let Γ := Luv / μ
    let Lm := Γ * Lh + LJ * G + 2 * Γ ^ 2 * LJ * G
    let c2 := G * ρJ + LJ * Lh + Γ * ρh + Γ * G * (2 * Γ * ρJ + LJ ^ 2) + 2 * Γ * LJ * Lm
    let Cd := Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2
    let Cξ := 2 * lam * η ^ 2
    let r0 := φ (y + d0) - φ y - Jφ y d0
    Integrable (fun ω => Vfun K h gh φ Jφ lam (x - η • (gradF K gh φ Jφ A x + ζ ω))) p ∧
    ∫ ω, Vfun K h gh φ Jφ lam (x - η • (gradF K gh φ Jφ A x + ζ ω)) ∂p ≤
      Vfun K h gh φ Jφ lam x - η * (‖a‖ ^ 2 - ⟪m, J a⟫) + lam * (‖Y‖ ^ 2 - ‖wv K φ x‖ ^ 2) +
        (‖m‖ + 2 * lam * ‖Y‖) * (‖r0‖ + LJ * η ^ 2 * σu ^ 2) +
        ‖Y‖ * (Lm * ‖d0‖ + c2 * η ^ 2 * σu ^ 2) +
        Cd * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * σu ^ 2) + Cξ * (2 * σv ^ 2 + 2 * Γ ^ 2 * σu ^ 2) +
        Lm * η ^ 2 * (σu * σv + Γ * σu ^ 2) := by
  intro y a J m d0 Y Γ Lm c2 Cd Cξ r0
  set w := wv K φ x
  set Qz : Ω → E := fun ω => Kᗮ.starProjection (ζ ω)
  set Pz : Ω → E := fun ω => K.starProjection (ζ ω)
  set e : Ω → E := fun ω => -η • Qz ω
  set dd : Ω → E := fun ω => d0 + e ω
  set x' : Ω → E := fun ω => x - η • (gradF K gh φ Jφ A x + ζ ω)
  set r : Ω → E := fun ω => φ (y + dd ω) - φ y - Jφ y (dd ω)
  set ξ : Ω → E := fun ω => Pz ω - J (Qz ω)
  have hΓ : 0 ≤ Γ := div_nonneg H.Luv_nn H.μpos.le
  have hLm : 0 ≤ Lm := by have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; positivity
  have hCd : 0 ≤ Cd := by have := H.Lh_nn; positivity
  have hCξ : 0 ≤ Cξ := by positivity
  have hJ : ‖J‖ ≤ Γ := H.Jr_norm y
  -- geometry of the step
  have hamem : a ∈ Kᗮ := Q_mem _
  have hvmem : ContinuousLinearMap.adjoint J (A w) ∈ Kᗮ := adjJ_mem Jφ _ _
  have hd0mem : d0 ∈ Kᗮ := by
    show -(η • (a - ContinuousLinearMap.adjoint J (A w))) ∈ Kᗮ
    exact Kᗮ.neg_mem (Kᗮ.smul_mem _ (Kᗮ.sub_mem hamem hvmem))
  have hddmem : ∀ ω, dd ω ∈ Kᗮ := fun ω =>
    Kᗮ.add_mem hd0mem (Kᗮ.smul_mem _ (Q_mem _))
  have hQx' : ∀ ω, Kᗮ.starProjection (x' ω) - Kᗮ.starProjection x = dd ω := by
    intro ω
    rw [H.Q_step x η (ζ ω)]
    simp only [dd, d0, d0v, e, Qz, smul_add, smul_sub, neg_smul, neg_sub]
    abel
  have hw' : ∀ ω, wv K φ (x' ω) = Y - η • ξ ω - r ω := by
    intro ω
    rw [H.w_path x η (ζ ω) (x' ω) (dd ω) rfl (hQx' ω).symm]
    rfl
  have hyd : ∀ ω, Kᗮ.starProjection (x' ω) = y + dd ω := fun ω => by
    rw [← hQx' ω]; abel
  have hpot := fun ω => H.potential_path x η (ζ ω) (x' ω) (dd ω) rfl (hQx' ω).symm
  have hr2 : ∀ ω, ‖r ω‖ ≤ 2 * Γ * ‖dd ω‖ := fun ω => H.φ_river y (dd ω) (hddmem ω)
  have hml : ∀ ω, ‖mr K gh Jφ (y + dd ω) - m‖ ≤ Lm * ‖dd ω‖ := fun ω => by
    have := H.mr_lip (y + dd ω) y; rwa [add_sub_cancel_left] at this
  have hdd2 : ∀ ω, ‖dd ω‖ ^ 2 ≤ 2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2 := by
    intro ω
    have h1 := norm_add_le d0 (e ω)
    have h2 : ‖e ω‖ = |η| * ‖Qz ω‖ := by simp [e, norm_smul]
    have : ‖dd ω‖ ≤ ‖d0‖ + |η| * ‖Qz ω‖ := by rw [← h2]; exact h1
    have hsq : (‖d0‖ + |η| * ‖Qz ω‖) ^ 2 ≤ 2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * ‖Qz ω‖ ^ 2 := by
      nlinarith [sq_nonneg (‖d0‖ - |η| * ‖Qz ω‖), sq_abs η]
    exact (pow_le_pow_left₀ (norm_nonneg _) this 2).trans hsq
  have hξ2 : ∀ ω, ‖ξ ω‖ ^ 2 ≤ 2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2 := by
    intro ω
    have h1 : ‖J (Qz ω)‖ ≤ Γ * ‖Qz ω‖ :=
      (J.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    have : ‖ξ ω‖ ≤ ‖Pz ω‖ + Γ * ‖Qz ω‖ := (norm_sub_le _ _).trans (add_le_add le_rfl h1)
    have hsq : (‖Pz ω‖ + Γ * ‖Qz ω‖) ^ 2 ≤ 2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Pz ω‖ - Γ * ‖Qz ω‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) this 2).trans hsq
  -- pathwise bound
  set C0 := Vfun K h gh φ Jφ lam x - η * (‖a‖ ^ 2 - ⟪m, J a⟫) + lam * (‖Y‖ ^ 2 - ‖w‖ ^ 2) +
    Cd * (2 * ‖d0‖ ^ 2)
  set m0 := mr K gh Jφ (y + d0)
  set U : Ω → ℝ := fun ω => C0 - (⟪η • a, Qz ω⟫ +
    ⟪η • m + (2 * lam * η) • Y + η • (m0 - m), ξ ω⟫) -
    ⟪m + (2 * lam) • Y, r ω⟫ + ⟪mr K gh Jφ (y + dd ω) - m, Y⟫ +
    (Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) + Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
      Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2))
  have hpath : ∀ ω, Vfun K h gh φ Jφ lam (x' ω) ≤ U ω := by
    intro ω
    have hp := hpot ω
    have hwω := hw' ω
    have hyω := hyd ω
    have hrω := hr2 ω
    have hmω := hml ω
    have hdω := hdd2 ω
    have hξω := hξ2 ω
    set W' := wv K φ (x' ω)
    have hw2 : ‖W'‖ ^ 2 ≤ ‖Y‖ ^ 2 - 2 * η * ⟪Y, ξ ω⟫ - 2 * ⟪Y, r ω⟫ + 2 * η ^ 2 * ‖ξ ω‖ ^ 2 +
        2 * ‖r ω‖ ^ 2 := by
      have e1 : W' = Y - (η • ξ ω + r ω) := by rw [hwω]; abel
      rw [e1, norm_sub_sq_real, inner_add_right, inner_smul_right]
      have := norm_add_le (η • ξ ω) (r ω)
      have h2 : ‖η • ξ ω + r ω‖ ^ 2 ≤ 2 * η ^ 2 * ‖ξ ω‖ ^ 2 + 2 * ‖r ω‖ ^ 2 := by
        have h3 : ‖η • ξ ω‖ = |η| * ‖ξ ω‖ := norm_smul _ _
        have h4 : (‖η • ξ ω‖ + ‖r ω‖) ^ 2 ≤ 2 * η ^ 2 * ‖ξ ω‖ ^ 2 + 2 * ‖r ω‖ ^ 2 := by
          rw [h3]; nlinarith [sq_nonneg (|η| * ‖ξ ω‖ - ‖r ω‖), sq_abs η]
        exact (pow_le_pow_left₀ (norm_nonneg _) this 2).trans h4
      linarith
    have hcross : ⟪mr K gh Jφ (y + dd ω) - m, W'⟫ ≤ ⟪mr K gh Jφ (y + dd ω) - m, Y⟫ -
        η * ⟪m0 - m, ξ ω⟫ + Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2) +
        2 * Γ * Lm * ‖dd ω‖ ^ 2 := by
      have e1 : W' = Y - η • ξ ω - r ω := hwω
      have hsplit : mr K gh Jφ (y + dd ω) - m = (mr K gh Jφ (y + dd ω) - m0) + (m0 - m) := by
        abel
      have hξs : ⟪mr K gh Jφ (y + dd ω) - m, ξ ω⟫ =
          ⟪mr K gh Jφ (y + dd ω) - m0, ξ ω⟫ + ⟪m0 - m, ξ ω⟫ := by
        rw [hsplit, inner_add_left]
      rw [e1, inner_sub_right, inner_sub_right, inner_smul_right, hξs]
      have hl1 : ‖mr K gh Jφ (y + dd ω) - m0‖ ≤ Lm * (|η| * ‖Qz ω‖) := by
        have := H.mr_lip (y + dd ω) (y + d0)
        have hdiff : y + dd ω - (y + d0) = e ω := by simp only [dd]; abel
        rw [hdiff] at this
        refine this.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hLm)
        rw [show e ω = -η • Qz ω from rfl, norm_smul, Real.norm_eq_abs, abs_neg]
      have hJq : ‖J (Qz ω)‖ ≤ Γ * ‖Qz ω‖ :=
        (J.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
      have hξn : ‖ξ ω‖ ≤ ‖Pz ω‖ + Γ * ‖Qz ω‖ := (norm_sub_le _ _).trans (add_le_add le_rfl hJq)
      have h1 : -(η * ⟪mr K gh Jφ (y + dd ω) - m0, ξ ω⟫) ≤
          Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2) := by
        have h2 : -(η * ⟪mr K gh Jφ (y + dd ω) - m0, ξ ω⟫) ≤
            |η| * (‖mr K gh Jφ (y + dd ω) - m0‖ * ‖ξ ω‖) := by
          have := abs_real_inner_le_norm (mr K gh Jφ (y + dd ω) - m0) (ξ ω)
          have h3 := mul_le_mul_of_nonneg_left this (abs_nonneg η)
          have h4 : -(η * ⟪mr K gh Jφ (y + dd ω) - m0, ξ ω⟫) ≤
              |η| * |⟪mr K gh Jφ (y + dd ω) - m0, ξ ω⟫| := by
            rw [← abs_mul]; exact neg_le_abs _
          linarith
        have h5 : ‖mr K gh Jφ (y + dd ω) - m0‖ * ‖ξ ω‖ ≤
            Lm * (|η| * ‖Qz ω‖) * (‖Pz ω‖ + Γ * ‖Qz ω‖) :=
          mul_le_mul hl1 hξn (norm_nonneg _) (by positivity)
        have h6 := mul_le_mul_of_nonneg_left h5 (abs_nonneg η)
        have hab : |η| * (Lm * (|η| * ‖Qz ω‖) * (‖Pz ω‖ + Γ * ‖Qz ω‖)) =
            Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2) := by
          have : |η| * |η| = η ^ 2 := by rw [← sq, sq_abs]
          linear_combination (Lm * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2)) * this
        linarith
      have h7 : -⟪mr K gh Jφ (y + dd ω) - m, r ω⟫ ≤ 2 * Γ * Lm * ‖dd ω‖ ^ 2 := by
        have := real_inner_le_norm (-(mr K gh Jφ (y + dd ω) - m)) (r ω)
        rw [inner_neg_left, norm_neg] at this
        have h8 := mul_le_mul hmω hrω (norm_nonneg _) (by positivity)
        nlinarith
      linarith
    have hr2sq : ‖r ω‖ ^ 2 ≤ 4 * Γ ^ 2 * ‖dd ω‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hrω 2
      linear_combination this
    have hV : Vfun K h gh φ Jφ lam (x' ω) =
        h (Kᗮ.starProjection (x' ω)) + ⟪mr K gh Jφ (Kᗮ.starProjection (x' ω)), W'⟫ +
          lam * ‖W'‖ ^ 2 := rfl
    rw [hV]
    have hp' := hp
    rw [hyω] at hp'
    simp only [U, C0]
    simp only [Vfun] at hp' ⊢
    have hξr : ⟪η • m + (2 * lam * η) • Y + η • (m0 - m), ξ ω⟫ =
        η * ⟪m, ξ ω⟫ + 2 * lam * η * ⟪Y, ξ ω⟫ + η * ⟪m0 - m, ξ ω⟫ := by
      rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
      simp
    have hmr : ⟪m + (2 * lam) • Y, r ω⟫ = ⟪m, r ω⟫ + 2 * lam * ⟪Y, r ω⟫ := by
      rw [inner_add_left, inner_smul_left]; simp
    have ha : ⟪η • a, Qz ω⟫ = η * ⟪a, Qz ω⟫ := by rw [inner_smul_left]; simp
    rw [hξr, hmr, ha]
    have hlamw := mul_le_mul_of_nonneg_left hw2 hlam
    have hr2lam := mul_le_mul_of_nonneg_left hr2sq hlam
    have hCdω := mul_le_mul_of_nonneg_left hdω hCd
    have hCξω := mul_le_mul_of_nonneg_left hξω hCξ
    have hp'' : h (y + dd ω) + ⟪mr K gh Jφ (y + dd ω), W'⟫ ≤ h y + ⟪m, w⟫ -
        η * (‖a‖ ^ 2 - ⟪m, J a⟫) - η * ⟪a, Qz ω⟫ - η * ⟪m, ξ ω⟫ - ⟪m, r ω⟫ +
        Lh / 2 * ‖dd ω‖ ^ 2 + ⟪mr K gh Jφ (y + dd ω) - m, W'⟫ := hp'
    have eCd : Cd = Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2 := rfl
    have eCξ : Cξ = 2 * lam * η ^ 2 := rfl
    have key : h (y + dd ω) + ⟪mr K gh Jφ (y + dd ω), W'⟫ + lam * ‖W'‖ ^ 2 ≤
        h y + ⟪m, w⟫ + lam * ‖w‖ ^ 2 - η * (‖a‖ ^ 2 - ⟪m, J a⟫) + lam * (‖Y‖ ^ 2 - ‖w‖ ^ 2) +
          Cd * (2 * ‖d0‖ ^ 2) - (η * ⟪a, Qz ω⟫ + (η * ⟪m, ξ ω⟫ + 2 * lam * η * ⟪Y, ξ ω⟫ +
            η * ⟪m0 - m, ξ ω⟫)) -
          (⟪m, r ω⟫ + 2 * lam * ⟪Y, r ω⟫) + ⟪mr K gh Jφ (y + dd ω) - m, Y⟫ +
          (Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) + Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
            Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2)) := by
      linear_combination hp'' + hcross + hlamw + 2 * hr2lam + hCdω + hCξω -
        ‖dd ω‖ ^ 2 * eCd - ‖ξ ω‖ ^ 2 * eCξ
    rw [hyω]
    exact key
  -- integrability and expectations
  obtain ⟨hri, hrE⟩ := H.exp_r N y d0 η
  obtain ⟨hmi, hmE⟩ := H.exp_m N y d0 η
  have hζi := N.int
  have hQzi : Integrable Qz p := Kᗮ.starProjection.integrable_comp hζi
  set Lξ : E →L[ℝ] E := K.starProjection - J.comp Kᗮ.starProjection
  have hξe : ∀ ω, ξ ω = Lξ (ζ ω) := fun ω => by
    simp [ξ, Lξ, Pz, Qz]
  have hξi : Integrable ξ p := by
    have := Lξ.integrable_comp hζi
    exact this.congr (Filter.Eventually.of_forall fun ω => (hξe ω).symm)
  have hrI : Integrable r p := hri
  have hMI : Integrable (fun ω => mr K gh Jφ (y + dd ω)) p := hmi
  set v1 : E := η • m + (2 * lam * η) • Y + η • (m0 - m)
  set v2 : E := m + (2 * lam) • Y
  have i1 : Integrable (fun ω => ⟪η • a, Qz ω⟫) p := (innerSL ℝ (η • a)).integrable_comp hQzi
  have i2 : Integrable (fun ω => ⟪v1, ξ ω⟫) p := (innerSL ℝ v1).integrable_comp hξi
  have i3 : Integrable (fun ω => ⟪v2, r ω⟫) p := (innerSL ℝ v2).integrable_comp hrI
  have i4 : Integrable (fun ω => ⟪mr K gh Jφ (y + dd ω) - m, Y⟫) p := by
    have := (innerSL ℝ Y).integrable_comp (hMI.sub (integrable_const m))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [real_inner_comm]
  obtain ⟨hcrossI, hcrossE⟩ := N.cross_le hσu hσv
  have j1 : Integrable (fun ω => Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2)) p :=
    (N.intQ.const_mul _).const_mul _
  have j2 : Integrable (fun ω => 2 * ‖Pz ω‖ ^ 2) p := N.intP.const_mul _
  have j3 : Integrable (fun ω => 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) p := N.intQ.const_mul _
  have j23 : Integrable (fun ω => 2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) p := j2.add j3
  have j4 : Integrable (fun ω => Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2)) p :=
    j23.const_mul _
  have j5 : Integrable (fun ω => ‖Qz ω‖ * ‖Pz ω‖) p := hcrossI
  have j6 : Integrable (fun ω => Γ * ‖Qz ω‖ ^ 2) p := N.intQ.const_mul _
  have j56 : Integrable (fun ω => ‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2) p := j5.add j6
  have j7 : Integrable (fun ω => Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2)) p :=
    j56.const_mul _
  have j14 : Integrable (fun ω => Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) +
      Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2)) p := j1.add j4
  have i5 : Integrable (fun ω => Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) +
      Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
      Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2)) p := j14.add j7
  have hUi : Integrable U p :=
    ((((integrable_const C0).sub (i1.add i2)).sub i3).add i4).add i5
  have e1 : ∫ ω, ⟪η • a, Qz ω⟫ ∂p = 0 := N.inner_mean Kᗮ.starProjection _
  have e2 : ∫ ω, ⟪v1, ξ ω⟫ ∂p = 0 := by
    simp_rw [hξe]; exact N.inner_mean Lξ _
  have e3 : ∫ ω, ⟪v2, r ω⟫ ∂p = ⟪v2, ∫ ω, r ω ∂p⟫ := integral_inner hrI v2
  have hMs : Integrable (fun ω => mr K gh Jφ (y + dd ω) - m) p := hMI.sub (integrable_const m)
  have e4 : ∫ ω, ⟪mr K gh Jφ (y + dd ω) - m, Y⟫ ∂p =
      ⟪Y, (∫ ω, mr K gh Jφ (y + dd ω) ∂p) - m⟫ := by
    have hc : (fun ω => ⟪mr K gh Jφ (y + dd ω) - m, Y⟫) =
        fun ω => ⟪Y, mr K gh Jφ (y + dd ω) - m⟫ := funext fun ω => real_inner_comm _ _
    rw [hc, integral_inner hMs Y, integral_sub hMI (integrable_const m), integral_const]
    simp only [probReal_univ, one_smul]
  have e5 : ∫ ω, (Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) +
      Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
      Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2)) ∂p ≤
      Cd * (2 * η ^ 2 * σu ^ 2) + Cξ * (2 * σv ^ 2 + 2 * Γ ^ 2 * σu ^ 2) +
      Lm * η ^ 2 * (σu * σv + Γ * σu ^ 2) := by
    rw [integral_add j14 j7, integral_add j1 j4, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add j2 j3, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add j5 j6, integral_const_mul]
    have hq : ∫ ω, ‖Qz ω‖ ^ 2 ∂p ≤ σu ^ 2 := N.varQ
    have hp : ∫ ω, ‖Pz ω‖ ^ 2 ∂p ≤ σv ^ 2 := N.varP
    have hc : ∫ ω, ‖Qz ω‖ * ‖Pz ω‖ ∂p ≤ σu * σv := hcrossE
    have k1 := mul_le_mul_of_nonneg_left hq (mul_nonneg hCd (by positivity : (0:ℝ) ≤ 2 * η ^ 2))
    have k2 := mul_le_mul_of_nonneg_left hp (mul_nonneg hCξ (by norm_num : (0:ℝ) ≤ 2))
    have k3 := mul_le_mul_of_nonneg_left hq (mul_nonneg hCξ (by positivity : (0:ℝ) ≤ 2 * Γ ^ 2))
    have k4 := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ Lm * η ^ 2)
    have k5 := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ Lm * η ^ 2 * Γ)
    linear_combination k1 + k2 + k3 + k4 + k5
  have hb3 : -⟪v2, ∫ ω, r ω ∂p⟫ ≤ (‖m‖ + 2 * lam * ‖Y‖) * (‖r0‖ + LJ * η ^ 2 * σu ^ 2) := by
    have h1 : -⟪v2, ∫ ω, r ω ∂p⟫ ≤ ‖v2‖ * ‖∫ ω, r ω ∂p‖ := by
      have := real_inner_le_norm (-v2) (∫ ω, r ω ∂p)
      rwa [inner_neg_left, norm_neg] at this
    have h2 : ‖v2‖ ≤ ‖m‖ + 2 * lam * ‖Y‖ := (norm_add_le _ _).trans (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
    exact h1.trans (mul_le_mul h2 hrE (norm_nonneg _) (by positivity))
  have hb4 : ⟪Y, (∫ ω, mr K gh Jφ (y + dd ω) ∂p) - m⟫ ≤
      ‖Y‖ * (Lm * ‖d0‖ + c2 * η ^ 2 * σu ^ 2) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hmE (norm_nonneg _))
  have hUE : ∫ ω, U ω ∂p ≤ Vfun K h gh φ Jφ lam x - η * (‖a‖ ^ 2 - ⟪m, J a⟫) +
      lam * (‖Y‖ ^ 2 - ‖w‖ ^ 2) +
      (‖m‖ + 2 * lam * ‖Y‖) * (‖r0‖ + LJ * η ^ 2 * σu ^ 2) +
      ‖Y‖ * (Lm * ‖d0‖ + c2 * η ^ 2 * σu ^ 2) +
      Cd * (2 * ‖d0‖ ^ 2 + 2 * η ^ 2 * σu ^ 2) + Cξ * (2 * σv ^ 2 + 2 * Γ ^ 2 * σu ^ 2) +
      Lm * η ^ 2 * (σu * σv + Γ * σu ^ 2) := by
    have hU : ∫ ω, U ω ∂p = C0 - (∫ ω, ⟪η • a, Qz ω⟫ ∂p + ∫ ω, ⟪v1, ξ ω⟫ ∂p) -
        ∫ ω, ⟪v2, r ω⟫ ∂p + ∫ ω, ⟪mr K gh Jφ (y + dd ω) - m, Y⟫ ∂p +
        ∫ ω, (Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) +
          Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
          Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2)) ∂p := by
      have k0 : Integrable (fun ω => C0 - (⟪η • a, Qz ω⟫ + ⟪v1, ξ ω⟫)) p :=
        (integrable_const C0).sub (i1.add i2)
      have k1 : Integrable (fun ω => C0 - (⟪η • a, Qz ω⟫ + ⟪v1, ξ ω⟫) - ⟪v2, r ω⟫) p := k0.sub i3
      have k2 : Integrable (fun ω => C0 - (⟪η • a, Qz ω⟫ + ⟪v1, ξ ω⟫) - ⟪v2, r ω⟫ +
          ⟪mr K gh Jφ (y + dd ω) - m, Y⟫) p := k1.add i4
      have k3 : Integrable (fun ω => ⟪η • a, Qz ω⟫ + ⟪v1, ξ ω⟫) p := i1.add i2
      show ∫ ω, (C0 - (⟪η • a, Qz ω⟫ + ⟪v1, ξ ω⟫) - ⟪v2, r ω⟫ +
          ⟪mr K gh Jφ (y + dd ω) - m, Y⟫ + (Cd * (2 * η ^ 2 * ‖Qz ω‖ ^ 2) +
          Cξ * (2 * ‖Pz ω‖ ^ 2 + 2 * Γ ^ 2 * ‖Qz ω‖ ^ 2) +
          Lm * η ^ 2 * (‖Qz ω‖ * ‖Pz ω‖ + Γ * ‖Qz ω‖ ^ 2))) ∂p = _
      rw [integral_add k2 i5, integral_add k1 i4, integral_sub k0 i3,
        integral_sub (integrable_const C0) k3, integral_add i1 i2, integral_const]
      simp
    rw [hU, e1, e2, e3, e4]
    simp only [C0]
    linarith
  have hx'm : Measurable x' := measurable_const.sub ((measurable_const.add N.meas).const_smul η)
  have hFm : Measurable (fun ω => Vfun K h gh φ Jφ lam (x' ω)) :=
    (H.Vfun_cont lam).measurable.comp hx'm
  set B0 := ‖Y‖ + 2 * Γ * ‖d0‖
  set B1 := |η| * (1 + Γ) + 2 * Γ * |η|
  have hB0 : 0 ≤ B0 := by positivity
  have hB1 : 0 ≤ B1 := by positivity
  set g : Ω → ℝ := fun ω => (|h y| + G * ‖d0‖ + Γ * G * B0 + 2 * lam * B0 ^ 2) +
    (G * |η| + Γ * G * B1) * ‖ζ ω‖ + 2 * lam * B1 ^ 2 * ‖ζ ω‖ ^ 2
  have hgi : Integrable g p :=
    ((integrable_const _).add (N.norm_int.const_mul _)).add (N.sq_int.const_mul _)
  have hFb : ∀ ω, ‖Vfun K h gh φ Jφ lam (x' ω)‖ ≤ g ω := by
    intro ω
    have hQn : ‖Qz ω‖ ≤ ‖ζ ω‖ := starProj_norm_le _ _
    have hPn : ‖Pz ω‖ ≤ ‖ζ ω‖ := starProj_norm_le _ _
    have hen : ‖e ω‖ ≤ |η| * ‖ζ ω‖ := by
      rw [show e ω = -η • Qz ω from rfl, norm_smul, Real.norm_eq_abs, abs_neg]
      exact mul_le_mul_of_nonneg_left hQn (abs_nonneg _)
    have hdd : ‖dd ω‖ ≤ ‖d0‖ + |η| * ‖ζ ω‖ := by
      rw [show dd ω = d0 + e ω from rfl]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hen)
    have hξn : ‖ξ ω‖ ≤ (1 + Γ) * ‖ζ ω‖ := by
      have h1 : ‖J (Qz ω)‖ ≤ Γ * ‖ζ ω‖ :=
        (J.le_opNorm _).trans (mul_le_mul hJ hQn (norm_nonneg _) hΓ)
      calc ‖ξ ω‖ ≤ ‖Pz ω‖ + ‖J (Qz ω)‖ := norm_sub_le _ _
        _ ≤ ‖ζ ω‖ + Γ * ‖ζ ω‖ := add_le_add hPn h1
        _ = _ := by ring
    have hW : ‖wv K φ (x' ω)‖ ≤ B0 + B1 * ‖ζ ω‖ := by
      rw [hw' ω]
      have h1 : ‖η • ξ ω‖ ≤ |η| * ((1 + Γ) * ‖ζ ω‖) := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hξn (abs_nonneg _)
      have h2 : ‖r ω‖ ≤ 2 * Γ * (‖d0‖ + |η| * ‖ζ ω‖) :=
        (hr2 ω).trans (mul_le_mul_of_nonneg_left hdd (by positivity))
      calc ‖Y - η • ξ ω - r ω‖ ≤ ‖Y‖ + ‖η • ξ ω‖ + ‖r ω‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ ‖Y‖ + |η| * ((1 + Γ) * ‖ζ ω‖) + 2 * Γ * (‖d0‖ + |η| * ‖ζ ω‖) := by gcongr
        _ = _ := by simp only [B0, B1]; ring
    have hhb : |h (y + dd ω)| ≤ |h y| + G * (‖d0‖ + |η| * ‖ζ ω‖) := by
      have := H.h_lip (y + dd ω) y
      rw [add_sub_cancel_left] at this
      have := abs_sub_abs_le_abs_sub (h (y + dd ω)) (h y)
      have := mul_le_mul_of_nonneg_left hdd H.G_nn
      linarith
    have hmn : ‖mr K gh Jφ (y + dd ω)‖ ≤ Γ * G := H.mr_norm _
    set W' := wv K φ (x' ω)
    have hin : |⟪mr K gh Jφ (y + dd ω), W'⟫| ≤ Γ * G * (B0 + B1 * ‖ζ ω‖) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul hmn hW (norm_nonneg _) (mul_nonneg hΓ H.G_nn))
    have hsq : ‖W'‖ ^ 2 ≤ 2 * B0 ^ 2 + 2 * B1 ^ 2 * ‖ζ ω‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hW 2
      nlinarith [sq_nonneg (B0 - B1 * ‖ζ ω‖)]
    have hV : Vfun K h gh φ Jφ lam (x' ω) =
        h (y + dd ω) + ⟪mr K gh Jφ (y + dd ω), W'⟫ + lam * ‖W'‖ ^ 2 := by
      simp only [Vfun, hyd ω, W']
    rw [hV, Real.norm_eq_abs]
    have hl := mul_le_mul_of_nonneg_left hsq hlam
    have hl0 : 0 ≤ lam * ‖W'‖ ^ 2 := by positivity
    calc |h (y + dd ω) + ⟪mr K gh Jφ (y + dd ω), W'⟫ + lam * ‖W'‖ ^ 2|
        ≤ |h (y + dd ω)| + |⟪mr K gh Jφ (y + dd ω), W'⟫| + lam * ‖W'‖ ^ 2 := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_of_nonneg hl0).le)
      _ ≤ g ω := by simp only [g]; nlinarith
  have hFi : Integrable (fun ω => Vfun K h gh φ Jφ lam (x' ω)) p :=
    Integrable.mono' hgi hFm.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
  refine ⟨hFi, ?_⟩
  exact (integral_mono hFi hUi hpath).trans hUE

end Model

end OracleTemplate.RiverValley
