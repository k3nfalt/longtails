import LongTails.Proofs.PLHessianExpect
import LongTails.Proofs.NormalizedStormOrthogonality
import LongTails.Proofs.HessianNcscProcess

open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.PLHessian

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

noncomputable def sgdSeq (g : E → Ω → E) (η : ℝ) (x0 : E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => x0
  | n + 1 => sgdSeq g η x0 ξ n - η • g (sgdSeq g η x0 ξ n) (ξ n)

lemma sgdSeq_congr (g : E → Ω → E) (η : ℝ) (x0 : E) {ξ ξ' : ℕ → Ω} :
    ∀ n, (∀ i, i < n → ξ i = ξ' i) → sgdSeq g η x0 ξ n = sgdSeq g η x0 ξ' n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [sgdSeq]
      rw [sgdSeq_congr g η x0 n (fun i hi => h i (by omega)), h n (by omega)]

lemma measurable_sgdSeq [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (η : ℝ) (x0 : E) :
    ∀ n, Measurable (fun ξ : ℕ → Ω => sgdSeq g η x0 ξ n)
  | 0 => measurable_const
  | n + 1 => by
      have hn := measurable_sgdSeq hg η x0 n
      simp only [sgdSeq]
      exact hn.sub ((hg.comp (hn.prodMk (measurable_pi_apply n))).const_smul η)

section Run

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E} {u : E}
  {L μ ρ σ K : ℝ}

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma Hyp.gap_le_pot (H : Hyp p f g u L μ ρ σ K) {lam Φ0 : ℝ} (hlam : 0 ≤ lam) (hΦ0 : 0 < Φ0)
    (x : E) : f x - f u ≤ L / 2 * pot f u lam Φ0 x := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨p0, hp0f, hpd⟩ := nearest (u := u) H.continuous x
  have hmin0 : IsMinOn f univ p0 := fun z _ => by
    show f p0 ≤ f z; rw [hp0f]; exact H.min (mem_univ z)
  have hg0 := grad_zero_of_min H.L_pos H.grad H.lip hmin0
  have hup := Gradient.smooth_upper_bound H.grad H.lip p0 x
  rw [hg0, inner_zero_left, hp0f] at hup
  have hD : distSq f u x = ‖x - p0‖ ^ 2 := by unfold distSq; rw [hpd]
  have hpot : distSq f u x ≤ pot f u lam Φ0 x := by
    unfold pot
    have := hub_nonneg (a := Φ0 / 4) (by positivity : (0 : ℝ) < Φ0 / 4) (f x - f u)
    have := mul_nonneg hlam this
    linarith
  have hL := H.L_pos
  have : L / 2 * ‖x - p0‖ ^ 2 ≤ L / 2 * pot f u lam Φ0 x :=
    mul_le_mul_of_nonneg_left (hD ▸ hpot) (by positivity)
  linarith

local notation "Pω" => Measure.infinitePi fun _ : ℕ => p

lemma Hyp.run_step (H : Hyp p f g u L μ ρ σ K) {η Φ0 : ℝ} (hη : 0 < η)
    (hΦ0 : 0 < Φ0) (hΦ0ρ : 36864 * ρ ^ 2 * Φ0 ≤ μ ^ 3) (h1 : 16 * L * η ≤ 1)
    (h2 : 768 * Real.sqrt (L / μ) * K * L * σ ^ 2 * η ≤ μ * Φ0)
    (h3 : 196 * Real.sqrt (L / μ) * L ^ 2 * η ^ 2 ≤ 1) (x0 : E) (n : ℕ)
    (hI : Integrable (fun ξ => pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ n)) Pω) :
    Integrable (fun ξ => pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ (n + 1))) Pω ∧
      Integrable (fun ξ => f (sgdSeq g η x0 ξ n) - f u) Pω ∧
      ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ (n + 1)) ∂Pω ≤
        (1 - μ * η / 32) * ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ n) ∂Pω -
          η / 2 * ∫ ξ, (f (sgdSeq g η x0 ξ n) - f u) ∂Pω + 2 * η ^ 2 * σ ^ 2 := by
  set lam := 32 * Real.sqrt (L / μ) / μ with hlamdef
  have hlam0 : 0 ≤ lam := by have := H.μ_pos; positivity
  set S := fun ξ : ℕ → Ω => sgdSeq g η x0 ξ n with hSdef
  have hS : Measurable S := measurable_sgdSeq H.meas η x0 n
  have hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n → ξ i = ξ' i) → S ξ = S ξ' :=
    fun ξ ξ' h => sgdSeq_congr g η x0 n h
  have hpc := H.pot_continuous (lam := lam) hΦ0
  set Φf : E → Ω → ℝ := fun y ω => pot f u lam Φ0 (y - η • g y ω) with hΦfdef
  have hΦm : Measurable (Function.uncurry Φf) :=
    hpc.measurable.comp (measurable_fst.sub (H.meas.const_smul η))
  have hstep := fun y => H.step hη hΦ0 hΦ0ρ h1 h2 h3 y
  have hnext : ∀ ξ, pot f u lam Φ0 (sgdSeq g η x0 ξ (n + 1)) = Φf (S ξ) (ξ n) := fun ξ => rfl
  have hgapm : Measurable fun ξ => f (S ξ) - f u := (H.continuous.measurable.comp hS).sub_const _
  have hgap0 : ∀ ξ, 0 ≤ f (S ξ) - f u := fun ξ => sub_nonneg.mpr (H.min (mem_univ _))
  have igap : Integrable (fun ξ => f (S ξ) - f u) Pω := by
    refine Integrable.mono' (hI.const_mul (L / 2)) hgapm.aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgap0 ξ)]
    exact H.gap_le_pot hlam0 hΦ0 (S ξ)
  have hq : 0 ≤ μ * η / 32 := by have := H.μ_pos; positivity
  have hq1 : μ * η / 32 ≤ 1 := by
    have := H.μ_le; have := H.L_pos; nlinarith
  have hbound : ∀ y, ∫ ω, Φf y ω ∂p ≤ pot f u lam Φ0 y + 2 * η ^ 2 * σ ^ 2 := by
    intro y
    have hb := (hstep y).2
    have h0 : 0 ≤ f y - f u := sub_nonneg.mpr (H.min (mem_univ _))
    have hp0 := pot_nonneg (f := f) (u := u) hlam0 hΦ0 y
    have : (1 - μ * η / 32) * pot f u lam Φ0 y ≤ pot f u lam Φ0 y := by nlinarith
    have : 0 ≤ η / 2 * (f y - f u) := by positivity
    exact le_trans hb (by linarith)
  have inext : Integrable (fun ξ => pot f u lam Φ0 (sgdSeq g η x0 ξ (n + 1))) Pω := by
    refine NormalizedStorm.integrable_of_lintegral_le
      (hpc.measurable.comp (measurable_sgdSeq H.meas η x0 (n + 1)))
      (fun ξ => pot_nonneg hlam0 hΦ0 _) (hI.add (integrable_const (2 * η ^ 2 * σ ^ 2))) ?_
    simp_rw [hnext]
    have hh : Measurable fun z : E × Ω => ENNReal.ofReal (Φf z.1 z.2) :=
      ENNReal.measurable_ofReal.comp hΦm
    rw [HessianNcsc.fresh_lintegral p n S hS hdep (fun z => ENNReal.ofReal (Φf z.1 z.2)) hh]
    refine lintegral_mono fun ξ => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hstep (S ξ)).1
      (Filter.Eventually.of_forall fun ω => pot_nonneg hlam0 hΦ0 _)]
    exact ENNReal.ofReal_le_ofReal (hbound (S ξ))
  refine ⟨inext, igap, ?_⟩
  set Ψ : E → Ω → ℝ := fun y ω => Φf y ω -
    ((1 - μ * η / 32) * pot f u lam Φ0 y - η / 2 * (f y - f u) + 2 * η ^ 2 * σ ^ 2) with hΨdef
  have hΨm : Measurable (Function.uncurry Ψ) := by
    refine hΦm.sub ?_
    have hm1 : Measurable fun z : E × Ω => pot f u lam Φ0 z.1 := hpc.measurable.comp measurable_fst
    have hm2 : Measurable fun z : E × Ω => f z.1 := H.continuous.measurable.comp measurable_fst
    exact (((hm1.const_mul _).sub ((hm2.sub_const _).const_mul _)).add_const _)
  have ibd : Integrable (fun ξ => (1 - μ * η / 32) * pot f u lam Φ0 (S ξ) -
      η / 2 * (f (S ξ) - f u) + 2 * η ^ 2 * σ ^ 2) Pω :=
    ((hI.const_mul _).sub (igap.const_mul _)).add (integrable_const _)
  have iΨ : Integrable (fun ξ => Ψ (S ξ) (ξ n)) Pω := inext.sub ibd
  have hΨeq := TwoSidedPL.integral_prefix_dep p n S hS hdep Ψ hΨm iΨ
  have hΨle : ∫ ξ, Ψ (S ξ) (ξ n) ∂Pω ≤ 0 := by
    rw [hΨeq]
    refine integral_nonpos fun ξ => ?_
    show ∫ ω, Ψ (S ξ) ω ∂p ≤ 0
    simp only [Ψ]
    rw [integral_sub (hstep (S ξ)).1 (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    have h := (hstep (S ξ)).2
    change ∫ ω, Φf (S ξ) ω ∂p ≤ _ at h
    simp only [Φf, hlamdef] at h ⊢
    linarith
  have hsplit : ∫ ξ, Ψ (S ξ) (ξ n) ∂Pω =
      ∫ ξ, pot f u lam Φ0 (sgdSeq g η x0 ξ (n + 1)) ∂Pω -
        ((1 - μ * η / 32) * ∫ ξ, pot f u lam Φ0 (S ξ) ∂Pω -
          η / 2 * ∫ ξ, (f (S ξ) - f u) ∂Pω + 2 * η ^ 2 * σ ^ 2) := by
    have inext' : Integrable (fun ξ => Φf (S ξ) (ξ n)) Pω := inext
    simp only [Ψ, hnext]
    have i1 : Integrable (fun ξ => (1 - μ * η / 32) * pot f u lam Φ0 (S ξ)) Pω := hI.const_mul _
    have i2 : Integrable (fun ξ => η / 2 * (f (S ξ) - f u)) Pω := igap.const_mul _
    have i12 : Integrable (fun ξ => (1 - μ * η / 32) * pot f u lam Φ0 (S ξ) -
        η / 2 * (f (S ξ) - f u)) Pω := i1.sub i2
    rw [integral_sub inext' ibd, integral_add i12 (integrable_const _), integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const]
    simp
  rw [hsplit] at hΨle
  linarith

lemma Hyp.run_bound (H : Hyp p f g u L μ ρ σ K) {η Φ0 : ℝ} (hη : 0 < η)
    (hΦ0 : 0 < Φ0) (hΦ0ρ : 36864 * ρ ^ 2 * Φ0 ≤ μ ^ 3) (h1 : 16 * L * η ≤ 1)
    (h2 : 768 * Real.sqrt (L / μ) * K * L * σ ^ 2 * η ≤ μ * Φ0)
    (h3 : 196 * Real.sqrt (L / μ) * L ^ 2 * η ^ 2 ≤ 1) (x0 : E) :
    ∀ n, Integrable (fun ξ => pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ n)) Pω ∧
      ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ n) ∂Pω ≤
        (1 - μ * η / 32) ^ n * pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x0 + 64 * η * σ ^ 2 / μ
  | 0 => by
      refine ⟨(integrable_const (pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x0) : _), ?_⟩
      simp only [sgdSeq, integral_const, probReal_univ, one_smul, pow_zero, one_mul]
      have : 0 ≤ 64 * η * σ ^ 2 / μ := by have := H.μ_pos; positivity
      linarith
  | n + 1 => by
      obtain ⟨hI, hb⟩ := H.run_bound hη hΦ0 hΦ0ρ h1 h2 h3 x0 n
      obtain ⟨hI', igap, hs⟩ := H.run_step hη hΦ0 hΦ0ρ h1 h2 h3 x0 n hI
      refine ⟨hI', ?_⟩
      have hμ := H.μ_pos
      have hq1 : 0 ≤ 1 - μ * η / 32 := by have := H.μ_le; have := H.L_pos; nlinarith
      have hgap : 0 ≤ ∫ ξ, (f (sgdSeq g η x0 ξ n) - f u) ∂Pω :=
        integral_nonneg fun ξ => sub_nonneg.mpr (H.min (mem_univ _))
      have hm := mul_le_mul_of_nonneg_left hb hq1
      have e : (1 - μ * η / 32) * ((1 - μ * η / 32) ^ n *
          pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x0 + 64 * η * σ ^ 2 / μ) + 2 * η ^ 2 * σ ^ 2 =
          (1 - μ * η / 32) ^ (n + 1) * pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x0 +
            64 * η * σ ^ 2 / μ := by
        field_simp; ring
      have : 0 ≤ η / 2 * ∫ ξ, (f (sgdSeq g η x0 ξ n) - f u) ∂Pω := by positivity
      linarith

lemma Hyp.window_sum (H : Hyp p f g u L μ ρ σ K) {η Φ0 : ℝ} (hη : 0 < η)
    (hΦ0 : 0 < Φ0) (hΦ0ρ : 36864 * ρ ^ 2 * Φ0 ≤ μ ^ 3) (h1 : 16 * L * η ≤ 1)
    (h2 : 768 * Real.sqrt (L / μ) * K * L * σ ^ 2 * η ≤ μ * Φ0)
    (h3 : 196 * Real.sqrt (L / μ) * L ^ 2 * η ^ 2 ≤ 1) (x0 : E) (a : ℕ) :
    ∀ m, (∑ i ∈ Finset.range m, η / 2 * ∫ ξ, (f (sgdSeq g η x0 ξ (a + i)) - f u) ∂Pω) +
        ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ (a + m)) ∂Pω ≤
      ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ a) ∂Pω +
        m * (2 * η ^ 2 * σ ^ 2)
  | 0 => by simp
  | m + 1 => by
      have ih := H.window_sum hη hΦ0 hΦ0ρ h1 h2 h3 x0 a m
      obtain ⟨hI, -⟩ := H.run_bound hη hΦ0 hΦ0ρ h1 h2 h3 x0 (a + m)
      obtain ⟨-, -, hs⟩ := H.run_step hη hΦ0 hΦ0ρ h1 h2 h3 x0 (a + m) hI
      have hμ := H.μ_pos
      have hp : 0 ≤ ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 (sgdSeq g η x0 ξ (a + m)) ∂Pω :=
        integral_nonneg fun ξ => pot_nonneg (by positivity) hΦ0 _
      have hq : 0 ≤ μ * η / 32 := by positivity
      have : μ * η / 32 * ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0
          (sgdSeq g η x0 ξ (a + m)) ∂Pω ≥ 0 := by positivity
      rw [Finset.sum_range_succ, show a + (m + 1) = a + m + 1 by omega]
      push_cast
      nlinarith

end Run

end OracleTemplate.PLHessian
