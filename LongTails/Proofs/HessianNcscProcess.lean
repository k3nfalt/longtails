import LongTails.Proofs.HessianNcscPath
import LongTails.Proofs.HessianNcscTrajectory
import LongTails.Proofs.LinearDecaySgdExpectation
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

section Fresh

variable {Ω : Type*} [MeasurableSpace Ω] {St : Type*} [MeasurableSpace St]

lemma fresh_lintegral (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (S : (ℕ → Ω) → St) (hS : Measurable S)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ')
    (h : St × Ω → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ ξ, h (S ξ, ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) =
      ∫⁻ ξ, (∫⁻ ω, h (S ξ, ω) ∂p) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  set P := Measure.infinitePi fun _ : ℕ => p
  set π : (ℕ → Ω) → (Fin k → Ω) := fun ξ i => ξ i
  have hπ : Measurable π := by fun_prop
  set S' := S ∘ TwoSidedPL.extendPrefix ω0 k
  have hS' : Measurable S' := hS.comp (TwoSidedPL.measurable_extendPrefix ω0 k)
  have hf : ∀ ξ, S ξ = S' (π ξ) := fun ξ => TwoSidedPL.factor_prefix ω0 k S hdep ξ
  simp_rw [hf]
  have hpair : Measurable (fun ξ : ℕ → Ω => (π ξ, ξ k)) := by fun_prop
  let H : (Fin k → Ω) × Ω → ℝ≥0∞ := fun z => h (S' z.1, z.2)
  have hH : Measurable H := hh.comp ((hS'.comp measurable_fst).prodMk measurable_snd)
  have hmap := SampledConvex.map_prefix_pair p k
  calc ∫⁻ ξ, h (S' (π ξ), ξ k) ∂P = ∫⁻ z, H z ∂(P.map (fun ξ => (π ξ, ξ k))) :=
        (lintegral_map hH hpair).symm
    _ = ∫⁻ z, H z ∂((P.map π).prod p) := by rw [hmap]
    _ = ∫⁻ u, ∫⁻ ω, H (u, ω) ∂p ∂(P.map π) := lintegral_prod H hH.aemeasurable
    _ = ∫⁻ ξ, ∫⁻ ω, H (π ξ, ω) ∂p ∂P :=
        lintegral_map (hH.lintegral_prod_right') hπ

end Fresh

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Type*} [MeasurableSpace Ω]

lemma sq_add_mean_zero (p : Measure Ω) [IsProbabilityMeasure p] (a : V) (N : Ω → V)
    (hN : Integrable N p) (hN0 : ∫ ω, N ω ∂p = 0) (hN2 : Integrable (fun ω => ‖N ω‖ ^ 2) p) :
    ∫ ω, ‖a + N ω‖ ^ 2 ∂p = ‖a‖ ^ 2 + ∫ ω, ‖N ω‖ ^ 2 ∂p := by
  have hexp : ∀ ω, ‖a + N ω‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, N ω⟫ + ‖N ω‖ ^ 2 := fun ω => norm_add_sq_real _ _
  simp_rw [hexp]
  have hi : Integrable (fun ω => 2 * ⟪a, N ω⟫) p := (hN.const_inner a).const_mul 2
  rw [integral_add (by exact (integrable_const _).add hi) hN2, integral_add (integrable_const _) hi]
  rw [integral_const_mul, integral_inner hN, hN0, inner_zero_right]
  simp

end Pointwise

section Sequences

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
  (gx : E × F → E) (gy : E × F → F) (ξ : ℕ → Ω)

noncomputable def wq : ℕ → E
  | 0 => x0
  | k + 1 => (mainS cfg x0 y0 ox oy ξ k).1

noncomputable def uq (k : ℕ) : E := (mainS cfg x0 y0 ox oy ξ k).2.1

noncomputable def xq : ℕ → E
  | 0 => x0
  | k + 1 => lead cfg (wq cfg x0 y0 ox oy ξ (k + 1)) (uq cfg x0 y0 ox oy ξ k)

noncomputable def yq : ℕ → F
  | 0 => yC cfg x0 y0 ox oy ξ cfg.NC
  | k + 1 => (mainS cfg x0 y0 ox oy ξ k).2.2

noncomputable def nxq : ℕ → E
  | 0 => 0
  | k + 1 => ox (xq cfg x0 y0 ox oy ξ (k + 1), yq cfg x0 y0 ox oy ξ (k + 1)) (ξ (off cfg + k)) -
      gx (xq cfg x0 y0 ox oy ξ (k + 1), yq cfg x0 y0 ox oy ξ (k + 1))

noncomputable def nyq : ℕ → F
  | 0 => 0
  | k + 1 => oy (xq cfg x0 y0 ox oy ξ (k + 1), yq cfg x0 y0 ox oy ξ (k + 1)) (ξ (off cfg + k)) -
      gy (xq cfg x0 y0 ox oy ξ (k + 1), yq cfg x0 y0 ox oy ξ (k + 1))

end Sequences

section Instance

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

omit [FiniteDimensional ℝ F] in
lemma pathRel_seq (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
    (ox : E × F → Ω → E) (oy : E × F → Ω → F) (ξ : ℕ → Ω) :
    PathRel H cfg.α cfg.γ cfg.η cfg.lam (wq cfg x0 y0 ox oy ξ) (uq cfg x0 y0 ox oy ξ)
      (xq cfg x0 y0 ox oy ξ) (yq cfg x0 y0 ox oy ξ) (nxq cfg x0 y0 ox oy gx ξ)
      (nyq cfg x0 y0 ox oy gy ξ) where
  w_succ t := by
    cases t with
    | zero => simp [wq, uq, mainS, wOne]
    | succ k => simp [wq, uq, mainS]
  xt_eq t := by simp [xq, lead]
  u_succ t := by simp [uq, mainS, nxq, xq, wq, yq]
  y_succ t := by simp [yq, mainS, nyq, xq, wq, uq]

end Instance

section Dependence

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma yA_congr {ξ ξ' : ℕ → Ω} : ∀ j, (∀ i, i < j → ξ i = ξ' i) →
    yA cfg x0 y0 oy ξ j = yA cfg x0 y0 oy ξ' j
  | 0, _ => rfl
  | j + 1, h => by
      simp only [yA]
      rw [yA_congr j (fun i hi => h i (by omega)), h j (by omega)]

omit [InnerProductSpace ℝ E] in
lemma accB_congr {ξ ξ' : ℕ → Ω} : ∀ j, (∀ i, i < cfg.NA + j → ξ i = ξ' i) →
    accB cfg x0 y0 ox oy ξ j = accB cfg x0 y0 ox oy ξ' j
  | 0, _ => rfl
  | j + 1, h => by
      simp only [accB]
      rw [accB_congr j (fun i hi => h i (by omega)), h (cfg.NA + j) (by omega),
        yA_congr cfg x0 y0 oy cfg.NA (fun i hi => h i (by omega))]

lemma mInit_congr {ξ ξ' : ℕ → Ω} (h : ∀ i, i < cfg.NA + cfg.NB → ξ i = ξ' i) :
    mInit cfg x0 y0 ox oy ξ = mInit cfg x0 y0 ox oy ξ' := by
  simp only [mInit]; rw [accB_congr cfg x0 y0 ox oy cfg.NB h]

lemma yC_congr {ξ ξ' : ℕ → Ω} : ∀ j, (∀ i, i < cfg.NA + cfg.NB + j → ξ i = ξ' i) →
    yC cfg x0 y0 ox oy ξ j = yC cfg x0 y0 ox oy ξ' j
  | 0, h => by
      simp only [yC]; exact yA_congr cfg x0 y0 oy cfg.NA (fun i hi => h i (by omega))
  | j + 1, h => by
      simp only [yC]
      have hm := mInit_congr cfg x0 y0 ox oy (ξ := ξ) (ξ' := ξ') (fun i hi => h i (by omega))
      rw [yC_congr j (fun i hi => h i (by omega)), h (cfg.NA + cfg.NB + j) (by omega)]
      simp only [xtOne, wOne, hm]

lemma mainS_congr {ξ ξ' : ℕ → Ω} : ∀ k, (∀ i, i < off cfg + k → ξ i = ξ' i) →
    mainS cfg x0 y0 ox oy ξ k = mainS cfg x0 y0 ox oy ξ' k
  | 0, h => by
      simp only [mainS, off] at *
      have hm := mInit_congr cfg x0 y0 ox oy (ξ := ξ) (ξ' := ξ') (fun i hi => h i (by omega))
      rw [yC_congr cfg x0 y0 ox oy cfg.NC (fun i hi => h i (by omega))]
      simp only [wOne, hm]
  | k + 1, h => by
      have ih := mainS_congr k (fun i hi => h i (by omega))
      simp only [mainS]
      rw [ih, h (off cfg + k) (by omega)]

end Dependence

section Measurability

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [MeasurableSpace Ω]

lemma measurable_nphi (η lam : ℝ) : Measurable (nphi (E := E) η lam) := by
  unfold nphi nscale; fun_prop

lemma measurable_lead (cfg : IgtConfig) : Measurable (fun z : E × E => lead cfg z.1 z.2) := by
  unfold lead
  exact measurable_fst.add (((measurable_nphi cfg.η cfg.lam).comp measurable_snd).const_smul _)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_yA (cfg : IgtConfig) (x0 : E) (y0 : F) (oy : E × F → Ω → F)
    (hoy : Measurable (Function.uncurry oy)) : ∀ j, Measurable (fun ξ => yA cfg x0 y0 oy ξ j)
  | 0 => measurable_const
  | j + 1 => by
      have ih := measurable_yA cfg x0 y0 oy hoy j
      simp only [yA]
      exact ih.add ((hoy.comp ((measurable_const.prodMk ih).prodMk (measurable_pi_apply j))).const_smul _)

omit [InnerProductSpace ℝ E] in
lemma measurable_accB (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    ∀ j, Measurable (fun ξ => accB cfg x0 y0 ox oy ξ j)
  | 0 => measurable_const
  | j + 1 => by
      have ih := measurable_accB cfg x0 y0 ox oy hox hoy j
      simp only [accB]
      exact ih.add (hox.comp ((measurable_const.prodMk (measurable_yA cfg x0 y0 oy hoy cfg.NA)).prodMk
        (measurable_pi_apply _)))

lemma measurable_mInit (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    Measurable (fun ξ => mInit cfg x0 y0 ox oy ξ) := by
  simp only [mInit, mzero]
  exact (measurable_accB cfg x0 y0 ox oy hox hoy cfg.NB).const_smul _

lemma measurable_xtOne (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    Measurable (fun ξ => xtOne cfg x0 y0 ox oy ξ) := by
  have hm := measurable_mInit cfg x0 y0 ox oy hox hoy
  simp only [xtOne, wOne]
  exact (measurable_lead cfg).comp
    ((measurable_const.add ((measurable_nphi cfg.η cfg.lam).comp hm)).prodMk hm)

lemma measurable_yC (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    ∀ j, Measurable (fun ξ => yC cfg x0 y0 ox oy ξ j)
  | 0 => measurable_yA cfg x0 y0 oy hoy cfg.NA
  | j + 1 => by
      have ih := measurable_yC cfg x0 y0 ox oy hox hoy j
      simp only [yC]
      exact ih.add ((hoy.comp (((measurable_xtOne cfg x0 y0 ox oy hox hoy).prodMk ih).prodMk
        (measurable_pi_apply _))).const_smul _)

lemma measurable_mainS (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    ∀ k, Measurable (fun ξ => mainS cfg x0 y0 ox oy ξ k)
  | 0 => by
      have hm := measurable_mInit cfg x0 y0 ox oy hox hoy
      simp only [mainS, wOne]
      exact (measurable_const.add ((measurable_nphi cfg.η cfg.lam).comp hm)).prodMk
        (hm.prodMk (measurable_yC cfg x0 y0 ox oy hox hoy cfg.NC))
  | k + 1 => by
      have ih := measurable_mainS cfg x0 y0 ox oy hox hoy k
      have h1 : Measurable (fun ξ => (mainS cfg x0 y0 ox oy ξ k).1) := measurable_fst.comp ih
      have h2 : Measurable (fun ξ => (mainS cfg x0 y0 ox oy ξ k).2.1) :=
        measurable_fst.comp (measurable_snd.comp ih)
      have h3 : Measurable (fun ξ => (mainS cfg x0 y0 ox oy ξ k).2.2) :=
        measurable_snd.comp (measurable_snd.comp ih)
      have hq : Measurable (fun ξ => (lead cfg (mainS cfg x0 y0 ox oy ξ k).1
          (mainS cfg x0 y0 ox oy ξ k).2.1, (mainS cfg x0 y0 ox oy ξ k).2.2)) :=
        ((measurable_lead cfg).comp (h1.prodMk h2)).prodMk h3
      have hgo : Measurable (fun ξ => ox (lead cfg (mainS cfg x0 y0 ox oy ξ k).1
          (mainS cfg x0 y0 ox oy ξ k).2.1, (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k))) :=
        hox.comp (hq.prodMk (measurable_pi_apply _))
      have hgy : Measurable (fun ξ => oy (lead cfg (mainS cfg x0 y0 ox oy ξ k).1
          (mainS cfg x0 y0 ox oy ξ k).2.1, (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k))) :=
        hoy.comp (hq.prodMk (measurable_pi_apply _))
      have hu : Measurable (fun ξ => (1 - cfg.α) • (mainS cfg x0 y0 ox oy ξ k).2.1 +
          cfg.α • ox (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
            (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k))) :=
        (h2.const_smul _).add (hgo.const_smul _)
      simp only [mainS]
      exact (h1.add ((measurable_nphi cfg.η cfg.lam).comp hu)).prodMk
        (hu.prodMk (h3.add (hgy.const_smul _)))

end Measurability

end OracleTemplate.HessianNcsc
