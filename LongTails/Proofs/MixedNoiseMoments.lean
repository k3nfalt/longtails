import LongTails.Proofs.NormalizedStormOrthogonality

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace OracleTemplate.MixedNoise

open OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

variable (p : Measure Ω) [IsProbabilityMeasure p]

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure p] in
lemma centered_noise_memLp (g : E → Ω → E) (G : E → E)
    (hg : Measurable (Function.uncurry g))
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p) (x : E) :
    MemLp (fun ω => g x ω - G x) 2 p := by
  have hm : Measurable (fun ω => g x ω - G x) :=
    (hg.comp (measurable_const.prodMk measurable_id)).sub measurable_const
  exact (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hm.aestronglyMeasurable).mpr (hnoise x)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma oracle_integrable_of_centered_sq (g : E → Ω → E) (G : E → E)
    (hg : Measurable (Function.uncurry g))
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p) (x : E) :
    Integrable (g x) p := by
  have hi := (centered_noise_memLp p g G hg hnoise x).integrable (by norm_num)
  convert hi.add (integrable_const (G x)) using 1
  funext ω
  simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure p] in
lemma centered_difference_sq_integrable (g : E → Ω → E) (G : E → E)
    (hg : Measurable (Function.uncurry g))
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p) (x y : E) :
    Integrable (fun ω => ‖(g x ω - G x) - (g y ω - G y)‖ ^ 2) p := by
  have hm := (centered_noise_memLp p g G hg hnoise x).sub
    (centered_noise_memLp p g G hg hnoise y)
  exact (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hm.aestronglyMeasurable).mp hm

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma lipschitz_comp_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {X : α → E} {F : E → E} {L : ℝ≥0}
    (hF : LipschitzWith L F) (hX : MemLp X 2 μ) : MemLp (fun a => F (X a)) 2 μ := by
  have hshift : LipschitzWith L (fun x => F x - F 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hF.dist_le_mul x y
  have hm := hshift.comp_memLp (sub_self _) hX
  convert hm.add (memLp_const (F 0)) using 1
  funext a
  simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma fresh_oracle_memLp (k : ℕ) (X : (ℕ → Ω) → E) (hX : Measurable X)
    (hdep : ∀ ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X ξ = X ξ')
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) (hG : Measurable G) (hG2 : MemLp (fun ξ => G (X ξ)) 2 P)
    (r σ : ℝ) (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2) :
    MemLp (fun ξ => g (X ξ) (ξ k)) 2 P := by
  have hW : Measurable (Function.uncurry (fun x ω => g x ω - G x)) :=
    hg.sub (hG.comp measurable_fst)
  have hGi : Integrable (fun ξ => ‖G (X ξ)‖ ^ 2) P :=
    (OracleTemplate.TwoSidedPL.memLp_two_iff_sq (hG.comp hX).aestronglyMeasurable).mp hG2
  have hi := (fresh_sq_integrable p k X hX hdep (fun x ω => g x ω - G x)
    hW hnoise (fun x => r * ‖G x‖ ^ 2 + σ ^ 2) hbound
    ((hGi.const_mul r).add (integrable_const (σ ^ 2)))).1
  have hm : Measurable (fun ξ => g (X ξ) (ξ k) - G (X ξ)) :=
    hW.comp (hX.prodMk (measurable_pi_apply k))
  have hLp := (OracleTemplate.TwoSidedPL.memLp_two_iff_sq hm.aestronglyMeasurable).mpr hi
  convert hLp.add hG2 using 1
  funext ξ
  simp

lemma batch_sum_variable_variance (c0 : ℕ) {Y : Type} [MeasurableSpace Y] (S0 : (ℕ → Ω) → Y) (hS0 : Measurable S0)
    (hd0 : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < c0 → ξ i = ξ' i) → S0 ξ = S0 ξ')
    (B : (ℕ → Ω) → E) (hB : Measurable B)
    (hdB : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < c0 → ξ i = ξ' i) → B ξ = B ξ')
    (hB2 : Integrable (fun ξ => ‖B ξ‖ ^ 2) P)
    (W : Y → Ω → E) (hW : Measurable (Function.uncurry W))
    (hWi : ∀ y, Integrable (W y) p) (hW0 : ∀ y, ∫ ω, W y ω ∂p = 0)
    (hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) p)
    (w : Y → ℝ) (hw : ∀ y, ∫ ω, ‖W y ω‖ ^ 2 ∂p ≤ w y)
    (hwi : Integrable (fun ξ => w (S0 ξ)) P) :
    ∀ m, Integrable (fun ξ : ℕ → Ω => ‖B ξ + ∑ i ∈ Finset.range m, W (S0 ξ) (ξ (c0 + i))‖ ^ 2) P ∧
      ∫ ξ, ‖B ξ + ∑ i ∈ Finset.range m, W (S0 ξ) (ξ (c0 + i))‖ ^ 2 ∂P ≤
        ∫ ξ, ‖B ξ‖ ^ 2 ∂P + m * ∫ ξ, w (S0 ξ) ∂P
  | 0 => by simpa using hB2
  | m + 1 => by
      obtain ⟨hI, hle⟩ := batch_sum_variable_variance c0 S0 hS0 hd0 B hB hdB hB2 W hW hWi hW0 hW2 w hw hwi m
      have hsum : Measurable fun ξ : ℕ → Ω => ∑ i ∈ Finset.range m, W (S0 ξ) (ξ (c0 + i)) :=
        Finset.measurable_sum _ fun i _ => hW.comp (hS0.prodMk (measurable_pi_apply _))
      set S : (ℕ → Ω) → E × Y := fun ξ => (B ξ + ∑ i ∈ Finset.range m, W (S0 ξ) (ξ (c0 + i)), S0 ξ)
      have hS : Measurable S := (hB.add hsum).prodMk hS0
      have hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < c0 + m → ξ i = ξ' i) → S ξ = S ξ' := by
        intro ξ ξ' h
        have h0 : ∀ i, i < c0 → ξ i = ξ' i := fun i hi => h i (by omega)
        simp only [S]
        rw [hdB ξ ξ' h0, hd0 ξ ξ' h0]
        congr 2
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [h (c0 + i) (by have := Finset.mem_range.mp hi; omega)]
      have hW' : Measurable (Function.uncurry fun (y : E × Y) (ω : Ω) => W y.2 ω) :=
        hW.comp ((measurable_fst.snd).prodMk measurable_snd)
      have hres := fresh_step_sq p (c0 + m) S hS hdep (fun y => y.1) measurable_fst
        (fun y ω => W y.2 ω) hW' (fun y => hWi y.2) (fun y => hW0 y.2) (fun y => hW2 y.2)
        (fun y => w y.2) (fun y => hw y.2) hwi hI 1
      simp only [one_smul, one_mul, one_pow] at hres
      have e : ∀ ξ : ℕ → Ω, B ξ + ∑ i ∈ Finset.range (m + 1), W (S0 ξ) (ξ (c0 + i)) =
          (B ξ + ∑ i ∈ Finset.range m, W (S0 ξ) (ξ (c0 + i))) + W (S0 ξ) (ξ (c0 + m)) := by
        intro ξ; rw [Finset.sum_range_succ, add_assoc]
      simp_rw [e]
      refine ⟨hres.1, ?_⟩
      have := hres.2
      push_cast
      linarith


lemma batch_average_variable_variance (c0 : ℕ) {Y : Type} [MeasurableSpace Y]
    (S0 : (ℕ → Ω) → Y) (hS0 : Measurable S0)
    (hd0 : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < c0 → ξ i = ξ' i) → S0 ξ = S0 ξ')
    (B : (ℕ → Ω) → E) (hB : Measurable B)
    (hdB : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < c0 → ξ i = ξ' i) → B ξ = B ξ')
    (hB2 : Integrable (fun ξ => ‖B ξ‖ ^ 2) P)
    (W : Y → Ω → E) (hW : Measurable (Function.uncurry W))
    (hWi : ∀ y, Integrable (W y) p) (hW0 : ∀ y, ∫ ω, W y ω ∂p = 0)
    (hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) p)
    (w : Y → ℝ) (hw : ∀ y, ∫ ω, ‖W y ω‖ ^ 2 ∂p ≤ w y)
    (hwi : Integrable (fun ξ => w (S0 ξ)) P) (b : ℕ) (hb : 0 < b) :
    Integrable (fun ξ : ℕ → Ω =>
      ‖B ξ + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, W (S0 ξ) (ξ (c0 + i))‖ ^ 2) P ∧
      (∫ ξ, ‖B ξ + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, W (S0 ξ) (ξ (c0 + i))‖ ^ 2 ∂P) ≤
        (∫ ξ, ‖B ξ‖ ^ 2 ∂P) + (∫ ξ, w (S0 ξ) ∂P) / b := by
  let c : ℝ := (b : ℝ)⁻¹
  have he (y : Y) (ω : Ω) : ‖c • W y ω‖ ^ 2 = c ^ 2 * ‖W y ω‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hi (y : Y) : Integrable (fun ω => ‖c • W y ω‖ ^ 2) p := by
    simp_rw [he]
    exact (hW2 y).const_mul _
  have hz (y : Y) : ∫ ω, c • W y ω ∂p = 0 := by
    rw [integral_smul, hW0, smul_zero]
  have hbound (y : Y) : ∫ ω, ‖c • W y ω‖ ^ 2 ∂p ≤ c ^ 2 * w y := by
    simp_rw [he]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hw y) (sq_nonneg c)
  have h := batch_sum_variable_variance p c0 S0 hS0 hd0 B hB hdB hB2
    (fun y ω => c • W y ω) (hW.const_smul c) (fun y => (hWi y).smul c)
    hz hi (fun y => c ^ 2 * w y) hbound (hwi.const_mul _) b
  simp only [← Finset.smul_sum] at h
  rw [integral_const_mul] at h
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc : (b : ℝ) * (c ^ 2 * (∫ ξ, w (S0 ξ) ∂P)) =
      (∫ ξ, w (S0 ξ) ∂P) / b := by
    dsimp [c]
    field_simp
  rw [hc] at h
  exact h

end OracleTemplate.MixedNoise
