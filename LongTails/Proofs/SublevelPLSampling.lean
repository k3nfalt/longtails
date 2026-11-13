import LongTails.Proofs.SublevelPLBlocks

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]

noncomputable def subMean (b : ℕ) (g : E → Ω → E) (x : E) (ζ : Fin b → Ω) : E :=
  (1 / (b : ℝ)) • ∑ l : Fin b, g x (ζ l)

noncomputable def estimate {m b : ℕ} (hm : 0 < m) (B : ℝ) (g : E → Ω → E) (x : E)
    (ξ : Fin (m * b) → Ω) : E :=
  aggregate hm B (fun k => g x (ξ k))

omit [MeasurableSpace Ω] in
lemma estimate_eq {m b : ℕ} (hm : 0 < m) (B : ℝ) (g : E → Ω → E) (x : E)
    (ξ : Fin (m * b) → Ω) :
    estimate hm B g x ξ = robustCenter hm B (fun i => subMean b g x (reindex m b ξ i)) := rfl

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

structure Oracle (p : Measure Ω) (f : E → ℝ) (g : E → Ω → E) (σ : ℝ) : Prop where
  hg : Measurable (Function.uncurry g)
  hgi : ∀ x, Integrable (g x) p
  hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  h2i : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  hvar : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma robustCenter_failure_probability {Ξ : Type} [MeasurableSpace Ξ] (Q : Measure Ξ)
    [IsProbabilityMeasure Q] {V : Ξ → E} (hV : Measurable V) (u : E) {B : ℝ}
    (hp : Q.real {ζ | B / 6 < ‖V ζ - u‖} ≤ 1 / 16) {m : ℕ} (hm : 0 < m) :
    (Measure.pi fun _ : Fin m => Q)
      {η | B / 2 < ‖robustCenter hm B (fun i => V (η i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
  classical
  apply (measure_mono ?_).trans (majority_failure_probability (P := Q)
    (measurableSet_lt measurable_const ((hV.sub measurable_const).norm)) hp m)
  intro η hη
  have hgood : ¬ m < 2 * (Finset.univ.filter (fun i => ‖V (η i) - u‖ ≤ B / 6)).card := by
    intro hg
    exact (not_le_of_gt hη) (robustCenter_accuracy hm (fun i => V (η i)) u hg)
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun i => ‖V (η i) - u‖ ≤ B / 6)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  change m ≤ 2 * (Finset.univ.filter (fun i => B / 6 < ‖V (η i) - u‖)).card
  omega

omit [CompleteSpace E] in
lemma measurable_subMean (b : ℕ) {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : E × (Fin b → Ω) => subMean b g w.1 w.2) := by
  unfold subMean
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro l _
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))

omit [CompleteSpace E] in
lemma measurable_subMean_fixed (b : ℕ) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (x : E) : Measurable (fun ζ : Fin b → Ω => subMean b g x ζ) :=
  (measurable_subMean b hg).comp (measurable_const.prodMk measurable_id)

omit [CompleteSpace E] in
lemma measurable_estimate {m b : ℕ} (hm : 0 < m) (B : ℝ) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : E × (Fin (m * b) → Ω) => estimate hm B g w.1 w.2) := by
  have h : (fun w : E × (Fin (m * b) → Ω) => estimate hm B g w.1 w.2) =
      (robustCenter hm B) ∘ (fun w : E × (Fin (m * b) → Ω) =>
        fun i => subMean b g w.1 (reindex m b w.2 i)) := by
    funext w
    simp only [Function.comp, estimate_eq]
  rw [h]
  apply (measurable_robustCenter hm B).comp
  refine Measurable.of_eval (fun i => ?_)
  exact (measurable_subMean b hg).comp
    (measurable_fst.prodMk (((measurable_pi_apply i).comp (measurable_reindex m b)).comp
      measurable_snd))

lemma subMean_failure (p : Measure Ω) [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
    {σ : ℝ} (ho : Oracle p f g σ) (x : E) {b : ℕ} (hb : 0 < b) {B : ℝ} (hB : 0 < B)
    (hbB : 144 * σ ^ 2 ≤ b * (B / 2) ^ 2) :
    (Measure.pi fun _ : Fin b => p).real
      {ζ | B / 6 < ‖subMean b g x ζ - gradient f x‖} ≤ 1 / 16 := by
  have hg' : Measurable (g x) := ho.hg.comp (measurable_const.prodMk measurable_id)
  exact subbatch_failure p hg' (ho.hgi x) (gradient f x) (ho.h2i x) (ho.hmean x)
    (ho.hvar x) b hb hB hbB

lemma estimate_failure (p : Measure Ω) [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
    {σ : ℝ} (ho : Oracle p f g σ) (x : E) {m b : ℕ} (hm : 0 < m) (hb : 0 < b) {B : ℝ}
    (hB : 0 < B) (hbB : 144 * σ ^ 2 ≤ b * (B / 2) ^ 2) :
    (Measure.pi fun _ : Fin (m * b) => p)
      {ξ | B / 2 < ‖estimate hm B g x ξ - gradient f x‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
  have hV : Measurable (fun ζ : Fin b → Ω => subMean b g x ζ) :=
    measurable_subMean_fixed b ho.hg x
  have hfail := robustCenter_failure_probability (Measure.pi fun _ : Fin b => p) hV
    (gradient f x) (subMean_failure p ho x hb hB hbB) hm
  have hset : MeasurableSet {η : Fin m → Fin b → Ω |
      B / 2 < ‖robustCenter hm B (fun i => subMean b g x (η i)) - gradient f x‖} := by
    apply measurableSet_lt measurable_const
    apply Measurable.norm
    apply Measurable.sub _ measurable_const
    apply (measurable_robustCenter hm B).comp
    exact Measurable.of_eval (fun i => hV.comp (measurable_pi_apply i))
  have hpre := (reindex_preserving p m b).measure_preimage hset.nullMeasurableSet
  have heq : {ξ : Fin (m * b) → Ω | B / 2 < ‖estimate hm B g x ξ - gradient f x‖} =
      reindex m b ⁻¹' {η : Fin m → Fin b → Ω |
        B / 2 < ‖robustCenter hm B (fun i => subMean b g x (η i)) - gradient f x‖} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, estimate_eq]
  rw [heq, hpre]
  exact hfail

lemma subMean_second_moment (p : Measure Ω) [IsProbabilityMeasure p] {f : E → ℝ}
    {g : E → Ω → E} {σ : ℝ} (ho : Oracle p f g σ) (x : E) {b : ℕ} (hb : 0 < b) :
    (∫⁻ ζ, ENNReal.ofReal (‖subMean b g x ζ - gradient f x‖ ^ 2)
      ∂(Measure.pi fun _ : Fin b => p)) ≤ ENNReal.ofReal (σ ^ 2 / b) := by
  have hg' : Measurable (g x) := ho.hg.comp (measurable_const.prodMk measurable_id)
  have hv := RobustGradient.finite_mean_variance (P := p) hg' (ho.hgi x) (gradient f x)
    (ho.h2i x) (ho.hmean x) b hb
  simp only [subMean]
  rw [← ofReal_integral_eq_lintegral_ofReal hv.1 (Filter.Eventually.of_forall
    (fun ζ => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  rw [hv.2]
  exact div_le_div_of_nonneg_right (ho.hvar x) (by positivity)

lemma estimate_second_moment (p : Measure Ω) [IsProbabilityMeasure p] {f : E → ℝ}
    {g : E → Ω → E} {σ : ℝ} (ho : Oracle p f g σ) (x : E) {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (B : ℝ) :
    (∫⁻ ξ, ENNReal.ofReal (‖estimate hm B g x ξ - gradient f x‖ ^ 2)
      ∂(Measure.pi fun _ : Fin (m * b) => p)) ≤ ENNReal.ofReal (m * (σ ^ 2 / b)) := by
  have hV : Measurable (fun ζ : Fin b → Ω => subMean b g x ζ) :=
    measurable_subMean_fixed b ho.hg x
  let F : (Fin m → Fin b → Ω) → ENNReal := fun η =>
    ENNReal.ofReal (‖robustCenter hm B (fun i => subMean b g x (η i)) - gradient f x‖ ^ 2)
  have hF : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub _ measurable_const
    apply (measurable_robustCenter hm B).comp
    exact Measurable.of_eval (fun i => hV.comp (measurable_pi_apply i))
  have hcomp : (fun ξ : Fin (m * b) → Ω =>
      ENNReal.ofReal (‖estimate hm B g x ξ - gradient f x‖ ^ 2)) =
      fun ξ => F (reindex m b ξ) := by
    funext ξ
    simp only [F, estimate_eq]
  rw [hcomp, (reindex_preserving p m b).lintegral_comp hF]
  have hpt : ∀ η : Fin m → Fin b → Ω, F η ≤
      ∑ i : Fin m, ENNReal.ofReal (‖subMean b g x (η i) - gradient f x‖ ^ 2) := by
    intro η
    simp only [F]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal (robustCenter_sq_le hm B _ _)
  calc (∫⁻ η, F η ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin b => p))
      ≤ ∫⁻ η, ∑ i : Fin m, ENNReal.ofReal (‖subMean b g x (η i) - gradient f x‖ ^ 2)
          ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin b => p) :=
        lintegral_mono hpt
    _ = ∑ i : Fin m, ∫⁻ η, ENNReal.ofReal (‖subMean b g x (η i) - gradient f x‖ ^ 2)
          ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin b => p) := by
        apply lintegral_finsetSum
        intro i _
        exact ENNReal.measurable_ofReal.comp
          ((((hV.comp (measurable_pi_apply i)).sub measurable_const).norm).pow_const 2)
    _ = ∑ i : Fin m, ∫⁻ ζ, ENNReal.ofReal (‖subMean b g x ζ - gradient f x‖ ^ 2)
          ∂(Measure.pi fun _ : Fin b => p) := by
        apply Finset.sum_congr rfl
        intro i _
        have hev := measurePreserving_eval (fun _ : Fin m => Measure.pi fun _ : Fin b => p) i
        have hmeas : Measurable (fun ζ : Fin b → Ω =>
            ENNReal.ofReal (‖subMean b g x ζ - gradient f x‖ ^ 2)) :=
          ENNReal.measurable_ofReal.comp (((hV.sub measurable_const).norm).pow_const 2)
        exact hev.lintegral_comp hmeas
    _ ≤ ∑ _i : Fin m, ENNReal.ofReal (σ ^ 2 / b) :=
        Finset.sum_le_sum (fun i _ => subMean_second_moment p ho x hb)
    _ = ENNReal.ofReal (m * (σ ^ 2 / b)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end OracleTemplate.SublevelRobustGradient
