import LongTails.Proofs.HeavyTailedProductProcess

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedFreshProcess

variable {S E Ω : Type*}

def noiseSum (step : S → Ω → S) (noise : S → Ω → E) [Add E] :
    ℕ → S → E → (ℕ → Ω) → E
  | 0, _, z, _ => z
  | n + 1, s, z, ξ => noiseSum step noise n (step s (ξ 0)) (z + noise s (ξ 0))
      (fun k => ξ (k + 1))

lemma noiseSum_eq_sum [AddCommMonoid E] (step : S → Ω → S) (noise : S → Ω → E)
    (n : ℕ) (s : S) (z : E) (ξ : ℕ → Ω) :
    noiseSum step noise n s z ξ = z + ∑ k ∈ Finset.range n,
      noise (HeavyTailedProductProcess.trajectory step k s ξ) (ξ k) := by
  induction n generalizing s z ξ with
  | zero => simp [noiseSum]
  | succ n ih =>
      rw [noiseSum, ih, Finset.sum_range_succ']
      simp only [HeavyTailedProductProcess.trajectory]
      ac_rfl

variable [MeasurableSpace S] [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma noiseSum_measurable {step : S → Ω → S} {noise : S → Ω → E}
    (hs : Measurable (Function.uncurry step)) (he : Measurable (Function.uncurry noise))
    (n : ℕ) : Measurable (fun t : (S × E) × (ℕ → Ω) => noiseSum step noise n t.1.1 t.1.2 t.2) := by
  induction n with
  | zero => exact measurable_snd.comp measurable_fst
  | succ n ih =>
      exact ih.comp (((hs.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        ((measurable_snd.comp measurable_fst).add
          (he.comp ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_pi_apply 0).comp measurable_snd))))).prodMk (by fun_prop))

lemma noiseSum_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {step : S → Ω → S} {noise : S → Ω → E}
    (hs : Measurable (Function.uncurry step)) (he : Measurable (Function.uncurry noise))
    {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ s, Integrable (noise s) P) (hm : ∀ s, (∫ ω, noise s ω ∂P) = 0)
    (hpi : ∀ s, Integrable (fun ω => ‖noise s ω‖ ^ p) P)
    (hpb : ∀ s, (∫ ω, ‖noise s ω‖ ^ p ∂P) ≤ κ)
    (n : ℕ) (s : S) (z : E) :
    Integrable (fun ξ => ‖noiseSum step noise n s z ξ‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, ‖noiseSum step noise n s z ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ‖z‖ ^ p + 6 * n * κ := by
  induction n generalizing s z with
  | zero => simp [noiseSum]
  | succ n ih =>
      let F : Ω × (ℕ → Ω) → ℝ := fun t =>
        ‖noiseSum step noise n (step s t.1) (z + noise s t.1) t.2‖ ^ p
      have hF : Measurable F := by
        apply Measurable.pow_const
        apply Measurable.norm
        exact (noiseSum_measurable hs he n).comp
          ((((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk
            (measurable_const.add ((he.comp measurable_prodMk_left).comp measurable_fst))).prodMk
            measurable_snd)
      have hZi := HeavyTailedMomentBounds.integrable_norm_add_rpow z
        (by linarith : 0 < p) (hi s).aestronglyMeasurable (hpi s)
      have hcontrol := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
        hF.stronglyMeasurable (fun t => Real.rpow_nonneg (norm_nonneg _) _)
        (Filter.Eventually.of_forall (fun ω => (ih (step s ω) (z + noise s ω)).1))
        (hZi.add (integrable_const (6 * n * κ)))
        (Filter.Eventually.of_forall (fun ω => (ih (step s ω) (z + noise s ω)).2))
      have hsplit := HeavyTailedProductProcess.head_tail_preserving P
      have heq : (fun ξ => ‖noiseSum step noise (n + 1) s z ξ‖ ^ p) =
          F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
      rw [heq]
      refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
      have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
        hsplit.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hsplit.map_eq] at heint
      change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
      rw [← heint]
      have hone := HeavyTailedMomentBounds.integral_norm_add_rpow_le
        (w := z) hp hp2 (hi s) (hpi s) (hm s)
      simp only [Pi.add_apply] at hcontrol
      rw [integral_add hZi (integrable_const _), integral_const] at hcontrol
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [probReal_univ, smul_eq_mul, one_mul] at hcontrol
      linarith [hpb s]

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma noiseSum_nonnegative {step : S → Ω → S} {noise : S → Ω → ℝ}
    (he : ∀ s ω, 0 ≤ noise s ω) (n : ℕ) (s : S) {z : ℝ} (hz : 0 ≤ z) (ξ : ℕ → Ω) :
    0 ≤ noiseSum step noise n s z ξ := by
  induction n generalizing s z ξ with
  | zero => exact hz
  | succ n ih => exact ih (step s (ξ 0)) (add_nonneg hz (he s (ξ 0))) _

lemma noiseSum_nonnegative_integral (P : Measure Ω) [IsProbabilityMeasure P]
    {step : S → Ω → S} {noise : S → Ω → ℝ}
    (hs : Measurable (Function.uncurry step)) (he : Measurable (Function.uncurry noise))
    (hpos : ∀ s ω, 0 ≤ noise s ω) (hi : ∀ s, Integrable (noise s) P)
    {κ : ℝ} (hb : ∀ s, (∫ ω, noise s ω ∂P) ≤ κ)
    (n : ℕ) (s : S) {z : ℝ} (hz : 0 ≤ z) :
    Integrable (noiseSum step noise n s z) (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, noiseSum step noise n s z ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ z + n * κ := by
  induction n generalizing s z with
  | zero => simp [noiseSum]
  | succ n ih =>
      let F : Ω × (ℕ → Ω) → ℝ := fun t =>
        noiseSum step noise n (step s t.1) (z + noise s t.1) t.2
      have hF : Measurable F := (noiseSum_measurable hs he n).comp
        ((((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk
          (measurable_const.add ((he.comp measurable_prodMk_left).comp measurable_fst))).prodMk
          measurable_snd)
      have hFi := fun ω => (ih (step s ω) (add_nonneg hz (hpos s ω))).1
      have hFb := fun ω => (ih (step s ω) (add_nonneg hz (hpos s ω))).2
      have hboundi : Integrable (fun ω => z + noise s ω + n * κ) P :=
        ((integrable_const z).add (hi s)).add (integrable_const _)
      have hcontrol := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
        hF.stronglyMeasurable
        (fun t => noiseSum_nonnegative hpos n (step s t.1) (add_nonneg hz (hpos s t.1)) t.2)
        (Filter.Eventually.of_forall hFi) hboundi (Filter.Eventually.of_forall hFb)
      have hsplit := HeavyTailedProductProcess.head_tail_preserving P
      have heq : noiseSum step noise (n + 1) s z =
          F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
      rw [heq]
      refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
      have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
        hsplit.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hsplit.map_eq] at heint
      change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
      rw [← heint]
      have hh := hcontrol.2
      have hzi : Integrable (fun ω => z + noise s ω) P := (integrable_const z).add (hi s)
      rw [integral_add hzi (integrable_const _),
        integral_add (integrable_const z) (hi s)] at hh
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [hb s]


omit [MeasurableSpace S] in
lemma iid_sum_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {e : Ω → E} (he : Measurable e) {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable e P) (hm : (∫ ω, e ω ∂P) = 0)
    (hpi : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hb : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ κ) (n : ℕ) :
    Integrable (fun ξ => ‖∑ k ∈ Finset.range n, e (ξ k)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖∑ k ∈ Finset.range n, e (ξ k)‖ ^ p
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 6 * n * κ := by
  have hh := noiseSum_moment P (S := Unit)
    (step := fun _ _ => ()) (noise := fun _ ω => e ω)
    measurable_const (he.comp measurable_snd) hp hp2
    (fun _ => hi) (fun _ => hm) (fun _ => hpi) (fun _ => hb) n () (0 : E)
  simp only [noiseSum_eq_sum, zero_add, norm_zero, Real.zero_rpow (by linarith : p ≠ 0)] at hh
  simpa using hh

omit [MeasurableSpace S] in
lemma iid_batch_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {e : Ω → E} (he : Measurable e) {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable e P) (hm : (∫ ω, e ω ∂P) = 0)
    (hpi : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hb : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ κ) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ => ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k)‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k)‖ ^ p
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 6 * κ / (n : ℝ) ^ (p - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := iid_sum_moment P he hp hp2 hi hm hpi hb n
  have heq (ξ : ℕ → Ω) :
      ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k)‖ ^ p =
        (n : ℝ)⁻¹ ^ p * ‖∑ k ∈ Finset.range n, e (ξ k)‖ ^ p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn0.le),
      Real.mul_rpow (inv_nonneg.mpr hn0.le) (norm_nonneg _)]
  simp_rw [heq]
  refine ⟨hh.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb' := mul_le_mul_of_nonneg_left hh.2 (Real.rpow_nonneg (inv_nonneg.mpr hn0.le) p)
  have hpow : (n : ℝ)⁻¹ ^ p * n = ((n : ℝ) ^ (p - 1))⁻¹ := by
    rw [Real.inv_rpow hn0.le, Real.rpow_sub hn0, Real.rpow_one]
    field_simp
  calc
    _ ≤ (n : ℝ)⁻¹ ^ p * (6 * n * κ) := hb'
    _ = 6 * κ * ((n : ℝ)⁻¹ ^ p * n) := by ring
    _ = _ := by rw [hpow]; rfl


lemma masked_noiseSum_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {step : S → Ω → S} {noise : S → Ω → E} (active : S → Bool)
    (hs : Measurable (Function.uncurry step)) (he : Measurable (Function.uncurry noise))
    (ha : Measurable active) {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hκ : 0 ≤ κ)
    (hi : ∀ s, Integrable (noise s) P) (hm : ∀ s, (∫ ω, noise s ω ∂P) = 0)
    (hpi : ∀ s, Integrable (fun ω => ‖noise s ω‖ ^ p) P)
    (hb : ∀ s, (∫ ω, ‖noise s ω‖ ^ p ∂P) ≤ κ)
    (n : ℕ) (s : S) (z : E) :
    Integrable (fun ξ => ‖noiseSum step (fun s ω => if active s then noise s ω else 0)
      n s z ξ‖ ^ p) (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, ‖noiseSum step (fun s ω => if active s then noise s ω else 0) n s z ξ‖ ^ p
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ‖z‖ ^ p + 6 * n * κ := by
  have hp0 : p ≠ 0 := by linarith
  apply noiseSum_moment P hs
  · exact Measurable.ite (measurableSet_eq_fun (ha.comp measurable_fst) measurable_const)
      he measurable_const
  · exact hp
  · exact hp2
  · intro u
    cases hh : active u <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact integrable_const _
    · exact hi u
  · intro u
    cases hh : active u <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · simp
    · exact hm u
  · intro u
    cases hh : active u <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact integrable_const _
    · exact hpi u
  · intro u
    cases hh : active u <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · simpa [hp0] using hκ
    · exact hb u


lemma noiseSum_remaining_moment (P : Measure Ω) [IsProbabilityMeasure P]
    {step : S → Ω → S} {noise : S → Ω → E}
    (hs : Measurable (Function.uncurry step)) (he : Measurable (Function.uncurry noise))
    (remaining charge : S → ℕ) (hcharge : ∀ s ω, remaining (step s ω) + charge s ≤ remaining s)
    {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hκ : 0 ≤ κ)
    (hi : ∀ s, Integrable (noise s) P) (hm : ∀ s, (∫ ω, noise s ω ∂P) = 0)
    (hpi : ∀ s, Integrable (fun ω => ‖noise s ω‖ ^ p) P)
    (hb : ∀ s, (∫ ω, ‖noise s ω‖ ^ p ∂P) ≤ charge s * κ)
    (n : ℕ) (s : S) (z : E) :
    Integrable (fun ξ => ‖noiseSum step noise n s z ξ‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, ‖noiseSum step noise n s z ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ‖z‖ ^ p + 6 * remaining s * κ := by
  induction n generalizing s z with
  | zero =>
    simp only [noiseSum, integral_const, probReal_univ, one_smul]
    exact ⟨integrable_const _, le_add_of_nonneg_right (by positivity)⟩
  | succ n ih =>
    let F : Ω × (ℕ → Ω) → ℝ := fun t =>
      ‖noiseSum step noise n (step s t.1) (z + noise s t.1) t.2‖ ^ p
    have hF : Measurable F := by
      apply Measurable.pow_const
      apply Measurable.norm
      exact (noiseSum_measurable hs he n).comp
        ((((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk
          (measurable_const.add ((he.comp measurable_prodMk_left).comp measurable_fst))).prodMk
          measurable_snd)
    have hZi := HeavyTailedMomentBounds.integrable_norm_add_rpow z
      (by linarith : 0 < p) (hi s).aestronglyMeasurable (hpi s)
    have hr (ω : Ω) : (remaining (step s ω) : ℝ) ≤ remaining s - charge s := by
      have hh : (remaining (step s ω) : ℝ) + charge s ≤ remaining s := by
        exact_mod_cast hcharge s ω
      linarith
    have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
      hF.stronglyMeasurable (fun t => Real.rpow_nonneg (norm_nonneg _) _)
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω) (z + noise s ω)).1))
      (hZi.add (integrable_const (6 * ((remaining s : ℝ) - charge s) * κ)))
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω) (z + noise s ω)).2.trans
        (by
          simp only [Pi.add_apply]
          nlinarith [mul_le_mul_of_nonneg_right (hr ω) hκ])))
    have hsplit := HeavyTailedProductProcess.head_tail_preserving P
    have heq : (fun ξ => ‖noiseSum step noise (n + 1) s z ξ‖ ^ p) =
        F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
    rw [heq]
    refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
    have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at heint
    change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
    rw [← heint]
    have hone := HeavyTailedMomentBounds.integral_norm_add_rpow_le
      (w := z) hp hp2 (hi s) (hpi s) (hm s)
    simp only [Pi.add_apply] at hcontrol
    rw [integral_add hZi (integrable_const _), integral_const] at hcontrol
    simp only [probReal_univ, smul_eq_mul, one_mul] at hcontrol
    nlinarith [hb s]

lemma noiseSum_remaining_moment_on (P : Measure Ω) [IsProbabilityMeasure P]
    {step : S → Ω → S} {noise : S → Ω → E} (V : S → Prop)
    (hV : ∀ s, V s → ∀ ω, V (step s ω))
    (hs : Measurable (Function.uncurry step)) (he : Measurable (Function.uncurry noise))
    (remaining charge : S → ℕ)
    (hcharge : ∀ s, V s → ∀ ω, remaining (step s ω) + charge s ≤ remaining s)
    {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hκ : 0 ≤ κ)
    (hi : ∀ s, V s → Integrable (noise s) P)
    (hm : ∀ s, V s → (∫ ω, noise s ω ∂P) = 0)
    (hpi : ∀ s, V s → Integrable (fun ω => ‖noise s ω‖ ^ p) P)
    (hb : ∀ s, V s → (∫ ω, ‖noise s ω‖ ^ p ∂P) ≤ charge s * κ)
    (n : ℕ) (s : S) (hvalid : V s) (z : E) :
    Integrable (fun ξ => ‖noiseSum step noise n s z ξ‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, ‖noiseSum step noise n s z ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      ‖z‖ ^ p + 6 * remaining s * κ := by
  let stepV : {s // V s} → Ω → {s // V s} := fun s ω => ⟨step s.val ω, hV s.val s.property ω⟩
  let noiseV : {s // V s} → Ω → E := fun s ω => noise s.val ω
  have hstep : Measurable (Function.uncurry stepV) :=
    (hs.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)).subtype_mk
  have hnoise : Measurable (Function.uncurry noiseV) :=
    he.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have heq (n : ℕ) (s : {s // V s}) (z : E) (ξ : ℕ → Ω) :
      noiseSum stepV noiseV n s z ξ = noiseSum step noise n s.val z ξ := by
    induction n generalizing s z ξ with
    | zero => rfl
    | succ n ih => exact ih _ _ _
  have hresult := noiseSum_remaining_moment P hstep hnoise
    (fun s => remaining s.val) (fun s => charge s.val)
    (fun s ω => hcharge s.val s.property ω) hp hp2 hκ
    (fun s => hi s.val s.property) (fun s => hm s.val s.property)
    (fun s => hpi s.val s.property) (fun s => hb s.val s.property) n ⟨s, hvalid⟩ z
  simpa only [heq] using hresult

end LongTails.Proofs.HeavyTailedFreshProcess
