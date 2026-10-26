import LongTails.Proofs.StochasticEnvelopeRecursion
open MeasureTheory OracleTemplate
namespace LongTails.Proofs.StochasticEnvelopeRecursion
open LongTails.Algorithms.StochasticEnvelope LongTails.Algorithms.StochasticEnvelopeProgram
open StochasticEnvelopeWork RecursiveEnvelopeGeometry

structure AccuracyTuning (c : Parameters) (p s a t : ℝ) (d : ℕ) : Prop where
  smoothness_pos : ∀ i, 0 < c.smoothness i
  moment_zero : c.moment 0 = p
  moments : ∀ i, 1 < c.moment i ∧ c.moment i ≤ 2
  additive_nonneg : ∀ i, 0 ≤ c.additive i
  relative_pos : ∀ i, 0 < c.relative i
  batch_pos : 0 < c.batchSize
  initial_additive : 4 * (c.batchSize : ℝ) ^ (-(1 / (p / (p - 1)))) * s ≤ c.additive 0
  initial_relative : 4 * (c.batchSize : ℝ) ^ (-(1 / (p / (p - 1)))) * a ≤ c.relative 0
  base_work : 1 ≤ c.baseWork
  base_work_condition : ∀ i, Real.sqrt ((c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)) ≤ c.baseWork
  drift_pos : 0 < t
  drift_le : t ≤ 1
  probability : c.levelProbability = levelProbability t drift_pos.le drift_le
  condition : ∀ i, 2 ≤ (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)
  relative_small : ∀ i, c.relative i ≤
    ((c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1)) ^ (-2 : ℝ)
  recurrence : ∀ i, c.moment (i + 1) =
    (c.moment i / (c.moment i - 1) * (1 + t)) / (c.moment i / (c.moment i - 1) * (1 + t) - 1)
  additive_next : ∀ i, i < d → (2 : ℝ) ^ (28 : ℝ) * (c.moment i / (c.moment i - 1)) / t *
    c.baseWork ^ (-(c.moment (i + 1) / (c.moment i / (c.moment i - 1)))) *
      (c.additive i) ^ c.moment (i + 1) ≤ (c.additive (i + 1)) ^ c.moment (i + 1)
  relative_next : ∀ i, i < d → (2 : ℝ) ^ (28 : ℝ) * (c.moment i / (c.moment i - 1)) / t *
    c.baseWork ^ (-(c.moment (i + 1) / (c.moment i / (c.moment i - 1)))) *
      (c.relative i) ^ c.moment (i + 1) ≤ (c.relative (i + 1)) ^ c.moment (i + 1)

lemma parameters_accuracy_tuning {L R ε δ σ0 σ p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hs : 0 ≤ σ0) (ha : 0 ≤ σ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hT : 1 ≤ L * R ^ 2 / ε) (d : ℕ) (hd : 1 ≤ d)
    (hdW : (d : ℝ) ≤ 2 + p / (p - 1) + Real.log
      (4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ (p / (p - 1)) + 1 / δ)) :
    AccuracyTuning (parameters L R ε δ σ0 σ p d hd) p σ0 σ (1 / (d : ℝ) ^ 2) d := by
  let q := p / (p - 1)
  let T := L * R ^ 2 / ε
  let M := 4 + T + (σ0 * R / ε) ^ q + 1 / δ
  let W := 2 + q + Real.log M
  let H := W ^ ((2 : ℝ) ^ (20 : ℕ) * (1 + q) ^ (3 : ℕ))
  let k := (2 * T) ^ (1 / (d : ℝ))
  let κ := k + 1
  let t := 1 / (d : ℝ) ^ 2
  let Q := fun i : ℕ => q * (1 + t) ^ i
  let m := (⌈Real.sqrt κ * H ^ (4 * q)⌉₊ : ℝ)
  let ρ := H * m ^ (-(1 / Q d))
  let B := ⌈(4 * (1 + σ) * κ ^ 2 * H) ^ q⌉₊
  let s := 4 * σ0 * (B : ℝ) ^ (-(1 / q))
  let a := κ ^ (-2 : ℝ) / H
  let c := parameters L R ε δ σ0 σ p d hd
  have hq : 2 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hM : 4 ≤ M := by
    have hv : 0 ≤ (σ0 * R / ε) ^ q := Real.rpow_nonneg (by positivity) _
    have hδi : 0 ≤ 1 / δ := by positivity
    dsimp only [M]
    linarith
  have hW : 2 + q ≤ W := by
    dsimp [W]
    have hl := Real.log_nonneg (show 1 ≤ M by linarith)
    linarith
  have hH : 1 ≤ H := Real.one_le_rpow (by linarith) (by positivity)
  have hk : 1 < k := (geometric_depth_tuning hT d hd).1
  have hκ : 2 ≤ κ := by dsimp [κ]; linarith
  have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity : 0 < (d : ℝ) ^ 2)).2
    nlinarith
  have hQd := depth_conjugates hq d hd d le_rfl
  change 2 ≤ Q d ∧ Q d ≤ 2 * q at hQd
  have hwork := base_work_tuning hκ hH hq (by linarith : 0 < Q d) hQd.2
  change 1 ≤ m ∧ Real.sqrt κ ≤ m ∧ m ≤ 2 * Real.sqrt κ * H ^ (4 * q) ∧ 0 < ρ ∧ ρ ≤ 1 at hwork
  have hbatch := initial_batch_relative ha hκ hH (by linarith : 0 < q)
  change 0 < B ∧ 4 * (B : ℝ) ^ (-(1 / q)) * σ ≤ a ∧ _ at hbatch
  have hQi : ∀ i, 2 ≤ Q i := fun i => (level_conjugate_range hq ht.le i i le_rfl).1
  have hratio : ∀ i, (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1) = κ :=
    fun i => level_smoothness_ratio hL (by linarith : 0 < k) i
  have hmoment : ∀ i, c.moment i / (c.moment i - 1) = Q i :=
    fun i => (conjugate_moment_range (hQi i)).2.2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, hbatch.1, ?_, ?_, hwork.1, ?_, ht, ht1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change 0 < L / k ^ i
    positivity
  · change (q * (1 + t) ^ 0) / (q * (1 + t) ^ 0 - 1) = p
    simpa only [pow_zero, mul_one] using conjugate_involution hp
  · intro i
    exact ⟨(conjugate_moment_range (hQi i)).1, (conjugate_moment_range (hQi i)).2.1⟩
  · intro i
    change 0 ≤ s * ρ ^ i
    positivity
  · intro i
    exact (attenuated_relative_bound (by linarith : 0 < κ) hH hwork.2.2.2.1 hwork.2.2.2.2 i).1
  · change 4 * (B : ℝ) ^ (-(1 / q)) * σ0 ≤ s * ρ ^ 0
    dsimp [s]
    simp only [pow_zero, mul_one]
    ring_nf
    exact le_rfl
  · change 4 * (B : ℝ) ^ (-(1 / q)) * σ ≤ a * ρ ^ 0
    simpa only [pow_zero, mul_one] using hbatch.2.1
  · intro i
    rw [hratio]
    exact hwork.2.1
  · intro i
    rw [hratio]
    exact hκ
  · intro i
    rw [hratio]
    exact (attenuated_relative_bound (by linarith : 0 < κ) hH hwork.2.2.2.1 hwork.2.2.2.2 i).2
  · intro i
    exact geometric_moment_recurrence hq ht.le i
  · intro i hi
    change (2 : ℝ) ^ (28 : ℝ) * (c.moment i / (c.moment i - 1)) / t * _ * _ ≤ _
    rw [hmoment]
    exact geometric_scale_moment hq hW hκ d hd hdW i hi s hs0
  · intro i hi
    change (2 : ℝ) ^ (28 : ℝ) * (c.moment i / (c.moment i - 1)) / t * _ * _ ≤ _
    rw [hmoment]
    exact geometric_scale_moment hq hW hκ d hd hdW i hi a ha0


variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma AccuracyTuning.gradient_contract {c : Parameters} {p s a t : ℝ} {d : ℕ}
    (htune : AccuracyTuning c p s a t d) (P : Measure Ω) [IsProbabilityMeasure P]
    {g : E → Ω → E} {f : E → ℝ} {field : E → E} (h : Model (c.smoothness 0) f field)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p) :
    ∀ i, i ≤ d → ∀ x : E,
      Integrable (gradientValue c g i x) (gradientLaw c P i) ∧
      (∫ w, gradientValue c g i x w ∂gradientLaw c P i) = (tower f field c.smoothness i).2 x ∧
      Integrable (fun w => ‖gradientValue c g i x w - (tower f field c.smoothness i).2 x‖ ^ c.moment i)
        (gradientLaw c P i) ∧
      (∫ w, ‖gradientValue c g i x w - (tower f field c.smoothness i).2 x‖ ^ c.moment i
        ∂gradientLaw c P i) ≤ c.additive i ^ c.moment i +
        c.relative i ^ c.moment i * ‖(tower f field c.smoothness i).2 x‖ ^ c.moment i := by
  exact gradientValue_contract P c d h htune.smoothness_pos
    (fun i _ => (htune.moments i).1) (fun i _ => (htune.moments i).2)
    hs ha htune.batch_pos (by simpa only [htune.moment_zero] using htune.initial_additive)
    (by simpa only [htune.moment_zero] using htune.initial_relative)
    (fun i _ => htune.additive_nonneg i) (fun i _ => htune.relative_pos i) htune.base_work
    htune.drift_pos htune.drift_le htune.probability (fun i _ => htune.condition i)
    (fun i _ => htune.relative_small i) (fun i _ => htune.recurrence i)
    htune.additive_next htune.relative_next hg hi hmean
    (by simpa only [htune.moment_zero] using hpi) (by simpa only [htune.moment_zero] using hm)


lemma parameters_recovery_failure {L R ε δ σ0 σ p : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hδ : 0 < δ) (hs : 0 ≤ σ0) (ha : 0 ≤ σ) (hp : 1 < p) (hp2 : p ≤ 2)
    (hT : 1 ≤ L * R ^ 2 / ε) (d : ℕ) (hd : 1 ≤ d)
    (hdW : (d : ℝ) ≤ 2 + p / (p - 1) + Real.log
      (4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ (p / (p - 1)) + 1 / δ))
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {f : E → ℝ} {field : E → E}
    (h : Model L f field) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ σ0 ^ p + σ ^ p * ‖field x‖ ^ p)
    (x xs : E) (hmin : ∀ y, f xs ≤ f y) (hRdist : ‖x - xs‖ ≤ R) :
    let c := parameters L R ε δ σ0 σ p d hd
    ((recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)).prod
      (Measure.infinitePi fun _ : ℕ => P))
      {w | ε < f (recoveryValue c g d x w) - f xs} ≤ ENNReal.ofReal (δ / 4) := by
  let c := parameters L R ε δ σ0 σ p d hd
  let k := (2 * (L * R ^ 2 / ε)) ^ (1 / (d : ℝ))
  let κ := k + 1
  let e := ε / (4 * (d : ℝ))
  have hd' : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have htune := parameters_accuracy_tuning hL hR hε hδ hs ha hp hp2 hT d hd hdW
  have hzero : c.smoothness 0 = L := by simp [c, parameters]
  have hmodel : Model (c.smoothness 0) f field := by simpa only [hzero] using h
  have he : 0 < e := by dsimp [e]; positivity
  have hη : 0 < c.recoveryFailure := by change 0 < δ / (4 * (d : ℝ)); positivity
  have hD : ∀ i, i < d → c.recoveryDistance i =
      Real.sqrt (2 * e / (c.smoothness i + c.smoothness (i + 1))) := by
    intro i _
    have hk : 0 < k := (geometric_depth_tuning hT d hd).1.le.trans_lt' zero_lt_one
    have hr := level_smoothness_ratio hL hk i
    change (c.smoothness i + c.smoothness (i + 1)) / c.smoothness (i + 1) = κ at hr
    have hadd := (div_eq_iff (htune.smoothness_pos (i + 1)).ne').1 hr
    change Real.sqrt (ε / (2 * (d : ℝ) * c.smoothness (i + 1) * κ)) = _
    rw [hadd]
    congr 1
    dsimp [e]
    field_simp
    ring
  have hendpoint : c.smoothness d = ε / (2 * R ^ 2) := depth_smoothness_endpoint hL hR hε hT d hd
  have hinitial : (tower f field c.smoothness d).1 x - f xs ≤ ε - (d : ℝ) * e := by
    have hgap := tower_initial_gap hmodel htune.smoothness_pos hmin x (d - 1)
    rw [Nat.sub_add_cancel hd, hendpoint] at hgap
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hRdist 2
    have hratio : ε / (2 * R ^ 2) / 2 * R ^ 2 = ε / 4 := by field_simp; ring
    have hsmall : (tower f field c.smoothness d).1 x - f xs ≤ ε / 4 :=
      hgap.trans (by rw [← hratio]; exact mul_le_mul_of_nonneg_left hsquare (by positivity))
    have heq : (d : ℝ) * e = ε / 4 := by dsimp [e]; field_simp
    rw [heq]
    linarith
  have hcontract := htune.gradient_contract P hmodel hs ha hg hi hmean hpi hm
  have hh := recoveryValue_tower_failure hg c P d hmodel htune.smoothness_pos hmin hε.le he
    (fun i _ => (htune.moments i).1) (fun i _ => (htune.moments i).2)
    (fun i _ => htune.additive_nonneg i) (fun i _ => htune.relative_pos i)
    (fun i _ => htune.condition i) (fun i _ => htune.relative_small i)
    hD (fun _ _ => le_rfl) hη (fun i hi => hcontract i hi.le) x hinitial
  refine hh.trans_eq ?_
  change (d : ENNReal) * ENNReal.ofReal (δ / (4 * (d : ℝ))) = ENNReal.ofReal (δ / 4)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  congr 1
  field_simp


lemma chosen_depth_bound {L R ε δ σ0 p : ℝ} (hR : 0 < R) (hε : 0 < ε) (hs : 0 ≤ σ0) (hδ : 0 < δ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hT : 1 ≤ L * R ^ 2 / ε) :
    (depth L R ε δ σ0 p : ℝ) ≤ 2 + p / (p - 1) + Real.log
      (4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ (p / (p - 1)) + 1 / δ) := by
  have hq : 2 ≤ p / (p - 1) := (le_div_iff₀ (by linarith : 0 < p - 1)).2 (by linarith)
  have hM : 4 ≤ 4 + L * R ^ 2 / ε + (σ0 * R / ε) ^ (p / (p - 1)) + 1 / δ := by
    have hv := Real.rpow_nonneg (by positivity : 0 ≤ σ0 * R / ε) (p / (p - 1))
    have hi : 0 < 1 / δ := by positivity
    linarith
  have hd := depth_choice hM hq
  unfold depth
  rw [max_eq_right hd.1]
  exact hd.2.1

lemma setup_recovery_failure (q : LongTails.Setups.AffineMomentConvex.Params)
    (hq : LongTails.Setups.AffineMomentConvex.spec.valid q)
    (hT : 1 ≤ q.L * q.R ^ 2 / q.ε)
    (P : Measure q.Ω) [IsProbabilityMeasure P] (f : q.E → ℝ) (g : q.E → q.Ω → q.E)
    (hc : ConvexOn ℝ Set.univ f) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖)
    (ho : LongTails.Setups.AffineMomentConvex.IsFiniteMomentOracle P f g q.α q.σ q.σ0)
    (xs : q.E) (hmin : IsMinOn f Set.univ xs) (hR : ‖q.x0 - xs‖ ≤ q.R) :
    let d := depth q.L q.R q.ε q.δ q.σ0 q.α
    let c := parameters q.L q.R q.ε q.δ q.σ0 q.σ q.α d (Nat.le_max_left _ _)
    ((recoverySeedLaw c.levelProbability d : Measure (RecoverySeed d)).prod
      (Measure.infinitePi fun _ : ℕ => P))
      {w | q.ε < f (recoveryValue c g d q.x0 w) - f xs} ≤ ENNReal.ofReal (q.δ / 4) := by
  rcases hq with ⟨hL, hR0, ha, hs, hp, hp2, hε, hδ, _⟩
  have hmodel : Model q.L f (gradient f) := by
    refine ⟨hL, ?_, ?_⟩
    · intro x y
      have hh := OracleTemplate.Gradient.convex_support hc hf x y
      linarith
    · exact OracleTemplate.Gradient.smooth_upper_bound hf hlip
  exact parameters_recovery_failure hL hR0 hε hδ hs ha hp hp2 hT _ (Nat.le_max_left _ _)
    (chosen_depth_bound hR0 hε hs hδ hp hp2 hT) P hmodel ho.measurable ho.integrable ho.unbiased
    ho.integrable_moment ho.moment q.x0 xs (fun y => hmin (Set.mem_univ y)) hR

end LongTails.Proofs.StochasticEnvelopeRecursion
