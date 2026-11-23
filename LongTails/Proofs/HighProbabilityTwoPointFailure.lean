import LongTails.Setups.HighDimensionalHighProbabilityStationarity
import LongTails.Proofs.AbcLowerMeasure
import LongTails.Proofs.Execution
import Mathlib.Probability.ProductMeasure

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HighProbabilityTwoPointFailure

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcLowerMeasure

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def reveal (p ω : ℝ) : ℝ := if ω ≤ p then 1 / p else 0

noncomputable def objective (L ε s : ℝ) (e x0 x : E) : ℝ :=
  L / 2 * (⟪e, x - x0⟫ * ⟪e, x - x0⟫) + 2 * s * ε * ⟪e, x - x0⟫

noncomputable def grad (L ε s : ℝ) (e x0 x : E) : E :=
  (L * ⟪e, x - x0⟫ + 2 * s * ε) • e

noncomputable def reply (L ε s p : ℝ) (e x0 x : E) (ω : ℝ) : E :=
  (L * ⟪e, x - x0⟫ + 2 * s * ε * reveal p ω) • e

lemma objective_hasGradientAt [CompleteSpace E] (L ε s : ℝ) (e x0 x : E) :
    HasGradientAt (objective L ε s e x0) (grad L ε s e x0 x) x := by
  have hu : HasFDerivAt (fun y : E => ⟪e, y - x0⟫) (InnerProductSpace.toDual ℝ E e) x := by
    convert (InnerProductSpace.toDual ℝ E e).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const x0) using 1 <;>
      simp [Function.comp_def]
  set u := ⟪e, x - x0⟫
  have hφ : HasDerivAt (fun t : ℝ => L / 2 * (t * t) + 2 * s * ε * t)
      (L * u + 2 * s * ε) u := by
    have h := (((hasDerivAt_id' u).mul (hasDerivAt_id' u)).const_mul (L / 2)).add
      ((hasDerivAt_id' u).const_mul (2 * s * ε))
    convert h using 1
    ring
  have hc := hφ.comp_hasFDerivAt x hu
  rw [hasGradientAt_iff_hasFDerivAt]
  have he : InnerProductSpace.toDual ℝ E (grad L ε s e x0 x) =
      (L * u + 2 * s * ε) • InnerProductSpace.toDual ℝ E e := by
    rw [grad, map_smul]
  rw [he]
  exact hc

lemma objective_gradient [CompleteSpace E] (L ε s : ℝ) (e x0 x : E) :
    gradient (objective L ε s e x0) x = grad L ε s e x0 x :=
  (objective_hasGradientAt L ε s e x0 x).gradient

lemma grad_lipschitz {L : ℝ} (hL : 0 ≤ L) (ε s : ℝ) {e : E} (he : ‖e‖ = 1) (x0 x y : E) :
    ‖grad L ε s e x0 x - grad L ε s e x0 y‖ ≤ L * ‖x - y‖ := by
  have hi : ⟪e, x - x0⟫ - ⟪e, y - x0⟫ = ⟪e, x - y⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hd : grad L ε s e x0 x - grad L ε s e x0 y = (L * ⟪e, x - y⟫) • e := by
    simp only [grad, ← sub_smul]
    congr 1
    rw [← hi]
    ring
  rw [hd, norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL]
  have hcs := abs_real_inner_le_norm e (x - y)
  rw [he, one_mul] at hcs
  exact mul_le_mul_of_nonneg_left hcs hL

lemma objective_lower (L ε s : ℝ) (hL : 0 < L) (hs : s * s = 1) (e x0 x : E) :
    -(2 * ε ^ 2 / L) ≤ objective L ε s e x0 x := by
  have h : objective L ε s e x0 x + 2 * ε ^ 2 / L =
      L / 2 * (⟪e, x - x0⟫ + 2 * s * ε / L) ^ 2 := by
    unfold objective
    field_simp
    nlinarith [hs]
  nlinarith [sq_nonneg (⟪e, x - x0⟫ + 2 * s * ε / L), hL]

lemma objective_attained (L ε s : ℝ) (hL : 0 < L) (hs : s * s = 1) {e : E} (he : ‖e‖ = 1)
    (x0 : E) : objective L ε s e x0 (x0 + (-(2 * s * ε / L)) • e) = -(2 * ε ^ 2 / L) := by
  have hi : ⟪e, x0 + (-(2 * s * ε / L)) • e - x0⟫ = -(2 * s * ε / L) := by
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  unfold objective
  rw [hi]
  field_simp
  nlinarith [hs]

lemma objective_initial (L ε s : ℝ) (e x0 : E) : objective L ε s e x0 x0 = 0 := by
  simp [objective]

lemma not_both_stationary {L ε : ℝ} (hε : 0 < ε) {e : E} (he : ‖e‖ = 1) (x0 y : E)
    (h1 : ‖grad L ε 1 e x0 y‖ ≤ ε) (h2 : ‖grad L ε (-1) e x0 y‖ ≤ ε) : False := by
  simp only [grad, norm_smul, he, mul_one, Real.norm_eq_abs] at h1 h2
  have a1 := (abs_le.mp h1)
  have a2 := (abs_le.mp h2)
  linarith [a1.1, a1.2, a2.1, a2.2]

lemma reply_sub_grad (L ε s p : ℝ) (e x0 x : E) (ω : ℝ) :
    reply L ε s p e x0 x ω - grad L ε s e x0 x = (2 * s * ε * (reveal p ω - 1)) • e := by
  simp only [reply, grad, ← sub_smul]
  congr 1
  ring

lemma reply_norm_le {L ε s p : ℝ} (hε : 0 < ε) (hp : 0 < p) {e : E} (he : ‖e‖ = 1)
    (x0 x : E) (ω : ℝ) :
    ‖reply L ε s p e x0 x ω‖ ≤ |L * ⟪e, x - x0⟫| + 2 * |s| * ε * (1 / p) := by
  have h2 : |2 * s * ε * reveal p ω| ≤ 2 * |s| * ε * (1 / p) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hε]
    gcongr
    unfold reveal
    split_ifs
    · rw [abs_of_pos (by positivity)]
    · simp only [abs_zero]; positivity
  rw [reply, norm_smul, he, mul_one, Real.norm_eq_abs]
  linarith [abs_add_le (L * ⟪e, x - x0⟫) (2 * s * ε * reveal p ω)]

end General

section Measures

lemma unif_Iic {p : ℝ} (hp1 : p ≤ 1) : unif (Set.Iic p) = ENNReal.ofReal p := by
  rw [unif, Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hp1⟩
  rw [this, Real.volume_Icc, sub_zero]

lemma unif_Ioi {p : ℝ} (hp0 : 0 ≤ p) :
    unif (Set.Ioi p) = ENNReal.ofReal (1 - p) := by
  rw [unif, Measure.restrict_apply measurableSet_Ioi]
  have : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, hp0.trans h1.le, h2⟩
  rw [this, Real.volume_Ioc]

lemma measurable_reveal (p : ℝ) : Measurable (reveal p) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma reveal_integral {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : ∫ ω, reveal p ω ∂unif = 1 := by
  have h : reveal p = Set.indicator (Set.Iic p) (fun _ => 1 / p) := by
    funext ω
    simp only [reveal, Set.indicator, Set.mem_Iic]
  rw [h, integral_indicator_const _ measurableSet_Iic, measureReal_def, unif_Iic hp1,
    ENNReal.toReal_ofReal hp0.le, smul_eq_mul]
  field_simp

lemma reveal_sq_integral {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫ ω, (reveal p ω - 1) ^ 2 ∂unif = 1 / p - 1 := by
  have h : (fun ω => (reveal p ω - 1) ^ 2) =
      fun ω => Set.indicator (Set.Iic p) (fun _ => 1 / p ^ 2 - 2 / p) ω + 1 := by
    funext ω
    simp only [reveal, Set.indicator, Set.mem_Iic]
    split_ifs <;> field_simp <;> ring
  rw [h, integral_add ((integrable_const _).indicator measurableSet_Iic) (integrable_const _),
    integral_indicator_const _ measurableSet_Iic, measureReal_def, unif_Iic hp1,
    ENNReal.toReal_ofReal hp0.le, smul_eq_mul, integral_const, probReal_univ, one_smul]
  field_simp
  ring

lemma reveal_bounded (p ω : ℝ) (hp : 0 < p) : |reveal p ω| ≤ 1 / p := by
  unfold reveal
  split_ifs
  · rw [abs_of_pos (by positivity)]
  · simp only [abs_zero]; positivity

lemma stream_no_reveal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    stream.real {ω : ℕ → ℝ | ∀ k ∈ Finset.range N, ω k ∈ Set.Ioi p} = (1 - p) ^ N := by
  have hset : {ω : ℕ → ℝ | ∀ k ∈ Finset.range N, ω k ∈ Set.Ioi p} =
      Set.pi (↑(Finset.range N)) (fun _ => Set.Ioi p) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe]
  have h : stream (Set.pi (↑(Finset.range N)) fun _ => Set.Ioi p) =
      ∏ _i ∈ Finset.range N, unif (Set.Ioi p) := by
    rw [stream]
    exact Measure.infinitePi_pi (μ := fun _ : ℕ => unif) (fun _ _ => measurableSet_Ioi)
  rw [hset, measureReal_def, h]
  simp only [unif_Ioi hp0, Finset.prod_const, Finset.card_range]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]

lemma measurableSet_no_reveal (p : ℝ) (N : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | ∀ k ∈ Finset.range N, ω k ∈ Set.Ioi p} := by
  have hset : {ω : ℕ → ℝ | ∀ k ∈ Finset.range N, ω k ∈ Set.Ioi p} =
      ⋂ k ∈ Finset.range N, (fun ω : ℕ → ℝ => ω k) ⁻¹' Set.Ioi p := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  exact Finset.measurableSet_biInter _ fun k _ => measurable_pi_apply k measurableSet_Ioi

end Measures

section Execution

variable {Q R U : Type*}

lemma iterate_congr {St : Type*} (upd : St → R → St) (qry : St → Fin 1 × Q)
    (r1 r2 : ℕ → (Fin 1 × Q) → R) (N : ℕ) (h : ∀ k < N, ∀ z, r1 k z = r2 k z) (s0 : St) :
    ∀ n ≤ N,
      ((fun sc : St × ℕ => (upd sc.1 (r1 sc.2 (qry sc.1)), sc.2 + 1))^[n] (s0, 0)) =
      ((fun sc : St × ℕ => (upd sc.1 (r2 sc.2 (qry sc.1)), sc.2 + 1))^[n] (s0, 0)) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hcount : ((fun sc : St × ℕ => (upd sc.1 (r1 sc.2 (qry sc.1)), sc.2 + 1))^[n]
          (s0, 0)).2 = n := by
        clear ih hn
        induction n with
        | zero => rfl
        | succ m ihm => rw [Function.iterate_succ_apply', ihm]
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih (by omega)]
      simp only [hcount, h n (by omega)]

lemma execute_congr (O1 O2 : Oracle Q R) (A : Algorithm Q R U) (N : ℕ) (seed : A.Seed)
    (ξ1 : (k : ℕ) → O1.Seed k) (ξ2 : (k : ℕ) → O2.Seed k)
    (r1 r2 : ℕ → (Fin 1 × Q) → R)
    (h1 : ∀ history query, O1.answer history query (ξ1 history.length) = r1 history.length query)
    (h2 : ∀ history query, O2.answer history query (ξ2 history.length) = r2 history.length query)
    (h : ∀ k < N, ∀ z, r1 k z = r2 k z) :
    execute O1 A (fun _ => N) seed ξ1 = execute O2 A (fun _ => N) seed ξ2 := by
  rw [execute_indexed_of_answer O1 A N seed ξ1 r1 h1, execute_indexed_of_answer O2 A N seed ξ2 r2 h2,
    iterate_congr A.update A.query r1 r2 N h (A.initial seed) N le_rfl]

end Execution

open LongTails.Setups.HighDimensionalHighProbabilityStationarity

noncomputable def unitVector (d : ℕ) (hd : 0 < d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single ⟨0, hd⟩ 1

lemma unitVector_norm (d : ℕ) (hd : 0 < d) : ‖unitVector d hd‖ = 1 := by
  simp [unitVector]

noncomputable def revealLevel (σ ε : ℝ) : ℝ := 4 * ε ^ 2 / (σ ^ 2 + 4 * ε ^ 2)

lemma revealLevel_pos {σ ε : ℝ} (hε : 0 < ε) : 0 < revealLevel σ ε := by
  unfold revealLevel; positivity

lemma revealLevel_le_one (σ ε : ℝ) (hε : 0 < ε) : revealLevel σ ε ≤ 1 := by
  unfold revealLevel
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg σ]

lemma revealLevel_inv_sub_one (σ ε : ℝ) (hε : 0 < ε) :
    1 / revealLevel σ ε - 1 = σ ^ 2 / (4 * ε ^ 2) := by
  unfold revealLevel
  field_simp
  ring

noncomputable def hardReply (q : Params) (hd : 0 < q.d) (s : ℝ) :
    EuclideanSpace ℝ (Fin q.d) → ℝ → EuclideanSpace ℝ (Fin q.d) :=
  fun x ω => reply q.L q.ε s (revealLevel q.σ q.ε) (unitVector q.d hd) q.x0 x ω

noncomputable def hardOracle (q : Params) (hd : 0 < q.d) (s : ℝ) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => hardReply q hd s x ω

noncomputable def hardObjective (q : Params) (hd : 0 < q.d) (s : ℝ) :
    EuclideanSpace ℝ (Fin q.d) → ℝ :=
  objective q.L q.ε s (unitVector q.d hd) q.x0

lemma hardObjective_gradient (q : Params) (hd : 0 < q.d) (s : ℝ) (x : EuclideanSpace ℝ (Fin q.d)) :
    gradient (hardObjective q hd s) x = grad q.L q.ε s (unitVector q.d hd) q.x0 x :=
  objective_gradient _ _ _ _ _ x

lemma hardReply_noise (q : Params) (hd : 0 < q.d) (s : ℝ) (x : EuclideanSpace ℝ (Fin q.d)) (ω : ℝ) :
    hardReply q hd s x ω - gradient (hardObjective q hd s) x =
      (2 * s * q.ε * (reveal (revealLevel q.σ q.ε) ω - 1)) • unitVector q.d hd := by
  rw [hardObjective_gradient]
  exact reply_sub_grad _ _ _ _ _ _ _ _

lemma measurable_hardReply (q : Params) (hd : 0 < q.d) (s : ℝ) :
    Measurable (Function.uncurry (hardReply q hd s)) := by
  have h1 : Measurable (fun z : EuclideanSpace ℝ (Fin q.d) × ℝ =>
      q.L * ⟪unitVector q.d hd, z.1 - q.x0⟫ + 2 * s * q.ε * reveal (revealLevel q.σ q.ε) z.2) :=
    ((measurable_const.mul ((continuous_const.inner (continuous_fst.sub
      continuous_const)).measurable))).add
      (measurable_const.mul ((measurable_reveal _).comp measurable_snd))
  exact h1.smul_const (unitVector q.d hd)

lemma hardReply_integrable (q : Params) (hd : 0 < q.d) (s : ℝ) (hε : 0 < q.ε)
    (x : EuclideanSpace ℝ (Fin q.d)) : Integrable (hardReply q hd s x) unif := by
  have hm : Measurable (hardReply q hd s x) := by
    unfold hardReply reply
    exact (measurable_const.add (measurable_const.mul (measurable_reveal _))).smul_const _
  have hb : ∀ ω, ‖hardReply q hd s x ω‖ ≤
      |q.L * ⟪unitVector q.d hd, x - q.x0⟫| + 2 * |s| * q.ε * (1 / revealLevel q.σ q.ε) := by
    intro ω
    unfold hardReply
    exact reply_norm_le hε (revealLevel_pos hε) (unitVector_norm q.d hd) q.x0 x ω
  exact Integrable.of_bound hm.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)

lemma reveal_integrable {p : ℝ} (hp : 0 < p) : Integrable (fun ω => reveal p ω) unif :=
  Integrable.of_bound (measurable_reveal p).aestronglyMeasurable (1 / p)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact reveal_bounded p ω hp)

lemma noise_sq_eq (q : Params) (hd : 0 < q.d) (s : ℝ) (x : EuclideanSpace ℝ (Fin q.d)) (ω : ℝ) :
    ‖hardReply q hd s x ω - gradient (hardObjective q hd s) x‖ ^ 2 =
      (2 * s * q.ε) ^ 2 * (reveal (revealLevel q.σ q.ε) ω - 1) ^ 2 := by
  rw [hardReply_noise, norm_smul, unitVector_norm, mul_one, Real.norm_eq_abs, sq_abs]
  ring

lemma hardObjective_hasGradient (q : Params) (hd : 0 < q.d) (s : ℝ) (x : EuclideanSpace ℝ (Fin q.d)) :
    HasGradientAt (hardObjective q hd s) (gradient (hardObjective q hd s) x) x := by
  rw [hardObjective_gradient]
  exact objective_hasGradientAt _ _ _ _ _ x

lemma hard_lipschitz (q : Params) (hd : 0 < q.d) (s : ℝ) (hL : 0 < q.L)
    (x y : EuclideanSpace ℝ (Fin q.d)) :
    ‖gradient (hardObjective q hd s) x - gradient (hardObjective q hd s) y‖ ≤ q.L * ‖x - y‖ := by
  rw [hardObjective_gradient, hardObjective_gradient]
  exact grad_lipschitz hL.le q.ε s (unitVector_norm q.d hd) q.x0 x y

lemma hard_lower (q : Params) (hd : 0 < q.d) (s : ℝ) (hs : s * s = 1) (hL : 0 < q.L)
    (x : EuclideanSpace ℝ (Fin q.d)) : -(2 * q.ε ^ 2 / q.L) ≤ hardObjective q hd s x :=
  objective_lower q.L q.ε s hL hs _ q.x0 x

lemma hard_inf (q : Params) (hd : 0 < q.d) (s : ℝ) (hs : s * s = 1) (hL : 0 < q.L) (η : ℝ)
    (hη : 0 < η) : ∃ x, hardObjective q hd s x < -(2 * q.ε ^ 2 / q.L) + η := by
  refine ⟨q.x0 + (-(2 * s * q.ε / q.L)) • unitVector q.d hd, ?_⟩
  have h := objective_attained q.L q.ε s hL hs (unitVector_norm q.d hd) q.x0
  unfold hardObjective
  rw [h]
  linarith

lemma hard_gap (q : Params) (hd : 0 < q.d) (s : ℝ) (hL : 0 < q.L)
    (hreg : 2 ^ 54 * q.ε ^ 2 ≤ q.L * q.Δ) :
    hardObjective q hd s q.x0 - -(2 * q.ε ^ 2 / q.L) ≤ q.Δ := by
  unfold hardObjective
  rw [objective_initial]
  have : 2 * q.ε ^ 2 / q.L ≤ q.Δ := by
    rw [div_le_iff₀ hL]
    nlinarith [sq_nonneg q.ε]
  linarith

lemma hard_mean (q : Params) (hd : 0 < q.d) (s : ℝ) (hε : 0 < q.ε)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    ∫ ω, hardReply q hd s x ω ∂unif = gradient (hardObjective q hd s) x := by
  have hp0 : 0 < revealLevel q.σ q.ε := revealLevel_pos hε
  have hp1 : revealLevel q.σ q.ε ≤ 1 := revealLevel_le_one q.σ q.ε hε
  have h : hardReply q hd s x = fun ω => gradient (hardObjective q hd s) x +
      (2 * s * q.ε * (reveal (revealLevel q.σ q.ε) ω - 1)) • unitVector q.d hd := by
    funext ω
    rw [← hardReply_noise q hd s x ω]
    abel
  have hi : Integrable (fun ω => (2 * s * q.ε * (reveal (revealLevel q.σ q.ε) ω - 1)) •
      unitVector q.d hd) unif :=
    (((reveal_integrable hp0).sub (integrable_const 1)).const_mul (2 * s * q.ε)).smul_const _
  rw [h, integral_add (integrable_const _) hi, integral_const, probReal_univ, one_smul,
    integral_smul_const, integral_const_mul, integral_sub (reveal_integrable hp0)
      (integrable_const _), reveal_integral hp0 hp1, integral_const, probReal_univ, one_smul]
  simp

lemma hard_var_integrable (q : Params) (hd : 0 < q.d) (s : ℝ) (hε : 0 < q.ε)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    Integrable (fun ω => ‖hardReply q hd s x ω - gradient (hardObjective q hd s) x‖ ^ 2) unif := by
  have hp0 : 0 < revealLevel q.σ q.ε := revealLevel_pos hε
  simp only [noise_sq_eq]
  refine (Integrable.of_bound (((measurable_reveal _).sub_const 1).pow_const 2).aestronglyMeasurable
    ((1 / revealLevel q.σ q.ε + 1) ^ 2) ?_).const_mul _
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_pow]
  have hb := reveal_bounded (revealLevel q.σ q.ε) ω hp0
  have : |reveal (revealLevel q.σ q.ε) ω - 1| ≤ 1 / revealLevel q.σ q.ε + 1 :=
    (abs_sub _ _).trans (by rw [abs_one]; linarith [hb])
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma hard_variance (q : Params) (hd : 0 < q.d) (s : ℝ) (hs : s * s = 1) (hε : 0 < q.ε)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    ∫ ω, ‖hardReply q hd s x ω - gradient (hardObjective q hd s) x‖ ^ 2 ∂unif ≤ q.σ ^ 2 := by
  have hp0 : 0 < revealLevel q.σ q.ε := revealLevel_pos hε
  have hp1 : revealLevel q.σ q.ε ≤ 1 := revealLevel_le_one q.σ q.ε hε
  simp only [noise_sq_eq]
  rw [integral_const_mul, reveal_sq_integral hp0 hp1, revealLevel_inv_sub_one q.σ q.ε hε]
  have hss : (2 * s * q.ε) ^ 2 = 4 * q.ε ^ 2 := by nlinarith [hs]
  rw [hss]
  apply le_of_eq
  field_simp

lemma hard_admissible (q : Params) (hv : spec.valid q) (hd : 0 < q.d) (s : ℝ) (hs : s * s = 1) :
    spec.admissible q (hardObjective q hd s) (hardOracle q hd s) := by
  obtain ⟨hL, hσ, hε, hδ, hδ1, hreg, _⟩ := hv
  refine ⟨hardReply q hd s, ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, -(2 * q.ε ^ 2 / q.L), stream_iid, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only [toGeneral]
  · exact fun x => hardObjective_hasGradient q hd s x
  · exact fun x y => hard_lipschitz q hd s hL x y
  · exact fun x => hard_lower q hd s hs hL x
  · exact fun η hη => hard_inf q hd s hs hL η hη
  · exact hard_gap q hd s hL hreg
  · exact measurable_hardReply q hd s
  · exact fun x => hardReply_integrable q hd s hε x
  · exact fun x => hard_mean q hd s hε x
  · exact fun x => hard_var_integrable q hd s hε x
  · exact fun x => hard_variance q hd s hs hε x

lemma exists_failure (q : Params) (hv : spec.valid q)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ)
    (hN : (N : ℝ) * (8 * q.ε ^ 2) ≤ q.σ ^ 2 * Real.log (1 / (4 * q.δ))) (hd : 0 < q.d) :
    ∃ s : ℝ, s * s = 1 ∧
      ¬ spec.successful q (hardObjective q hd s)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle q hd s).Seed k) =>
          execute (hardOracle q hd s) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((hardOracle q hd s).law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hσ, hε, hδ, hδ1, hreg, _⟩ := hv
  have he : ‖unitVector q.d hd‖ = 1 := unitVector_norm q.d hd
  have hp0 : 0 < revealLevel q.σ q.ε := revealLevel_pos hε
  have hp1 : revealLevel q.σ q.ε ≤ 1 := revealLevel_le_one q.σ q.ε hε
  by_contra hcon
  push Not at hcon
  have hc1 := hcon 1 (by norm_num)
  have hc2 := hcon (-1) (by norm_num)
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let out : ℝ → A.Seed × (ℕ → ℝ) → EuclideanSpace ℝ (Fin q.d) := fun s w =>
    execute (hardOracle q hd s) A (fun _ => N) w.1 w.2
  have hcont (s : ℝ) : Continuous (gradient (hardObjective q hd s)) := by
    have hK : LipschitzWith ⟨q.L, hL.le⟩ (gradient (hardObjective q hd s)) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm, hardObjective_gradient, hardObjective_gradient]
        exact grad_lipschitz hL.le q.ε s he q.x0 x y
    exact hK.continuous
  let G : ℝ → Set (A.Seed × (ℕ → ℝ)) := fun s =>
    {w | ‖gradient (hardObjective q hd s) (out s w)‖ ≤ q.ε}
  have hm (s : ℝ) (hs : s * s = 1) : MeasurableSet (G s) :=
    measurableSet_le ((hcont s).measurable.comp (hcon s hs).1).norm measurable_const
  have hc (s : ℝ) (hs : s * s = 1) : P.real (G s)ᶜ ≤ q.δ := by
    rw [measureReal_compl (hm s hs), probReal_univ]
    have h : 1 - q.δ ≤ P.real (G s) := (hcon s hs).2
    linarith
  let Ev : Set (ℕ → ℝ) := {ω | ∀ k ∈ Finset.range N, ω k ∈ Set.Ioi (revealLevel q.σ q.ε)}
  have hEv : MeasurableSet Ev := measurableSet_no_reveal _ N
  have hsub : (Prod.snd ⁻¹' Ev : Set (A.Seed × (ℕ → ℝ))) ⊆ (G 1)ᶜ ∪ (G (-1))ᶜ := by
    intro w hw
    have hsame : out 1 w = out (-1) w := by
      apply execute_congr (hardOracle q hd 1) (hardOracle q hd (-1)) A N w.1 w.2 w.2
        (fun k z => hardReply q hd 1 z.2 (w.2 k))
        (fun k z => hardReply q hd (-1) z.2 (w.2 k))
        (fun _ _ => rfl) (fun _ _ => rfl)
      intro k hk z
      have hk' : revealLevel q.σ q.ε < w.2 k := hw k (Finset.mem_range.mpr hk)
      have hr : reveal (revealLevel q.σ q.ε) (w.2 k) = 0 := by simp [reveal, not_le.mpr hk']
      simp only [hardReply, reply, hr, mul_zero]
    by_contra hnot
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hnot
    obtain ⟨g1, g2⟩ := hnot
    have g1' : ‖grad q.L q.ε 1 (unitVector q.d hd) q.x0 (out 1 w)‖ ≤ q.ε := by
      have h := g1
      simp only [G, Set.mem_ofPred_eq, hardObjective_gradient] at h
      exact h
    have g2' : ‖grad q.L q.ε (-1) (unitVector q.d hd) q.x0 (out 1 w)‖ ≤ q.ε := by
      have h := g2
      simp only [G, Set.mem_ofPred_eq, hardObjective_gradient] at h
      rw [hsame]
      exact h
    exact not_both_stationary hε he q.x0 (out 1 w) g1' g2'
  have hPE : P.real (Prod.snd ⁻¹' Ev) = (1 - revealLevel q.σ q.ε) ^ N := by
    have hmap : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    rw [Measure.real, ← Measure.map_apply measurable_snd hEv, hmap]
    exact stream_no_reveal hp0.le hp1 N
  have hle : (1 - revealLevel q.σ q.ε) ^ N ≤ 2 * q.δ := by
    rw [← hPE]
    calc P.real (Prod.snd ⁻¹' Ev) ≤ P.real ((G 1)ᶜ ∪ (G (-1))ᶜ) := measureReal_mono hsub
      _ ≤ P.real (G 1)ᶜ + P.real (G (-1))ᶜ := measureReal_union_le _ _
      _ ≤ 2 * q.δ := by linarith [hc 1 (by norm_num), hc (-1) (by norm_num)]
  have hlog : 0 < Real.log (1 / (2 * q.δ)) - Real.log (1 / (4 * q.δ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have : 1 / (2 * q.δ) / (1 / (4 * q.δ)) = 2 := by field_simp; ring
    rw [this]
    exact Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log (1 / (4 * q.δ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hgt : 2 * q.δ < (1 - revealLevel q.σ q.ε) ^ N := by
    rcases eq_or_lt_of_le hσ with hσ0 | hσpos
    · have hN0 : N = 0 := by
        have h0 : (N : ℝ) * (8 * q.ε ^ 2) ≤ 0 := by simpa [← hσ0] using hN
        have hNn : (N : ℝ) ≤ 0 := by
          by_contra hneg
          push Not at hneg
          have : 0 < (N : ℝ) * (8 * q.ε ^ 2) := by positivity
          linarith
        exact_mod_cast le_antisymm hNn (Nat.cast_nonneg N)
      rw [hN0, pow_zero]
      linarith
    · have h1p : 1 - revealLevel q.σ q.ε = q.σ ^ 2 / (q.σ ^ 2 + 4 * q.ε ^ 2) := by
        unfold revealLevel
        field_simp
        ring
      have hpos : 0 < 1 - revealLevel q.σ q.ε := by rw [h1p]; positivity
      have hx : Real.log (1 - revealLevel q.σ q.ε) ≥ -(4 * q.ε ^ 2 / q.σ ^ 2) := by
        have hinv : (1 - revealLevel q.σ q.ε)⁻¹ = 1 + 4 * q.ε ^ 2 / q.σ ^ 2 := by
          rw [h1p, inv_div]
          field_simp
        have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
        rw [Real.log_inv, hinv] at hl
        linarith
      have hNx : (N : ℝ) * (4 * q.ε ^ 2 / q.σ ^ 2) ≤ Real.log (1 / (4 * q.δ)) := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [hN, hlog4, sq_nonneg q.ε]
      have hlogpow : Real.log (2 * q.δ) < Real.log ((1 - revealLevel q.σ q.ε) ^ N) := by
        rw [Real.log_pow]
        have h2 : Real.log (2 * q.δ) = -Real.log (1 / (2 * q.δ)) := by
          rw [one_div, Real.log_inv, neg_neg]
        rw [h2]
        nlinarith [hx, hNx, hlog, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlogpow
  linarith

end LongTails.Proofs.HighProbabilityTwoPointFailure
