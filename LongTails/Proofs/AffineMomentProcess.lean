import LongTails.Proofs.AffineMomentCoupling
import LongTails.Proofs.AffineMomentBatch
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.RobustGeneralizedMeasurability

open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentAcceleratedGeometry

namespace LongTails.Proofs.AffineMomentProcess

abbrev ProofState (E : Type*) := ℕ × (E × E) × Bool × E × Bool

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stateEnergy (t : Tuning) (f : E → ℝ) (u : E) (s : ProofState E) : ℝ :=
  accumulatedWeight t s.1 * (f s.2.1.1 - f u) + energy u s.2.1.2

noncomputable def active (t : Tuning) (g : E → E) (s : ProofState E) : Prop :=
  s.2.2.2.2 = false ∧ s.1 < iterations t ∧ ‖s.2.1.1‖ ≤ 4 ∧ ‖s.2.1.2‖ ≤ 1 ∧
    (s.2.2.1 = true → ‖s.2.2.2.1 - g (point t s.1 s.2.1)‖ ≤ (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8)

noncomputable def next {Ω : Type*} (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) : ProofState E := by
  classical
  let replies := OracleTemplate.RobustGeneralized.sampleReplies oracle (point t s.1 s.2.1) ξ
  exact if active t g s ∧ n = sampleSize t then
    if s.2.2.1 then
      (s.1 + 1, advance t s.1 s.2.1 s.2.2.2.1
        (OracleTemplate.RobustGeneralized.meanBlock 0 n replies), false, 0, false)
    else
      let h := pilotEstimate t replies
      if ‖h - g (point t s.1 s.2.1)‖ ≤ (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8 then
        (s.1, s.2.1, true, h, false)
      else (s.1, s.2.1, false, 0, true)
    else s

noncomputable def increment {Ω : Type*} (t : Tuning) (f : E → ℝ) (g : E → E) (u : E)
    (oracle : E → Ω → E) (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) : ℝ := by
  classical
  exact if active t g s ∧ n = sampleSize t ∧ s.2.2.1 = true then
    (stateEnergy t f u (next t g oracle n s ξ) - stateEnergy t f u s -
      1 / (iterations t : ℝ)) / 4 else 0

lemma next_inactive {Ω : Type*} (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) (hs : ¬ active t g s) :
    next t g oracle n s ξ = s := by simp [next, hs]

lemma increment_inactive {Ω : Type*} (t : Tuning) (f : E → ℝ) (g : E → E) (u : E)
    (oracle : E → Ω → E) (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω)
    (hs : ¬ active t g s) : increment t f g u oracle n s ξ = 0 := by
  simp [increment, hs]

lemma next_pilot_energy {Ω : Type*} (t : Tuning) (f : E → ℝ) (g : E → E) (u : E)
    (oracle : E → Ω → E) (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω)
    (hs : s.2.2.1 = false) : stateEnergy t f u (next t g oracle n s ξ) = stateEnergy t f u s := by
  classical
  unfold next
  split
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  · rfl

lemma next_radius {Ω : Type*} {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    (g : E → E) (oracle : E → Ω → E) (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω)
    (hx : ‖s.2.1.1‖ ≤ 4) (hz : ‖s.2.1.2‖ ≤ 1) :
    ‖(next t g oracle n s ξ).2.1.1‖ ≤ 4 ∧ ‖(next t g oracle n s ξ).2.1.2‖ ≤ 1 := by
  classical
  unfold next
  split
  · split
    · exact LongTails.Proofs.AffineMomentCoupling.advance_radius ht _ _ hx hz _ _
    · dsimp only
      split <;> exact ⟨hx, hz⟩
  · exact ⟨hx, hz⟩

lemma next_round_bound {Ω : Type*} (t : Tuning) (g : E → E) (oracle : E → Ω → E)
    (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) (hk : s.1 ≤ iterations t) :
    (next t g oracle n s ξ).1 ≤ iterations t := by
  classical
  unfold next
  split
  · rename_i hs
    split
    · exact Nat.succ_le_of_lt hs.1.2.1
    · dsimp only
      split <;> exact hk
  · exact hk

lemma increment_telescope {Ω : Type*} (t : Tuning) (f : E → ℝ) (g : E → E) (u : E)
    (oracle : E → Ω → E) (n : ℕ) (s : ProofState E) (ξ : Fin n → Ω) :
    4 * increment t f g u oracle n s ξ =
      (stateEnergy t f u (next t g oracle n s ξ) - ((next t g oracle n s ξ).1 : ℝ) / iterations t) -
      (stateEnergy t f u s - (s.1 : ℝ) / iterations t) := by
  classical
  by_cases hs : active t g s ∧ n = sampleSize t
  · by_cases hp : s.2.2.1 = true
    · simp only [increment, hs.1, hs.2, hp, and_self, ↓reduceIte, next,
        Nat.cast_add, Nat.cast_one]
      ring
    · have hp0 : s.2.2.1 = false := Bool.eq_false_iff.mpr hp
      have he := next_pilot_energy t f g u oracle n s ξ hp0
      have hk : (next t g oracle n s ξ).1 = s.1 := by
        unfold next
        simp only [hs.1, hs.2, and_self, ↓reduceIte, hp0, Bool.false_eq_true]
        split <;> rfl
      rw [he, hk]
      simp [increment, hp]
  · have hn : next t g oracle n s ξ = s := by simp [next, hs]
    rw [hn]
    have hi : increment t f g u oracle n s ξ = 0 := by
      unfold increment
      split
      · rename_i hh
        exact False.elim (hs ⟨hh.1, hh.2.1⟩)
      · rfl
    rw [hi]
    ring

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_point (t : Tuning) : Measurable (fun s : ℕ × (E × E) => point t s.1 s.2) := by
  apply measurable_from_prod_countable_right
  intro k
  unfold point couplingPoint
  fun_prop

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurable_stateEnergy (t : Tuning) {f : E → ℝ} (hf : Measurable f) (u : E) :
    Measurable (stateEnergy t f u) := by
  unfold stateEnergy energy
  fun_prop

lemma measurable_active (t : Tuning) {g : E → E} (hg : Measurable g) :
    MeasurableSet {s : ProofState E | active t g s} := by
  have hpoint : Measurable (fun s : ProofState E => point t s.1 s.2.1) := by
    apply measurable_from_prod_countable_right
    intro k
    unfold point couplingPoint
    fun_prop
  have hgood : MeasurableSet {s : ProofState E |
      ‖s.2.2.2.1 - g (point t s.1 s.2.1)‖ ≤ (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8} := by
    apply measurableSet_le
    · exact (by fun_prop : Measurable (fun s : ProofState E => s.2.2.2.1)).sub (hg.comp hpoint) |>.norm
    · exact ((hg.comp hpoint).norm.add_const (pilotRadius t)).div_const 8
  unfold active
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_lt (show Measurable (fun s : ProofState E => s.1) by fun_prop) measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (show Measurable (fun s : ProofState E => ‖s.2.1.1‖) by fun_prop) measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le (show Measurable (fun s : ProofState E => ‖s.2.1.2‖) by fun_prop) measurable_const
  have he : {s : ProofState E | s.2.2.1 = true →
      ‖s.2.2.2.1 - g (point t s.1 s.2.1)‖ ≤ (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8} =
      {s : ProofState E | s.2.2.1 = true}ᶜ ∪
        {s : ProofState E | ‖s.2.2.2.1 - g (point t s.1 s.2.1)‖ ≤ (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8} := by
    ext s
    simp [imp_iff_not_or]
  change MeasurableSet {s : ProofState E | s.2.2.1 = true →
    ‖s.2.2.2.1 - g (point t s.1 s.2.1)‖ ≤ (‖g (point t s.1 s.2.1)‖ + pilotRadius t) / 8}
  rw [he]
  exact (measurableSet_eq_fun (show Measurable (fun s : ProofState E => s.2.2.1) by fun_prop)
    (measurable_const (a := true))).compl.union hgood


lemma measurable_pilotEstimate (t : Tuning) : Measurable (pilotEstimate (E := E) t) := by
  have hm : Measurable (fun replies : ℕ → E => fun i : Fin (pilotGroups t) =>
      OracleTemplate.RobustGeneralized.meanBlock (i * batchSize t) (batchSize t) replies) :=
    Measurable.of_eval (fun i => OracleTemplate.RobustGeneralized.measurable_meanBlock _ _)
  exact (OracleTemplate.AffineGradient.measurable_center (E := E) (pilotRadius t) (pilotGroups t)).comp
    (measurable_const.prodMk hm)

lemma measurable_advance (t : Tuning) :
    Measurable (fun v : (ℕ × (E × E)) × (E × E) => advance t v.1.1 v.1.2 v.2.1 v.2.2) := by
  have hy : Measurable (fun v : (ℕ × (E × E)) × (E × E) => point t v.1.1 v.1.2) :=
    (measurable_point (E := E) t).comp measurable_fst
  unfold advance primalStep primalFraction primalVertex mirrorStep
  apply Measurable.prodMk
  · fun_prop
  · exact (OracleTemplate.measurable_clip 1).comp (by fun_prop)

variable {Ω : Type*} [MeasurableSpace Ω]

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_replies {oracle : E → Ω → E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : E × (Fin n → Ω) => OracleTemplate.RobustGeneralized.sampleReplies oracle w.1 w.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i < n
  · simp only [OracleTemplate.RobustGeneralized.sampleReplies, hi, ↓reduceDIte]
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply (⟨i, hi⟩ : Fin n)).comp measurable_snd))
  · simp only [OracleTemplate.RobustGeneralized.sampleReplies, hi, ↓reduceDIte]
    exact measurable_const

lemma measurable_next (t : Tuning) {g : E → E} (hg : Measurable g)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (next t g oracle n)) := by
  classical
  have hpoint : Measurable (fun s : ProofState E => point t s.1 s.2.1) := by
    apply measurable_from_prod_countable_right
    intro k
    unfold point couplingPoint
    fun_prop
  have hy : Measurable (fun v : ProofState E × (Fin n → Ω) => point t v.1.1 v.1.2.1) :=
    hpoint.comp measurable_fst
  have hr := (measurable_replies ho n).comp (hy.prodMk measurable_snd)
  have hh := (measurable_pilotEstimate (E := E) t).comp hr
  have hraw := (OracleTemplate.RobustGeneralized.measurable_meanBlock 0 n).comp hr
  have hadv := (measurable_advance (E := E) t).comp
    ((show Measurable (fun v : ProofState E × (Fin n → Ω) => (v.1.1, v.1.2.1)) by fun_prop).prodMk
      ((show Measurable (fun v : ProofState E × (Fin n → Ω) => v.1.2.2.2.1) by fun_prop).prodMk hraw))
  by_cases hn : n = sampleSize t
  · unfold Function.uncurry next
    simp only [eq_true hn, and_true]
    apply Measurable.ite ((measurable_active t hg).preimage measurable_fst)
    · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      · exact (by fun_prop : Measurable (fun v : ProofState E × (Fin n → Ω) => v.1.1 + 1)).prodMk
          (hadv.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_const)))
      · apply Measurable.ite (measurableSet_le (hh.sub (hg.comp hy)).norm (((hg.comp hy).norm.add_const (pilotRadius t)).div_const 8))
        · exact (by fun_prop : Measurable (fun v : ProofState E × (Fin n → Ω) => v.1.1)).prodMk
            ((by fun_prop : Measurable (fun v : ProofState E × (Fin n → Ω) => v.1.2.1)).prodMk
              (measurable_const.prodMk (hh.prodMk measurable_const)))
        · fun_prop
    · exact measurable_fst
  · have he : Function.uncurry (next t g oracle n) =
        (fun v : ProofState E × (Fin n → Ω) => v.1) := by
      funext v
      simp [Function.uncurry, next, hn]
    rw [he]
    exact measurable_fst

lemma measurable_increment (t : Tuning) {f : E → ℝ} (hf : Measurable f)
    {g : E → E} (hg : Measurable g) (u : E)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (increment t f g u oracle n)) := by
  classical
  have he := (measurable_stateEnergy t hf u).comp (measurable_next t hg ho n)
  have he0 : Measurable (fun v : ProofState E × (Fin n → Ω) => stateEnergy t f u v.1) :=
    (measurable_stateEnergy t hf u).comp measurable_fst
  unfold Function.uncurry increment
  apply Measurable.ite
  · exact ((measurable_active t hg).preimage measurable_fst).inter
      ((MeasurableSet.const (n = sampleSize t)).inter (measurableSet_eq_fun (by fun_prop) measurable_const))
  · exact ((he.sub he0).sub_const _).div_const 4
  · exact measurable_const

variable [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
lemma increment_mgf {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    {f : E → ℝ} {g : E → E} (u : E) (hu : ‖u‖ ≤ 1)
    (hs : ∀ x y, f x + inner ℝ (g x) (y - x) ≤ f y)
    (hsm : ∀ x y, f y ≤ f x + inner ℝ (g x) (y - x) + (1 / 2) * ‖y - x‖ ^ 2)
    (hmin : ∀ x, f u ≤ f x) (hzero : g u = 0)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ ‖x - y‖)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle))
    (hoi : ∀ x, Integrable (oracle x) P) (homean : ∀ x, (∫ ω, oracle x ω ∂P) = g x)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - g x‖ ^ t.p) P)
    (hom : ∀ x, (∫ ω, ‖oracle x ω - g x‖ ^ t.p ∂P) ≤ t.σ0 ^ t.p + t.σ ^ t.p * ‖g x‖ ^ t.p)
    (s : ProofState E) :
    Integrable (fun ξ => Real.exp (increment t f g u oracle (sampleSize t) s ξ))
      (Measure.pi fun _ : Fin (sampleSize t) => P) ∧
    (∫ ξ, Real.exp (increment t f g u oracle (sampleSize t) s ξ)
      ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤ 1 := by
  classical
  by_cases ha : active t g s
  · by_cases hphase : s.2.2.1 = true
    · let y := point t s.1 s.2.1
      have hoy : Measurable (oracle y) := ho.comp measurable_prodMk_left
      have hν := LongTails.Proofs.AffineMomentParameters.pilotRadius_pos ht
      have hscaled := (hom y).trans (LongTails.Proofs.AffineMomentBatch.affine_scale_bound
        (le_of_lt ht.exponent_gt) ht.noise_nonneg ht.additive_nonneg hν (norm_nonneg (g y)))
      have hpilot : ‖s.2.2.2.1 - g (point t s.1 s.2.1)‖ ≤
          ‖g (point t s.1 s.2.1)‖ / 8 + pilotRadius t := by
        have hh := ha.2.2.2.2 hphase
        linarith
      have hraw := LongTails.Proofs.AffineMomentBatch.raw_mean_moment ht.exponent_gt ht.exponent_le hν.le
        hoy (hoi y) (g y) (homean y) (hop y) hscaled (sampleSize t)
        (LongTails.Proofs.AffineMomentParameters.sampleSize_pos ht)
        (LongTails.Proofs.AffineMomentParameters.sample_raw_moment ht)
      have hmean := (LongTails.Proofs.PowerMirrorMoments.finite_mean_mean (hoi y) (sampleSize t)
        (LongTails.Proofs.AffineMomentParameters.sampleSize_pos ht)).trans (homean y)
      have hG : Measurable (fun ξ : Fin (sampleSize t) → Ω =>
          (1 / (sampleSize t : ℝ)) • ∑ i, oracle y (ξ i)) := by fun_prop
      have hi := LongTails.Proofs.AffineMomentCoupling.advance_energy_mgf
        (P := Measure.pi fun _ : Fin (sampleSize t) => P) ht u hu hs hsm hmin hzero hlip
        s.1 ha.2.1 s.2.1 ha.2.2.1 ha.2.2.2.1 s.2.2.2.1 hpilot hG
        (LongTails.Proofs.PowerMirrorMoments.finite_mean_integrable (hoi y) (sampleSize t))
        hraw.1 hmean hraw.2
      simpa only [increment, ha, hphase, and_self, ↓reduceIte, next, stateEnergy,
        OracleTemplate.RobustGeneralized.meanBlock, OracleTemplate.RobustGeneralized.sampleReplies,
        Nat.zero_add, Fin.isLt, ↓reduceDIte] using hi
    · simp [increment, hphase]
  · simp [increment, ha]

omit [CompleteSpace E] in
lemma accumulated_mgf (t : Tuning) {f : E → ℝ} (hf : Measurable f)
    {g : E → E} (hg : Measurable g) (u : E)
    {oracle : E → Ω → E} (ho : Measurable (Function.uncurry oracle))
    (hstep : ∀ s : ProofState E,
      Integrable (fun ξ => Real.exp (increment t f g u oracle (sampleSize t) s ξ))
        (Measure.pi fun _ : Fin (sampleSize t) => P) ∧
      (∫ ξ, Real.exp (increment t f g u oracle (sampleSize t) s ξ)
        ∂Measure.pi (fun _ : Fin (sampleSize t) => P)) ≤ 1)
    (m : ℕ) (s : ProofState E) :
    Integrable (fun ξ => Real.exp (OracleTemplate.StochasticGeneralized.accumulated
      (fun _ => sampleSize t) (next t g oracle) (increment t f g u oracle) m s ξ))
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, Real.exp (OracleTemplate.StochasticGeneralized.accumulated
      (fun _ => sampleSize t) (next t g oracle) (increment t f g u oracle) m s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 1 := by
  exact OracleTemplate.StochasticGeneralized.accumulated_exp_control P measurable_const
    (measurable_next t hg ho) (measurable_increment t hf hg u ho)
    (fun s => (hstep s).1) (fun s => (hstep s).2) m s

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma accumulated_telescope (t : Tuning) (f : E → ℝ) (g : E → E) (u : E)
    (oracle : E → Ω → E) (m : ℕ) (s : ProofState E) (ξ : ℕ → Ω) :
    let v := (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
      (next t g oracle) s ξ m).1
    4 * OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
      (next t g oracle) (increment t f g u oracle) m s ξ =
      (stateEnergy t f u v - (v.1 : ℝ) / iterations t) -
      (stateEnergy t f u s - (s.1 : ℝ) / iterations t) := by
  induction m generalizing s ξ with
  | zero => simp [OracleTemplate.StochasticGeneralized.accumulated,
      OracleTemplate.StochasticGeneralized.blockTrace]
  | succ m ih =>
    rw [OracleTemplate.StochasticGeneralized.blockTrace_start_succ]
    simp only [OracleTemplate.StochasticGeneralized.accumulated]
    have hi := ih (next t g oracle (sampleSize t) s (fun i => ξ i)) (fun i => ξ (sampleSize t + i))
    have hs := increment_telescope t f g u oracle (sampleSize t) s (fun i => ξ i)
    dsimp only at hi ⊢
    linarith

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma trace_invariant {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    (g : E → E) (oracle : E → Ω → E) (m : ℕ) (s : ProofState E) (ξ : ℕ → Ω)
    (hx : ‖s.2.1.1‖ ≤ 4) (hz : ‖s.2.1.2‖ ≤ 1) (hk : s.1 ≤ iterations t) :
    let v := (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
      (next t g oracle) s ξ m).1
    ‖v.2.1.1‖ ≤ 4 ∧ ‖v.2.1.2‖ ≤ 1 ∧ v.1 ≤ iterations t := by
  induction m with
  | zero => exact ⟨hx, hz, hk⟩
  | succ m ih =>
    rw [OracleTemplate.StochasticGeneralized.blockTrace_succ]
    let w := OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t) (next t g oracle) s ξ m
    have hr := next_radius ht g oracle (sampleSize t) w.1 (fun i => w.2 i) ih.1 ih.2.1
    exact ⟨hr.1, hr.2, next_round_bound t g oracle (sampleSize t) w.1 (fun i => w.2 i) ih.2.2⟩

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma trace_accuracy {t : Tuning} (ht : LongTails.Proofs.AffineMomentParameters.Valid t)
    (f : E → ℝ) (g : E → E) (u : E) (hu : ‖u‖ ≤ 1) (oracle : E → Ω → E) (m : ℕ) (ξ : ℕ → Ω)
    (hround : (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
      (next t g oracle) (0, (0, 0), false, 0, false) ξ m).1.1 = iterations t)
    (hacc : OracleTemplate.StochasticGeneralized.accumulated (fun _ => sampleSize t)
      (next t g oracle) (increment t f g u oracle) m (0, (0, 0), false, 0, false) ξ ≤ 2 * confidence t) :
    f (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
      (next t g oracle) (0, (0, 0), false, 0, false) ξ m).1.2.1.1 - f u ≤ t.ε := by
  let v := (OracleTemplate.StochasticGeneralized.blockTrace (fun _ => sampleSize t)
    (next t g oracle) (0, (0, 0), false, 0, false) ξ m).1
  have he := accumulated_telescope t f g u oracle m (0, (0, 0), false, 0, false) ξ
  dsimp only at he
  change _ = (stateEnergy t f u v - (v.1 : ℝ) / iterations t) -
    (stateEnergy t f u (0, (0, 0), false, 0, false) - ((0 : ℕ) : ℝ) / iterations t) at he
  simp only [Nat.cast_zero, zero_div, sub_zero] at he
  change v.1 = iterations t at hround
  have hinit : stateEnergy t f u (0, (0, 0), false, 0, false) ≤ 1 / 2 := by
    simp only [stateEnergy, accumulatedWeight, Nat.cast_zero, zero_mul, zero_div, zero_add,
      energy, zero_sub, norm_neg]
    nlinarith [norm_nonneg u]
  have hk : (v.1 : ℝ) / iterations t = 1 := by
    rw [hround]
    exact div_self (Nat.cast_ne_zero.mpr (LongTails.Proofs.AffineMomentParameters.iterations_pos ht).ne')
  rw [hk] at he
  apply LongTails.Proofs.AffineMomentParameters.final_accuracy ht
  have hD := energy_nonneg u v.2.1.2
  have hl := LongTails.Proofs.AffineMomentParameters.confidence_ge_one ht
  change accumulatedWeight t (iterations t) * (f v.2.1.1 - f u) ≤ 16 * confidence t
  dsimp [stateEnergy] at he hinit
  change v.1 = iterations t at hround
  rw [hround] at he
  nlinarith

end LongTails.Proofs.AffineMomentProcess
