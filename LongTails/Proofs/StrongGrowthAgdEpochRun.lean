import LongTails.Proofs.StrongGrowthAgdEpoch
import LongTails.Proofs.StrongGrowthAgdDrift

namespace LongTails.Proofs.StrongGrowthAgdEpochRun

open MeasureTheory LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdMoments LongTails.Proofs.StrongGrowthAgdMeasurable
  LongTails.Proofs.StrongGrowthAgdWeights LongTails.Proofs.StrongGrowthAgdModel
  LongTails.Proofs.StrongGrowthAgdEpochEnd LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdEpoch LongTails.Proofs.StrongGrowthAgdBlocks
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable (cfg : Config) (x0 : E) (g : E → Ω → E) (f : E → ℝ) {L ρ κ Δ εi : ℝ}

structure Hyps (p : Measure Ω) (L ρ κ Δ εi : ℝ) : Prop where
  hb : 0 < cfg.b
  h : Hyp f L ρ
  ho : OracleHyp g (gradient f) p κ
  hκ : 1 ≤ κ
  hc : CfgHyp cfg
  hη : cfg.η = 1 / (8 * L)
  hθ8 : cfg.θ ≤ 1 / 8
  hδ : (κ - 1) / cfg.b ≤ 1 / 800
  hηf : cfg.ηf = 1 / L
  hΔ : ∀ x, f x0 - f x ≤ Δ
  hΔ0 : 0 ≤ Δ
  hKθ : 1 ≤ cfg.θ * cfg.K
  hK2 : (cfg.K : ℝ) * cfg.θ ≤ 2
  hN1 : 0 < cfg.N1
  hm : 1 ≤ cfg.m
  hεi : 0 < εi
  hthr : cfg.thr = 3 / 2 * εi

omit [MeasurableSpace E] [BorelSpace E] in
lemma spectral (h : Hyp f L ρ) (xS : E) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (eig : Fin (Module.finrank ℝ E) → ℝ),
      ∀ j v, ⟪b j, fderiv ℝ (gradient f) xS v⟫ = eig j * ⟪b j, v⟫ := by
  have hs := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric h.hf xS
  refine ⟨hs.eigenvectorBasis rfl, hs.eigenvalues rfl, fun j v => ?_⟩
  simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq,
    ContinuousLinearMap.coe_coe] using hs.eigenvectorBasis_apply_self_apply rfl v j

noncomputable def cStep (ρ : ℝ) : ℝ := (58 / 25 * (cfg.η / cfg.θ) + 8 * cfg.η) * Dm cfg ρ ^ 2
noncomputable def cEnd (ρ : ℝ) : ℝ := 8 * ρ * cfg.B ^ 3 + 18 * cfg.η * Dm cfg ρ ^ 2
noncomputable def cEpoch (ρ : ℝ) : ℝ := cfg.K * cStep cfg ρ + cEnd cfg ρ

noncomputable def gMs (s : State E) : E :=
  gradModel (fderiv ℝ (gradient f) s.xStart) s.xStart (gradient f s.xStart) (ypoint cfg s)

noncomputable def Dblk (sN : State E × E) (ω : Fin cfg.b → Ω) : ℝ :=
  if sN.1.done = false ∧ cfg.pos sN.1.t < cfg.K ∧ sN.1.trig = false then
    cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g sN.1 ω).x - sN.1.x‖ ^ 2 +
      cfg.η / 32 * ‖gMs cfg f sN.1‖ ^ 2
  else 0

noncomputable def Dep (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : ℝ :=
  ∑ t ∈ Finset.range (cfg.Eb - 1), Dblk cfg x0 g f (run (astep cfg x0 g f) sN tail t) (tail t)

def isStart (s : State E) : Prop := s.done = false ∧ s.t % (cfg.N1 * cfg.Eb) = 0

instance (s : State E) : Decidable (isStart cfg s) :=
  inferInstanceAs (Decidable (s.done = false ∧ s.t % (cfg.N1 * cfg.Eb) = 0))

noncomputable def Yep (Δ : ℝ) (sN : State E × E) : ℝ :=
  f sN.1.x - (f x0 - Δ) - (if isStart cfg sN.1 then Δ else 0)

noncomputable def cep (ρ Δ : ℝ) (sN : State E × E) : ℝ :=
  cEpoch cfg ρ + (if isStart cfg sN.1 then Δ else 0)

variable {cfg x0 g f}

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma Dblk_nonneg (hc : CfgHyp cfg) (sN : State E × E) (ω : Fin cfg.b → Ω) : 0 ≤ Dblk cfg x0 g f sN ω := by
  unfold Dblk
  split_ifs
  · have := hc.hη; have := hc.hθ0; positivity
  · exact le_rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma Dep_nonneg (hc : CfgHyp cfg) (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) : 0 ≤ Dep cfg x0 g f sN tail :=
  Finset.sum_nonneg (fun _ _ => Dblk_nonneg hc _ _)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma astep_of_done {sN : State E × E} (hd : sN.1.done = true) (ω : Fin cfg.b → Ω) :
    astep cfg x0 g f sN ω = sN := by
  obtain ⟨s, N⟩ := sN
  unfold astep
  rw [blockStep_of_done cfg x0 g hd, nextN_of_not cfg g f ω (by simp [show s.done = true from hd])]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma run_of_done {sN : State E × E} (hd : sN.1.done = true) (tail : ℕ → (Fin cfg.b → Ω)) (t : ℕ) :
    run (astep cfg x0 g f) sN tail t = sN := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, ih, astep_of_done hd]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma astep_fst (sN : State E × E) (ω : Fin cfg.b → Ω) :
    (astep cfg x0 g f sN ω).1 = blockStep cfg x0 g sN.1 ω := rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma done_mono (sN : State E × E) (ω : Fin cfg.b → Ω) (hd : sN.1.done = true) :
    (astep cfg x0 g f sN ω).1.done = true := by
  rw [astep_fst, blockStep_of_done cfg x0 g hd]; exact hd

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma t_succ_of_not_done (sN : State E × E) (ω : Fin cfg.b → Ω) (hd : (astep cfg x0 g f sN ω).1.done = false) :
    (astep cfg x0 g f sN ω).1.t = sN.1.t + 1 := by
  obtain ⟨s, N⟩ := sN
  rw [astep_fst] at hd ⊢
  by_cases hs : s.done = true
  · rw [blockStep_of_done cfg x0 g hs] at hd; simp [hs] at hd
  have hs' : s.done = false := by simpa using hs
  unfold blockStep batchUpdate restart
  simp only [hs', Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma not_done_of_step {sN : State E × E} {ω : Fin cfg.b → Ω}
    (hd : (astep cfg x0 g f sN ω).1.done = false) : sN.1.done = false := by
  by_contra hcon
  have : sN.1.done = true := by simpa using hcon
  have := done_mono (cfg := cfg) (x0 := x0) (g := g) (f := f) sN ω this
  rw [this] at hd; exact Bool.noConfusion hd

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma run_t (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) (t : ℕ)
    (hd : (run (astep cfg x0 g f) sN tail t).1.done = false) :
    (run (astep cfg x0 g f) sN tail t).1.t = sN.1.t + t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ] at hd ⊢
    rw [t_succ_of_not_done _ _ hd, ih (not_done_of_step hd)]
    ring

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma run_done_of_done (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) {t t' : ℕ} (htt : t ≤ t')
    (hd : (run (astep cfg x0 g f) sN tail t).1.done = true) :
    (run (astep cfg x0 g f) sN tail t').1.done = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htt
  clear htt
  induction k with
  | zero => simpa using hd
  | succ k ih => rw [← add_assoc, run_succ]; exact done_mono _ _ ih

omit [BorelSpace E] [MeasurableSpace E] [MeasurableSpace Ω] in
lemma run_inv (hc : CfgHyp cfg) (h : Hyp f L ρ) {sN : State E × E} (hinv : Inv cfg x0 f ρ sN)
    (tail : ℕ → (Fin cfg.b → Ω)) (t : ℕ) : Inv cfg x0 f ρ (run (astep cfg x0 g f) sN tail t) := by
  induction t with
  | zero => exact hinv
  | succ t ih => rw [run_succ]; exact inv_preserved cfg x0 g f ρ hc h ih _

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [FiniteDimensional ℝ E] in
lemma blockStep_not_last {s : State E} (hd : s.done = false) (hlt : cfg.pos s.t + 1 < cfg.Eb)
    (ω : Fin cfg.b → Ω) :
    (blockStep cfg x0 g s ω).done = false ∧ (blockStep cfg x0 g s ω).xStart = s.xStart ∧
      (blockStep cfg x0 g s ω).t = s.t + 1 := by
  by_cases hk : cfg.pos s.t < cfg.K
  · by_cases htr : s.trig = true
    · rw [blockStep_frozen cfg x0 g hd hk htr]; exact ⟨hd, rfl, rfl⟩
    · rw [blockStep_agd cfg x0 g hd hk (by simpa using htr)]; exact ⟨hd, rfl, rfl⟩
  · by_cases hkE : cfg.pos s.t = cfg.K
    · rw [blockStep_gd cfg x0 g hd hkE]; exact ⟨hd, rfl, rfl⟩
    · rw [blockStep_val cfg x0 g hd (by omega) hlt]; exact ⟨hd, rfl, rfl⟩

variable (cfg) in
lemma pos_add_of_zero {t0 t : ℕ} (h0 : cfg.pos t0 = 0) (ht : t < cfg.Eb) : cfg.pos (t0 + t) = t := by
  unfold Config.pos at *
  rw [Nat.add_mod, h0, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ht]

section integrability

variable (H : Hyps cfg x0 g f p L ρ κ Δ εi)
include H

omit [IsProbabilityMeasure p] in
lemma measurable_astep' : Measurable (Function.uncurry (astep cfg x0 g f)) :=
  measurable_astep cfg x0 g f H.h H.ho.meas

lemma W_run_integrable (sN : State E × E) (t : ℕ) :
    Integrable (fun tail => W x0 (run (astep cfg x0 g f) sN tail t))
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) := by
  obtain ⟨A, C, hA, hC, hAC⟩ := W_astep_bound cfg x0 g f H.hb H.h H.ho H.hκ H.hc
  exact run_dominated (astep cfg x0 g f) sN (Measure.pi fun _ : Fin cfg.b => p) (measurable_astep' H)
    (W x0) (W_measurable x0) (W_nonneg x0) A C (by linarith)
    (W_astep_integrable cfg x0 g f H.hb H.h H.ho H.hc) hAC t

lemma integrable_of_le_W (F : State E × E → ℝ) (hF : Measurable F) (C : ℝ)
    (hbd : ∀ sN, |F sN| ≤ C * W x0 sN) (sN : State E × E) (t : ℕ) :
    Integrable (fun tail => F (run (astep cfg x0 g f) sN tail t))
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) :=
  ((W_run_integrable H sN t).const_mul C).mono'
    (hF.comp (run_measurable _ sN (measurable_astep' H) t)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun tail => by rw [Real.norm_eq_abs]; exact hbd _)

omit [IsProbabilityMeasure p] [BorelSpace E] in
lemma gMs_sq_le (s : State E) (N : E) :
    ‖gMs cfg f s‖ ^ 2 ≤ (3 * ‖gradient f x0‖ ^ 2 + 30 * L ^ 2) * W x0 (s, N) := by
  have h1 := gradModel_norm_le f H.h (xS := s.xStart) (ypoint cfg s)
  have h2 : ‖gradient f s.xStart‖ ≤ ‖gradient f x0‖ + L * ‖s.xStart - x0‖ := by
    have := H.h.lip s.xStart x0
    have h3 := norm_sub_norm_le (gradient f s.xStart) (gradient f x0)
    linarith
  have h3 : ‖ypoint cfg s - s.xStart‖ ≤ ‖ypoint cfg s - x0‖ + ‖s.xStart - x0‖ := by
    have e : ypoint cfg s - s.xStart = (ypoint cfg s - x0) - (s.xStart - x0) := by abel
    rw [e]; exact norm_sub_le _ _
  have h4 := ypoint_sub_sq_le cfg x0 H.hc s
  have hL := H.h.hL
  have hW := W_pos x0 (s, N)
  unfold gMs at *
  have hg : ‖gradModel (fderiv ℝ (gradient f) s.xStart) s.xStart (gradient f s.xStart) (ypoint cfg s)‖ ≤
      ‖gradient f x0‖ + 2 * L * ‖s.xStart - x0‖ + L * ‖ypoint cfg s - x0‖ := by
    nlinarith [norm_nonneg (ypoint cfg s - s.xStart)]
  have hsq : (‖gradient f x0‖ + 2 * L * ‖s.xStart - x0‖ + L * ‖ypoint cfg s - x0‖) ^ 2 ≤
      3 * ‖gradient f x0‖ ^ 2 + 12 * L ^ 2 * ‖s.xStart - x0‖ ^ 2 + 3 * L ^ 2 * ‖ypoint cfg s - x0‖ ^ 2 := by
    nlinarith [sq_nonneg (‖gradient f x0‖ - 2 * L * ‖s.xStart - x0‖),
      sq_nonneg (‖gradient f x0‖ - L * ‖ypoint cfg s - x0‖),
      sq_nonneg (2 * L * ‖s.xStart - x0‖ - L * ‖ypoint cfg s - x0‖)]
  have hn0 : 0 ≤ ‖gradient f x0‖ + 2 * L * ‖s.xStart - x0‖ + L * ‖ypoint cfg s - x0‖ := by positivity
  have h5 : ‖gradModel (fderiv ℝ (gradient f) s.xStart) s.xStart (gradient f s.xStart) (ypoint cfg s)‖ ^ 2 ≤
      (‖gradient f x0‖ + 2 * L * ‖s.xStart - x0‖ + L * ‖ypoint cfg s - x0‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg 2
  unfold W at hW ⊢
  simp only at hW ⊢
  nlinarith [sq_nonneg L, sq_nonneg ‖gradient f x0‖, sq_nonneg ‖s.x - x0‖, sq_nonneg ‖s.xPrev - x0‖,
    sq_nonneg ‖s.xStart - x0‖, sq_nonneg ‖s.glast‖, sq_nonneg ‖s.ybar‖, sq_nonneg ‖N‖,
    mul_nonneg (sq_nonneg L) (sq_nonneg ‖s.xStart - x0‖), mul_nonneg (sq_nonneg L) (sq_nonneg ‖s.x - x0‖),
    mul_nonneg (sq_nonneg L) (sq_nonneg ‖s.xPrev - x0‖)]

omit [IsProbabilityMeasure p] [BorelSpace E] in
lemma Dblk_abs_le (sN : State E × E) (ω : Fin cfg.b → Ω) :
    |Dblk cfg x0 g f sN ω| ≤
      (cfg.θ / cfg.η / 8 + cfg.η / 32 * (3 * ‖gradient f x0‖ ^ 2 + 30 * L ^ 2)) *
        (W x0 sN + W x0 (astep cfg x0 g f sN ω)) := by
  have hθη : 0 ≤ cfg.θ / cfg.η / 16 := by have := H.hc.hη; have := H.hc.hθ0; positivity
  have hη := H.hc.hη
  have hWs := W_nonneg x0 sN
  have hWs' := W_nonneg x0 (astep cfg x0 g f sN ω)
  have hg := gMs_sq_le H sN.1 sN.2
  have hL2 : 0 ≤ 3 * ‖gradient f x0‖ ^ 2 + 30 * L ^ 2 := by positivity
  rw [abs_of_nonneg (Dblk_nonneg H.hc _ _)]
  unfold Dblk
  split_ifs with hcond
  · have hdd : ‖(blockStep cfg x0 g sN.1 ω).x - sN.1.x‖ ^ 2 ≤
        2 * W x0 (astep cfg x0 g f sN ω) + 2 * W x0 sN := by
      have e : (blockStep cfg x0 g sN.1 ω).x - sN.1.x = ((blockStep cfg x0 g sN.1 ω).x - x0) - (sN.1.x - x0) := by abel
      rw [e]
      have := norm_sub_sq_le_two ((blockStep cfg x0 g sN.1 ω).x - x0) (sN.1.x - x0)
      unfold W astep; simp only
      nlinarith [sq_nonneg ‖(blockStep cfg x0 g sN.1 ω).xPrev - x0‖, sq_nonneg ‖(blockStep cfg x0 g sN.1 ω).xStart - x0‖,
        sq_nonneg ‖(blockStep cfg x0 g sN.1 ω).glast‖, sq_nonneg ‖(blockStep cfg x0 g sN.1 ω).ybar‖,
        sq_nonneg ‖nextN cfg g f sN ω‖, sq_nonneg ‖sN.1.xPrev - x0‖, sq_nonneg ‖sN.1.xStart - x0‖,
        sq_nonneg ‖sN.1.glast‖, sq_nonneg ‖sN.1.ybar‖, sq_nonneg ‖sN.2‖]
    nlinarith [mul_le_mul_of_nonneg_left hdd hθη, mul_le_mul_of_nonneg_left hg (by positivity : (0:ℝ) ≤ cfg.η / 32),
      mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ cfg.η / 32) hL2) hWs']
  · have hθ := H.hc.hθ0
    exact mul_nonneg (by positivity) (add_nonneg hWs hWs')

omit [IsProbabilityMeasure p] in
lemma gMs_measurable : Measurable (fun s : State E => gMs cfg f s) := by
  unfold gMs gradModel
  have hgc : Continuous (gradient f) := H.h.gradDiff.continuous
  have hfc : Continuous (fderiv ℝ (gradient f)) :=
    (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one H.h.hf).continuous_fderiv one_ne_zero
  have h1 : Continuous (fun q : E × E => gradient f q.1 + fderiv ℝ (gradient f) q.1 (q.2 - q.1)) := by
    fun_prop
  exact h1.measurable.comp (measurable_xStart.prodMk (measurable_ypoint cfg))

omit [IsProbabilityMeasure p] in
lemma Dblk_measurable : Measurable (Function.uncurry (Dblk cfg x0 g f)) := by
  unfold Function.uncurry Dblk
  have hT : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.t) :=
    measurable_t.comp (measurable_fst.comp measurable_fst)
  have hD : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.done) :=
    measurable_done.comp (measurable_fst.comp measurable_fst)
  have hTr : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.trig) :=
    measurable_trig.comp (measurable_fst.comp measurable_fst)
  have hset : MeasurableSet {z : (State E × E) × (Fin cfg.b → Ω) |
      z.1.1.done = false ∧ cfg.pos z.1.1.t < cfg.K ∧ z.1.1.trig = false} := by
    refine MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false}))) ?_
    exact MeasurableSet.inter (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n < cfg.K})))
      (hTr (MeasurableSet.of_discrete (s := {false})))
  refine Measurable.ite hset ?_ measurable_const
  have hbs : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => blockStep cfg x0 g z.1.1 z.2) :=
    (measurable_blockStep cfg x0 H.ho.meas).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hx : Measurable (fun z : (State E × E) × (Fin cfg.b → Ω) => z.1.1.x) :=
    measurable_x.comp (measurable_fst.comp measurable_fst)
  refine Measurable.add ?_ ?_
  · exact (((measurable_x.comp hbs).sub hx).norm.pow_const 2).const_mul _
  · exact (((gMs_measurable H).comp (measurable_fst.comp measurable_fst)).norm.pow_const 2).const_mul _

lemma Dblk_run_integrable (sN : State E × E) (t : ℕ) :
    Integrable (fun tail => Dblk cfg x0 g f (run (astep cfg x0 g f) sN tail t) (tail t))
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) := by
  have h1 := W_run_integrable H sN t
  have h2 := W_run_integrable H sN (t + 1)
  refine ((h1.add h2).const_mul
    (cfg.θ / cfg.η / 8 + cfg.η / 32 * (3 * ‖gradient f x0‖ ^ 2 + 30 * L ^ 2))).mono' ?_
    (Filter.Eventually.of_forall fun tail => ?_)
  · exact ((Dblk_measurable H).comp ((run_measurable _ sN (measurable_astep' H) t).prodMk
      (measurable_pi_apply t))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    have := Dblk_abs_le H (run (astep cfg x0 g f) sN tail t) (tail t)
    show _ ≤ _ * (W x0 (run (astep cfg x0 g f) sN tail t) + W x0 (run (astep cfg x0 g f) sN tail (t + 1)))
    rw [run_succ]
    exact this

end integrability

section epoch

variable (H : Hyps cfg x0 g f p L ρ κ Δ εi)
include H

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma cStep_nonneg : 0 ≤ cStep cfg ρ := by
  unfold cStep; have := H.hc.hη; have := H.hc.hθ0; positivity

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma cEnd_nonneg : 0 ≤ cEnd cfg ρ := by
  unfold cEnd; have := H.hc.hη; have := H.h.hρ; have := H.hc.hB; positivity

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma cEpoch_nonneg : 0 ≤ cEpoch cfg ρ := by
  unfold cEpoch; have := cStep_nonneg H; have := cEnd_nonneg H; positivity

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] [IsProbabilityMeasure p] H in
lemma Psi_start {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) {s : State E}
    (h1 : s.xPrev = s.x) (h2 : s.glast = 0) : Psi cfg f b eig s.x s = f s.x := by
  unfold Psi
  rw [h1, sub_self, h2, norm_zero]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
  exact Phi_start _ _ _ _ _

theorem epoch_ineq {sN : State E × E} (hinv : Inv cfg x0 f ρ sN) (hpos : cfg.pos sN.1.t = 0) :
    ∫ tail, (Yep cfg x0 f Δ (run (astep cfg x0 g f) sN tail cfg.Eb) + Dep cfg x0 g f sN tail)
        ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) ≤
      Yep cfg x0 f Δ sN + cep cfg ρ Δ sN := by
  obtain ⟨s, N⟩ := sN
  have hpos' : cfg.pos s.t = 0 := hpos
  have hEb : 1 < cfg.Eb := Eb_gt cfg (by have := H.hc.hK; omega)
  have hKE : cfg.K < cfg.Eb := K_lt_Eb cfg
  have hKE2 : cfg.K + 1 < cfg.Eb := by have := H.hm; unfold Config.Eb; omega
  have hcE := cEpoch_nonneg H
  by_cases hd : s.done = true
  · have hrun : ∀ tail t, run (astep cfg x0 g f) (s, N) tail t = (s, N) := fun tail t => run_of_done hd tail t
    have hD : ∀ tail, Dep cfg x0 g f (s, N) tail = 0 := by
      intro tail
      unfold Dep
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hrun]
      unfold Dblk
      rw [ite_eq_right]
      simp [hd]
    simp only [hrun, hD, add_zero, integral_const, probReal_univ, one_smul]
    unfold cep
    have : (if isStart cfg s then Δ else 0) = 0 := by
      rw [ite_eq_right]; intro h'; exact absurd h'.1 (by simp [hd])
    linarith
  have hd' : s.done = false := by simpa using hd
  set xS := s.x with hxS
  have hxSt : s.xStart = xS := by
    have := (hinv.hagd hd' (by rw [hpos]; exact Nat.zero_le _) (hinv.hfresh hd' hpos)).hstart hpos
    exact this.2.1.symm
  obtain ⟨b, eig, hH⟩ := spectral f H.h xS
  set ν := (Measure.pi fun _ : Fin cfg.b => p) with hν
  let Inv₁ : ℕ → Set (State E × E) := fun t => {sN' | Inv cfg x0 f ρ sN' ∧
    (t < cfg.Eb → sN'.1.t = s.t + t ∧ sN'.1.done = false ∧ sN'.1.xStart = xS)}
  let Y₁ : State E × E → ℝ := fun sN' =>
    if cfg.pos sN'.1.t ≤ cfg.K then Psi cfg f b eig xS sN'.1 else f sN'.1.x
  let c₁ : State E × E → ℝ := fun sN' =>
    if sN'.1.done = false ∧ cfg.pos sN'.1.t < cfg.K ∧ sN'.1.trig = false then cStep cfg ρ
    else if sN'.1.done = false ∧ cfg.pos sN'.1.t = cfg.K then cEnd cfg ρ else 0
  let D₁ : State E × E → (ℕ → (Fin cfg.b → Ω)) → ℝ := fun sN' tail' => Dblk cfg x0 g f sN' (tail' 0)
  have hInv₁ : ∀ t, ∀ sN' ∈ Inv₁ t, ∀ ω, astep cfg x0 g f sN' ω ∈ Inv₁ (t + 1) := by
    intro t sN' hsN' ω
    refine ⟨inv_preserved cfg x0 g f ρ H.hc H.h hsN'.1 ω, fun ht => ?_⟩
    obtain ⟨ht', hd'', hxS'⟩ := hsN'.2 (by omega)
    have hp : cfg.pos sN'.1.t = t := by rw [ht']; exact pos_add_of_zero cfg hpos' (by omega)
    obtain ⟨h1, h2, h3⟩ := blockStep_not_last (cfg := cfg) (x0 := x0) (g := g) hd'' (by omega) ω
    refine ⟨?_, h1, ?_⟩
    · rw [astep_fst, h3, ht']; ring
    · rw [astep_fst, h2, hxS']
  have hs0 : (s, N) ∈ Inv₁ 0 := ⟨hinv, fun _ => ⟨rfl, hd', hxSt⟩⟩
  have hstep := measurable_astep' H
  have hY₁ : Measurable Y₁ := by
    refine Measurable.ite ((measurable_t.comp measurable_fst) (MeasurableSet.of_discrete (s := {n | cfg.pos n ≤ cfg.K}))) ?_ ?_
    · exact (Psi_measurable cfg f).comp measurable_fst
    · exact H.h.hf.continuous.measurable.comp (measurable_x.comp measurable_fst)
  have hc₁ : Measurable c₁ := by
    have hT : Measurable (fun sN' : State E × E => sN'.1.t) := measurable_t.comp measurable_fst
    have hD : Measurable (fun sN' : State E × E => sN'.1.done) := measurable_done.comp measurable_fst
    have hTr : Measurable (fun sN' : State E × E => sN'.1.trig) := measurable_trig.comp measurable_fst
    refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
    · exact MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false})))
        (MeasurableSet.inter (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n < cfg.K})))
          (hTr (MeasurableSet.of_discrete (s := {false}))))
    · exact MeasurableSet.inter (hD (MeasurableSet.of_discrete (s := {false})))
        (hT (MeasurableSet.of_discrete (s := {n | cfg.pos n = cfg.K})))
  have hD₁ : Measurable (Function.uncurry D₁) :=
    (Dblk_measurable H).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  obtain ⟨C, hC0, hCW⟩ := Psi_abs_le_W cfg x0 f H.hc H.h (b := b) (eig := eig) (xS := xS)
  have hfW : ∀ sN' : State E × E, |f sN'.1.x| ≤ (|f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L)) * W x0 sN' := by
    intro sN'
    have h1 := f_sub_abs_le x0 f H.h sN'.1.x
    have h2 : |f sN'.1.x| ≤ |f x0| + |f sN'.1.x - f x0| := by
      have := abs_add_le (f x0) (f sN'.1.x - f x0); rwa [add_sub_cancel] at this
    have h3 : ‖gradient f x0‖ * ‖sN'.1.x - x0‖ ≤ ‖gradient f x0‖ ^ 2 / 2 + ‖sN'.1.x - x0‖ ^ 2 / 2 := by
      nlinarith [sq_nonneg (‖gradient f x0‖ - ‖sN'.1.x - x0‖)]
    have hW := W_pos x0 sN'
    have hWx : ‖sN'.1.x - x0‖ ^ 2 ≤ W x0 sN' := by
      unfold W; nlinarith [sq_nonneg ‖sN'.1.xPrev - x0‖, sq_nonneg ‖sN'.1.xStart - x0‖, sq_nonneg ‖sN'.1.glast‖,
        sq_nonneg ‖sN'.1.ybar‖, sq_nonneg ‖sN'.2‖]
    have hL := H.h.hL
    nlinarith [abs_nonneg (f x0), sq_nonneg ‖gradient f x0‖, sq_nonneg ‖sN'.1.x - x0‖]
  have hY₁W : ∀ sN', |Y₁ sN'| ≤ (C + (|f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L))) * W x0 sN' := by
    intro sN'
    have hW := W_nonneg x0 sN'
    have hA : 0 ≤ |f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L) := by have := H.h.hL; positivity
    simp only [Y₁]
    split_ifs
    · nlinarith [hCW sN', mul_nonneg hA hW]
    · nlinarith [hfW sN', mul_nonneg hC0 hW]
  have hYint : ∀ t, Integrable (fun tail => Y₁ (run (astep cfg x0 g f) (s, N) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    fun t => integrable_of_le_W H Y₁ hY₁ _ hY₁W (s, N) t
  have hc₁W : ∀ sN', |c₁ sN'| ≤ (cStep cfg ρ + cEnd cfg ρ) * W x0 sN' := by
    intro sN'
    have hW := W_pos x0 sN'
    have h1 := cStep_nonneg H
    have h2 := cEnd_nonneg H
    simp only [c₁]
    split_ifs
    · rw [abs_of_nonneg h1]; nlinarith
    · rw [abs_of_nonneg h2]; nlinarith
    · rw [abs_zero]; exact mul_nonneg (add_nonneg h1 h2) (by linarith)
  have hcint : ∀ t, Integrable (fun tail => c₁ (run (astep cfg x0 g f) (s, N) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    fun t => integrable_of_le_W H c₁ hc₁ _ hc₁W (s, N) t
  have hDint : ∀ e, Integrable (fun tail => D₁ (run (astep cfg x0 g f) (s, N) tail (e * 1)) (shift (e * 1) tail))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    simp only [D₁, mul_one, shift, add_zero]
    exact Dblk_run_integrable H (s, N) e
  have hdrift : ∀ e < cfg.Eb - 1, ∀ sN' ∈ Inv₁ (e * 1),
      ∫ tail, (Y₁ (run (astep cfg x0 g f) sN' tail 1) + D₁ sN' tail) ∂(Measure.infinitePi fun _ : ℕ => ν)
        ≤ Y₁ sN' + c₁ sN' := by
    intro e he sN' hsN'
    rw [mul_one] at hsN'
    obtain ⟨hinv', ht', hd'', hxS'⟩ := And.imp_right (fun h' => h' (by omega)) hsN'
    have hp : cfg.pos sN'.1.t = e := by rw [ht']; exact pos_add_of_zero cfg hpos' (by omega)
    have hrw : ∀ tail : ℕ → (Fin cfg.b → Ω), Y₁ (run (astep cfg x0 g f) sN' tail 1) + D₁ sN' tail =
        (fun ω => Y₁ (astep cfg x0 g f sN' ω) + Dblk cfg x0 g f sN' ω) (tail 0) := fun tail => rfl
    simp_rw [hrw]
    have hmeas : Measurable (fun ω => Y₁ (astep cfg x0 g f sN' ω) + Dblk cfg x0 g f sN' ω) :=
      (hY₁.comp (measurable_astep_fun cfg x0 g f H.h H.ho.meas sN')).add
        ((Dblk_measurable H).comp (measurable_const.prodMk measurable_id))
    rw [integral_eval ν _ hmeas]
    obtain ⟨s', N'⟩ := sN'
    simp only at hp hd'' hxS'
    by_cases hk : e < cfg.K
    · have hp1 : cfg.pos (s'.t + 1) = e + 1 := by
        rw [pos_succ_of_lt cfg hEb (by omega), hp]
      by_cases htr : s'.trig = true
      ·
        have hval : ∀ ω, Y₁ (astep cfg x0 g f (s', N') ω) + Dblk cfg x0 g f (s', N') ω = Y₁ (s', N') := by
          intro ω
          simp only [Y₁, Dblk, astep]
          rw [blockStep_frozen cfg x0 g hd'' (by omega) htr]
          simp only [hp1, hp, hk.le, ↓reduceIte, show e + 1 ≤ cfg.K by omega, htr]
          rw [ite_eq_right (by simp)]
          simp [Psi]
        simp_rw [hval]
        simp only [integral_const, probReal_univ, one_smul]
        have : 0 ≤ c₁ (s', N') := by
          simp only [c₁]; split_ifs
          · exact cStep_nonneg H
          · exact cEnd_nonneg H
          · exact le_rfl
        linarith
      · have htr' : s'.trig = false := by simpa using htr
        have hA := hinv'.hagd hd'' (by show cfg.pos s'.t ≤ cfg.K; omega) htr'
        have hval : ∀ ω, Y₁ (astep cfg x0 g f (s', N') ω) + Dblk cfg x0 g f (s', N') ω =
            Psi cfg f b eig xS (blockStep cfg x0 g s' ω) +
              (cfg.θ / cfg.η / 16 * ‖(blockStep cfg x0 g s' ω).x - s'.x‖ ^ 2 +
                cfg.η / 32 * ‖gradModel (fderiv ℝ (gradient f) xS) xS (gradient f xS) (ypoint cfg s')‖ ^ 2) := by
          intro ω
          simp only [Y₁, Dblk, astep, gMs]
          have ht1 : (blockStep cfg x0 g s' ω).t = s'.t + 1 := (blockStep_not_last hd'' (by omega) ω).2.2
          rw [ht1, hp1, ite_eq_left (by omega), ite_eq_left (by exact ⟨hd'', by omega, htr'⟩), hxS']
        simp_rw [hval]
        have hagd := agd_block cfg x0 g f H.hb H.h H.ho H.hκ H.hc H.hη H.hθ8 hH H.hδ hd'' (by omega) htr' hxS' hA
        simp only [Y₁, c₁, hp, hk.le, hk, hd'', htr', and_self, ↓reduceIte]
        unfold cStep
        exact hagd
    · by_cases hkE : e = cfg.K
      · have hp1 : cfg.pos (s'.t + 1) = e + 1 := by
          rw [pos_succ_of_lt cfg hEb (by omega), hp]
        have hval : ∀ ω, Y₁ (astep cfg x0 g f (s', N') ω) + Dblk cfg x0 g f (s', N') ω =
            f (blockStep cfg x0 g s' ω).x := by
          intro ω
          simp only [Y₁, Dblk, astep]
          have ht1 : (blockStep cfg x0 g s' ω).t = s'.t + 1 := (blockStep_not_last hd'' (by omega) ω).2.2
          rw [ht1, hp1, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
        simp_rw [hval]
        have hlast := hinv'.hlast hd'' (by show cfg.pos s'.t ≤ cfg.K; omega)
        simp only at hlast
        rw [hxS'] at hlast
        have hgd := gd_block cfg x0 g f H.hb H.h H.ho H.hκ H.hc H.hη hH H.hδ hd'' (by rw [hp, hkE]) hxS' H.hηf hlast
        simp only [Y₁, c₁, hp, hkE, le_refl, ↓reduceIte, lt_self_iff_false, false_and, and_false, and_self,
          hd'']
        unfold cEnd
        linarith [hgd]
      ·
        have hK' : cfg.K < e := by omega
        have hp1 : cfg.pos (s'.t + 1) = e + 1 := by
          rw [pos_succ_of_lt cfg hEb (by omega), hp]
        have hval : ∀ ω, Y₁ (astep cfg x0 g f (s', N') ω) + Dblk cfg x0 g f (s', N') ω = Y₁ (s', N') := by
          intro ω
          simp only [Y₁, Dblk, astep]
          rw [blockStep_val cfg x0 g hd'' (by rw [hp]; exact hK') (by rw [hp]; omega)]
          simp only [hp1, hp, ite_eq_right (by omega : ¬ e + 1 ≤ cfg.K), ite_eq_right (by omega : ¬ e ≤ cfg.K)]
          rw [ite_eq_right (by omega), add_zero]
        simp_rw [hval]
        simp only [integral_const, probReal_univ, one_smul]
        have : 0 ≤ c₁ (s', N') := by
          simp only [c₁]; split_ifs
          · exact cStep_nonneg H
          · exact cEnd_nonneg H
          · exact le_rfl
        linarith
  have hdr := drift (astep cfg x0 g f) (s, N) ν hstep 1 Inv₁ hInv₁ hs0 Y₁ c₁ D₁ hY₁ hc₁ hD₁ hYint hcint hDint
    (cfg.Eb - 1) hdrift
  simp only [mul_one] at hdr
  have hY0 : Y₁ (s, N) = f xS := by
    simp only [Y₁, hpos, Nat.zero_le, ↓reduceIte]
    exact Psi_start b eig ((hinv.hagd hd' (by rw [hpos]; exact Nat.zero_le _) (hinv.hfresh hd' hpos)).hstart hpos).1
      ((hinv.hagd hd' (by rw [hpos]; exact Nat.zero_le _) (hinv.hfresh hd' hpos)).hstart hpos).2.2.1
  have hDsum : ∀ tail, Dep cfg x0 g f (s, N) tail =
      ∑ t ∈ Finset.range (cfg.Eb - 1), D₁ (run (astep cfg x0 g f) (s, N) tail t) (shift t tail) := by
    intro tail; rfl
  have hcsum : ∀ tail, ∑ t ∈ Finset.range (cfg.Eb - 1), c₁ (run (astep cfg x0 g f) (s, N) tail t) ≤ cEpoch cfg ρ := by
    intro tail
    have hcK : ∀ t ∈ Finset.range (cfg.Eb - 1), c₁ (run (astep cfg x0 g f) (s, N) tail t) ≤
        (if t < cfg.K then cStep cfg ρ else 0) + (if t = cfg.K then cEnd cfg ρ else 0) := by
      intro t ht
      have ht' : t < cfg.Eb - 1 := Finset.mem_range.mp ht
      have hmem := run_mem_inv (astep cfg x0 g f) (s, N) Inv₁ hInv₁ hs0 tail t
      obtain ⟨_, htt, hdd, _⟩ := And.imp_right (fun h' => h' (by omega)) hmem
      have hp : cfg.pos (run (astep cfg x0 g f) (s, N) tail t).1.t = t := by
        rw [htt]; exact pos_add_of_zero cfg hpos' (by omega)
      simp only [c₁, hp]
      have h1 := cStep_nonneg H
      have h2 := cEnd_nonneg H
      split_ifs <;> first | omega | linarith
    refine (Finset.sum_le_sum hcK).trans ?_
    rw [Finset.sum_add_distrib]
    have hK1 : ∑ t ∈ Finset.range (cfg.Eb - 1), (if t < cfg.K then cStep cfg ρ else 0) = cfg.K * cStep cfg ρ := by
      rw [← Finset.sum_filter]
      have : (Finset.range (cfg.Eb - 1)).filter (fun t => t < cfg.K) = Finset.range cfg.K := by
        ext t; simp only [Finset.mem_filter, Finset.mem_range]; constructor
        · intro h'; exact h'.2
        · intro h'; exact ⟨by omega, h'⟩
      rw [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hK2 : ∑ t ∈ Finset.range (cfg.Eb - 1), (if t = cfg.K then cEnd cfg ρ else 0) = cEnd cfg ρ := by
      rw [Finset.sum_ite_eq']
      rw [ite_eq_left]
      exact Finset.mem_range.mpr (by have := H.hm; unfold Config.Eb at *; omega)
    rw [hK1, hK2]
    unfold cEpoch
    exact le_rfl
  have hDint1 : ∀ t, Integrable (fun tail => D₁ (run (astep cfg x0 g f) (s, N) tail t) (shift t tail))
      (Measure.infinitePi fun _ : ℕ => ν) := fun t => by
    have := hDint t
    rwa [mul_one] at this
  have hDint' : Integrable (fun tail => Dep cfg x0 g f (s, N) tail) (Measure.infinitePi fun _ : ℕ => ν) := by
    simp_rw [hDsum]
    exact integrable_finsetSum _ (fun t _ => hDint1 t)
  have hcint' : Integrable (fun tail => ∑ t ∈ Finset.range (cfg.Eb - 1), c₁ (run (astep cfg x0 g f) (s, N) tail t))
      (Measure.infinitePi fun _ : ℕ => ν) :=
    integrable_finsetSum _ (fun t _ => hcint t)
  have hsumD : ∑ t ∈ Finset.range (cfg.Eb - 1),
      ∫ tail, D₁ (run (astep cfg x0 g f) (s, N) tail t) (shift t tail) ∂(Measure.infinitePi fun _ : ℕ => ν) =
      ∫ tail, Dep cfg x0 g f (s, N) tail ∂(Measure.infinitePi fun _ : ℕ => ν) := by
    simp_rw [hDsum]
    rw [integral_finsetSum _ (fun t _ => hDint1 t)]
  have hsumc : ∑ t ∈ Finset.range (cfg.Eb - 1),
      ∫ tail, c₁ (run (astep cfg x0 g f) (s, N) tail t) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤ cEpoch cfg ρ := by
    rw [← integral_finsetSum _ (fun t _ => hcint t)]
    calc _ ≤ ∫ tail, cEpoch cfg ρ ∂(Measure.infinitePi fun _ : ℕ => ν) :=
          integral_mono hcint' (integrable_const _) (fun tail => hcsum tail)
      _ = cEpoch cfg ρ := by simp
  have hYlast : ∀ tail, Yep cfg x0 f Δ (run (astep cfg x0 g f) (s, N) tail cfg.Eb) ≤
      Y₁ (run (astep cfg x0 g f) (s, N) tail (cfg.Eb - 1)) - (f x0 - Δ) := by
    intro tail
    have hmem := run_mem_inv (astep cfg x0 g f) (s, N) Inv₁ hInv₁ hs0 tail (cfg.Eb - 1)
    obtain ⟨hinv'', htt, hdd, _⟩ := And.imp_right (fun h' => h' (by omega)) hmem
    set sL := run (astep cfg x0 g f) (s, N) tail (cfg.Eb - 1) with hsL
    have hp : cfg.pos sL.1.t = cfg.Eb - 1 := by rw [htt]; exact pos_add_of_zero cfg hpos' (by omega)
    have hEb' : cfg.Eb = cfg.Eb - 1 + 1 := by omega
    have hrun : run (astep cfg x0 g f) (s, N) tail cfg.Eb = astep cfg x0 g f sL (tail (cfg.Eb - 1)) := by
      rw [hsL]
      conv_lhs => rw [hEb']
      exact run_succ _ _ _ _
    rw [hrun]
    have hY : Y₁ sL = f sL.1.x := by
      simp only [Y₁, hp]; rw [ite_eq_right (by omega)]
    rw [hY]
    unfold Yep astep
    simp only
    rw [blockStep_last cfg x0 g hdd (by rw [hp]; omega) (by rw [hp]; omega)]
    have hfl := H.hΔ sL.1.x
    by_cases hacc : ¬ sL.1.trig = true ∧ 2 * (if sL.1.trig = true then sL.1.vCount
        else sL.1.vCount + (if ‖bmean cfg g sL.1.ybar (tail (cfg.Eb - 1))‖ ≤ cfg.thr then 1 else 0)) > cfg.m
    · rw [ite_eq_left hacc]
      simp [isStart]
    · rw [ite_eq_right hacc]
      unfold restart
      by_cases h5 : (sL.1.t + 1) % (cfg.N1 * cfg.Eb) = 0
      · simp [isStart, h5, hdd]
        try linarith
      · simp [isStart, h5, hdd]
        try linarith
  have hYint' := hYint (cfg.Eb - 1)
  have hYepint : Integrable (fun tail => Yep cfg x0 f Δ (run (astep cfg x0 g f) (s, N) tail cfg.Eb))
      (Measure.infinitePi fun _ : ℕ => ν) := by
    have hm : Measurable (Yep cfg x0 f Δ) := by
      unfold Yep isStart
      refine ((H.h.hf.continuous.measurable.comp (measurable_x.comp measurable_fst)).sub measurable_const).sub ?_
      refine Measurable.ite ?_ measurable_const measurable_const
      exact MeasurableSet.inter ((measurable_done.comp measurable_fst) (MeasurableSet.of_discrete (s := {false})))
        ((measurable_t.comp measurable_fst) (MeasurableSet.of_discrete (s := {n | n % (cfg.N1 * cfg.Eb) = 0})))
    refine integrable_of_le_W H _ hm (|f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L) + |f x0 - Δ| + Δ) ?_ (s, N) cfg.Eb
    intro sN'
    have hW := W_pos x0 sN'
    have h1 := hfW sN'
    have hA : 0 ≤ |f x0| + ‖gradient f x0‖ ^ 2 / 2 + (1 / 2 + 3 / 2 * L) := by have := H.h.hL; positivity
    unfold Yep
    have h2 : |(if isStart cfg sN'.1 then Δ else 0)| ≤ Δ := by split_ifs <;> simp [abs_of_nonneg H.hΔ0, H.hΔ0]
    have h3 := abs_sub (f sN'.1.x - (f x0 - Δ)) (if isStart cfg sN'.1 then Δ else 0)
    have h4 := abs_sub (f sN'.1.x) (f x0 - Δ)
    have t1 : |f x0 - Δ| ≤ |f x0 - Δ| * W x0 sN' := le_mul_of_one_le_right (abs_nonneg _) hW
    have t2 : Δ ≤ Δ * W x0 sN' := le_mul_of_one_le_right H.hΔ0 hW
    linarith
  have hmain : ∫ tail, Yep cfg x0 f Δ (run (astep cfg x0 g f) (s, N) tail cfg.Eb) ∂(Measure.infinitePi fun _ : ℕ => ν) ≤
      ∫ tail, Y₁ (run (astep cfg x0 g f) (s, N) tail (cfg.Eb - 1)) ∂(Measure.infinitePi fun _ : ℕ => ν) - (f x0 - Δ) := by
    have hR : Integrable (fun tail => Y₁ (run (astep cfg x0 g f) (s, N) tail (cfg.Eb - 1)) - (f x0 - Δ))
        (Measure.infinitePi fun _ : ℕ => ν) := hYint'.sub (integrable_const _)
    have := integral_mono hYepint hR hYlast
    rwa [integral_sub hYint' (integrable_const _), integral_const, probReal_univ, one_smul] at this
  rw [integral_add hYepint hDint']
  have hYs : Yep cfg x0 f Δ (s, N) + cep cfg ρ Δ (s, N) = f xS - (f x0 - Δ) + cEpoch cfg ρ := by
    unfold Yep cep; ring
  rw [hYs]
  linarith [hdr, hsumD, hsumc, hY0, hmain]

end epoch

end LongTails.Proofs.StrongGrowthAgdEpochRun
