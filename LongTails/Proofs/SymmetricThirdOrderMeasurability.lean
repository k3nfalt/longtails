import LongTails.Proofs.SymmetricThirdOrderRound
import LongTails.Proofs.SymmetricThirdOrderEstimation

namespace LongTails.Proofs.SymmetricThirdOrderMeasurability

open MeasureTheory OracleTemplate LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Proofs.SymmetricThirdOrderExecution
open LongTails.Proofs.SymmetricThirdOrderMinimizers
open LongTails.Proofs.SymmetricThirdOrderHessian
open scoped RealInnerProductSpace BigOperators

variable {E Ω X : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] [MeasurableSpace X]

structure MeasurableState (s : X → OuterState E) : Prop where
  weight : Measurable (fun x => (s x).weight)
  point : Measurable (fun x => (s x).point)
  momentum : Measurable (fun x => (s x).momentum)
  grid : Measurable (fun x => (s x).grid)

lemma measurable_outerCenter (δ : ℝ) (s : X → OuterState E) (hs : MeasurableState s) :
    Measurable (fun x => outerCenter δ (s x)) := by
  have hw := hs.weight
  have hx := hs.point
  have hv := hs.momentum
  have hj := hs.grid
  unfold outerCenter LongTails.Algorithms.CompositeCubicAcceleration.center LongTails.Algorithms.CompositeCubicAcceleration.trialWeight
  fun_prop

lemma measurable_gradientPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (x : X → E) (hx : Measurable x) (call : ℕ) :
    Measurable (fun w => QueryPlan.sampledEval oracle (ξ w) (gradientPlan cfg (x w)) call) := by
  simp_rw [gradientPlan_eval]
  have hv : Measurable (fun w => (cfg.tolerance,
      fun (i : Fin cfg.groups) (j : Fin cfg.batch) =>
        (oracle (x w) (ξ w (call + cfg.batch * i.val + j.val))).1)) := by
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (ho.comp (hx.prodMk (hξ _))).fst
  exact (SymmetricThirdOrderEstimation.measurable_gradientPilot (E := E) cfg.groups cfg.batch).comp hv

omit [BorelSpace E] in
set_option maxHeartbeats 800000 in
lemma measurable_hessianPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (x : X → E) (hx : Measurable x) (call : ℕ) :
    Measurable (fun w => QueryPlan.sampledEval oracle (ξ w) (hessianPlan cfg (x w)) call) := by
  simp_rw [hessianPlan_eval]
  have hv : Measurable (fun w => (cfg.σh,
      fun i : Fin cfg.groups => (oracle (x w) (ξ w (call + i.val))).2)) := by
    apply measurable_const.prodMk
    apply Measurable.of_eval
    intro i
    exact (ho.comp (hx.prodMk (hξ _))).snd
  exact (SymmetricThirdOrderEstimation.measurable_hessianPilot (E := E) cfg.groups).comp hv

lemma measurable_meanPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (m : ℕ)
    (x : X → E) (hx : Measurable x) (call : ℕ) :
    Measurable (fun w => QueryPlan.sampledEval oracle (ξ w) (meanPlan m (x w)) call) := by
  simp_rw [meanPlan_eval]
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i _
  exact (ho.comp (hx.prodMk (hξ _))).fst

lemma measurable_modelGradientPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (c y : X → E) (B : X → E →L[ℝ] E)
    (hc : Measurable c) (hy : Measurable y) (hB : Measurable B) (call : ℕ) :
    Measurable (fun w => QueryPlan.sampledEval oracle (ξ w)
      (modelGradientPlan cfg (c w) (y w) (B w)) call) := by
  simp_rw [modelGradientPlan_eval]
  have hp := measurable_gradientPlan oracle ho ξ hξ cfg y hy call
  have hm := measurable_gradientPlan oracle ho ξ hξ cfg (fun w => c w - (y w - c w))
    (hc.sub (hy.sub hc)) (call + cfg.batch * cfg.groups)
  have hk : Measurable (fun w => kernelGradient (B w) cfg.L cfg.δ (y w - c w)) := by
    unfold kernelGradient
    have heval : Continuous (fun v : (E →L[ℝ] E) × E => v.1 v.2) :=
      continuous_fst.clm_apply continuous_snd
    exact (heval.measurable.comp (hB.prodMk (hy.sub hc))).add
      (((hy.sub hc).norm.pow_const 2 |>.const_mul (8 * cfg.L) |>.add_const cfg.δ).smul (hy.sub hc))
  exact ((hp.add hm).const_smul (1 / 2 : ℝ)).add hk

lemma measurable_innerPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (c : X → E) (B : X → E →L[ℝ] E) (hc : Measurable c) (hB : Measurable B)
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫) (hpos : ∀ p v, 0 ≤ ⟪v, B p v⟫)
    (J call : ℕ) :
    Measurable (fun w => QueryPlan.sampledEval oracle (ξ w)
      (innerPlan cfg (c w) (B w) J cfg.x0) call) := by
  simp_rw [innerPlan_eval_iterate]
  apply SymmetricThirdOrderInner.measurable_innerIterate cfg.C cfg.x0 hC hne hconv c B hL hδ
    _ hc hB _ hsym hpos
  intro j
  exact measurable_modelGradientPlan oracle ho (fun w : X × E => ξ w.1)
    (fun i => (hξ i).comp measurable_fst) cfg (fun w => c w.1) Prod.snd (fun w => B w.1)
    (hc.comp measurable_fst) measurable_snd (hB.comp measurable_fst) _

lemma measurable_cleanupPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C) (hδ : 0 < cfg.δ)
    (c y : X → E) (B : X → E →L[ℝ] E)
    (hc : Measurable c) (hy : Measurable y) (hB : Measurable B)
    (hsym : ∀ p x y, ⟪x, B p y⟫ = ⟪B p x, y⟫) (call : ℕ) :
    Measurable (fun w => QueryPlan.sampledEval oracle (ξ w)
      (cleanupPlan cfg (c w) (y w) (B w)) call) := by
  let qg := fun w => QueryPlan.sampledEval oracle (ξ w) (modelGradientPlan cfg (c w) (y w) (B w)) call
  let Hp := fun w => QueryPlan.sampledEval oracle (ξ w) (hessianPlan cfg (y w))
    (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups))
  let Hm := fun w => QueryPlan.sampledEval oracle (ξ w) (hessianPlan cfg (c w - (y w - c w)))
    (call + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) + cfg.groups)
  let Hq := fun w => shiftedHessian ((1 / 2 : ℝ) • (Hp w - Hm w) +
    kernelHessian (B w) cfg.L cfg.δ (y w - c w)) 0
  let z := fun w => cleanupPoint cfg.C cfg.x0 (y w) (Hq w) cfg.δ (qg w)
  have hqg : Measurable qg := measurable_modelGradientPlan oracle ho ξ hξ cfg c y B hc hy hB call
  have hHp : Measurable Hp := measurable_hessianPlan oracle ho ξ hξ cfg y hy _
  have hHm : Measurable Hm := measurable_hessianPlan oracle ho ξ hξ cfg _ (hc.sub (hy.sub hc)) _
  have hkcont : Continuous (fun v : (E →L[ℝ] E) × E => kernelHessian v.1 cfg.L cfg.δ v.2) := by
    unfold kernelHessian
    fun_prop
  have hk : Measurable (fun w => kernelHessian (B w) cfg.L cfg.δ (y w - c w)) :=
    hkcont.measurable.comp (hB.prodMk (hy.sub hc))
  have hHq : Measurable Hq := continuous_shiftedHessian.measurable.comp
    ((((hHp.sub hHm).const_smul (1 / 2 : ℝ)).add hk).prodMk measurable_const)
  have hHpsym : ∀ w x y, ⟪x, Hp w y⟫ = ⟪Hp w x, y⟫ := by
    intro w x y
    dsimp [Hp]
    rw [hessianPlan_eval]
    exact symmetricHessian_symmetric _ x y
  have hHmsym : ∀ w x y, ⟪x, Hm w y⟫ = ⟪Hm w x, y⟫ := by
    intro w x y
    dsimp [Hm]
    rw [hessianPlan_eval]
    exact symmetricHessian_symmetric _ x y
  have hHqsym : ∀ w x y, ⟪x, Hq w y⟫ = ⟪Hq w x, y⟫ := fun w =>
    SymmetricThirdOrderRound.cleanupHessian_symmetric (B w) (Hp w) (Hm w) cfg.L cfg.δ
      (y w - c w) (hsym w) (hHpsym w) (hHmsym w)
  have hHqpos : ∀ w v, 0 ≤ ⟪v, Hq w v⟫ := by
    intro w v
    simpa only [real_inner_comm] using shiftedHessian_nonneg
      ((1 / 2 : ℝ) • (Hp w - Hm w) + kernelHessian (B w) cfg.L cfg.δ (y w - c w)) 0 v
  have hz : Measurable z := measurable_cleanupPoint cfg.C cfg.x0 hC hne hconv y qg Hq hδ
    hy hqg hHq hHqsym hHqpos
  have heval : Continuous (fun v : (E →L[ℝ] E) × E => v.1 v.2) :=
    continuous_fst.clm_apply continuous_snd
  simp_rw [cleanupPlan_eval]
  change Measurable (fun w => (z w, -qg w - Hq w (z w - y w) - cfg.δ • (z w - y w)))
  exact hz.prodMk ((hqg.neg.sub (heval.measurable.comp (hHq.prodMk (hz.sub hy)))).sub
    ((hz.sub hy).const_smul cfg.δ))

lemma measurable_outerAdvance (cfg : Config E)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (s : X → OuterState E) (hs : MeasurableState s) (z g : X → E)
    (hz : Measurable z) (hg : Measurable g) :
    MeasurableState (fun w => outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop
      (s w) (z w) (g w)) := by
  classical
  let μ := fun w => cfg.δ * 4 ^ (s w).grid
  let a := fun w => LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (μ w) (s w).weight
  let lam := fun w => cfg.δ + 8 * cfg.L * ‖z w - outerCenter cfg.δ (s w)‖ ^ 2
  let β := fun w => min 1 (μ w / lam w)
  let A := fun w => (s w).weight + β w * a w
  have hw := hs.weight
  have hx := hs.point
  have hv := hs.momentum
  have hj := hs.grid
  have hc := measurable_outerCenter cfg.δ s hs
  have hμ : Measurable μ := by dsimp [μ]; fun_prop
  have ha : Measurable a := by dsimp [a]; unfold LongTails.Algorithms.CompositeCubicAcceleration.trialWeight; fun_prop
  have hl : Measurable lam := by dsimp [lam]; fun_prop
  have hβ : Measurable β := by dsimp [β]; fun_prop
  have hA : Measurable A := hw.add (hβ.mul ha)
  have hp := measurable_projectPoint cfg.C cfg.x0 hC hne hconv
    (fun w => (s w).momentum - (β w * a w) • g w) (hv.sub ((hβ.mul ha).smul hg))
  have ht : MeasurableSet {w | cfg.threshold ≤ (s w).weight} := measurableSet_le measurable_const hw
  have hd : MeasurableSet {w | lam w ≤ μ w} := measurableSet_le hl hμ
  constructor
  · have hh : Measurable (fun w => if cfg.threshold ≤ (s w).weight then (s w).weight else A w) :=
      Measurable.ite ht hw hA
    convert hh using 1
    funext w
    by_cases h : cfg.threshold ≤ (s w).weight <;> simp [outerAdvance, h, A, β, a, lam, μ]
  · have hn : Measurable (fun w => (A w)⁻¹ •
        (((1 - β w) * (s w).weight) • (s w).point + (β w * ((s w).weight + a w)) • z w)) := by fun_prop
    have hh : Measurable (fun w => if cfg.threshold ≤ (s w).weight then (s w).point else
        (A w)⁻¹ • (((1 - β w) * (s w).weight) • (s w).point + (β w * ((s w).weight + a w)) • z w)) :=
      Measurable.ite ht hx hn
    convert hh using 1
    funext w
    by_cases h : cfg.threshold ≤ (s w).weight <;> simp [outerAdvance, h, A, β, a, lam, μ]
  · have hh : Measurable (fun w => if cfg.threshold ≤ (s w).weight then (s w).momentum else
        projectPoint cfg.C cfg.x0 ((s w).momentum - (β w * a w) • g w)) :=
      Measurable.ite ht hv hp
    convert hh using 1
    funext w
    by_cases h : cfg.threshold ≤ (s w).weight <;> simp [outerAdvance, h, β, a, lam, μ]
  · have hn : Measurable (fun w => if lam w ≤ μ w then (s w).grid - 1 else min cfg.gridTop ((s w).grid + 1)) :=
      Measurable.ite hd (by fun_prop) (by fun_prop)
    have hh : Measurable (fun w => if cfg.threshold ≤ (s w).weight then (s w).grid else
        if lam w ≤ μ w then (s w).grid - 1 else min cfg.gridTop ((s w).grid + 1)) :=
      Measurable.ite ht hj hn
    convert hh using 1
    funext w
    by_cases h : cfg.threshold ≤ (s w).weight <;> simp [outerAdvance, h, lam, μ]

lemma measurable_roundPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (s : X → OuterState E) (hs : MeasurableState s) (call : ℕ) :
    MeasurableState (fun w => QueryPlan.sampledEval oracle (ξ w) (roundPlan cfg (s w)) call) := by
  let c := fun w => outerCenter cfg.δ (s w)
  let H := fun w => QueryPlan.sampledEval oracle (ξ w) (hessianPlan cfg (c w)) call
  let B := fun w => shiftedHessian (H w) (9 * cfg.σh)
  let y := fun w => QueryPlan.sampledEval oracle (ξ w) (innerPlan cfg (c w) (B w) cfg.innerRounds cfg.x0)
    (call + cfg.groups)
  let zn := fun w => QueryPlan.sampledEval oracle (ξ w) (cleanupPlan cfg (c w) (y w) (B w))
    (call + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds)
  let gm := fun w => QueryPlan.sampledEval oracle (ξ w) (meanPlan cfg.batch (zn w).1)
    (call + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
      ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)))
  have hc : Measurable c := measurable_outerCenter cfg.δ s hs
  have hH : Measurable H := measurable_hessianPlan oracle ho ξ hξ cfg c hc call
  have hB : Measurable B := continuous_shiftedHessian.measurable.comp (hH.prodMk measurable_const)
  have hBsym : ∀ w x y, ⟪x, B w y⟫ = ⟪B w x, y⟫ := by
    intro w
    apply shiftedHessian_symmetric
    intro x y
    dsimp [H]
    rw [hessianPlan_eval]
    exact symmetricHessian_symmetric _ x y
  have hBpos : ∀ w v, 0 ≤ ⟪v, B w v⟫ := by
    intro w v
    simpa only [real_inner_comm] using shiftedHessian_nonneg (H w) (9 * cfg.σh) v
  have hy : Measurable y := measurable_innerPlan oracle ho ξ hξ cfg hC hne hconv hL hδ
    c B hc hB hBsym hBpos cfg.innerRounds _
  have hzn : Measurable zn := measurable_cleanupPlan oracle ho ξ hξ cfg hC hne hconv hδ
    c y B hc hy hB hBsym _
  have hgm : Measurable gm := measurable_meanPlan oracle ho ξ hξ cfg.batch _ hzn.fst _
  have hh := measurable_outerAdvance cfg hC hne hconv s hs (fun w => (zn w).1)
    (fun w => gm w + (zn w).2) hzn.fst (hgm.add hzn.snd)
  simpa only [roundPlan_eval] using hh

lemma measurable_roundsPlan (oracle : E → Ω → Reply E)
    (ho : Measurable (Function.uncurry oracle)) (ξ : X → ℕ → Ω)
    (hξ : ∀ j, Measurable (fun w => ξ w j)) (cfg : Config E)
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (T : ℕ)
    (s : X → OuterState E) (hs : MeasurableState s) (call : ℕ) :
    MeasurableState (fun w => QueryPlan.sampledEval oracle (ξ w) (roundsPlan cfg T (s w)) call) := by
  induction T generalizing s call with
  | zero => exact hs
  | succ T ih =>
    simp_rw [roundsPlan, QueryPlan.sampledEval_bind]
    exact ih _ (measurable_roundPlan oracle ho ξ hξ cfg hC hne hconv hL hδ s hs call) _

lemma measurable_output (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (cfg : Config E) (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (T K : ℕ)
    (P : ProbabilityMeasure (ℕ → Ω))
    (hK : (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * T ≤ K) :
    Measurable (output cfg T K
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }) := by
  have hs : MeasurableState (fun _ : ℕ → Ω => outerInitial cfg.x0 cfg.gridTop) :=
    ⟨measurable_const, measurable_const, measurable_const, measurable_const⟩
  have hm := measurable_roundsPlan oracle ho (fun ξ : ℕ → Ω => ξ)
    (fun j => measurable_pi_apply j) cfg hC hne hconv hL hδ T _ hs 0
  have he : output cfg T K { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } =
      fun ξ => (QueryPlan.sampledEval oracle ξ (roundsPlan cfg T (outerInitial cfg.x0 cfg.gridTop)) 0).point := by
    funext ξ
    exact output_eq_sampledPlan cfg T K oracle P ξ hK
  rw [he]
  exact hm.point

end LongTails.Proofs.SymmetricThirdOrderMeasurability
