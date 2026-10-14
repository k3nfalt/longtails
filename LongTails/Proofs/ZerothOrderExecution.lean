import LongTails.Proofs.ZerothOrderAccuracy
import LongTails.Proofs.IIDBlocks
import Mathlib.Probability.ProductMeasure
import LongTails.Algorithms.AcceleratedTwoPointZerothOrderConvex
import LongTails.Algorithms.AcceleratedZerothOrderConvex
import LongTails.Proofs.AcceleratedBiasedStochastic
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.SeededExecution
import LongTails.Proofs.ZerothOrderGridEstimator
import LongTails.Setups.ZerothOrderSmoothAndConvex

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient BiasedStochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

lemma decode_values_estimate {d : ℕ} {Ω : Type} (g : Point d → Ω → ℝ)
    (h : ℝ) (s : ℕ × Point d × Point d) (ξ : Fin (Fintype.card (Fin d × Bool)) → Ω) :
    decodeValues h (fun i => g (valueQueries h s i) (ξ i)) =
      estimate g h (Gradient.acceleratedQuery s)
        (fun j => ξ (Fintype.equivFin (Fin d × Bool) j)) := by
  unfold decodeValues estimate valueQueries
  simp

lemma advance_projected {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (D R : ℝ) (x0 : E) (ξ : ℕ → Ω)
    (K call k : ℕ) (x z : E) :
    advance (fun j state => (projectedAccelerated D R x0).update state
      (g (((projectedAccelerated D R x0).query state).2) (ξ j))) K call (k, x, z) =
      (k + K, projectedRun g D R x0 K k x z (fun i => ξ (call + i))) := by
  dsimp only [projectedAccelerated]
  induction K generalizing call k x z with
  | zero => simp [advance, projectedRun]
  | succ K ih =>
    rw [advance]
    simpa only [projectedRun, projectedAccelerated, Fin.val_zero, Nat.add_zero,
      Fin.val_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (call + 1) (k + 1)
        (projectedUpdate D R x0 k (x,z) (g (Gradient.acceleratedQuery (k,x,z)) (ξ call))).1
        (projectedUpdate D R x0 k (x,z) (g (Gradient.acceleratedQuery (k,x,z)) (ξ call))).2

lemma execute_finite_difference {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hd : 0 < d) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → ℝ) (D R h : ℝ) (x0 : Point d) (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (acceleratedFiniteDifference hd D R h x0) (fun _ => (K * Fintype.card (Fin d × Bool))) () ξ =
      (projectedRun (estimate g h) D R x0 K 0 x0 x0
        (fun k j => ξ (k.val * Fintype.card (Fin d × Bool) +
          (Fintype.equivFin (Fin d × Bool) j).val))).1 := by
  unfold acceleratedFiniteDifference
  erw [execute_batched]
  dsimp only [projectedAccelerated]
  simp only [decode_values_estimate]
  have he := advance_projected (estimate g h) D R x0
    (fun k j => ξ (k * Fintype.card (Fin d × Bool) +
      (Fintype.equivFin (Fin d × Bool) j).val)) K 0 0 x0 x0
  simpa only [Nat.zero_add, projectedAccelerated] using
    congrArg (fun s => s.2.1) he

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma block_law {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p) (K : ℕ) :
    MeasurePreserving
      (fun ξ : ℕ → Ω => fun k : Fin K => fun j : J =>
        ξ (k.val * Fintype.card J + (Fintype.equivFin J j).val))
      P (Measure.pi (fun _ : Fin K => Measure.pi (fun _ : J => p))) := by
  classical
  let index : Fin K × J → ℕ := fun kj =>
    kj.1.val * Fintype.card J + (Fintype.equivFin J kj.2).val
  have hinj : Function.Injective index := by
    intro a b hab
    have ha := (Fintype.equivFin J a.2).isLt
    have hb := (Fintype.equivFin J b.2).isLt
    have hc : 0 < Fintype.card J := lt_of_le_of_lt (Nat.zero_le _) ha
    have hfirst : a.1.val = b.1.val := by
      have hdiv := congrArg (fun t => t / Fintype.card J) hab
      dsimp only [index] at hdiv
      rw [Nat.mul_comm a.1.val, Nat.mul_comm b.1.val, Nat.mul_add_div hc, Nat.mul_add_div hc, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb, Nat.add_zero, Nat.add_zero] at hdiv
      exact hdiv
    have hsecond : (Fintype.equivFin J a.2).val = (Fintype.equivFin J b.2).val := by
      dsimp [index] at hab
      rw [hfirst] at hab
      exact Nat.add_left_cancel hab
    exact Prod.ext (Fin.ext hfirst) ((Fintype.equivFin J).injective (Fin.ext hsecond))
  have hflat : MeasurePreserving (fun ξ : ℕ → Ω => fun kj : Fin K × J => ξ (index kj))
      P (Measure.pi (fun _ : Fin K × J => p)) := by
    refine ⟨by fun_prop, ?_⟩
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun kj => (measurable_pi_apply (index kj)).aemeasurable)).mp (hind.precomp hinj)
    simpa only [hmarg] using h
  have hcurry : MeasurePreserving (MeasurableEquiv.curry (Fin K) J Ω)
      (Measure.pi (fun _ : Fin K × J => p))
      (Measure.pi (fun _ : Fin K => Measure.pi (fun _ : J => p))) := by
    refine ⟨(MeasurableEquiv.curry (Fin K) J Ω).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : Fin K) (_ : J) => p))
  exact hcurry.comp hflat

end OracleTemplate.ZerothOrder

end

section

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient BiasedStochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

lemma decode_grid_values {d m K : ℕ} {Ω : Type} (hm : 0 < m) (g : Point d → Ω → ℝ)
    (h : ℝ) (s : ℕ × (Fin K → Fin d → Fin m) × (ℕ × Point d × Point d))
    (ξ : Fin (Fintype.card (Fin d × Bool)) → Ω) :
    decodeValues (2*h) (fun i => g (gridQueries hm h s i) (ξ i)) =
      gridOracle g h (Gradient.acceleratedQuery s.2.2)
        (drawGrid hm s.2.1 s.1,fun j => ξ (Fintype.equivFin (Fin d × Bool) j)) := by
  unfold decodeValues gridQueries gridOracle coordinateSecant
  simp

lemma execute_grid {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hd : 0 < d) (hm : 0 < m) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → ℝ) (D R h : ℝ) (x0 : Point d) (K : ℕ)
    (s : Fin K → Fin d → Fin m) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (acceleratedGrid hd hm K D R h x0) (fun _ => (K*Fintype.card (Fin d × Bool))) ((),s) ξ =
      (projectedRun (gridOracle g h) D R x0 K 0 x0 x0
        (fun k => (s k,fun j => ξ (k.val*Fintype.card (Fin d × Bool)+(Fintype.equivFin (Fin d × Bool) j).val)))).1 := by
  unfold acceleratedGrid
  erw [execute_batched]
  dsimp only [seeded, projectedAccelerated]
  simp only [decode_grid_values]
  have hs := advance_seeded (projectedAccelerated D R x0) (gridSeedLaw (d := d) hm K)
    (fun call seed k state => gridOracle g h (Gradient.acceleratedQuery state)
      (drawGrid hm seed k,fun j => ξ (call*Fintype.card (Fin d × Bool)+(Fintype.equivFin (Fin d × Bool) j).val)))
    K 0 s (0,x0,x0)
  change (seeded (projectedAccelerated D R x0) (gridSeedLaw (d := d) hm K)).output
    (advance _ K 0 (0,s,(0,x0,x0))) = _
  erw [hs]
  have he := advance_projected (gridOracle (m := m) g h) D R x0
    (fun k => (drawGrid hm s k,fun j => ξ (k*Fintype.card (Fin d × Bool)+(Fintype.equivFin (Fin d × Bool) j).val)))
    K 0 0 x0 x0
  have hdraw (k : Fin K) : drawGrid hm s k.val = s k := by simp [drawGrid,k.isLt]
  simpa only [seeded,projectedAccelerated,Nat.zero_add,hdraw] using
    congrArg (fun t => t.2.1) he

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

lemma joint_grid_law {G Ω J : Type*} [MeasurableSpace G] [MeasurableSpace Ω] [Fintype J]
    (r : Measure G) [IsProbabilityMeasure r] (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ : ℕ → Ω => ξ k) = p) (K : ℕ) :
    MeasurePreserving
      (fun s : (Fin K → G) × (ℕ → Ω) => fun k : Fin K =>
        (s.1 k,fun j : J => s.2 (k.val*Fintype.card J+(Fintype.equivFin J j).val)))
      ((Measure.pi fun _ : Fin K => r).prod P)
      (Measure.pi fun _ : Fin K => r.prod (Measure.pi fun _ : J => p)) := by
  have hb := block_law (J := J) p P hind hmarg K
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin K => r)).prod hb
  let e := MeasurableEquiv.arrowProdEquivProdArrow G (J → Ω) (Fin K)
  have he := measurePreserving_arrowProdEquivProdArrow G (J → Ω) (Fin K)
    (fun _ => r) (fun _ => Measure.pi fun _ : J => p)
  have hs : MeasurePreserving e.symm
      ((Measure.pi fun _ : Fin K => r).prod (Measure.pi fun _ : Fin K => Measure.pi fun _ : J => p))
      (Measure.pi fun _ : Fin K => r.prod (Measure.pi fun _ : J => p)) := by
    refine ⟨e.symm.measurable, ?_⟩
    exact (e.map_apply_eq_iff_map_symm_apply_eq.mp he.map_eq).symm
  exact hs.comp hp

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open BiasedStochasticGradient

attribute [local irreducible] direction midpointPoint midpointCoordinate coordinateSecant coordinateDifference gridOracle

set_option maxHeartbeats 100000 in
lemma grid_execution_transfer {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hd : 0 < d) (hm : 0 < m) (K : ℕ) (D R h ε : ℝ) (x0 u : Point d)
    (f : Point d → ℝ) (g : Point d → Ω → ℝ)
    (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _))
    (hgm : Measurable (Function.uncurry g))
    (ha : letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
      let q := (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure.prod (Measure.pi fun _ : Fin d × Bool => (p : Measure Ω))
      Integrable (fun ξ => f (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1-f u)
        (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1-f u
        ∂Measure.pi (fun _ : Fin K => q)) ≤ ε) :
    let A := acceleratedGrid hd hm K D R h x0
    let result := fun seed : A.Seed × (ℕ → Ω) => (execute
      { Seed := fun _ => Ω,law := P,answer := fun _ (_, x) ω => g x ω } A (fun _ => (K*(2*d))) seed.1 seed.2)
    Measurable result ∧ Integrable (fun seed => f (result seed)-f u) ((A.law : Measure _).prod (P : Measure _)) ∧
      (∫ seed, f (result seed)-f u ∂(A.law : Measure _).prod (P : Measure _)) ≤ ε := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let r := (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure
  let q := r.prod (Measure.pi fun _ : Fin d × Bool => (p : Measure Ω))
  let block := fun s : (Fin K → Fin d → Fin m) × (ℕ → Ω) => fun k : Fin K =>
    (s.1 k,fun j : Fin d × Bool => s.2 (k.val*Fintype.card (Fin d × Bool)+(Fintype.equivFin (Fin d × Bool) j).val))
  let output := fun ξ : Fin K → ((Fin d → Fin m) × (Fin d × Bool → Ω)) =>
    (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1
  have hmp : MeasurePreserving block ((gridSeedLaw (d := d) hm K : Measure (Fin K → Fin d → Fin m)).prod (P : Measure _))
      (Measure.pi fun _ : Fin K => q) := by
    change MeasurePreserving block ((Measure.pi fun _ : Fin K => r).prod (P : Measure _)) (Measure.pi fun _ : Fin K => q)
    have hj := @joint_grid_law (Fin d → Fin m) Ω (Fin d × Bool) inferInstance inferInstance inferInstance r (PMF.toMeasure.isProbabilityMeasure _) (p : Measure Ω) p.prop (P : Measure _) P.prop (by exact hind) (by exact hmarg) K
    exact hj
  have houtput : Measurable output :=
    ((measurable_projectedRun (measurable_gridOracle (m := m) hgm h) D R x0 K 0).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → ((Fin d → Fin m) × (Fin d × Bool → Ω)) => ((x0,x0),ξ)))).fst
  have hi := hmp.integrable_comp_of_integrable ha.1
  have heint := (integral_comp_preserving hmp ha.1).trans_le ha.2
  have hdrop : MeasurePreserving (fun s : (Unit × (Fin K → Fin d → Fin m)) × (ℕ → Ω) => (s.1.2,s.2))
      (((Measure.dirac () : Measure Unit).prod (gridSeedLaw (d := d) hm K : Measure (Fin K → Fin d → Fin m))).prod (P : Measure _))
      ((gridSeedLaw (d := d) hm K : Measure (Fin K → Fin d → Fin m)).prod (P : Measure _)) := by
    have hs := measurePreserving_snd (μ := (Measure.dirac () : Measure Unit)) (ν := (gridSeedLaw (d := d) hm K : Measure (Fin K → Fin d → Fin m)))
    have hp := hs.prod (MeasurePreserving.id (P : Measure (ℕ → Ω)))
    exact hp
  have hcard : Fintype.card (Fin d × Bool)=2*d := by simp; omega
  let result := fun seed : (Unit × (Fin K → Fin d → Fin m)) × (ℕ → Ω) => (execute
    { Seed := fun _ => Ω,law := P,answer := fun _ (_, x) ω => g x ω }
    (acceleratedGrid hd hm K D R h x0) (fun _ => (K*(2*d))) seed.1 seed.2)
  change Measurable result ∧ Integrable (fun seed => f (result seed)-f u)
      (((Measure.dirac () : Measure Unit).prod (gridSeedLaw (d := d) hm K : Measure (Fin K → Fin d → Fin m))).prod (P : Measure _)) ∧
    (∫ seed, f (result seed)-f u ∂((Measure.dirac () : Measure Unit).prod
      (gridSeedLaw (d := d) hm K : Measure (Fin K → Fin d → Fin m))).prod (P : Measure _)) ≤ ε
  have he : result = fun seed => output (block (seed.1.2,seed.2)) := by
    funext ⟨⟨⟨⟩,s⟩,ξ⟩
    dsimp [result]
    rw [← hcard]
    exact (execute_grid hd hm P g D R h x0 K s ξ)
  rw [he]
  exact ⟨(houtput.comp hmp.measurable).comp hdrop.measurable,
    hdrop.integrable_comp_of_integrable hi,(integral_comp_preserving hdrop hi).trans_le heint⟩

end OracleTemplate.ZerothOrder

end

section

open MeasureTheory Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

lemma advance_coupled {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → Ω → E) (M θ : ℝ) (x0 : E) (ξ : ℕ → Ω)
    (K call k : ℕ) (x z : E) :
    advance (fun j state => (coupledAccelerated M θ x0).update state
      (g (((coupledAccelerated M θ x0).query state).2) (ξ j))) K call (k,x,z) =
      (k+K,coupledRun g M θ K k x z (fun i => ξ (call+i))) := by
  dsimp only [coupledAccelerated]
  induction K generalizing call k x z with
  | zero => simp [advance,coupledRun]
  | succ K ih =>
    rw [advance]
    simpa only [coupledRun,coupledAccelerated,Fin.val_zero,Nat.add_zero,
      Fin.val_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (call+1) (k+1)
        (coupledUpdate M θ k (x,z) (g (Gradient.acceleratedQuery (k,x,z)) (ξ call))).1
        (coupledUpdate M θ k (x,z) (g (Gradient.acceleratedQuery (k,x,z)) (ξ call))).2

lemma decode_twoPoint_values {d K : ℕ} {Ω : Type} (hK : 0 < K) (h : ℝ)
    (s : ℕ × (Fin K → sphere (0 : Point d) 1) × (ℕ × Point d × Point d))
    (g : Point d → Ω → ℝ) (ξ : ℕ → Ω) (k : ℕ) :
    decodeTwoPoint hK h s (fun i => g (twoPointQueries hK h s i) (ξ (k*2+i.val))) =
      twoPointEstimate g h (Gradient.acceleratedQuery s.2.2)
        (drawTwoPointDirection hK s.2.1 s.1) (ξ (k*2),ξ (k*2+1)) := by
  simp [decodeTwoPoint,twoPointQueries,twoPointEstimate]

lemma execute_twoPoint {d K : ℕ} {Ω : Type} [MeasurableSpace Ω] (hK : 0 < K)
    (ρ : ProbabilityMeasure (sphere (0 : Point d) 1)) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point d → Ω → ℝ) (M θ h : ℝ) (x0 : Point d)
    (s : Fin K → sphere (0 : Point d) 1) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω,law := P,answer := fun _ (_, x) ω => g x ω }
      (acceleratedTwoPoint hK ρ M θ h x0) (fun _ => (K*2)) ((),s) ξ =
      (coupledRun (fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) => twoPointEstimate g h x w.1 w.2)
        M θ K 0 x0 x0 (fun k => (s k,(ξ (k.val*2),ξ (k.val*2+1))))).1 := by
  unfold acceleratedTwoPoint
  erw [execute_batched]
  dsimp only [seeded, coupledAccelerated]
  simp only [decode_twoPoint_values]
  have hs := advance_seeded (coupledAccelerated M θ x0) (twoPointSeedLaw ρ K)
    (fun call seed k state => twoPointEstimate g h (Gradient.acceleratedQuery state)
      (drawTwoPointDirection hK seed k) (ξ (call*2),ξ (call*2+1))) K 0 s (0,x0,x0)
  change (seeded (coupledAccelerated M θ x0) (twoPointSeedLaw ρ K)).output
    (advance _ K 0 (0,s,(0,x0,x0))) = _
  erw [hs]
  have he := advance_coupled
    (fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) => twoPointEstimate g h x w.1 w.2)
    M θ x0 (fun k => (drawTwoPointDirection hK s k,(ξ (k*2),ξ (k*2+1)))) K 0 0 x0 x0
  have hdraw (k : Fin K) : drawTwoPointDirection hK s k.val=s k := by
    simp [drawTwoPointDirection,k.isLt]
  simpa only [seeded,coupledAccelerated,Nat.zero_add,hdraw] using
    congrArg (fun t => t.2.1) he

end OracleTemplate.ZerothOrder

end


section

open MeasureTheory ProbabilityTheory Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

attribute [local irreducible] twoPointEstimate coupledRun

set_option maxHeartbeats 400000

lemma twoPoint_joint_law {G Ω : Type} [MeasurableSpace G] [MeasurableSpace Ω]
    (r : Measure G) [IsProbabilityMeasure r] (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ : ℕ → Ω => ξ k)=p) (K : ℕ) :
    MeasurePreserving (fun s : (Fin K → G) × (ℕ → Ω) => fun k : Fin K =>
      (s.1 k,(s.2 (k.val*2),s.2 (k.val*2+1))))
      ((Measure.pi fun _ : Fin K => r).prod P)
      (Measure.pi fun _ : Fin K => r.prod (p.prod p)) := by
  have hp := (prefix_measurePreserving (p.prod p) K).comp
    (FiniteVariance.paired_stream_law p P hind hmarg)
  have he := (measurePreserving_arrowProdEquivProdArrow G (Ω × Ω) (Fin K)
    (fun _ => r) (fun _ => p.prod p)).symm
  exact he.comp ((MeasurePreserving.id (Measure.pi fun _ : Fin K => r)).prod hp)

lemma twoPoint_execution_transfer {d K : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hK : 0 < K) (ρ : ProbabilityMeasure (sphere (0 : Point d) 1)) (M θ h ε : ℝ)
    (x0 u : Point d) (f : Point d → ℝ) (g : Point d → Ω → ℝ)
    (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k)=(p : Measure _))
    (hgm : Measurable (Function.uncurry g))
    (ha : let q := (ρ : Measure (sphere (0 : Point d) 1)).prod ((p : Measure Ω).prod (p : Measure Ω))
      Integrable (fun ξ => f (coupledRun (fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) =>
        twoPointEstimate g h x w.1 w.2) M θ K 0 x0 x0 ξ).1-f u) (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (coupledRun (fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) =>
        twoPointEstimate g h x w.1 w.2) M θ K 0 x0 x0 ξ).1-f u ∂Measure.pi (fun _ : Fin K => q)) ≤ ε) :
    let A := acceleratedTwoPoint hK ρ M θ h x0
    let result := fun seed : A.Seed × (ℕ → Ω) => (execute
      { Seed := fun _ => Ω,law := P,answer := fun _ (_, x) ω => g x ω } A (fun _ => (K*2)) seed.1 seed.2)
    Measurable result ∧ Integrable (fun seed => f (result seed)-f u) ((A.law : Measure _).prod (P : Measure _)) ∧
      (∫ seed, f (result seed)-f u ∂(A.law : Measure _).prod (P : Measure _)) ≤ ε := by
  let q := (ρ : Measure (sphere (0 : Point d) 1)).prod ((p : Measure Ω).prod (p : Measure Ω))
  let block := fun s : (Fin K → sphere (0 : Point d) 1) × (ℕ → Ω) => fun k : Fin K =>
    (s.1 k,(s.2 (k.val*2),s.2 (k.val*2+1)))
  let oracle := fun (x : Point d) (w : sphere (0 : Point d) 1 × (Ω × Ω)) => twoPointEstimate g h x w.1 w.2
  let output := fun ξ : Fin K → (sphere (0 : Point d) 1 × (Ω × Ω)) => (coupledRun oracle M θ K 0 x0 x0 ξ).1
  have hmp0 := @twoPoint_joint_law (sphere (0 : Point d) 1) Ω inferInstance inferInstance
    (ρ : Measure (sphere (0 : Point d) 1)) ρ.prop (p : Measure Ω) p.prop
    (P : Measure (ℕ → Ω)) P.prop hind hmarg K
  have hmp : MeasurePreserving block ((twoPointSeedLaw ρ K : Measure (Fin K → sphere (0 : Point d) 1)).prod (P : Measure _))
      (Measure.pi fun _ : Fin K => q) := hmp0
  have harg : Measurable (fun v : Point d × (sphere (0 : Point d) 1 × (Ω × Ω)) =>
      (v.1,((v.2.1:Point d),v.2.2))) := by fun_prop
  have ho0 := (measurable_twoPointEstimate hgm h).comp harg
  have ho : Measurable (Function.uncurry oracle) := ho0
  have houtput : Measurable output :=
    ((measurable_coupledRun (g := oracle) ho M θ K 0).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin K → (sphere (0 : Point d) 1 × (Ω × Ω)) => ((x0,x0),ξ)))).fst
  have hi := hmp.integrable_comp_of_integrable ha.1
  have heint := (integral_comp_preserving hmp ha.1).trans_le ha.2
  have hdrop : MeasurePreserving (fun s : (Unit × (Fin K → sphere (0 : Point d) 1)) × (ℕ → Ω) => (s.1.2,s.2))
      (((Measure.dirac () : Measure Unit).prod (twoPointSeedLaw ρ K : Measure (Fin K → sphere (0 : Point d) 1))).prod (P : Measure _))
      ((twoPointSeedLaw ρ K : Measure (Fin K → sphere (0 : Point d) 1)).prod (P : Measure _)) := by
    have hs := measurePreserving_snd (μ := (Measure.dirac () : Measure Unit)) (ν := (twoPointSeedLaw ρ K : Measure (Fin K → sphere (0 : Point d) 1)))
    exact hs.prod (MeasurePreserving.id (P : Measure (ℕ → Ω)))
  let result := fun seed : (Unit × (Fin K → sphere (0 : Point d) 1)) × (ℕ → Ω) => (execute
    { Seed := fun _ => Ω,law := P,answer := fun _ (_, x) ω => g x ω }
    (acceleratedTwoPoint hK ρ M θ h x0) (fun _ => (K*2)) seed.1 seed.2)
  change Measurable result ∧ Integrable (fun seed => f (result seed)-f u)
      (((Measure.dirac () : Measure Unit).prod (twoPointSeedLaw ρ K : Measure (Fin K → sphere (0 : Point d) 1))).prod (P : Measure _)) ∧
    (∫ seed, f (result seed)-f u ∂((Measure.dirac () : Measure Unit).prod
      (twoPointSeedLaw ρ K : Measure (Fin K → sphere (0 : Point d) 1))).prod (P : Measure _)) ≤ ε
  have he : result = fun seed => output (block (seed.1.2,seed.2)) := by
    funext ⟨⟨⟨⟩,s⟩,ξ⟩
    exact (execute_twoPoint hK ρ P g M θ h x0 s ξ)
  rw [he]
  exact ⟨(houtput.comp hmp.measurable).comp hdrop.measurable,
    hdrop.integrable_comp_of_integrable hi,(integral_comp_preserving hdrop hi).trans_le heint⟩

end OracleTemplate.ZerothOrder

end
