import LongTails.Algorithms.AcceleratedZerothOrderConvex
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import LongTails.Proofs.ZerothOrderAccuracy
import LongTails.Proofs.ZerothOrderExecution
import LongTails.Proofs.ExecutionHistory

open MeasureTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def coordinateHistory {d : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃ₗᵢ[ℝ] Point d)
    (history : List ((Fin 1 × Point d) × ℝ)) : List ((Fin 1 × E) × ℝ) :=
  history.map fun (query, reply) => ((query.1, e.symm query.2), reply)

private lemma cast_seed_apply {Seed : ℕ → Type*} (ξ : (k : ℕ) → Seed k)
    {a b : ℕ} (h : a = b) : cast (congrArg Seed h) (ξ a) = ξ b := by
  cases h
  rfl

@[reducible] def fixedSpaceSpec (E : Type) (Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] : Setup where
  Params := ℕ × ℝ × ℝ × ℝ × ℝ × E
  Public := ℕ × ℝ × ℝ × ℝ × ℝ × E
  Instance _ := E → ℝ
  Query _ := E
  Reply _ := ℝ
  Output _ := E
  publicInput p := p
  valid := fun (d, L, R, σ, ε, x0) =>
    spec.valid { E := E, Ω := Ω, d := d, L := L, R := R, σ := σ, ε := ε, x0 := x0 }
  admissible := fun (d, L, R, σ, ε, x0) =>
    spec.admissible { E := E, Ω := Ω, d := d, L := L, R := R, σ := σ, ε := ε, x0 := x0 }
  successful := fun (d, L, R, σ, ε, x0) =>
    spec.successful { E := E, Ω := Ω, d := d, L := L, R := R, σ := σ, ε := ε, x0 := x0 }

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def coordinateOracle {d : ℕ} (e : E ≃ₗᵢ[ℝ] Point d) (O : Oracle E ℝ) :
    Oracle (Point d) ℝ where
  Seed := O.Seed
  seedSpace := O.seedSpace
  law := O.law
  answer := fun history (i, x) seed => by
    have hlen : (coordinateHistory e history).length = history.length := by
      simp [coordinateHistory]
    exact O.answer (coordinateHistory e history) (i, (e.symm x))
      (cast (congrArg O.Seed hlen.symm) seed)

private lemma coordinateOracle_answer_at {d : ℕ} (e : E ≃ₗᵢ[ℝ] Point d)
    (O : Oracle E ℝ) (history : List ((Fin 1 × Point d) × ℝ))
    (query : Fin 1 × Point d) (ξ : (k : ℕ) → O.Seed k) :
    (coordinateOracle e O).answer history query (ξ history.length) =
      O.answer (coordinateHistory e history) (query.1, e.symm query.2)
        (ξ (coordinateHistory e history).length) := by
  dsimp [coordinateOracle]
  have hlen : (coordinateHistory e history).length = history.length := by
    simp [coordinateHistory]
  rw [cast_seed_apply ξ hlen.symm]

lemma execute_fromCoordinates {d : ℕ} (e : E ≃ₗᵢ[ℝ] Point d)
    (A : Algorithm (Point d) ℝ (Point d)) (O : Oracle E ℝ) (K : ℕ)
    (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (fromCoordinates e A) (fun _ => K) seed ξ =
      e.symm (execute (coordinateOracle e O) A (fun _ => K) seed ξ) := by
  have h : ∀ n,
      executeIndexedState O (fromCoordinates e A) seed ξ n =
        let sc := executeIndexedState (coordinateOracle e O) A seed ξ n
        (sc.1, coordinateHistory e sc.2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hs : executeIndexedState O (fromCoordinates e A) seed ξ (n + 1) =
            let sc := executeIndexedState O (fromCoordinates e A) seed ξ n
            let query := (fromCoordinates e A).query sc.1
            let reply := O.answer sc.2 query (ξ sc.2.length)
            ((fromCoordinates e A).update sc.1 reply, sc.2 ++ [(query, reply)]) := rfl
        have hc : executeIndexedState (coordinateOracle e O) A seed ξ (n + 1) =
            let sc := executeIndexedState (coordinateOracle e O) A seed ξ n
            let query := A.query sc.1
            let reply := (coordinateOracle e O).answer sc.2 query (ξ sc.2.length)
            (A.update sc.1 reply, sc.2 ++ [(query, reply)]) := rfl
        have hindex (s : A.State) : (A.query s).1 = 0 := Subsingleton.elim _ _
        rw [hs, hc, ih]
        simp [fromCoordinates, coordinateOracle_answer_at, coordinateHistory,
          List.map_append, hindex]
  change (executeWithTrace O (fromCoordinates e A) (fun _ => K) seed ξ).1 =
    e.symm ((executeWithTrace (coordinateOracle e O) A (fun _ => K) seed ξ).1)
  rw [executeWithTrace_eq_executeIndexedState O (fromCoordinates e A) K seed ξ,
    executeWithTrace_eq_executeIndexedState (coordinateOracle e O) A K seed ξ]
  change (fromCoordinates e A).output
      (executeIndexedState O (fromCoordinates e A) seed ξ K).1 =
    e.symm (A.output (executeIndexedState (coordinateOracle e O) A seed ξ K).1)
  rw [h K]
  rfl

variable [CompleteSpace E]

lemma gradient_coordinates {d : ℕ} (e : E ≃ₗᵢ[ℝ] Point d) {f : E → ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x) (x : Point d) :
    HasGradientAt (fun y => f (e.symm y)) (e (gradient f (e.symm x))) x := by
  have h := (hf (e.symm x)).hasFDerivAt.comp x e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert h using 1
  · rfl
  · ext y
    exact e.inner_map_eq_flip _ _

variable [MeasurableSpace E] [BorelSpace E]

lemma admissible_coordinates {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (e : E ≃ₗᵢ[ℝ] Point d) {L R σ ε : ℝ} {x0 : E} {f : E → ℝ} {O : Oracle E ℝ}
    (h : (fixedSpaceSpec E Ω).admissible (d,L,R,σ,ε,x0) f O) :
    (fixedSpaceSpec (Point d) Ω).admissible (d,L,R,σ,ε,e x0) (fun x => f (e.symm x))
      (coordinateOracle e O) := by
  rcases h with ⟨_,g,p,P,hi,hm,rfl,hc,hg,hl,⟨u,hu,hr⟩,hgm,hgi,hmean,hvi,hv⟩
  refine ⟨⟨LinearIsometryEquiv.refl ℝ (Point d)⟩,
    (fun x z => g (e.symm x) z),p,P,hi,hm,?_,?_,?_,?_,?_,?_,(fun x => hgi (e.symm x)),(fun x => hmean (e.symm x)),
    (fun x => hvi (e.symm x)),(fun x => hv (e.symm x))⟩
  · unfold coordinateOracle
    congr 1
  · have h := hc.comp_linearMap e.symm.toLinearEquiv.toLinearMap
    simp only [Set.preimage_univ] at h
    exact h
  · intro x
    exact (gradient_coordinates e hg x).differentiableAt.hasGradientAt
  · intro x y
    rw [(gradient_coordinates e hg x).gradient, (gradient_coordinates e hg y).gradient,
      ← e.map_sub, e.norm_map]
    simpa only [← e.symm.map_sub, e.symm.norm_map] using hl (e.symm x) (e.symm y)
  · refine ⟨e u, ?_, ?_⟩
    · intro x _
      simpa only [Set.mem_ofPred_eq, e.symm_apply_apply] using hu (Set.mem_univ (e.symm x))
    · simpa only [← e.map_sub, e.norm_map] using hr
  · exact hgm.comp ((e.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd)

end OracleTemplate.ZerothOrder

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable (E : Type) (Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]

lemma convergence_public (budget : (fixedSpaceSpec E Ω).Params → ℕ) :
    Convergence (fixedSpaceSpec E Ω) (fun p _ => budget p) ↔
      ∀ p, ∃ A : Algorithm E ℝ E, (fixedSpaceSpec E Ω).valid p →
        ∀ f O, (fixedSpaceSpec E Ω).admissible p f O →
          (fixedSpaceSpec E Ω).successful p f
            (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
              execute O A (fun _ => budget p) seed.1 seed.2)
            ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  constructor
  · rintro ⟨make, correct, _⟩ p
    exact ⟨make p, correct p⟩
  · intro h
    exact ⟨fun p => (h p).choose, fun p => (h p).choose_spec, fun _ _ => trivial⟩

lemma convergence_of_coordinates (B : ℕ → ℝ → ℝ → ℝ → ℝ → ℕ)
    (h : ∀ d, Convergence (fixedSpaceSpec (Point d) Ω) (fun (k,L,R,σ,ε,_) _ => B k L R σ ε)) :
    Convergence (fixedSpaceSpec E Ω) (fun (d,L,R,σ,ε,_) _ => B d L R σ ε) := by
  classical
  let data := fun d => (convergence_public (Point d) Ω (fun (k,L,R,σ,ε,_) => B k L R σ ε)).mp (h d)
  let make := fun d p => (data d p).choose
  have correct := fun d p => (data d p).choose_spec
  rw [convergence_public]
  rintro ⟨d,L,R,σ,ε,x0⟩
  by_cases he : Nonempty (E ≃ₗᵢ[ℝ] Point d)
  swap
  · refine ⟨{ State := E, initial := fun _ => x0, query := fun x => (0, x),
              update := fun x _ => x, output := id }, ?_⟩
    intro hp f O ho
    exact (he ho.1).elim
  let e := he.some
  let A := make d (d,L,R,σ,ε,e x0)
  refine ⟨fromCoordinates e A, ?_⟩
  intro hp f O ho
  have hc := correct d (d,L,R,σ,ε,e x0) hp (fun x => f (e.symm x))
    (coordinateOracle e O) (admissible_coordinates e ho)
  rcases hc with ⟨hm,u,hu,hi,hb⟩
  refine ⟨?_,e.symm u,?_,?_,?_⟩
  · have hm' := e.symm.continuous.measurable.comp hm
    change Measurable (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O (fromCoordinates e A) (fun _ => B d L R σ ε) seed.1 seed.2)
    simp only [execute_fromCoordinates]
    exact hm'
  · intro x _
    simpa only [Set.mem_ofPred_eq, e.symm_apply_apply] using hu (Set.mem_univ (e x))
  · change Integrable (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      f (execute O (fromCoordinates e A) (fun _ => B d L R σ ε) seed.1 seed.2) - f (e.symm u)) _
    simp only [execute_fromCoordinates]
    exact hi
  · change (∫ seed : A.Seed × ((k : ℕ) → O.Seed k),
      f (execute O (fromCoordinates e A) (fun _ => B d L R σ ε) seed.1 seed.2) - f (e.symm u) ∂_) ≤ ε
    simp only [execute_fromCoordinates]
    exact hb

end OracleTemplate.ZerothOrder


open MeasureTheory

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open BiasedStochasticGradient

attribute [local irreducible] direction midpointPoint midpointCoordinate coordinateSecant coordinateDifference gridOracle

variable (d : ℕ) (Ω : Type) [MeasurableSpace Ω]

set_option maxHeartbeats 1500000 in
lemma grid_convergence_coordinates :
    let budget : (fixedSpaceSpec (Point d) Ω).Params → ℕ := fun (dimension, L, R, σ, ε, _) => max 1 ⌈128 * Real.sqrt (L * R ^ 2 / ε) + 32768 * L * dimension * R ^ 2 * σ / ε ^ 2 + 8192 * L * dimension ^ 2 * R ^ 2 * σ ^ 2 / ε ^ 3 + 1⌉₊ * (2 * dimension)
    Convergence (fixedSpaceSpec (Point d) Ω) (fun p _ => budget p) := by
  classical
  rw [convergence_public]
  rintro ⟨dimension,L,R,σ,ε,x0⟩
  by_cases hd : 0 < d
  swap
  · refine ⟨{ State := Point d, initial := fun _ => x0, query := fun x => (0, x),
              update := fun x _ => x, output := id }, ?_⟩
    intro hp f O ho
    obtain ⟨e⟩ := ho.1
    have hdim : d = dimension := by
      simpa only [Point, finrank_euclideanSpace_fin] using e.toLinearEquiv.finrank_eq
    exact (hd (hdim ▸ hp.1)).elim
  refine ⟨
    let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
    let m := max 1 ⌈64*R*L*h*Real.sqrt d/ε⌉₊
    let v := 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2
    let K := max 1 ⌈128 * Real.sqrt (L * R ^ 2 / ε) + 32768 * L * d * R ^ 2 * σ / ε ^ 2 + 8192 * L * d ^ 2 * R ^ 2 * σ ^ 2 / ε ^ 3 + 1⌉₊
    let D := 2*L+32*(K:ℝ)*v/ε
    acceleratedGrid (m := m) hd (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) K D R h x0
    , ?_⟩
  intro hp f O ho
  rcases ho with ⟨⟨e⟩, ho⟩
  have hdim : d = dimension := by
    simpa only [Point, finrank_euclideanSpace_fin] using e.toLinearEquiv.finrank_eq
  subst dimension
  rcases hp with ⟨hd,hL,hR,hσ,hε⟩
  rcases ho with ⟨g,p,P,hind,hmarg,rfl,hc,hg,hlip,⟨u,hmin,hu⟩,hgm,hgi,hmean,hvi,hv⟩
  let h := Real.sqrt (min (ε/(4*L*d)) (σ/L+ε/(256*L*d*(Real.sqrt (L*R^2/ε)+1))))
  let m := max 1 ⌈64*R*L*h*Real.sqrt d/ε⌉₊
  let v := 2*(d:ℝ)*σ^2/h^2+44*(d:ℝ)*L^2*h^2
  let K := max 1 ⌈128 * Real.sqrt (L * R ^ 2 / ε) + 32768 * L * d * R ^ 2 * σ / ε ^ 2 + 8192 * L * d ^ 2 * R ^ 2 * σ ^ 2 / ε ^ 3 + 1⌉₊
  let D := 2*L+32*(K:ℝ)*v/ε
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  let : Nonempty (Fin m) := ⟨⟨0,hmpos⟩⟩
  let r := (PMF.uniformOfFintype (Fin d → Fin m)).toMeasure
  let q := r.prod (Measure.pi fun _ : Fin d × Bool => (p : Measure Ω))
  let output := fun ξ : Fin K → ((Fin d → Fin m) × (Fin d × Bool → Ω)) =>
    (projectedRun (gridOracle (m := m) g h) D R x0 K 0 x0 x0 ξ).1
  have hu' : ‖u-x0‖ ≤ R := by simpa only [norm_sub_rev] using hu
  have haccuracy : Integrable (fun ξ => f (output ξ)-f u) (Measure.pi fun _ : Fin K => q) ∧
      (∫ ξ, f (output ξ)-f u ∂Measure.pi (fun _ : Fin K => q)) ≤ ε := by
    by_cases hR0 : R=0
    · have he : ∀ ξ, output ξ=x0 := by
        intro ξ
        apply sub_eq_zero.mp
        apply norm_eq_zero.mp
        apply le_antisymm _ (norm_nonneg _)
        exact ((projectedRun_ball (gridOracle (m := m) g h) D hR x0 K 0 x0 x0
          (by simpa) (by simpa) ξ).1).trans_eq hR0
      have hxu : x0=u := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa [hR0] using hu) (norm_nonneg _)))
      simp only [he,hxu,sub_self]
      exact ⟨integrable_const _,by simpa using hε.le⟩
    · have ha := grid_accuracy (d := d) (Ω := Ω) (f := f) (g := g) (p := (p : Measure Ω))
        (L := L) (R := R) (σ := σ) (ε := ε) hd hL (lt_of_le_of_ne hR (Ne.symm hR0)) hσ hε
        hc hg hlip hgm hgi hmean hvi hv x0 u hmin hu'
      exact ha
  have ht := grid_execution_transfer hd hmpos K D R h ε x0 u f g p P (by exact hind) (by exact hmarg) hgm (by exact haccuracy)
  exact ⟨ht.1,u,hmin,ht.2⟩

end OracleTemplate.ZerothOrder


open MeasureTheory Metric

namespace OracleTemplate.ZerothOrder

open LongTails.Setups.ZerothOrderSmoothAndConvex

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

attribute [local irreducible] twoPointEstimate coupledRun

variable (d : ℕ) (Ω : Type) [MeasurableSpace Ω]

set_option maxHeartbeats 1500000 in
lemma two_point_convergence_coordinates :
    let budget : (fixedSpaceSpec (Point d) Ω).Params → ℕ := fun (dimension, L, R, σ, ε, _) => max 1 ⌈64 * dimension * Real.sqrt (L * R ^ 2 / ε) + 512 * L * dimension ^ 2 * R ^ 2 * σ / ε ^ 2 + 256 * L * dimension ^ 2 * R ^ 2 * σ ^ 2 / ε ^ 3 + 1⌉₊ * 2
    Convergence (fixedSpaceSpec (Point d) Ω) (fun p _ => budget p) := by
  classical
  rw [convergence_public]
  rintro ⟨dimension,L,R,σ,ε,x0⟩
  by_cases hd : 0 < d
  swap
  · refine ⟨{ State := Point d, initial := fun _ => x0, query := fun x => (0, x),
              update := fun x _ => x, output := id }, ?_⟩
    intro hp f O ho
    obtain ⟨e⟩ := ho.1
    have hdim : d = dimension := by
      simpa only [Point, finrank_euclideanSpace_fin] using e.toLinearEquiv.finrank_eq
    exact (hd (hdim ▸ hp.1)).elim
  refine ⟨
    letI : NeZero d := ⟨ne_of_gt hd⟩
    let h := Real.sqrt (min (ε/(4*L)) (σ/L+ε/(128*L*d*(Real.sqrt (L*R^2/ε)+1))))
    let v := 10*(d:ℝ)^2*L^2*h^2+(d:ℝ)^2*σ^2/h^2
    let K := max 1 ⌈64 * d * Real.sqrt (L * R ^ 2 / ε) + 512 * L * d ^ 2 * R ^ 2 * σ / ε ^ 2 + 256 * L * d ^ 2 * R ^ 2 * σ ^ 2 / ε ^ 3 + 1⌉₊
    let M := 128*L*d^2+8*(K:ℝ)*v/ε
    acceleratedTwoPoint (K := K) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
      (sphereLaw (Point d)) M (8*d) h x0
    , ?_⟩
  intro hp f O ho
  rcases ho with ⟨⟨e⟩, ho⟩
  have hdim : d = dimension := by
    simpa only [Point, finrank_euclideanSpace_fin] using e.toLinearEquiv.finrank_eq
  subst dimension
  rcases hp with ⟨hd,hL,hR,hσ,hε⟩
  let : NeZero d := ⟨ne_of_gt hd⟩
  rcases ho with ⟨g,p,P,hind,hmarg,rfl,hc,hg,hlip,⟨u,hmin,hu⟩,hgm,hgi,hmean,hvi,hv⟩
  let h := Real.sqrt (min (ε/(4*L)) (σ/L+ε/(128*L*d*(Real.sqrt (L*R^2/ε)+1))))
  let v := 10*(d:ℝ)^2*L^2*h^2+(d:ℝ)^2*σ^2/h^2
  let K := max 1 ⌈64 * d * Real.sqrt (L * R ^ 2 / ε) + 512 * L * d ^ 2 * R ^ 2 * σ / ε ^ 2 + 256 * L * d ^ 2 * R ^ 2 * σ ^ 2 / ε ^ 3 + 1⌉₊
  let M := 128*L*d^2+8*(K:ℝ)*v/ε
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have ha := twoPoint_accuracy (f := f) (g := g) (p := (p : Measure Ω)) hL hR hσ hε
    hc hg hlip hgm hgi hmean hvi hv x0 u hmin hu
  have ht := twoPoint_execution_transfer hK (sphereLaw (Point d)) M (8*d) h ε x0 u f g p P
    (by exact hind) (by exact hmarg) hgm (by exact ha)
  exact ⟨ht.1,u,hmin,ht.2⟩

end OracleTemplate.ZerothOrder
