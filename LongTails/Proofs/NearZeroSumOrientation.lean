import LongTails.Proofs.NearZeroSumModel
import LongTails.Proofs.NearZeroSumExecution

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

abbrev swappedPublic (p : Public) : Public where
  E := p.F
  F := p.E
  X := p.Y
  Y := p.X
  L := p.L
  μ := p.ν
  ν := p.μ
  δ := p.δ
  D := p.D
  ε := p.ε
  x0 := p.y0
  y0 := p.x0

noncomputable def swappedProblem {p : Public} (I : Problem p) : Problem (swappedPublic p) :=
  ⟨fun u => -I.h (swapPoint u), fun u => I.g (swapPoint u)⟩

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma swap_swap (u : Joint E F) : swapPoint (swapPoint u) = u := WithLp.toLp_ofLp 2 u

lemma swap_norm (u : Joint E F) : ‖swapPoint u‖ = ‖u‖ :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ E F).norm_map u

lemma swap_sub (u v : Joint E F) : swapPoint (u - v) = swapPoint u - swapPoint v :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ E F).map_sub u v

lemma swap_add (u v : Joint E F) : swapPoint (u + v) = swapPoint u + swapPoint v :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ E F).map_add u v

lemma swap_smul (a : ℝ) (u : Joint E F) : swapPoint (a • u) = a • swapPoint u :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ E F).map_smul a u

lemma swap_inner (u v : Joint E F) : ⟪swapPoint u, swapPoint v⟫ = ⟪u, v⟫ :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ E F).inner_map_map u v

lemma swap_mem {p : Public} (u : Space p) :
    swapPoint u ∈ domain (swappedPublic p) ↔ u ∈ domain p := by
  change (u.snd ∈ p.Y ∧ u.fst ∈ p.X) ↔ (u.fst ∈ p.X ∧ u.snd ∈ p.Y)
  exact and_comm

lemma swap_normal {p : Public} {u n : Space p}
    (hn : ConstrainedMonotone.Normal (domain p) u n) :
    ConstrainedMonotone.Normal (domain (swappedPublic p)) (swapPoint u) (swapPoint n) := by
  intro v hv
  have hm : swapPoint v ∈ domain p := (swap_mem (p := swappedPublic p) v).mpr hv
  have h := hn (swapPoint v) hm
  have he : ⟪swapPoint n, v - swapPoint u⟫ = ⟪n, swapPoint v - u⟫ := by
    rw [← swap_swap v, ← swap_sub, swap_inner, swap_swap]
  rwa [he]

lemma swap_projection {p : Public} {P : Space p → Space p}
    (hp : ConstrainedMonotone.Proj (domain p) P) :
    ConstrainedMonotone.Proj (domain (swappedPublic p)) (fun u => swapPoint (P (swapPoint u))) := by
  constructor
  · intro u
    exact (swap_mem _).mpr (hp.mem _)
  · intro u v hv
    have hm : swapPoint v ∈ domain p := (swap_mem (p := swappedPublic p) v).mpr hv
    have h := hp.var (swapPoint u) (swapPoint v) hm
    have he : ⟪u - swapPoint (P (swapPoint u)), v - swapPoint (P (swapPoint u))⟫ =
        ⟪swapPoint u - P (swapPoint u), swapPoint v - P (swapPoint u)⟫ := by
      rw [← swap_inner (u - swapPoint (P (swapPoint u))) (v - swapPoint (P (swapPoint u))),
        swap_sub, swap_sub, swap_swap]
    rwa [he]

lemma eval_transportPlan {Q R U Q' R' U' : Type*} (query : Q' → Q) (reply : R → R')
    (output : U' → U) (g : Q → R) {k : ℕ} (plan : QueryPlan Q' R' U' k) :
    QueryPlan.eval g (transportPlan query reply output plan) =
      output (QueryPlan.eval (fun q => reply (g (query q))) plan) := by
  induction plan with
  | done u => rfl
  | ask q next ih => exact ih (reply (g (query q)))

lemma safe_transportPlan {Q R U Q' R' U' : Type*} (query : Q' → Q) (reply : R → R')
    (output : U' → U) (g : Q → R) (valid : Q → Prop) {k : ℕ}
    (plan : QueryPlan Q' R' U' k)
    (hp : safeQueries (fun q => valid (query q)) (fun q => reply (g (query q))) plan) :
    safeQueries valid g (transportPlan query reply output plan) := by
  induction plan with
  | done u => trivial
  | ask q next ih => exact ⟨hp.1, ih _ hp.2⟩


lemma swap_gradient {p : Public} {f : Space p → ℝ} {g : Space p}
    {u : Space (swappedPublic p)}
    (hg : HasGradientWithinAt f g (domain p) (swapPoint u)) :
    HasGradientWithinAt (fun v => f (swapPoint v)) (swapPoint g) (domain (swappedPublic p)) u := by
  let T := (LinearIsometryEquiv.withLpProdComm 2 ℝ p.F p.E).toContinuousLinearEquiv.toContinuousLinearMap
  have hT (v : Space (swappedPublic p)) : T v = swapPoint v := rfl
  have h := gradient_comp_affine_within T (b := 0) (q := swapPoint g)
    (by simpa only [hT, add_zero] using hg)
    (fun v hv => by simpa only [hT, add_zero] using (swap_mem (p := swappedPublic p) v).mpr hv)
    (by intro v; simpa only [hT, swap_swap] using (swap_inner g (swapPoint v)).symm)
  simpa only [hT, add_zero] using h

lemma swapped_own_gradient {p : Public} (H G : Space p → Space p) (u : Space (swappedPublic p)) :
    ownGradient (p := swappedPublic p) (fun v => -swapPoint (H (swapPoint v)))
      (fun v => swapPoint (G (swapPoint v))) u = swapPoint (ownGradient H G (swapPoint u)) := by
  apply WithLp.ofLp_injective 2
  change (-(H (swapPoint u)).snd + (G (swapPoint u)).snd,
      -(-(H (swapPoint u)).fst) + (G (swapPoint u)).fst) =
    (-(H (swapPoint u)).snd + (G (swapPoint u)).snd,
      (H (swapPoint u)).fst + (G (swapPoint u)).fst)
  simp only [neg_neg]

lemma swapped_geometry {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) :
    GameGeometry (swappedPublic p) (swappedProblem I)
      (fun u => -swapPoint (H (swapPoint u))) (fun u => swapPoint (G (swapPoint u))) := by
  refine ⟨geom.convexY, geom.convexX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact geom.strongY y hy
  · intro x hx
    simpa only [swappedProblem, swapPoint, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp, neg_neg]
      using geom.strongX x hx
  · have h := geom.convexG.comp_linearMap
      (LinearIsometryEquiv.withLpProdComm 2 ℝ p.F p.E).toLinearEquiv.toLinearMap
    convert h using 1
    · ext u
      change (u.fst ∈ p.Y ∧ u.snd ∈ p.X) ↔ (u.snd ∈ p.X ∧ u.fst ∈ p.Y)
      exact and_comm
    · rfl
  · intro u hu
    exact gradient_neg_within (swap_gradient (geom.gradientH _ ((swap_mem (p := swappedPublic p) u).mpr hu)))
  · intro u hu
    exact swap_gradient (geom.gradientG _ ((swap_mem (p := swappedPublic p) u).mpr hu))
  · intro u hu v hv
    rw [← swap_sub, swap_norm]
    have h := geom.lipschitzG _ ((swap_mem (p := swappedPublic p) u).mpr hu)
      _ ((swap_mem (p := swappedPublic p) v).mpr hv)
    simpa only [← swap_sub, swap_norm] using h

lemma swapped_equilibrium {p : Public} {I : Problem p} {u : Space p}
    (hu : IsEquilibrium I u) : IsEquilibrium (swappedProblem I) (swapPoint u) := by
  refine ⟨(swap_mem u).mpr hu.1, ?_, ?_⟩
  · intro y hy
    have h := hu.2.2 y hy
    simpa only [swappedProblem, swapPoint, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp,
      WithLp.toLp_ofLp, sub_eq_add_neg, add_comm] using h
  · intro x hx
    have h := hu.2.1 x hx
    simpa only [swappedProblem, swapPoint, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp,
      WithLp.toLp_ofLp, sub_neg_eq_add, add_comm] using h

lemma swap_field_lipschitz {p : Public} {B : Space p → Space p} {L : ℝ}
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖B u - B v‖ ≤ L * ‖u - v‖) :
    ∀ u ∈ domain (swappedPublic p), ∀ v ∈ domain (swappedPublic p),
      ‖swapPoint (B (swapPoint u)) - swapPoint (B (swapPoint v))‖ ≤ L * ‖u - v‖ := by
  intro u hu v hv
  rw [← swap_sub, swap_norm]
  have h := hlip _ ((swap_mem (p := swappedPublic p) u).mpr hu)
    _ ((swap_mem (p := swappedPublic p) v).mpr hv)
  simpa only [← swap_sub, swap_norm] using h


lemma swapped_oracle_eval {p : Public} (B P : Space p → Space p) :
    (fun q => swapPoint ((Sum.elim B P) ((Sum.map swapPoint swapPoint) q))) =
      Sum.elim (fun u => swapPoint (B (swapPoint u))) (fun u => swapPoint (P (swapPoint u))) := by
  funext q
  cases q <;> rfl

lemma swapped_feasible_query (p : Public) :
    (fun q => feasibleQuery (domain p) ((Sum.map swapPoint swapPoint) q)) =
      feasibleQuery (domain (swappedPublic p)) := by
  funext q
  apply propext
  cases q with
  | inl u => exact swap_mem (p := swappedPublic p) u
  | inr u => rfl

lemma safe_oriented_plan {p : Public} (B P : Space p → Space p)
    (hP : ConstrainedMonotone.Proj (domain p) P) (cfg : FoamConfig) (β : ℝ) (N : ℕ)
    (u0 : Space p) (hu0 : u0 ∈ domain p) (swap : Bool) :
    safeQueries (feasibleQuery (domain p)) (Sum.elim B P)
      (orientedProximalFoamPlan cfg β N u0 swap) := by
  cases swap with
  | false => exact (safe_proximalFoamPlan B P hP.mem cfg β N u0 hu0).1
  | true =>
    have hp := swap_projection hP
    have hm := (swap_mem u0).mpr hu0
    have hh := (safe_proximalFoamPlan (fun u => swapPoint (B (swapPoint u)))
      (fun u => swapPoint (P (swapPoint u))) hp.mem cfg β N (swapPoint u0) hm).1
    have ht := safe_transportPlan (Sum.map swapPoint swapPoint) swapPoint swapPoint
      (Sum.elim B P) (feasibleQuery (domain p)) (proximalFoamPlan cfg β N (swapPoint u0))
      (by simpa only [swapped_oracle_eval, swapped_feasible_query] using hh)
    exact ht

lemma execute_oriented_proximalFoam {p : Public} (B P : Space p → Space p)
    (hP : ConstrainedMonotone.Proj (domain p) P) (cfg : FoamConfig) (β : ℝ) (N K : ℕ)
    (u0 : Space p) (hu0 : u0 ∈ domain p) (swap : Bool)
    (oracle : Oracle (Space p ⊕ Space p) (Space p))
    (hf : ∀ k seed u, u ∈ domain p → oracle.answer k (0, Sum.inl u) seed = B u)
    (hp : ∀ k seed u, oracle.answer k (0, Sum.inr u) seed = P u)
    (ω : (i : ℕ) → oracle.Seed i) (hK : foamCalls cfg * N ≤ K) :
    execute oracle (orientedProximalFoam cfg β N u0 swap) (fun _ => K) () ω =
      QueryPlan.eval (Sum.elim B P) (orientedProximalFoamPlan cfg β N u0 swap) := by
  apply execute_safe_plan _ _ _ _ _ _ (Sum.elim B P) (feasibleQuery (domain p)) oracle () ω
  · intro k q hq
    cases q with
    | inl u => exact hf k (ω k.length) u hq
    | inr u => exact hp k (ω k.length) u
  · exact safe_oriented_plan B P hP cfg β N u0 hu0 swap
  · exact hK


lemma swap_complete {p : Public} (hC : IsComplete (domain p)) :
    IsComplete (domain (swappedPublic p)) := by
  have he : domain (swappedPublic p) =
      (LinearIsometryEquiv.withLpProdComm 2 ℝ p.F p.E) ⁻¹' domain p := by
    ext u
    change (u.fst ∈ p.Y ∧ u.snd ∈ p.X) ↔ (u.snd ∈ p.X ∧ u.fst ∈ p.Y)
    exact and_comm
  rw [he]
  exact (hC.isClosed.preimage (LinearIsometryEquiv.withLpProdComm 2 ℝ p.F p.E).continuous).isComplete

lemma swap_diameter {p : Public} (hD : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖u - v‖ ≤ p.D) :
    ∀ u ∈ domain (swappedPublic p), ∀ v ∈ domain (swappedPublic p), ‖u - v‖ ≤ p.D := by
  intro u hu v hv
  have h := hD _ ((swap_mem (p := swappedPublic p) u).mpr hu)
    _ ((swap_mem (p := swappedPublic p) v).mpr hv)
  simpa only [← swap_sub, swap_norm] using h

lemma swap_accuracy {p : Public} {s : Space p} {u : Space (swappedPublic p)} {ε : ℝ}
    (hu : u ∈ domain (swappedPublic p) ∧ ‖u - swapPoint s‖ ^ 2 ≤ ε) :
    swapPoint u ∈ domain p ∧ ‖swapPoint u - s‖ ^ 2 ≤ ε := by
  refine ⟨(swap_mem (p := swappedPublic p) u).mpr hu.1, ?_⟩
  have he : ‖swapPoint u - s‖ = ‖u - swapPoint s‖ := by
    rw [← swap_norm (swapPoint u - s), swap_sub, swap_swap]
  rw [he]
  exact hu.2

end OracleTemplate.NearZeroSum
