import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace LongTails.Proofs.FiniteSumNondualLowerAffine

open LongTails.Setups.FiniteSumNondualSmoothConvex OracleTemplate

noncomputable def signed (b : Bool) : ℝ := if b then 1 else -1

lemma signed_sq (b : Bool) : signed b ^ 2 = 1 := by cases b <;> norm_num [signed]

lemma signed_abs (b : Bool) : |signed b| = 1 := by cases b <;> norm_num [signed]

noncomputable def needleVector (p : Params) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden i : Fin p.n) : Point p :=
  if i = hidden then (signed b * M) • EuclideanSpace.single j 1 else 0

noncomputable def needleComponent (p : Params) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden i : Fin p.n) (x : Point p) : ℝ :=
  inner ℝ (needleVector p j M b hidden i) x

noncomputable def needleOracle (p : Params) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden : Fin p.n) : Oracle (Fin p.n × Feasible p) (Point p) where
  answer := fun _ q _ => needleVector p j M b hidden q.2.1

lemma needle_hasGradient (p : Params) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden i : Fin p.n) (x : Point p) :
    HasGradientAt (needleComponent p j M b hidden i) (needleVector p j M b hidden i) x := by
  exact (InnerProductSpace.toDual ℝ (Point p) (needleVector p j M b hidden i)).hasFDerivAt

lemma needle_admissible (p : Params) (hL : 0 ≤ p.L) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden : Fin p.n) : spec.admissible p (needleComponent p j M b hidden)
      (needleOracle p j M b hidden) := by
  have hg (i : Fin p.n) (x : Point p) : gradient (needleComponent p j M b hidden i) x =
      needleVector p j M b hidden i := (needle_hasGradient p j M b hidden i x).gradient
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (InnerProductSpace.toDual ℝ (Point p) (needleVector p j M b hidden i)).toLinearMap.convexOn
      convex_univ
  · intro i x
    rw [hg]
    exact needle_hasGradient p j M b hidden i x
  · intro i x y
    rw [hg, hg, sub_self, norm_zero]
    exact mul_nonneg hL (norm_nonneg _)
  · intro history seed i x
    exact (hg i x.val).symm

lemma needle_objective (p : Params) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden : Fin p.n) (x : Point p) :
    objective (needleComponent p j M b hidden) x = (p.n : ℝ)⁻¹ * (signed b * M * x j) := by
  unfold objective LongTails.Setups.FiniteSumSmoothAndConvex.objective
  congr 1
  rw [Finset.sum_eq_single hidden]
  · simp [needleComponent, needleVector, inner_smul_left, EuclideanSpace.inner_single_left]
  · intro i _ hi
    simp [needleComponent, needleVector, hi]
  · simp

lemma feasible_coordinate (p : Params) (x : Feasible p) (j : Fin p.d) : |x.val j| ≤ p.R := by
  exact (Finset.single_le_sum (fun i _ => abs_nonneg (x.val i)) (Finset.mem_univ j)).trans x.property

noncomputable def needleMinimizer (p : Params) (j : Fin p.d) (b : Bool) : Feasible p :=
  ⟨EuclideanSpace.single j (-(signed b) * p.R), by
    change (∑ i, |EuclideanSpace.single j (-(signed b) * p.R) i|) ≤ p.R
    simp [PiLp.single_apply, apply_ite, abs_mul, signed_abs, abs_of_nonneg p.hR]⟩

lemma needle_minimum_value (p : Params) (j : Fin p.d) (M : ℝ) (b : Bool)
    (hidden : Fin p.n) :
    objective (needleComponent p j M b hidden) (needleMinimizer p j b).val = -(M * p.R / p.n) := by
  rw [needle_objective]
  simp only [needleMinimizer, PiLp.single_apply, ite_true]
  cases b <;> simp [signed, div_eq_mul_inv] <;> ring

lemma needle_gap_nonneg (p : Params) (j : Fin p.d) (M : ℝ) (hM : 0 ≤ M) (b : Bool)
    (hidden : Fin p.n) (x : Feasible p) :
    0 ≤ objective (needleComponent p j M b hidden) x.val + M * p.R / p.n := by
  rw [needle_objective]
  have hx := feasible_coordinate p x j
  have hn : (0 : ℝ) < p.n := by exact_mod_cast (NeZero.pos p.n)
  have he : (p.n : ℝ)⁻¹ * (signed b * M * x.val j) + M * p.R / p.n =
      (p.n : ℝ)⁻¹ * (M * (signed b * x.val j + p.R)) := by ring
  rw [he]
  apply mul_nonneg (inv_nonneg.mpr hn.le)
  apply mul_nonneg hM
  cases b <;> simp only [signed, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
  · linarith [le_abs_self (x.val j)]
  · linarith [neg_le_abs (x.val j)]

lemma needle_minimum (p : Params) (j : Fin p.d) (M : ℝ) (hM : 0 ≤ M) (b : Bool)
    (hidden : Fin p.n) : IsMinOn (objective (needleComponent p j M b hidden)) (domain p)
      (needleMinimizer p j b).val := by
  intro x hx
  change objective (needleComponent p j M b hidden) (needleMinimizer p j b).val ≤
    objective (needleComponent p j M b hidden) x
  rw [needle_minimum_value]
  have h := needle_gap_nonneg p j M hM b hidden ⟨x, hx⟩
  linarith

noncomputable def zeroState {p : Params}
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p)) (seed : A.Seed) (t : ℕ) : A.State :=
  (fun s => A.update s 0)^[t] (A.initial seed)

noncomputable def visited {p : Params}
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p)) (seed : A.Seed) (T : ℕ) :
    Finset (Fin p.n) := (Finset.range T).image (fun t => (A.query (zeroState A seed t)).2.1)

lemma visited_card {p : Params}
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p)) (seed : A.Seed) (T : ℕ) :
    (visited A seed T).card ≤ T := by
  exact (Finset.card_image_le).trans (by simp)

lemma execute_unvisited {p : Params} (j : Fin p.d) (M : ℝ) (b : Bool) (hidden : Fin p.n)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (hh : hidden ∉ visited A seed T) :
    execute (needleOracle p j M b hidden) A (fun _ => T) seed ξ = A.output (zeroState A seed T) := by
  have hξ : ξ = fun _ => () := by funext t; exact Subsingleton.elim _ _
  subst ξ
  have hi : ∀ t, t ≤ T →
      (fun s => A.update s (needleVector p j M b hidden (A.query s).2.1))^[t] (A.initial seed) =
        zeroState A seed t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hn : (A.query (zeroState A seed t)).2.1 ≠ hidden := by
        intro he
        apply hh
        exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), he⟩
      rw [needleVector, ite_eq_right hn]
      exact (Function.iterate_succ_apply' (fun s => A.update s 0) t (A.initial seed)).symm
  change execute { answer := fun _ q _ => needleVector p j M b hidden q.2.1 }
    A (fun _ => T) seed = _
  have he := execute_iterate (fun q : Fin p.n × Feasible p => needleVector p j M b hidden q.1) A T seed
  exact he.trans (congrArg A.output (hi T le_rfl))

noncomputable def signedGap {p : Params} (j : Fin p.d) (M : ℝ)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (hidden : Fin p.n) (b : Bool) : ℝ :=
  objective (needleComponent p j M b hidden)
    (execute (needleOracle p j M b hidden) A (fun _ => T) seed ξ).val + M * p.R / p.n

lemma pair_gap_unvisited {p : Params} (j : Fin p.d) (M : ℝ)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (hidden : Fin p.n)
    (hh : hidden ∉ visited A seed T) :
    signedGap j M A T seed ξ hidden false + signedGap j M A T seed ξ hidden true =
      2 * (M * p.R / p.n) := by
  simp only [signedGap, execute_unvisited j M false hidden A T seed ξ hh,
    execute_unvisited j M true hidden A T seed ξ hh, needle_objective]
  norm_num [signed]
  ring

lemma pair_gap_sum {p : Params} (j : Fin p.d) (M : ℝ) (hM : 0 ≤ M)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (T : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (hT : 4 * T ≤ p.n) :
    23 * (2 * (M * p.R / p.n)) * p.n ≤
      32 * ∑ hidden : Fin p.n,
        (signedGap j M A T seed ξ hidden false + signedGap j M A T seed ξ hidden true) := by
  classical
  have hs : (∑ i : Fin p.n, if i ∈ visited A seed T then (1 : ℝ) else 0) =
      ((visited A seed T).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have hv : 4 * ((visited A seed T).card : ℝ) ≤ p.n := by
    exact_mod_cast (Nat.mul_le_mul_left 4 (visited_card A seed T)).trans hT
  have hR := p.hR
  have hg (hidden : Fin p.n) (b : Bool) : 0 ≤ signedGap j M A T seed ξ hidden b :=
    needle_gap_nonneg p j M hM b hidden _
  have h := FiniteSumNondualLowerAveraging.finite_gap_average
    (Finset.univ : Finset (Fin p.n)) (Finset.univ : Finset Unit)
    (fun hidden _ => hidden ∈ visited A seed T) (fun _ _ => False)
    (fun hidden _ => signedGap j M A T seed ξ hidden false + signedGap j M A T seed ξ hidden true)
    (2 * (M * p.R / p.n)) (by positivity)
    (fun hidden _ _ _ => add_nonneg (hg hidden false) (hg hidden true))
    (fun hidden _ _ _ hh _ => (pair_gap_unvisited j M A T seed ξ hidden hh).ge)
    (fun _ _ => by simpa only [hs, Finset.card_univ, Fintype.card_fin] using hv)
    (fun _ _ => by simp)
  simpa using h

lemma successful_signed_objective {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (p : Params) (j : Fin p.d) (M : ℝ) (hM : 0 ≤ M) (b : Bool) (hidden : Fin p.n)
    (output : Ω → Feasible p) (hs : spec.successful p (needleComponent p j M b hidden) output P) :
    Integrable (fun ω => objective (needleComponent p j M b hidden) (output ω).val + M * p.R / p.n)
        (P : Measure Ω) ∧
      (∫ ω, objective (needleComponent p j M b hidden) (output ω).val + M * p.R / p.n
        ∂(P : Measure Ω)) ≤ p.ε := by
  obtain ⟨_, xstar, hm, hi, he⟩ := hs
  have hvalue : objective (needleComponent p j M b hidden) xstar.val = -(M * p.R / p.n) := by
    apply le_antisymm
    · have h := hm (needleMinimizer p j b).property
      change objective (needleComponent p j M b hidden) xstar.val ≤
        objective (needleComponent p j M b hidden) (needleMinimizer p j b).val at h
      rwa [needle_minimum_value] at h
    · have h := needle_gap_nonneg p j M hM b hidden xstar
      linarith
  simpa only [hvalue, sub_neg_eq_add] using And.intro hi he

lemma exists_needle_failure {p : Params} (j : Fin p.d) (M : ℝ) (hM : 0 ≤ M)
    (A : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p))
    (P : ProbabilityMeasure (A.Seed × (ℕ → Unit))) (T : ℕ) (hT : 4 * T ≤ p.n)
    (hε : 32 * p.ε < 23 * (M * p.R / p.n)) :
    ∃ hidden : Fin p.n, ∃ b : Bool,
      ¬ spec.successful p (needleComponent p j M b hidden)
        (fun ω : A.Seed × (ℕ → Unit) => execute (needleOracle p j M b hidden)
          A (fun _ => T) ω.1 ω.2) P := by
  classical
  by_contra h
  push Not at h
  have hs (hidden : Fin p.n) (b : Bool) :=
    successful_signed_objective P p j M hM b hidden _ (h hidden b)
  let f := fun (ω : A.Seed × (ℕ → Unit)) (hidden : Fin p.n) (_ : Unit) =>
    signedGap j M A T ω.1 ω.2 hidden false + signedGap j M A T ω.1 ω.2 hidden true
  have hi (hidden : Fin p.n) (b : Bool) :
      Integrable (fun ω : A.Seed × (ℕ → Unit) => signedGap j M A T ω.1 ω.2 hidden b)
        (P : Measure _) := (hs hidden b).1
  have hf (hidden : Fin p.n) (u : Unit) : Integrable (fun ω => f ω hidden u) (P : Measure _) :=
    (hi hidden false).add (hi hidden true)
  have hb (hidden : Fin p.n) : (∫ ω, f ω hidden () ∂(P : Measure _)) ≤ 2 * p.ε := by
    rw [show (fun ω => f ω hidden ()) =
      (fun ω : A.Seed × (ℕ → Unit) => signedGap j M A T ω.1 ω.2 hidden false +
        signedGap j M A T ω.1 ω.2 hidden true) from rfl,
      integral_add (hi hidden false) (hi hidden true)]
    have hfalse := (hs hidden false).2
    have htrue := (hs hidden true).2
    change (∫ ω : A.Seed × (ℕ → Unit), signedGap j M A T ω.1 ω.2 hidden false ∂(P : Measure _)) ≤ p.ε at hfalse
    change (∫ ω : A.Seed × (ℕ → Unit), signedGap j M A T ω.1 ω.2 hidden true ∂(P : Measure _)) ≤ p.ε at htrue
    linarith
  have hl := FiniteSumNondualLowerBound.finite_integral_lower P f
    (23 * (2 * (M * p.R / p.n)) * p.n) hf
    (fun ω => by simpa [f] using pair_gap_sum j M hM A T ω.1 ω.2 hT)
  have hu : (∑ hidden : Fin p.n, ∑ u : Unit, ∫ ω, f ω hidden u ∂(P : Measure _)) ≤
      (p.n : ℝ) * (2 * p.ε) := by
    simp only [Fintype.sum_unique]
    have h := Finset.sum_le_sum (fun hidden (_ : hidden ∈ (Finset.univ : Finset (Fin p.n))) => hb hidden)
    simpa using h
  have hn : (0 : ℝ) < p.n := by exact_mod_cast (NeZero.pos p.n)
  have hc := mul_lt_mul_of_pos_right hε hn
  nlinarith [mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 32)]

lemma component_not_convergence (budget : Params → Fin 1 → ℕ) (p : Params)
    (hp : spec.valid p) (hT : 4 * budget p 0 ≤ p.n) : ¬ Convergence spec budget := by
  classical
  rintro ⟨make, hresult, _⟩
  let j : Fin p.d := ⟨0, hp.1⟩
  let M : ℝ := 2 * p.n * p.ε / p.R
  have hR : 0 < p.R := hp.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2
  have hn : (0 : ℝ) < p.n := by exact_mod_cast (NeZero.pos p.n)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hratio : M * p.R / p.n = 2 * p.ε := by
    dsimp [M]
    field_simp
  have hgap : 32 * p.ε < 23 * (M * p.R / p.n) := by rw [hratio]; linarith
  let A := make p
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨hidden, b, hf⟩ := exists_needle_failure j M hM A P (budget p 0) hT hgap
  apply hf
  have hs := hresult p hp (needleComponent p j M b hidden) (needleOracle p j M b hidden)
    (needle_admissible p hp.2.2.1.le j M b hidden)
  have hb : budget p = fun _ => budget p 0 := by
    funext i
    exact congrArg (budget p) (Subsingleton.elim i 0)
  rw [hb] at hs
  exact hs

end LongTails.Proofs.FiniteSumNondualLowerAffine
