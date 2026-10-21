import LongTails.Algorithms.OnlineGradientDescent
import LongTails.Proofs.FrankWolfeDescent
import LongTails.Proofs.TerminalClippingEnergy

namespace OracleTemplate.OnlineGradientDescent

open LongTails.Setups.OnlineConvexBoundedGradient
open scoped RealInnerProductSpace

lemma steps_pos (p : Public) (hp : spec.valid p.toParams p.T) : 0 < steps p :=
  hp.2.2.1

lemma project_distance (p : Public) (hc : Convex ℝ p.K) (hk : IsCompact p.K)
    (z : EuclideanSpace ℝ (Fin p.d)) (u : p.K) :
    ‖(project p z).val - u.val‖ ^ 2 ≤ ‖z - u.val‖ ^ 2 := by
  have hm : ‖z - (project p z).val‖ = ⨅ w : p.K, ‖z - w.val‖ := by
    classical
    simp only [project, dite_eq_left (And.intro hk hc)]
    exact (exists_norm_eq_iInf_of_complete_convex ⟨p.x0.val, p.x0.property⟩
      hk.isComplete hc z).choose_spec.2
  exact TerminalClipping.projection_distance
    ((norm_eq_iInf_iff_real_inner_le_zero hc (project p z).property).mp hm u u.property)

lemma step_bound (p : Public) (hp : spec.valid p.toParams p.T)
    (losses : ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ)
    (hl : ∀ t < (steps p), ConvexOn ℝ p.K (losses t) ∧
      ∀ x ∈ p.K, HasGradientAt (losses t) (gradient (losses t) x) x ∧
        ‖gradient (losses t) x‖ ≤ p.G)
    (t : ℕ) (ht : t < (steps p)) (u : p.K) :
    2 * stepSize p * (losses t (trajectory p losses t) - losses t u) ≤
      ‖(trajectory p losses t).val - u.val‖ ^ 2 -
        ‖(trajectory p losses (t + 1)).val - u.val‖ ^ 2 + stepSize p ^ 2 * p.G ^ 2 := by
  have hη : 0 < stepSize p := by
    unfold stepSize
    exact div_pos hp.2.2.2.1 (mul_pos hp.2.2.2.2.1 (Real.sqrt_pos.mpr (by exact_mod_cast steps_pos p hp)))
  have hs := FrankWolfe.convex_support_on (hl t ht).1
    (trajectory p losses t).property u.property ((hl t ht).2 _ (trajectory p losses t).property).1
  rw [show u.val - (trajectory p losses t).val = -((trajectory p losses t).val - u.val) by module,
    inner_neg_right] at hs
  have hsη := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * stepSize p)
  have hg := pow_le_pow_left₀ (norm_nonneg _) ((hl t ht).2 _ (trajectory p losses t).property).2 2
  have hd := project_distance p hp.1 hp.2.1
    ((trajectory p losses t).val - stepSize p • gradient (losses t) (trajectory p losses t)) u
  change ‖(trajectory p losses (t + 1)).val - u.val‖ ^ 2 ≤ _ at hd
  have he : (trajectory p losses t).val - stepSize p • gradient (losses t) (trajectory p losses t) - u.val =
      ((trajectory p losses t).val - u.val) - stepSize p • gradient (losses t) (trajectory p losses t) := by module
  rw [he, norm_sub_sq_real ((trajectory p losses t).val - u.val)
    (stepSize p • gradient (losses t) (trajectory p losses t)),
    real_inner_smul_right, real_inner_comm,
    norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow] at hd
  nlinarith [mul_le_mul_of_nonneg_left hg (sq_nonneg (stepSize p))]

lemma regret_bound (p : Public) (hp : spec.valid p.toParams p.T)
    (losses : ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ)
    (hl : ∀ t < (steps p), ConvexOn ℝ p.K (losses t) ∧
      ∀ x ∈ p.K, HasGradientAt (losses t) (gradient (losses t) x) x ∧
        ‖gradient (losses t) x‖ ≤ p.G) (u : p.K) :
    (∑ t ∈ Finset.range (steps p), losses t (trajectory p losses t)) -
      (∑ t ∈ Finset.range (steps p), losses t u) ≤ p.D * p.G * Real.sqrt (steps p) := by
  have hsum : ∀ n ≤ (steps p),
      2 * stepSize p * (∑ t ∈ Finset.range n, (losses t (trajectory p losses t) - losses t u)) ≤
        ‖p.x0.val - u.val‖ ^ 2 - ‖(trajectory p losses n).val - u.val‖ ^ 2 +
          n * stepSize p ^ 2 * p.G ^ 2 := by
    intro n
    induction n with
    | zero => intro _; simp [trajectory]
    | succ n ih =>
      intro hn
      have hs := step_bound p hp losses hl n (by omega) u
      have hi := ih (by omega)
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith
  have hs := hsum (steps p) le_rfl
  have hD := pow_le_pow_left₀ (norm_nonneg _) (hp.2.2.2.2.2 _ p.x0.property _ u.property) 2
  have hT : 0 < ((steps p) : ℝ) := by exact_mod_cast steps_pos p hp
  have hroot := Real.sqrt_pos.mpr hT
  have hη : 0 < stepSize p := div_pos hp.2.2.2.1 (mul_pos hp.2.2.2.2.1 hroot)
  have htune : p.D ^ 2 + ((steps p) : ℝ) * stepSize p ^ 2 * p.G ^ 2 =
      2 * stepSize p * (p.D * p.G * Real.sqrt (steps p)) := by
    unfold stepSize
    have hr := Real.sq_sqrt hT.le
    field_simp [hp.2.2.2.2.1.ne', hroot.ne']
    nlinarith
  rw [Finset.sum_sub_distrib] at hs
  have hn := sq_nonneg ‖(trajectory p losses (steps p)).val - u.val‖
  nlinarith

lemma trace_indexed {Query Reply Output : Type*} (oracle : Oracle Query Reply)
    (A : Algorithm Query Reply Output) (K : ℕ) (seed : A.Seed)
    (ξ : (k : ℕ) → oracle.Seed k) :
    (executeWithTrace oracle A (fun _ => K) seed ξ).2 =
      (List.range K).map (fun k =>
        let sc := ((fun sc : A.State × ℕ =>
          (A.update sc.1 (oracle.answer sc.2 (A.query sc.1) (ξ sc.2)), sc.2 + 1))^[k]
          (A.initial seed, 0))
        (A.query sc.1, oracle.answer sc.2 (A.query sc.1) (ξ sc.2))) := by
  unfold executeWithTrace
  simp only [Fin.sum_univ_one]
  generalize A.initial seed = state
  generalize (0 : ℕ) = call
  induction K generalizing state call with
  | zero => rfl
  | succ k ih =>
    change (if k + 1 = 0 then (A.output state, []) else _).2 = _
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    have hr : Function.update (fun _ : Fin 1 => k + 1) (A.query state).1 k = fun _ => k := by
      funext i
      have hi : i = (A.query state).1 := Subsingleton.elim _ _
      subst i
      simp
    simp only [Nat.add_sub_cancel]
    rw [hr]
    rw [List.range_succ_eq_map, List.map_cons]
    simp only [Function.iterate_zero, id_eq, List.map_map, Function.comp_def,
      Function.iterate_succ_apply]
    congr 1
    exact ih _ _

lemma execution_trace (p : Public) (losses : ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ)
    (O : Oracle p.K (EuclideanSpace ℝ (Fin p.d)))
    (ho : ∀ t < (steps p), ∀ query seed, O.answer t query seed = gradient (losses t) query.2)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    (executeWithTrace O (algorithm p) (fun _ => (steps p)) seed ξ).2 =
      (List.range (steps p)).map (fun t =>
        ((0, trajectory p losses t), gradient (losses t) (trajectory p losses t))) := by
  let advance := fun sc : (algorithm p).State × ℕ =>
    ((algorithm p).update sc.1 (O.answer sc.2 ((algorithm p).query sc.1) (ξ sc.2)), sc.2 + 1)
  have hi : ∀ t ≤ (steps p), advance^[t] ((algorithm p).initial seed, 0) = (trajectory p losses t, t) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', ih (by omega)]
      dsimp [advance, algorithm]
      rw [ho t (by omega)]
      rfl
  rw [trace_indexed]
  apply List.map_congr_left
  intro t ht
  have h := hi t (Nat.le_of_lt (List.mem_range.mp ht))
  change (let sc := advance^[t] ((algorithm p).initial seed, 0); _) = _
  rw [h]
  dsimp [algorithm]
  rw [ho t (List.mem_range.mp ht)]

lemma execution_success (p : Public) (hp : spec.valid p.toParams p.T)
    (losses : ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ)
    (O : Oracle p.K (EuclideanSpace ℝ (Fin p.d))) (ho : spec.admissible p.toParams p.T losses O)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    let trace := (executeWithTrace O (algorithm p) (fun _ => (steps p)) seed ξ).2
    trace.length = p.T ∧ ∀ u : p.K,
      (trace.zipIdx.map fun xt => losses xt.2 xt.1.1.2).sum -
        ∑ t ∈ Finset.range p.T, losses t u.val ≤ p.D * p.G * Real.sqrt p.T := by
  dsimp only
  rw [execution_trace p losses O (fun t _ query seed => ho.2 t query seed)]
  simp only [List.length_map, List.length_range]
  refine ⟨rfl, ?_⟩
  intro u
  have hm : (((List.range (steps p)).map (fun t =>
        (((0 : Fin 1), trajectory p losses t), gradient (losses t) (trajectory p losses t)))).zipIdx.map
        (fun xt => losses xt.2 xt.1.1.2)) =
      (List.range (steps p)).map (fun t => losses t (trajectory p losses t)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [hm]
  have hsum : ∀ n, ((List.range n).map (fun t => losses t (trajectory p losses t))).sum =
      ∑ t ∈ Finset.range n, losses t (trajectory p losses t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [List.sum_range_succ, Finset.sum_range_succ, ih]
  rw [hsum]
  exact regret_bound p hp losses (fun t _ => ho.1 t) u

end OracleTemplate.OnlineGradientDescent
