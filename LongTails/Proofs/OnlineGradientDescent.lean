import LongTails.Algorithms.OnlineGradientDescent
import LongTails.Proofs.Execution
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

lemma execution_trace (p : Public) (losses : ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ)
    (O : Oracle p.K (EuclideanSpace ℝ (Fin p.d)))
    (ho : ∀ history, history.length < steps p → ∀ query seed,
      O.answer history query seed = gradient (losses history.length) query.2)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    (executeWithTrace O (algorithm p) (fun _ => steps p) seed ξ).2 =
      (List.range (steps p)).map (fun t =>
        ((0, trajectory p losses t), gradient (losses t) (trajectory p losses t))) := by
  let entry := fun t =>
    (((0 : Fin 1), trajectory p losses t), gradient (losses t) (trajectory p losses t))
  let advance := fun sc : (algorithm p).State × List ((Fin 1 × p.K) × EuclideanSpace ℝ (Fin p.d)) =>
    let query := (algorithm p).query sc.1
    let reply := O.answer sc.2 query (ξ sc.2.length)
    ((algorithm p).update sc.1 reply, sc.2 ++ [(query, reply)])
  have hi : ∀ t ≤ steps p, advance^[t] ((algorithm p).initial seed, []) =
      (trajectory p losses t, (List.range t).map entry) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', ih (by omega)]
      dsimp only [advance]
      rw [ho _ (by simpa using (show t < steps p by omega))]
      simp only [List.length_map, List.length_range]
      simp [algorithm, trajectory, List.range_succ, List.map_append, entry]
  rw [executeWithTrace_indexed]
  change (advance^[steps p] ((algorithm p).initial seed, [])).2 = _
  rw [hi _ le_rfl]

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
