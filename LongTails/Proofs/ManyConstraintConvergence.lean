import LongTails.Algorithms.ManyConstraintMethod
import LongTails.Proofs.ManyConstraintPlanEval
import LongTails.Proofs.ManyConstraintFinal
import LongTails.Proofs.ManyConstraintBudget
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Set

namespace LongTails.Proofs.ManyConstraintConvergence

open OracleTemplate LongTails.Setups.ManyConstraintStochasticConvex
  LongTails.Algorithms.ManyConstraintPlan LongTails.Algorithms.ManyConstraintVR
  LongTails.Algorithms.ManyConstraintMethod LongTails.Proofs.ManyConstraintTuning
  LongTails.Proofs.ManyConstraintPlanEval LongTails.Proofs.ManyConstraintFinal
  LongTails.Proofs.ManyConstraintBudget

noncomputable def budgetG (q : Params) : ℕ :=
  2 * q.m * ⌈(13 + 3264 * Real.sqrt (q.κ / q.m) * (q.σ * q.R / q.ε + q.R * Real.sqrt (q.L / q.ε))) * Real.log (50000 * q.κ * (1 + q.σ * q.R / q.ε + q.L * q.R ^ 2 / q.ε) ^ 2)⌉₊ * ⌈3 + 544 * (q.σ * q.R / q.ε + q.R * Real.sqrt (q.L / q.ε)) / Real.sqrt (q.m * q.κ)⌉₊

noncomputable def budgetP (q : Params) : ℕ :=
  ⌈q.κ * Real.log (4 * q.R ^ 2 / q.δ ^ 2)⌉₊ + 5 * q.m * ⌈(13 + 3264 * Real.sqrt (q.κ / q.m) * (q.σ * q.R / q.ε + q.R * Real.sqrt (q.L / q.ε))) * Real.log (50000 * q.κ * (1 + q.σ * q.R / q.ε + q.L * q.R ^ 2 / q.ε) ^ 2)⌉₊

lemma transfer {q : Params} {M : Model q.E q.Ξ q.m} {O : Oracle (q.E × Option (Fin q.m)) q.E 2}
    {B : Fin 2 → ℕ} {A A' : Algorithm (q.E × Option (Fin q.m)) q.E q.E 2} (h : A = A')
    (hA : spec.successful q M (fun seed : A'.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A' B seed.1 seed.2) ⟨(A'.law : Measure _).prod (O.law : Measure _), inferInstance⟩) :
    spec.successful q M (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A B seed.1 seed.2) ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  subst h; exact hA

noncomputable def oracleOf (q : Params) (M : Model q.E q.Ξ q.m) (P : ProbabilityMeasure (ℕ → q.Ξ)) :
    Oracle (q.E × Option (Fin q.m)) q.E 2 :=
  { Seed := fun _ => q.Ξ, law := P, answer := fun _ query ξ => oracleAnswer M query ξ }

lemma success_generic {q : Params} {M : Model q.E q.Ξ q.m} {P : ProbabilityMeasure (ℕ → q.Ξ)}
    {B : Fin 2 → ℕ} (A : Algorithm (q.E × Option (Fin q.m)) q.E q.E 2)
    (out : A.Seed → (ℕ → q.Ξ) → q.E)
    (hexec : ∀ s ξ, execute (oracleOf q M P) A B s ξ = out s ξ)
    {xs : q.E} (hxs : xs ∈ feasible M) (hmin : IsMinOn (objective M) (feasible M) xs)
    (hF : Measurable (fun w : A.Seed × (ℕ → q.Ξ) => out w.1 w.2))
    (hI1 : Integrable (fun w : A.Seed × (ℕ → q.Ξ) => max (objective M (out w.1 w.2) -
      objective M xs) 0) ((A.law : Measure _).prod (P : Measure _)))
    (hE1 : (∫ w : A.Seed × (ℕ → q.Ξ), max (objective M (out w.1 w.2) - objective M xs) 0
      ∂(A.law : Measure _).prod (P : Measure _)) ≤ q.ε)
    (hI2 : Integrable (fun w : A.Seed × (ℕ → q.Ξ) => Metric.infDist (out w.1 w.2) (feasible M) ^ 2)
      ((A.law : Measure _).prod (P : Measure _)))
    (hE2 : (∫ w : A.Seed × (ℕ → q.Ξ), Metric.infDist (out w.1 w.2) (feasible M) ^ 2
      ∂(A.law : Measure _).prod (P : Measure _)) ≤ q.δ ^ 2) :
    spec.successful q M (fun seed : A.Seed × ((k : ℕ) → q.Ξ) =>
      execute (oracleOf q M P) A B seed.1 seed.2)
      ⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩ := by
  have he : (fun seed : A.Seed × ((k : ℕ) → q.Ξ) =>
      execute (oracleOf q M P) A B seed.1 seed.2) =
      fun w => out w.1 w.2 := funext fun w => hexec w.1 w.2
  rw [he]
  exact ⟨hF, xs, hxs, hmin, hI1, hE1, hI2, hE2⟩

theorem convergence_main :
    Convergence spec (fun q i => if i = 0 then budgetG q else budgetP q) := by
  refine ⟨method, ?_, fun _ _ => trivial⟩
  rintro q ⟨hm, hL, hR, hσ, hκ, hε, hδ⟩ M O ⟨P, hIID, rfl, hmeas, hconv, hgrad, hlip, hint, hC,
    hproj, hLR, xs, hxs, hmin, hx0, hsqi, hsec⟩
  intro A result
  set B : Fin 2 → ℕ := fun i => if i = 0 then budgetG q else budgetP q
  have hPlaw : (P : Measure (ℕ → q.Ξ)) = Measure.infinitePi (fun _ => (M.law : Measure q.Ξ)) := by
    have h := hIID.stream_law.map_eq
    change (P : Measure (ℕ → q.Ξ)).map id = _ at h
    simpa only [Measure.map_id] using h
  rcases hR.eq_or_lt with hR0 | hRpos
  · have hdif : method q = trivialMethod q := by
      unfold method
      split_ifs with h
      · exact absurd h.1 (by linarith)
      · rfl
    refine transfer (A := method q) hdif ?_
    have hx : q.x0 = xs := by
      have : ‖q.x0 - xs‖ ≤ 0 := hR0 ▸ hx0
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    have hexec : ∀ (seed : Unit) (ξ : (k : ℕ) → q.Ξ),
        execute (oracleOf q M P)
          (trivialMethod q) B seed ξ = q.x0 := by
      intro seed ξ
      unfold trivialMethod
      exact Plan2.execute_plan _ _ _ _ _ _ (oracleOf q M P) B (Nat.zero_le _) (Nat.zero_le _) seed ξ
        (fun n qq => oracleAnswer M qq (ξ n)) (fun _ _ => rfl)
    refine success_generic (trivialMethod q) (fun _ _ => q.x0) hexec hxs hmin measurable_const
      ?_ ?_ ?_ ?_
    · simp [hx]
    · simp [hx]; exact hε.le
    · simp [Metric.infDist_zero_of_mem (hx ▸ hxs : q.x0 ∈ feasible M)]
    · simp [Metric.infDist_zero_of_mem (hx ▸ hxs : q.x0 ∈ feasible M)]; positivity
  · have : NeZero q.m := ⟨hm.ne'⟩
    have hdif : method q = penaltyKatyusha q := by
      unfold method
      split_ifs with h
      · rfl
      · exact absurd ⟨hRpos, hm⟩ h
    refine transfer (A := method q) hdif ?_
    set k := knobs q.m q.κ q.σ q.ε q.L q.R q.x0
    set S := LongTails.Proofs.ManyConstraintTuning.ST q.m q.κ q.σ q.ε q.L q.R
    set Q' := QT q.κ q.R q.δ
    have hreg : ManyConstraintStochastic.Regular (M.law : Measure q.Ξ) M.loss M.grad q.L q.σ xs :=
      ⟨inferInstance, hmeas, hconv, hgrad, hlip, hint, hsqi, hsec⟩
    have H := hyp_of (m := q.m) (ε := q.ε) (K := M.C) (P := M.proj) (x0 := q.x0) hreg hL hσ hκ
      hε hRpos hproj (fun j => (hC j).1) hxs hmin hLR hx0
    have hS := ST_le (m := q.m) hκ hσ hε hL hRpos
    have hb := bT_le (m := q.m) hκ hσ hε hL hRpos
    have hb0 : S * (k.M * k.b) ≤ B 0 := by
      show S * (2 * q.m * bT q.m q.κ q.σ q.ε q.L q.R) ≤ budgetG q
      unfold budgetG
      calc S * (2 * q.m * bT q.m q.κ q.σ q.ε q.L q.R) =
          2 * q.m * S * bT q.m q.κ q.σ q.ε q.L q.R := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hS) hb
    have hb1 : Q' + S * (k.M * 2 + q.m) ≤ B 1 := by
      show Q' + S * (2 * q.m * 2 + q.m) ≤ budgetP q
      unfold budgetP
      have : S * (2 * q.m * 2 + q.m) = 5 * q.m * S := by ring
      rw [this]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hS) _
    have hexec : ∀ (seed : (penaltyKatyusha q).Seed)
        (ξ : (k : ℕ) → q.Ξ),
        execute (oracleOf q M P)
          (penaltyKatyusha q) B seed ξ = out M.grad M.proj k S Q' seed ξ := by
      intro seed ξ
      unfold penaltyKatyusha
      exact (Plan2.execute_plan _ _ _ _ _ _ (oracleOf q M P) B hb0 hb1 seed ξ
        (fun n qq => oracleAnswer M qq (ξ n)) (fun _ _ => rfl)).trans
        (evalS_fullPlan M.grad M.proj ξ k S Q' seed)
    obtain ⟨hF, hI1, hE1, hI2, hE2⟩ := final_bounds H hκ hε hRpos hδ
    have hlaw : ((penaltyKatyusha q).law : Measure (penaltyKatyusha q).Seed).prod (P : Measure (ℕ → q.Ξ)) =
        (PMF.uniformOfFintype (Sd q.m S Q')).toMeasure.prod
          (Measure.infinitePi fun _ => (M.law : Measure q.Ξ)) := by
      rw [hPlaw]; rfl
    refine success_generic (penaltyKatyusha q) (fun s ξ => out M.grad M.proj k S Q' s ξ) hexec
      hxs hmin hF ?_ ?_ ?_ ?_
    · rw [hlaw]; exact hI1
    · rw [hlaw]; exact hE1
    · rw [hlaw]; exact hI2
    · rw [hlaw]; exact hE2

end LongTails.Proofs.ManyConstraintConvergence
