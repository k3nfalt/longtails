import LongTails.Proofs.HolderNoiseInitialization
import LongTails.Proofs.HolderNoiseHardExecution
import LongTails.Proofs.HolderNoiseCoinExposure

namespace LongTails.Proofs.HolderNoiseInitializationExecution

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower
open HolderNoiseInitialization HolderNoiseHardOracle HolderNoiseHardAdmissible HolderNoiseHardExecution
open HolderNoiseHiding

lemma exposure_zero (β : ℕ → Bool) (N : ℕ) (hN : exposure β N = 0) (t : ℕ) (ht : t < N) : β t = false := by
  have hm := exposure_mono β (show t + 1 ≤ N by omega)
  rw [hN, exposure] at hm
  cases hb : β t
  · rfl
  · simp only [hb, ite_true] at hm
    omega

lemma execute_silent (q : LowerParams) (A : Alg q) (u : EuclideanSpace ℝ (Fin q.d))
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (seed : A.Seed) (β : ℕ → Bool)
    (hN : exposure β N = 0) :
    execute (pairOracle q hp hp1 (oracleValue p (field q.L u q.x0) (noise q.L u)))
      A (fun _ => N) seed β =
      A.output ((fun s => A.update s (q.L • ((A.query s).2.1 - q.x0),
        q.L • ((A.query s).2.2 - q.x0)))^[N] (A.initial seed)) := by
  let response := fun t (z : Fin 1 × (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d))) =>
    (oracleValue p (field q.L u q.x0) (noise q.L u) z.2.1 (β t),
      oracleValue p (field q.L u q.x0) (noise q.L u) z.2.2 (β t))
  rw [execute_indexed_of_answer (pairOracle q hp hp1
    (oracleValue p (field q.L u q.x0) (noise q.L u))) A N seed β response (fun _ _ => rfl)]
  let step := fun s => A.update s (q.L • ((A.query s).2.1 - q.x0), q.L • ((A.query s).2.2 - q.x0))
  have he (t : ℕ) (ht : t ≤ N) :
      (fun sc : A.State × ℕ => (A.update sc.1 (response sc.2 (A.query sc.1)), sc.2 + 1))^[t]
        (A.initial seed, 0) = (step^[t] (A.initial seed), t) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      simp only [response, exposure_zero β N hN t (by omega), oracle_silent]
      rw [Function.iterate_succ_apply']
  rw [he N le_rfl]

lemma execution_pair_lower (q : LowerParams) (hL : 0 ≤ q.L) (A : Alg q) (u : EuclideanSpace ℝ (Fin q.d))
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (seed : A.Seed) (β : ℕ → Bool) :
    2 * q.L * ‖u‖ * (1 - (exposure β N : ℝ)) ≤
      ‖gradient (objective q.L u q.x0)
        (execute (pairOracle q hp hp1 (oracleValue p (field q.L u q.x0) (noise q.L u)))
          A (fun _ => N) seed β)‖ +
      ‖gradient (objective q.L (-u) q.x0)
        (execute (pairOracle q hp hp1 (oracleValue p (field q.L (-u) q.x0) (noise q.L (-u))))
          A (fun _ => N) seed β)‖ := by
  by_cases hN : exposure β N = 0
  · rw [hN, Nat.cast_zero, sub_zero, mul_one, execute_silent q A u hp hp1 N seed β hN,
      execute_silent q A (-u) hp hp1 N seed β hN]
    rw [(objective_gradient q.L u q.x0 _).gradient, (objective_gradient q.L (-u) q.x0 _).gradient]
    exact field_pair hL u q.x0 _
  · have hn : (1 : ℝ) ≤ exposure β N := by exact_mod_cast (show 1 ≤ exposure β N by omega)
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith : 1 - (exposure β N : ℝ) ≤ 0)).trans
      (add_nonneg (norm_nonneg _) (norm_nonneg _))

end LongTails.Proofs.HolderNoiseInitializationExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseInitializationLower

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower
open HolderNoiseInitialization HolderNoiseInitializationExecution HolderNoiseHardOracle
open HolderNoiseHardAdmissible HolderNoiseHardExecution HolderNoiseHiding HolderNoiseCoinExposure QuasarCoinLaw

lemma pair_failure (q : LowerParams) (hL : 0 ≤ q.L) (A : Alg q) (u : EuclideanSpace ℝ (Fin q.d))
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ)
    (hacc : q.ε < q.L * ‖u‖ * (1 - N * p)) :
    ∃ v : EuclideanSpace ℝ (Fin q.d), (v = u ∨ v = -u) ∧
      ¬ spec.successful q (objective q.L v q.x0)
        (fun z : A.Seed × (ℕ → Bool) =>
          execute (pairOracle q hp hp1 (oracleValue p (field q.L v q.x0) (noise q.L v)))
            A (fun _ => N) z.1 z.2)
        ⟨(A.law : Measure _).prod (coinPath p hp hp1 : Measure _), inferInstance⟩ := by
  classical
  by_contra hfail
  push Not at hfail
  let P : ProbabilityMeasure (A.Seed × (ℕ → Bool)) :=
    ⟨(A.law : Measure _).prod (coinPath p hp hp1 : Measure _), inferInstance⟩
  let f := fun (v : EuclideanSpace ℝ (Fin q.d)) (z : A.Seed × (ℕ → Bool)) =>
    ‖gradient (objective q.L v q.x0)
      (execute (pairOracle q hp hp1 (oracleValue p (field q.L v q.x0) (noise q.L v)))
        A (fun _ => N) z.1 z.2)‖
  have h0 := hfail u (Or.inl rfl)
  have h1 := hfail (-u) (Or.inr rfl)
  have hi0 : Integrable (f u) (P : Measure _) := h0.2.1
  have hi1 : Integrable (f (-u)) (P : Measure _) := h1.2.1
  have hb0 : (∫ z, f u z ∂(P : Measure _)) ≤ q.ε := h0.2.2
  have hb1 : (∫ z, f (-u) z ∂(P : Measure _)) ≤ q.ε := h1.2.2
  have heint : Integrable (fun z : A.Seed × (ℕ → Bool) => (exposure z.2 N : ℝ)) (P : Measure _)  := by
    simpa only [P, ProbabilityMeasure.coe_mk] using (exposure_integrable p hp hp1 N).comp_snd (A.law : Measure A.Seed)
  have hlint : Integrable (fun z : A.Seed × (ℕ → Bool) => 2 * q.L * ‖u‖ * (1 - (exposure z.2 N : ℝ)))
      (P : Measure _) := ((integrable_const 1).sub heint).const_mul _
  have hpoint (z : A.Seed × (ℕ → Bool)) :
      2 * q.L * ‖u‖ * (1 - (exposure z.2 N : ℝ)) ≤ f u z + f (-u) z :=
    execution_pair_lower q hL A u hp hp1 N z.1 z.2
  have hl := integral_mono hlint (hi0.add hi1) hpoint
  have he : (∫ z : A.Seed × (ℕ → Bool), (exposure z.2 N : ℝ) ∂(P : Measure _)) = N * p := by
    change (∫ z, (exposure z.2 N : ℝ) ∂((A.law : Measure A.Seed).prod (coinPath p hp hp1 : Measure (ℕ → Bool)))) = _
    have hprod := integral_fun_snd (μ := (A.law : Measure A.Seed))
      (ν := (coinPath p hp hp1 : Measure (ℕ → Bool))) (fun β : ℕ → Bool => (exposure β N : ℝ))
    rw [exposure_integral] at hprod
    simpa only [probReal_univ, one_smul] using hprod
  simp only [Pi.add_apply] at hl
  rw [integral_const_mul, integral_sub (integrable_const 1) heint, integral_const, he,
    integral_add hi0 hi1] at hl
  simp only [probReal_univ, one_smul] at hl
  nlinarith

end LongTails.Proofs.HolderNoiseInitializationLower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseInitializationFailure

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower
open HolderNoiseInitialization HolderNoiseInitializationLower HolderNoiseHardOracle
open HolderNoiseHardAdmissible HolderNoiseHardExecution

lemma dimension_pos (q : LowerParams) (hq : spec.valid q) : 0 < q.d := by
  rcases hq with ⟨hv, _, hd⟩
  change 0 < q.L ∧ 0 ≤ q.M ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hv
  rcases hv with ⟨hL, _, _, _, _, hΔ, hε⟩
  exact (Nat.ceil_pos.mpr (by positivity)).trans_le hd

lemma failure_of_parameters (q : LowerParams) (hL : 0 ≤ q.L) (hM : 0 ≤ q.M)
    (A : Alg q) (u : EuclideanSpace ℝ (Fin q.d)) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (N : ℕ)
    (hΔ : q.L / 2 * ‖u‖ ^ 2 ≤ q.Δ)
    (hσ : p = 1 ∨ q.L ^ 2 * ‖u‖ ^ 2 / p ≤ q.σ ^ 2)
    (hacc : q.ε < q.L * ‖u‖ * (1 - N * p)) :
    ∃ (f : spec.Instance q) (O : Oracle (spec.Query q) (spec.Reply q)),
      spec.admissible q f O ∧
        ¬ spec.successful q f
          (fun z : A.Seed × ((t : ℕ) → O.Seed t) => execute O A (fun _ => N) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨v, hv, hf⟩ := pair_failure q hL A u hp.le hp1 N hacc
  have hn : ‖v‖ = ‖u‖ := by rcases hv with rfl | rfl <;> simp
  refine ⟨objective q.L v q.x0, pairOracle q hp.le hp1 (oracleValue p (field q.L v q.x0) (noise q.L v)), ?_, hf⟩
  apply HolderNoiseInitializationAdmissible.admissible q hL hM v hp hp1
  · simpa only [hn] using hΔ
  · simpa only [hn] using hσ

lemma failure (q : LowerParams) (hq : spec.valid q) (A : Alg q) (N : ℕ)
    (hN : (N : ℝ) ≤ q.σ ^ 2 / (64 * q.ε ^ 2)) :
    ∃ (f : spec.Instance q) (O : Oracle (spec.Query q) (spec.Reply q)),
      spec.admissible q f O ∧
        ¬ spec.successful q f
          (fun z : A.Seed × ((t : ℕ) → O.Seed t) => execute O A (fun _ => N) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hd := dimension_pos q hq
  rcases hq with ⟨hv, hgap, _⟩
  change 0 < q.L ∧ 0 ≤ q.M ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hv
  rcases hv with ⟨hL, hM, _, _, _, _, hε⟩
  let u : EuclideanSpace ℝ (Fin q.d) := (4 * q.ε / q.L) • EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ)
  have hu : ‖u‖ = 4 * q.ε / q.L := by
    simp [u, norm_smul, abs_of_pos hε, abs_of_pos hL]
  have hg : q.L / 2 * ‖u‖ ^ 2 ≤ q.Δ := by
    rw [hu]
    have he : q.L / 2 * (4 * q.ε / q.L) ^ 2 = 8 * q.ε ^ 2 / q.L := by field_simp; ring
    rw [he, div_le_iff₀ hL]
    nlinarith [sq_nonneg q.ε]
  have hs : q.L * ‖u‖ = 4 * q.ε := by rw [hu]; field_simp
  by_cases hzero : N = 0
  · subst N
    apply failure_of_parameters q hL.le hM A u (p := 1) (by norm_num) le_rfl 0 hg (Or.inl rfl)
    rw [hs]
    norm_num
    linarith
  · have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hσ : 0 < q.σ ^ 2 := by
      have h := (le_div_iff₀ (show 0 < 64 * q.ε ^ 2 by positivity)).mp hN
      nlinarith [sq_pos_of_pos hε]
    have hσne : q.σ ≠ 0 := by intro he; rw [he] at hσ; norm_num at hσ
    let p := 16 * q.ε ^ 2 / q.σ ^ 2
    have hp : 0 < p := by dsimp [p]; positivity
    have hp1 : p ≤ 1 := by
      dsimp [p]
      rw [div_le_iff₀ hσ]
      have h := (le_div_iff₀ (show 0 < 64 * q.ε ^ 2 by positivity)).mp hN
      nlinarith [sq_nonneg q.ε]
    have hv : q.L ^ 2 * ‖u‖ ^ 2 / p ≤ q.σ ^ 2 := by
      rw [hu]
      dsimp [p]
      apply le_of_eq
      field_simp
      ring
    have hnp : (N : ℝ) * p ≤ 1 / 4 := by
      have h := mul_le_mul_of_nonneg_right hN hp.le
      have he : (q.σ ^ 2 / (64 * q.ε ^ 2)) * p = 1 / 4 := by dsimp [p]; field_simp [hσne]; norm_num
      simpa only [he] using h
    apply failure_of_parameters q hL.le hM A u hp hp1 N hg (Or.inr hv)
    rw [hs]
    nlinarith

end LongTails.Proofs.HolderNoiseInitializationFailure
