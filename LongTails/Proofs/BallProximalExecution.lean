import LongTails.Setups.ConvexBallProximal
import LongTails.Proofs.Execution
import LongTails.Proofs.ExecutionHistory
import LongTails.Proofs.BallProximalTrajectory
import LongTails.Proofs.BallProximalBudget

open scoped RealInnerProductSpace

namespace OracleTemplate.BallProximal

open LongTails.Setups.ConvexBallProximal

noncomputable def oracleIterate {E : Type*} (x0 : E) (O : Oracle E E)
    (ξ : (k : ℕ) → O.Seed k) : ℕ → E :=
  fun k => (executeIndexedState O (algorithm x0) () ξ k).1

lemma oracleIterate_succ {E : Type*} (x0 : E) (O : Oracle E E)
    (ξ : (k : ℕ) → O.Seed k) (k : ℕ) :
    oracleIterate x0 O ξ (k + 1) =
      O.answer (executeIndexedState O (algorithm x0) () ξ k).2
        (0, oracleIterate x0 O ξ k)
        (ξ (executeIndexedState O (algorithm x0) () ξ k).2.length) := by
  simp [oracleIterate, executeIndexedState, algorithm]

lemma execute_algorithm {E : Type*} (x0 : E) (O : Oracle E E) (K : ℕ)
    (seed : (algorithm x0).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm x0) (fun _ => K) seed ξ = oracleIterate x0 O ξ K := by
  simp only [execute]
  rw [executeWithTrace_eq_executeIndexedState]
  rfl

lemma iterate_feasible (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k) (k : ℕ) :
    oracleIterate p.x0 O ξ k ∈ I.C := by
  induction k with
  | zero => exact h.2.2.1
  | succ k ih =>
      let history := (executeIndexedState O (algorithm p.x0) () ξ k).2
      have hy := (h.2.2.2.1 history (ξ history.length) (oracleIterate p.x0 O ξ k) ih).1
      rw [oracleIterate_succ]
      simpa [oracleIterate, history] using hy

lemma iterate_objective_antitone (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k) :
    Antitone (fun k => I.f (oracleIterate p.x0 O ξ k)) := by
  apply antitone_nat_of_succ_le
  intro k
  have hx := iterate_feasible p I O h ξ k
  let history := (executeIndexedState O (algorithm p.x0) () ξ k).2
  have hh := h.2.2.2.1 history (ξ history.length) (oracleIterate p.x0 O ξ k) hx
  rw [oracleIterate_succ]
  simpa [oracleIterate, history] using hh.2.2 (oracleIterate p.x0 O ξ k) hx (by simp [hv.1.le])

lemma iterate_radial_certificates (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) {N : ℕ}
    (hg : I.f z < I.f (oracleIterate p.x0 O ξ N)) :
    ∃ c : ℕ → ℝ, ∀ i < N,
      let x := oracleIterate p.x0 O ξ
      0 < c i ∧ ‖x i - x (i + 1)‖ = p.t ∧
        ∀ w ∈ I.C, I.f (x (i + 1)) + ⟪c i • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ I.f w := by
  classical
  let x := oracleIterate p.x0 O ξ
  have hm := iterate_objective_antitone p I O hv h ξ
  have hex : ∀ i, ∃ c : ℝ, i < N → 0 < c ∧ ‖x i - x (i + 1)‖ = p.t ∧
      ∀ w ∈ I.C, I.f (x (i + 1)) + ⟪c • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ I.f w := by
    intro i
    by_cases hi : i < N
    · let sc := executeIndexedState O (algorithm p.x0) () ξ i
      have hball := h.2.2.2.1 sc.2 (ξ sc.2.length) (oracleIterate p.x0 O ξ i)
        (iterate_feasible p I O h ξ i)
      have hball' : x (i + 1) ∈ I.C ∧ ‖x (i + 1) - x i‖ ≤ p.t ∧
          ∀ w ∈ I.C, ‖w - x i‖ ≤ p.t → I.f (x (i + 1)) ≤ I.f w := by
        simpa [x, oracleIterate, sc, oracleIterate_succ] using hball
      rcases hball' with ⟨hnext, hdist, hmin⟩
      obtain ⟨c, hc⟩ := positive_radial_support h.1 hv.1
        (iterate_feasible p I O h ξ i) (iterate_feasible p I O h ξ (i + 1)) hz
        (lt_of_lt_of_le hg (hm (by omega))) hdist (fun w hw => hmin w hw)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => False.elim (hi h)⟩
  choose c hc using hex
  exact ⟨c, hc⟩


lemma positive_execution_bounds (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) (hR : ‖p.x0 - z‖ ≤ p.R)
    (hΔ : I.f p.x0 - I.f z ≤ p.Δ) {N : ℕ} (hN : 0 < N)
    (hg : p.ε < I.f (oracleIterate p.x0 O ξ N) - I.f z) :
    ((N : ℝ) * p.t) ^ 2 < p.R ^ 2 * accuracyCoefficient p.Δ p.ε ∧
      (N : ℝ) * p.t ^ 2 < p.R ^ 2 := by
  cases N with
  | zero => omega
  | succ N =>
      let x := oracleIterate p.x0 O ξ
      let g := I.f (x (N + 1)) - I.f z
      have hg0 : 0 < g := lt_trans hv.2.2.2 hg
      obtain ⟨c, hc⟩ := iterate_radial_certificates p I O hv h ξ hz
        (N := N + 1) (by change I.f z < I.f (x (N + 1)); dsimp [g] at hg0; linarith)
      have hx : ∀ i ≤ N + 1, x i ∈ I.C := fun i _ => iterate_feasible p I O h ξ i
      have hcp : ∀ i < N + 1, 0 < c i := fun i hi => (hc i hi).1
      have hs := fun i (hi : i < N + 1) => (hc i hi).2
      let qs := radialProfile p.t c (N + 1)
      let m := c N * p.t
      have hm : 0 < m := mul_pos (hcp N (by omega)) hv.1
      have hqt : ∀ q ∈ qs, 0 ≤ q.1 := by
        intro q hq
        obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
        exact hv.1.le
      have hqa : ∀ q ∈ qs, m ≤ q.2 := by
        intro q hq
        obtain ⟨i, hi, rfl⟩ := radialProfile_mem hq
        exact radial_slopes_antitone hv.1 hx hcp hs (by omega) (by omega)
      have hA := radialProfile_mass_pos hv.1 hcp
      have hmass := radialProfile_mass hx hs
      have hAg : profileMass qs + g ≤ p.Δ := by
        change profileMass qs ≤ I.f p.x0 - I.f (x (N + 1)) at hmass
        dsimp [g]
        linarith
      have he := radialProfile_terminal_energy hv.1 hz hx hcp hs hg0.le
      have hR2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
      have henergy : profileWork g qs + (g / m) ^ 2 ≤ p.R ^ 2 := le_trans he hR2
      have htarg := profile_target_strict hm hv.2.2.2 hg hv.2.1 hqt hqa hA hAg henergy
      have htime := radialProfile_time p.t c (N + 1)
      refine ⟨?_, ?_⟩
      · simpa only [qs, htime] using htarg
      · have hl := radialProfile_work_lower hv.1.le hg0.le
          (fun i hi => mul_pos (hcp i hi) hv.1)
        have hp := sq_pos_of_pos (div_pos hg0 hm)
        change (N + 1 : ℕ) * p.t ^ 2 ≤ profileWork g qs at hl
        nlinarith

lemma execution_accuracy (p : Public) (I : Instance p) (O : Oracle p.E p.E)
    (hv : spec.valid p) (h : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k)
    {z : p.E} (hz : z ∈ I.C) (hR : ‖p.x0 - z‖ ≤ p.R)
    (hΔ : I.f p.x0 - I.f z ≤ p.Δ) {K : ℕ}
    (hK : ⌈min ((p.R / p.t) ^ 2) ((p.R / p.t) * Real.sqrt (accuracyCoefficient p.Δ p.ε))⌉₊ ≤ K) :
    I.f (oracleIterate p.x0 O ξ K) - I.f z ≤ p.ε := by
  by_contra hbad
  have hg := lt_of_not_ge hbad
  have hm := iterate_objective_antitone p I O hv h ξ (Nat.zero_le K)
  have hinit : p.ε < I.f p.x0 - I.f z := by
    change I.f (oracleIterate p.x0 O ξ K) ≤ I.f p.x0 at hm
    linarith
  have heΔ : p.ε < p.Δ := lt_of_lt_of_le hinit hΔ
  have hxz : p.x0 ≠ z := by intro he; rw [he, sub_self] at hinit; linarith [hv.2.2.2]
  have hRp : 0 < p.R := lt_of_lt_of_le (norm_pos_iff.mpr (sub_ne_zero.mpr hxz)) hR
  have hKp := lt_of_lt_of_le (budget_positive hRp hv.1 hv.2.2.1 hv.2.2.2 heΔ) hK
  obtain ⟨h2, h1⟩ := positive_execution_bounds p I O hv h ξ hz hR hΔ hKp hg
  exact budget_contradiction hv.2.1 hv.1 hK h1 h2

end OracleTemplate.BallProximal
