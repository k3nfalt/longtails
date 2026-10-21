import LongTails.Proofs.BallProximalExecution
import LongTails.Proofs.BallProximalRealization
import Mathlib.Topology.Order.Compact

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.BallProximal

def iterate {E : Type*} (x0 : E) (reply : ℕ → E → E) : ℕ → E
  | 0 => x0
  | k + 1 => reply k (iterate x0 reply k)

open LongTails.Setups.ConvexBallProximal

noncomputable section

def profileFeasible (N : ℕ) (r S : ℝ) : Prop :=
  ∃ a : ℕ → ℝ, (∀ i < N, 0 < a i) ∧
    (∀ i j, i ≤ j → j < N → a j ≤ a i) ∧
    profileMass (radialProfile 1 a N) = 1 - r ∧
    profileWork r (radialProfile 1 a N) + (r / a (N - 1)) ^ 2 ≤ S

def executionFeasible (N : ℕ) (r S : ℝ) : Prop :=
  ∃ (p : Public) (I : Instance p) (O : Oracle p.E p.E)
      (ξ : (k : ℕ) → O.Seed k) (z : p.E),
    spec.valid p ∧ spec.admissible p I O ∧ p.t = 1 ∧
    z ∈ I.C ∧ IsMinOn I.f I.C z ∧ I.f p.x0 - I.f z = 1 ∧
    I.f (execute O (algorithm p.x0) (fun _ => N) () ξ) - I.f z = r ∧
    ‖p.x0 - z‖ ^ 2 ≤ S

lemma profile_of_execution {N : ℕ} (hN : 0 < N) {r S : ℝ} (hr : 0 < r)
    (h : executionFeasible N r S) : profileFeasible N r S := by
  obtain ⟨p, I, O, ξ, z, hv, ha, ht, hz, hmin, hinit, hfinal, hdist⟩ := h
  erw [execute_algorithm] at hfinal
  let x := oracleIterate p.x0 O ξ
  obtain ⟨c, hc⟩ := iterate_radial_certificates p I O hv ha ξ hz (N := N)
    (by change I.f z < I.f (x N); change I.f (x N) - I.f z = r at hfinal; linarith)
  have hx : ∀ i ≤ N, x i ∈ I.C := fun i _ => iterate_feasible p I O ha ξ i
  have hcp : ∀ i < N, 0 < c i := fun i hi => (hc i hi).1
  have hs : ∀ i < N, ‖x i - x (i + 1)‖ = 1 ∧
      ∀ w ∈ I.C, I.f (x (i + 1)) + ⟪c i • (x i - x (i + 1)), w - x (i + 1)⟫ ≤ I.f w := by
    intro i hi
    exact ⟨(hc i hi).2.1.trans ht, (hc i hi).2.2⟩
  have hm : ∀ i j, i ≤ j → j < N → c j ≤ c i := by
    intro i j hij hj
    simpa using radial_slopes_antitone (by norm_num : (0 : ℝ) < 1) hx hcp hs hij hj
  have hmass := radialProfile_mass hx hs
  have hmass' : profileMass (radialProfile 1 c N) ≤ 1 - r := by
    change I.f (x 0) - I.f z = 1 at hinit
    change I.f (x N) - I.f z = r at hfinal
    linarith
  obtain ⟨b, hbp, hbm, hbn, hbe⟩ := normalize_profile hN hcp hm hr.le hmass'
  refine ⟨b, hbp, hbm, hbn, le_trans hbe ?_⟩
  cases N with
  | zero => omega
  | succ N =>
      have he := radialProfile_terminal_energy (by norm_num : (0 : ℝ) < 1) hz hx hcp hs
        (by linarith)
      change I.f (x (N + 1)) - I.f z = r at hfinal
      rw [hfinal] at he
      simpa [x, iterate] using le_trans he hdist

lemma continuous_ball_reply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : Continuous f) :
    ∃ b : E → E, ∀ x, ‖b x - x‖ ≤ 1 ∧ ∀ z, ‖z - x‖ ≤ 1 → f (b x) ≤ f z := by
  have hex : ∀ x : E, ∃ y : E, ‖y - x‖ ≤ 1 ∧ ∀ z, ‖z - x‖ ≤ 1 → f y ≤ f z := by
    intro x
    obtain ⟨y, hy, hm⟩ := (isCompact_closedBall x 1).exists_isMinOn
      (show (Metric.closedBall x (1 : ℝ)).Nonempty from ⟨x, by simp⟩) hf.continuousOn
    refine ⟨y, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    · intro z hz
      exact hm (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  choose b hb using hex
  exact ⟨b, hb⟩

lemma execution_of_profile {N : ℕ} (hN : 0 < N) {r S : ℝ} (hr : 0 ≤ r)
    (h : profileFeasible N r S) : executionFeasible N r S := by
  obtain ⟨a, hap, ham, hmass, henergy⟩ := h
  obtain ⟨f, x, hconv, hcont, hnonneg, hf0, hval, hnorm, hnear, hsteps⟩ :=
    realized_profile hN hap ham hr
  obtain ⟨b, hb⟩ := continuous_ball_reply hcont
  let p : Public := { E := EuclideanSpace ℝ (Fin N), t := 1, R := ‖x 0‖, Δ := 1, ε := 1, x0 := x 0 }
  let I : Instance p := { C := Set.univ, f := f }
  let O : Oracle p.E p.E := { answer := fun _ q _ => b q.2 }
  have horacle : ∀ k, oracleIterate p.x0 O (fun _ => ()) k = iterate (x 0) (fun _ y => b y) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [oracleIterate_succ, ih]
      simp [iterate, O]
  have hiter : ∀ k ≤ N, iterate (x 0) (fun _ y => b y) k = x k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hkN : k < N := by omega
        simp only [iterate, ih (by omega)]
        exact (hsteps k hkN).2.2 _ (hb (x k)).1
          ((hb (x k)).2 _ ((hsteps k hkN).1.le))
  have hinit : f (x 0) = 1 := by
    have he := radialProfile_mass_eq (t := 1) (c := a) (F := tailValue N a r) (N := N)
      (by intro i hi; simpa using tailValue_step hi a r)
    rw [hmass] at he
    have hlast : tailValue N a r N = r := by simp [tailValue]
    rw [hlast] at he
    rw [hval]
    linarith
  have hmin : IsMinOn f Set.univ 0 := fun z _ => by rw [hf0]; exact hnonneg z
  have hclosed : IsClosed {q : p.E × ℝ | q.1 ∈ Set.univ ∧ f q.1 ≤ q.2} := by
    simpa using isClosed_le (hcont.comp continuous_fst) continuous_snd
  refine ⟨p, I, O, fun _ => (), 0, ?_, ?_, rfl, Set.mem_univ _, hmin, ?_, ?_, ?_⟩
  · exact ⟨by norm_num [p], norm_nonneg _, by norm_num [p], by norm_num [p]⟩
  · refine ⟨hconv, hclosed, Set.mem_univ _, ?_, 0, Set.mem_univ _, hmin, ?_, ?_⟩
    · intro k seed y hy
      exact ⟨Set.mem_univ _, (hb y).1, fun z _ hz => (hb y).2 z hz⟩
    · simp [p]
    · change f (x 0) - f 0 ≤ 1
      rw [hinit, hf0]; norm_num
  · change f (x 0) - f 0 = 1
    rw [hinit, hf0]; norm_num
  · erw [execute_algorithm]
    rw [horacle]
    rw [hiter N le_rfl]
    change f (x N) - f 0 = r
    rw [hf0, hval]
    simp [tailValue]
  · change ‖x 0 - 0‖ ^ 2 ≤ S
    simpa [sub_zero, hnorm] using henergy

lemma exact_profile_characterization {N : ℕ} (hN : 0 < N) {r S : ℝ} (hr : 0 < r) :
    executionFeasible N r S ↔ profileFeasible N r S :=
  ⟨profile_of_execution hN hr, execution_of_profile hN hr.le⟩


def relaxedProfileFeasible (N : ℕ) (r S : ℝ) : Prop :=
  ∃ a : ℕ → ℝ, (∀ i < N, 0 < a i) ∧
    (∀ i j, i ≤ j → j < N → a j ≤ a i) ∧
    profileMass (radialProfile 1 a N) ≤ 1 - r ∧
    profileWork r (radialProfile 1 a N) + (r / a (N - 1)) ^ 2 ≤ S

lemma exact_relaxed_characterization {N : ℕ} (hN : 0 < N) {r S : ℝ} (hr : 0 < r) :
    executionFeasible N r S ↔ relaxedProfileFeasible N r S := by
  rw [exact_profile_characterization hN hr]
  constructor
  · rintro ⟨a, hap, ham, hmass, he⟩
    exact ⟨a, hap, ham, hmass.le, he⟩
  · rintro ⟨a, hap, ham, hmass, he⟩
    obtain ⟨b, hbp, hbm, hmass', he'⟩ := normalize_profile hN hap ham hr.le hmass
    exact ⟨b, hbp, hbm, hmass', le_trans he' he⟩

end

end OracleTemplate.BallProximal
