import LongTails.Setups.HighProbabilityStationarity
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Algorithms.SublevelRobustGradient
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.HighProbabilityStationarity

open OracleTemplate RobustGradient
open LongTails.Algorithms.StochasticEnvelopeProgram

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def stepRepeat {Q R S : Type*} {c : ℕ} : (n : ℕ) →
    (S → QueryPlan Q R S c) → S → QueryPlan Q R S (c * n)
  | 0, _, s => .done s
  | n + 1, body, s => QueryPlan.bind (body s) (stepRepeat n body)

def samplePlan (x : E) (n : ℕ) : QueryPlan E E (Fin n → E) n :=
  castPlan (one_mul n) (collectPlans n (fun _ => .ask x .done))

def qualifies {m : ℕ} (B : ℝ) (v : Fin m → E) (k : ℕ) : Prop :=
  ∃ i, m < 2 * (neighbors (2 ^ k * B) v i).card

def gradedLevel {m : ℕ} (B : ℝ) (K : ℕ) (v : Fin m → E) : Option ℕ := by
  classical
  exact if h : ∃ k, k ≤ K ∧ qualifies B v k then some (Nat.find h) else none

def gradedPilot {m : ℕ} (B : ℝ) (K : ℕ) (v : Fin m → E) (fallback : E) : E :=
  match gradedLevel B K v with
  | some k => pilotCenter (2 ^ k * B) v
  | none => fallback

def clipEstimate (B : ℝ) (K mp mc : ℕ) (v : Fin (mp + mc) → E) : E :=
  let c := gradedPilot B K (fun i : Fin mp => v (Fin.castAdd mc i)) 0
  c + (1 / (mc : ℝ)) • ∑ i : Fin mc, clip B (v (Fin.natAdd mp i) - c)

def normalizedStep (η : ℝ) (x g : E) : E := by
  classical
  exact if g = 0 then x else x - (η / ‖g‖) • g

structure Trajectory (E : Type) where
  point : E
  time : ℕ
  path : ℕ → E

def trajectoryStep (B η : ℝ) (K mp mc : ℕ) (s : Trajectory E) (v : Fin (mp + mc) → E) :
    Trajectory E :=
  ⟨normalizedStep η s.point (clipEstimate B K mp mc v), s.time + 1,
    Function.update s.path s.time s.point⟩

def phaseOne (B η : ℝ) (K mp mc T : ℕ) (x0 : E) :
    QueryPlan E E (Trajectory E) ((mp + mc) * T) :=
  stepRepeat T (fun s => (samplePlan s.point (mp + mc)).map (trajectoryStep B η K mp mc s))
    ⟨x0, 0, fun _ => x0⟩

def testPasses {β : Type*} (α τ : ℝ) {k r : ℕ} (hk : 0 < k) (entry : Option β)
    (v : Fin (k * r) → E) : Bool := by
  classical
  exact entry.isSome && decide (‖SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α) v‖ ≤ τ)

def testPlan {J : ℕ} (α τ : ℝ) {k : ℕ} (hk : 0 < k) (r : ℕ) (x0 : E) (Y : Fin J → E)
    (entry : Option (Fin J)) : QueryPlan E E Bool (k * r) :=
  (samplePlan ((entry.map Y).getD x0) (k * r)).map (testPasses α τ hk entry)

def passers {β : Type*} {K : ℕ} (entries : ℕ → Option β) (pass : Fin K → Bool) : ℕ → Option β :=
  fun j => if h : j < (Finset.univ.filter (fun i => pass i = true)).card then
    entries ((Finset.univ.filter (fun i => pass i = true)).orderEmbOfFin rfl ⟨j, h⟩) else none

def slots {β : Type*} {J : ℕ} (e : Fin J → Option β) : ℕ → Option β :=
  fun i => if h : i < J then e ⟨i, h⟩ else none

def nextSlots {β : Type*} {J K : ℕ} (e : Fin J → Option β) (pass : Fin K → Bool) :
    Fin J → Option β :=
  fun j => passers (slots e) pass j

abbrev Ladder (J : ℕ) := ℕ × (Fin J → Option (Fin J))

lemma round_calls (Λ k0 r lv : ℕ) (hlv : lv ≤ Λ) :
    (k0 * 2 ^ lv * r) * 2 ^ (Λ - lv) = k0 * r * 2 ^ Λ := by
  have h : 2 ^ lv * 2 ^ (Λ - lv) = 2 ^ Λ := by
    rw [← pow_add, Nat.add_sub_cancel' hlv]
  calc (k0 * 2 ^ lv * r) * 2 ^ (Λ - lv) = k0 * r * (2 ^ lv * 2 ^ (Λ - lv)) := by ring
    _ = k0 * r * 2 ^ Λ := by rw [h]

def threshold (ε α : ℝ) (lv : ℕ) : ℝ := ε / 2 + (2 * lv + 1) * α

def roundPlan (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E) (Y : Fin (2 ^ Λ) → E)
    (s : Ladder (2 ^ Λ)) : QueryPlan E E (Ladder (2 ^ Λ)) (k0 * r * 2 ^ Λ) :=
  castPlan (round_calls Λ k0 r (min s.1 Λ) (min_le_right _ _))
    ((collectPlans (2 ^ (Λ - min s.1 Λ)) (fun i =>
      testPlan α (threshold ε α (min s.1 Λ))
        (Nat.mul_pos hk0 (Nat.two_pow_pos (min s.1 Λ))) r x0 Y (slots s.2 i))).map
      (fun pass => (s.1 + 1, nextSlots s.2 pass)))

def phaseTwo (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E) (Y : Fin (2 ^ Λ) → E) :
    QueryPlan E E E ((k0 * r * 2 ^ Λ) * (Λ + 1)) :=
  (stepRepeat (Λ + 1) (roundPlan ε α Λ k0 r hk0 x0 Y) (0, fun j => some j)).map
    (fun s => ((s.2 ⟨0, Nat.two_pow_pos Λ⟩).map Y).getD x0)

def method (B η ε α : ℝ) (K mp mc T Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E)
    (τ : Fin (2 ^ Λ) → Fin T) :
    QueryPlan E E E ((k0 * r * 2 ^ Λ) * (Λ + 1) + (mp + mc) * T) :=
  (phaseOne B η K mp mc T x0).bind
    (fun s => phaseTwo ε α Λ k0 r hk0 x0 (fun j => s.path (τ j)))

end

section Tuning

open LongTails.Setups.HighProbabilityStationarity

variable (q : Params)

noncomputable def confidence : ℝ := Real.log (16 / q.δ)

noncomputable def noiseScale : ℝ := q.σ + q.ε

noncomputable def gradientScale : ℝ := Real.sqrt (q.L * q.Δ) + q.ε

noncomputable def radius : ℝ := 2 ^ 20 * noiseScale q ^ 2 / q.ε

noncomputable def levels : ℕ := Nat.clog 2 ⌈gradientScale q / q.ε⌉₊ + 4

noncomputable def baseSteps : ℕ := ⌈2 ^ 20 * (q.L * q.Δ / q.ε ^ 2 + confidence q + 1)⌉₊

noncomputable def steps : ℕ := baseSteps q + 1

noncomputable def stepSize : ℝ := 128 * (q.Δ + q.ε ^ 2 / q.L) / (steps q * q.ε)

noncomputable def pilotSize : ℕ :=
  ⌈2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2 + gradientScale q * (confidence q + 4) / (steps q * q.ε))⌉₊

noncomputable def clipSize : ℕ := ⌈2 ^ 40 * noiseScale q ^ 2 / q.ε ^ 2⌉₊

noncomputable def rounds : ℕ := Nat.clog 2 ⌈64 * confidence q⌉₊

noncomputable def accuracy : ℝ := q.ε / (64 * (rounds q + 1))

noncomputable def blockSize : ℕ := ⌈2 ^ 22 * noiseScale q ^ 2 * (rounds q + 1) ^ 2 / q.ε ^ 2⌉₊

instance steps_nonempty : Nonempty (Fin (steps q)) := ⟨⟨0, Nat.succ_pos _⟩⟩

noncomputable def seedLaw :
    MeasureTheory.ProbabilityMeasure (Fin (2 ^ rounds q) → Fin (steps q)) :=
  ⟨MeasureTheory.Measure.pi fun _ => (PMF.uniformOfFintype (Fin (steps q))).toMeasure, inferInstance⟩

noncomputable def algorithm : Algorithm q.E q.E q.E :=
  QueryPlan.algorithm (seedLaw q) q.x0 q.x0 _ (fun τ =>
    method (radius q) (stepSize q) q.ε (accuracy q) (levels q) (pilotSize q) (clipSize q)
      (steps q) (rounds q) 8 (blockSize q) (by norm_num) q.x0 τ)

end Tuning

end LongTails.Algorithms.HighProbabilityStationarity
