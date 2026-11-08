import LongTails.Proofs.BirchResourceReplay
import LongTails.Proofs.BirchResourceDispatch
import LongTails.Proofs.BirchPowerTime
import LongTails.Proofs.BirchRoutedTime

namespace LongTails.Proofs.BirchResourceEuclidean

open Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.BirchSgd (gradientOracle main_theorem stepSize)
open LongTails.Setups.BirchSgd
open LongTails.Proofs.BirchResourceForest
open LongTails.Proofs.BirchResourceReplay
open LongTails.Proofs.BirchResourceDispatch
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

noncomputable def blockSize (p : Params) : ℕ :=
  1 + ⌈p.σ ^ 2 / p.ε⌉₊

noncomputable def phases (p : Params) : ℕ :=
  1 + ⌈12 * p.L * p.Δ / p.ε⌉₊

lemma phase_clock (clock : ℕ → ℝ) (T : ℝ) (h₀ : clock 0 ≤ 0)
    (hstep : ∀ k, clock (k + 1) ≤ clock k + T) (K : ℕ) :
    clock K ≤ K * T := by
  induction K with
  | zero => simpa using h₀
  | succ k ih =>
    have h := (hstep k).trans (add_le_add ih (le_refl T))
    push_cast
    linarith only [h]

lemma tuned_edges (p : Params) (hp : spec.valid p) (hR : p.R + 1 ≤ (blockSize p : ℝ))
    (gap : ℝ) (hgap : gap ≤ p.Δ) :
    4 * (p.R + 1) * p.L * gap / p.ε + 8 * p.σ ^ 2 * p.L * gap / p.ε ^ 2 ≤
      (phases p * blockSize p : ℕ) := by
  have hL : 0 < p.L := hp.1
  have hε : 0 < p.ε := hp.2.2.1
  have hΔ : 0 ≤ p.Δ := hp.2.2.2.1
  have hR₀ : 0 ≤ p.R := hp.2.2.2.2.1
  have h₁ : 4 * (p.R + 1) * p.L * gap / p.ε ≤ 4 * (blockSize p : ℝ) * p.L * p.Δ / p.ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    exact (mul_le_mul_of_nonneg_left hgap (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hR (by norm_num)) hL.le) hΔ)
  have h₂ : 8 * p.σ ^ 2 * p.L * gap / p.ε ^ 2 ≤ 8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by positivity)) (sq_nonneg _)
  have hB : p.σ ^ 2 / p.ε ≤ (blockSize p : ℝ) := by
    unfold blockSize
    push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  have hK : 12 * p.L * p.Δ / p.ε ≤ (phases p : ℝ) := by
    unfold phases
    push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  have h₃ := mul_le_mul_of_nonneg_right hB (show 0 ≤ 8 * p.L * p.Δ / p.ε by positivity)
  have h₄ := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (blockSize p) : (0 : ℝ) ≤ blockSize p)
  have he : (p.σ ^ 2 / p.ε) * (8 * p.L * p.Δ / p.ε) =
      8 * p.σ ^ 2 * p.L * p.Δ / p.ε ^ 2 := by ring
  rw [he] at h₃
  have he' : (blockSize p : ℝ) * (8 * p.L * p.Δ / p.ε) =
      8 * (blockSize p : ℝ) * p.L * p.Δ / p.ε := by ring
  rw [he'] at h₃
  have he'' : (12 * p.L * p.Δ / p.ε) * (blockSize p : ℝ) =
      12 * (blockSize p : ℝ) * p.L * p.Δ / p.ε := by ring
  rw [he''] at h₄
  push_cast
  linear_combination h₁ + h₂ + h₃ + h₄

noncomputable def forestParams (p : Params) (s : Forest) : Params :=
  { p with R := ((blockSize p - 1 : ℕ) : ℝ), tree := tree s, branch := branch }

lemma forestParams_valid (p : Params) (s : Forest) (hs : s.Valid (blockSize p))
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ) :
    spec.valid (forestParams p s) :=
  ⟨hL, hσ, hε, hΔ, Nat.cast_nonneg _, tree_wellFormed s _ hs, main_branch s,
    contained s _ hs, distance s _ hs⟩

lemma timed_prefix {Ω : Type} [MeasurableSpace Ω] (p : Params) (s : Forest)
    (hs : s.Valid (blockSize p)) (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun ξ => ξ c) = (μ : Measure Ω))
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ)
    (clock : ℕ → ℝ) (T : ℝ) (h₀ : clock 0 ≤ 0)
    (hstep : ∀ k, clock (k + 1) ≤ clock k + T) :
    let q := forestParams p s
    let γ := (publicInput q).gamma
    let K := phases p * blockSize p
    let n := LongTails.Algorithms.BirchCollectionEuclidean.native q
    let a := program s γ K
    a.oracleCalls = K ∧
    (1 / (K : ℝ) * ∑ k ∈ range K, ∫ ξ, ‖gradient I.f
      (if hk : k < a.outputCount + 1 then
        execute (gradientOracle P g)
          (LongTails.Setups.BirchNonEuclidean.programAlgorithm n a (fun _ => 0))
          (fun _ => K) ⟨k, hk⟩ (fun j => ξ (2 * j))
      else p.x0)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε ∧
      clock (phases p) ≤ phases p * T := by
  dsimp only
  let q := forestParams p s
  let γ := (publicInput q).gamma
  let K := phases p * blockSize p
  have hK : 0 < K := Nat.mul_pos (by unfold phases; omega) (by unfold blockSize; omega)
  have hq := forestParams_valid p s hs hL hσ hε hΔ
  have hB : 0 < blockSize p := by unfold blockSize; omega
  have hR : q.R + 1 ≤ (blockSize p : ℝ) := by
    change (((blockSize p - 1 : ℕ) : ℝ) + 1) ≤ _
    rw [Nat.cast_sub (by omega : 1 ≤ blockSize p), Nat.cast_one, sub_add_cancel]
  have hbound := tuned_edges q hq hR _ hgap
  have hmain := (main_theorem I.f p.L p.σ p.ε q.R I.lower p.x0 (tree s) branch μ P g
    hL hσ hε hq.2.2.2.2.1 hsmooth hlower hg hlaw
    (tree_wellFormed s _ hs) (main_branch s)
    (iid_independent s _ hs γ p.x0 g hg.measurable μ P hiid)
    (contained s _ hs) (distance s _ hs) K hbound).2
  refine ⟨prefix_calls s γ K, ?_, phase_clock clock T h₀ hstep _⟩
  convert hmain using 2
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < (program s γ K).outputCount + 1 := by
    have hk'' := mem_range.mp hk
    change k < K - 1 + 1
    omega
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact congrArg (fun v : Point p.d => ‖gradient I.f v‖ ^ 2)
    ((dite_eq_left hk').trans (execute_replay
      (LongTails.Algorithms.BirchCollectionEuclidean.native q) s _ hs γ K hK P g ξ ⟨k, hk'⟩))

lemma routed_prefix {Route Device Pool : Type*}
    (profile : LongTails.Setups.BirchRoutedTime.Profile Route Device)
    (jobs : ℕ → LongTails.Setups.BirchRoutedTime.Job Route) (pool : Route → Pool) {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (head saved : ℕ → ℕ) (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun ξ => ξ c) = (μ : Measure Ω))
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ)
    (clock : ℕ → ℝ) (T : ℝ) (h₀ : clock 0 ≤ 0)
    (hstep : ∀ k, clock (k + 1) ≤ clock k + T) :
    let s := forest (routed profile jobs pool) (blockSize p) head saved
    let q := forestParams p s
    let γ := (publicInput q).gamma
    let K := phases p * blockSize p
    let n := LongTails.Algorithms.BirchCollectionEuclidean.native q
    let a := program s γ K
    a.oracleCalls = K ∧
    (1 / (K : ℝ) * ∑ k ∈ range K, ∫ ξ, ‖gradient I.f
      (if hk : k < a.outputCount + 1 then
        execute (gradientOracle P g)
          (LongTails.Setups.BirchNonEuclidean.programAlgorithm n a (fun _ => 0))
          (fun _ => K) ⟨k, hk⟩ (fun j => ξ (2 * j))
      else p.x0)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε ∧
      clock (phases p) ≤ phases p * T := by
  have hb : 0 < blockSize p := by unfold blockSize; omega
  exact timed_prefix p _ (forest_valid (routed profile jobs pool) _ hb head saved)
    hL hσ hε hΔ I μ P g hsmooth hlower hg hlaw hiid hgap clock T h₀ hstep

lemma power_prefix {Mode Device : Type*}
    (profile : LongTails.Setups.BirchPowerTime.Profile Mode Device)
    (packet : ℕ → LongTails.Setups.BirchPowerTime.Job Mode) {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (head saved : ℕ → ℕ) (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun ξ => ξ c) = (μ : Measure Ω))
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ)
    (clock : ℕ → ℝ) (T : ℝ) (h₀ : clock 0 ≤ 0)
    (hstep : ∀ k, clock (k + 1) ≤ clock k + T) :
    let s := forest (power profile packet) (blockSize p) head saved
    let q := forestParams p s
    let γ := (publicInput q).gamma
    let K := phases p * blockSize p
    let n := LongTails.Algorithms.BirchCollectionEuclidean.native q
    let a := program s γ K
    a.oracleCalls = K ∧
    (1 / (K : ℝ) * ∑ k ∈ range K, ∫ ξ, ‖gradient I.f
      (if hk : k < a.outputCount + 1 then
        execute (gradientOracle P g)
          (LongTails.Setups.BirchNonEuclidean.programAlgorithm n a (fun _ => 0))
          (fun _ => K) ⟨k, hk⟩ (fun j => ξ (2 * j))
      else p.x0)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε ∧
      clock (phases p) ≤ phases p * T := by
  have hb : 0 < blockSize p := by unfold blockSize; omega
  exact timed_prefix p _ (forest_valid (power profile packet) _ hb head saved)
    hL hσ hε hΔ I μ P g hsmooth hlower hg hlaw hiid hgap clock T h₀ hstep

lemma fixed_phase_prefix {Pool : Type*} {Ω : Type} [MeasurableSpace Ω] (p : Params) (d : Dispatch Pool)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : SmoothObjective I.f p.L) (hlower : LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun ξ => ξ c) = (μ : Measure Ω))
    (hiid : IID (fun j (ξ : ℕ → Ω) => ξ j) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgap : I.f p.x0 - I.lower ≤ p.Δ)
    (T : ℝ) (hphase : ∀ j < blockSize p, 0 ≤ d.launch j ∧ d.finish j ≤ T) :
    let dispatch := repeated d (blockSize p) T
    let s := localForest dispatch (blockSize p)
    let q := forestParams p s
    let γ := (publicInput q).gamma
    let K := phases p * blockSize p
    let n := LongTails.Algorithms.BirchCollectionEuclidean.native q
    let a := program s γ K
    a.oracleCalls = K ∧
    (1 / (K : ℝ) * ∑ k ∈ range K, ∫ ξ, ‖gradient I.f
      (if hk : k < a.outputCount + 1 then
        execute (gradientOracle P g)
          (LongTails.Setups.BirchNonEuclidean.programAlgorithm n a (fun _ => 0))
          (fun _ => K) ⟨k, hk⟩ (fun j => ξ (2 * j))
      else p.x0)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ p.ε ∧
      (∀ k, (k / blockSize p : ℕ) * T ≤ dispatch.launch k ∧
        dispatch.finish k ≤ ((k / blockSize p + 1 : ℕ) : ℝ) * T) := by
  let B := blockSize p
  let dispatch := repeated d B T
  let s := localForest dispatch B
  have hB : 0 < B := by dsimp only [B]; unfold blockSize; omega
  have hclock (k : ℕ) : ((k + 1 : ℕ) : ℝ) * T ≤ (k : ℝ) * T + T := by
    push_cast
    linarith only
  obtain ⟨hcalls, hstat, _⟩ := timed_prefix p s (localForest_valid dispatch B hB)
    hL hσ hε hΔ I μ P g hsmooth hlower hg hlaw hiid hgap
    (fun k => (k : ℝ) * T) T (by simp) hclock
  exact ⟨hcalls, hstat, repeated_window d B hB T hphase⟩

end LongTails.Proofs.BirchResourceEuclidean
