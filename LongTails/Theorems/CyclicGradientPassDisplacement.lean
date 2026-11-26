import LongTails.Setups.InterpolatedFiniteSum
import LongTails.Algorithms.CyclicGradientPassDisplacement
import LongTails.Proofs.CyclicGradientPassDisplacement
import LongTails.Theorems.CyclicGradientInterpolation

namespace OracleTemplate.CyclicGradientPassDisplacement

open LongTails.Setups.InterpolatedFiniteSum CyclicInterpolation

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let u := p.L * p.R ^ 2 / p.ε
  let B := 1 + (p.m : ℝ) * (p.m - 1)
  if p.L * p.R ^ 2 ≤ 2 * p.ε then 0 else
    min (p.m * ⌈(p.m : ℝ) ^ 3 * u⌉₊) (p.m * (1 + ⌈2 * B * Real.sqrt B * u / p.m⌉₊))

lemma budget_le_existing (p : Params) (i : Fin 1) :
    budget p i ≤ CyclicInterpolation.budget p i := by
  unfold budget CyclicInterpolation.budget
  split
  · exact Nat.zero_le _
  · convert min_le_left _ _ using 2
    ring_nf

theorem result : Convergence LongTails.Setups.InterpolatedFiniteSum.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => rfl⟩
  rintro p ⟨hL, hR, hε⟩ f oracle ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g : Fin p.m × p.E → p.E := fun z => oracle.answer [] (0, z) seed0
  have hanswer : ∀ k z seed, oracle.answer k (0, z) seed = g z :=
    fun k z seed => (hg k seed z.1 z.2).unique (hg [] seed0 z.1 z.2)
  have h : Hyp p.m f g p.L xstar :=
    ⟨hL, hc, fun i x => hg [] seed0 i x, fun i x y => hlip [] seed0 i x y, hmin⟩
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  intro seed
  change (p.m : ℝ)⁻¹ * ∑ i, (f i (execute oracle (cyclicGradient p.m p.L p.x0)
    (fun _ => budget p 0) seed.1 seed.2) - f i xstar) ≤ p.ε
  have hexec := (execute_eq_of_answer_eq oracle g hanswer (cyclicGradient p.m p.L p.x0)
    (budget p 0) seed.1 seed.2).trans (execute_cyclic p.m g p.L p.x0 (budget p 0))
  rw [hexec]
  unfold budget
  split
  · exact h.initial_accuracy p.x0 hdist ‹_›
  · rename_i hlarge
    let B := 1 + (p.m : ℝ) * (p.m - 1)
    let u := p.L * p.R ^ 2 / p.ε
    let a := 2 * B * Real.sqrt B * u / p.m
    change _ * ∑ i, (f i (iter p.m g p.L p.x0
      (min (p.m * ⌈(p.m : ℝ) ^ 3 * u⌉₊) (p.m * (1 + ⌈a⌉₊)))) - f i xstar) ≤ _
    rcases le_total (p.m * ⌈(p.m : ℝ) ^ 3 * u⌉₊) (p.m * (1 + ⌈a⌉₊)) with hold | hnew
    · rw [min_eq_left hold]
      apply h.accuracy p.x0 hdist hε
      convert Nat.le_ceil ((p.m : ℝ) ^ 3 * u) using 1
      dsimp [u]
      ring
    · rw [min_eq_right hnew]
      have hm : (1 : ℝ) ≤ p.m := by exact_mod_cast NeZero.pos p.m
      have hB : 0 < B := by dsimp [B]; nlinarith
      have hu : 0 < u := div_pos (by linarith) hε
      have ha : 0 < a := by dsimp [a]; positivity
      have hn : 0 < ⌈a⌉₊ := Nat.ceil_pos.mpr ha
      apply (h.pass_accuracy_relaxed p.x0 hdist (1 + ⌈a⌉₊) (by omega)).trans
      push_cast
      change 2 * B * Real.sqrt B * p.L * p.R ^ 2 / _ ≤ p.ε
      have hr : (0 : ℝ) < ⌈a⌉₊ := by exact_mod_cast hn
      rw [div_le_iff₀ (mul_pos (by positivity) (by linarith))]
      have hc' := (div_le_iff₀ (by positivity : 0 < (p.m : ℝ))).mp (Nat.le_ceil a)
      dsimp [u] at hc'
      rw [← mul_div_assoc, div_le_iff₀ hε] at hc'
      linarith

end OracleTemplate.CyclicGradientPassDisplacement
