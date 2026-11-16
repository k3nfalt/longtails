import LongTails.Proofs.ManyConstraintExpected

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintRun

open LongTails.Proofs.ManyConstraintPenalty LongTails.Proofs.ManyConstraintFinite
  LongTails.Proofs.ManyConstraintNoise LongTails.Proofs.ManyConstraintBall
  LongTails.Proofs.ManyConstraintCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ξ : Type*}
variable {m : ℕ}

structure Knobs (E : Type*) where
  β : ℝ
  μ : ℝ
  ρ : ℝ
  τ : ℝ
  α : ℝ
  Lt : ℝ
  θ : ℝ
  x0 : E
  b : ℕ
  M : ℕ

noncomputable def step (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (s hs : E)
    (yz : E × E) (j : Fin m) (ω : Fin k.b → Ξ) : E × E :=
  let x := mix k.τ s yz.1 yz.2
  let v := batch grad ω x + (penGrad k.β (P j) x - penGrad k.β (P j) s + hs)
  (proxBall k.μ k.x0 k.ρ (1 / (3 * k.Lt)) x v, proxBall k.μ k.x0 k.ρ k.α yz.2 v)

noncomputable def innerRun (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (s hs : E) :
    (n : ℕ) → (E × E) → (Fin n → Fin m) → (ℕ → Ξ) → (E × E) × E
  | 0, yz, _, _ => (yz, 0)
  | n + 1, yz, js, ξ =>
    let next := step grad P k s hs yz (js 0) (fun i => ξ i)
    let rest := innerRun grad P k s hs n next (fun i => js i.succ) (fun t => ξ (k.b + 2 + t))
    (rest.1, next.1 + k.θ • rest.2)

noncomputable def weightSum (θ : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, θ ^ i

structure St (E : Type*) where
  s : E
  y : E
  z : E

noncomputable def epoch (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (st : St E)
    (js : Fin k.M → Fin m) (ξ : ℕ → Ξ) : St E :=
  let res := innerRun grad P k st.s (hgrad k.β P st.s) k.M (st.y, st.z) js (fun t => ξ (m + t))
  ⟨(weightSum k.θ k.M)⁻¹ • res.2, res.1.1, res.1.2⟩

def epochLen (m : ℕ) (k : Knobs E) : ℕ := m + k.M * (k.b + 2)

noncomputable def run (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) :
    (S : ℕ) → St E → (Fin S → Fin k.M → Fin m) → (ℕ → Ξ) → St E
  | 0, st, _, _ => st
  | S + 1, st, jss, ξ =>
    run grad P k S (epoch grad P k st (jss 0) ξ) (fun i => jss i.succ)
      (fun t => ξ (epochLen m k + t))

noncomputable def cleanup (P : Fin m → E → E) : (Q : ℕ) → E → (Fin Q → Fin m) → E
  | 0, p, _ => p
  | Q + 1, p, js => cleanup P Q (P (js 0) p) (fun i => js i.succ)

lemma weightSum_pos {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 0 < n) : 0 < weightSum θ n := by
  unfold weightSum
  exact Finset.sum_pos (fun i _ => pow_pos hθ i) (Finset.nonempty_range_iff.mpr hn.ne')

lemma weightSum_succ (θ : ℝ) (n : ℕ) : weightSum θ (n + 1) = 1 + θ * weightSum θ n := by
  unfold weightSum
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  ring_nf

lemma step_mem (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (hρ : 0 ≤ k.ρ)
    (s hs : E) (yz : E × E) (j : Fin m) (ω : Fin k.b → Ξ) :
    (step grad P k s hs yz j ω).1 ∈ closedBall k.x0 k.ρ ∧
      (step grad P k s hs yz j ω).2 ∈ closedBall k.x0 k.ρ :=
  ⟨proxBall_mem hρ _ _, proxBall_mem hρ _ _⟩

lemma innerRun_mem (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (hρ : 0 ≤ k.ρ)
    (hθ : 0 < k.θ) (s hs : E) :
    ∀ (n : ℕ) (yz : E × E) (js : Fin n → Fin m) (ξ : ℕ → Ξ),
      ((yz.1 ∈ closedBall k.x0 k.ρ ∧ yz.2 ∈ closedBall k.x0 k.ρ) ∨ 0 < n) →
      (innerRun grad P k s hs n yz js ξ).1.1 ∈ closedBall k.x0 k.ρ ∧
      (innerRun grad P k s hs n yz js ξ).1.2 ∈ closedBall k.x0 k.ρ ∧
      ‖(innerRun grad P k s hs n yz js ξ).2 - weightSum k.θ n • k.x0‖ ≤
        weightSum k.θ n * k.ρ := by
  intro n
  induction n with
  | zero =>
    intro yz js ξ h
    rcases h with h | h
    · simp [innerRun, weightSum, h.1, h.2]
    · omega
  | succ n ih =>
    intro yz js ξ _
    set next := step grad P k s hs yz (js 0) (fun i => ξ i)
    have hn := step_mem grad P k hρ s hs yz (js 0) (fun i => ξ i)
    obtain ⟨h1, h2, h3⟩ := ih next (fun i => js i.succ) (fun t => ξ (k.b + 2 + t)) (Or.inl hn)
    refine ⟨h1, h2, ?_⟩
    change ‖next.1 + k.θ • (innerRun grad P k s hs n next (fun i => js i.succ)
      (fun t => ξ (k.b + 2 + t))).2 - weightSum k.θ (n + 1) • k.x0‖ ≤ _
    rw [weightSum_succ, add_smul, one_smul, mul_smul]
    have hy : ‖next.1 - k.x0‖ ≤ k.ρ := by rw [← dist_eq_norm]; exact hn.1
    have he : next.1 + k.θ • (innerRun grad P k s hs n next (fun i => js i.succ)
        (fun t => ξ (k.b + 2 + t))).2 - (k.x0 + k.θ • (weightSum k.θ n • k.x0)) =
        (next.1 - k.x0) + k.θ • ((innerRun grad P k s hs n next (fun i => js i.succ)
          (fun t => ξ (k.b + 2 + t))).2 - weightSum k.θ n • k.x0) := by
      rw [smul_sub]; abel
    rw [he]
    calc _ ≤ ‖next.1 - k.x0‖ + ‖k.θ • ((innerRun grad P k s hs n next (fun i => js i.succ)
          (fun t => ξ (k.b + 2 + t))).2 - weightSum k.θ n • k.x0)‖ := norm_add_le _ _
      _ ≤ k.ρ + k.θ * (weightSum k.θ n * k.ρ) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
          gcongr
      _ = (1 + k.θ * weightSum k.θ n) * k.ρ := by ring

lemma epoch_mem (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (hρ : 0 ≤ k.ρ)
    (hθ : 0 < k.θ) (hM : 0 < k.M) (st : St E) (js : Fin k.M → Fin m) (ξ : ℕ → Ξ) :
    (epoch grad P k st js ξ).s ∈ closedBall k.x0 k.ρ ∧
      (epoch grad P k st js ξ).y ∈ closedBall k.x0 k.ρ ∧
      (epoch grad P k st js ξ).z ∈ closedBall k.x0 k.ρ := by
  obtain ⟨h1, h2, h3⟩ := innerRun_mem grad P k hρ hθ st.s (hgrad k.β P st.s) k.M (st.y, st.z) js
    (fun t => ξ (m + t)) (Or.inr hM)
  refine ⟨?_, h1, h2⟩
  have hw := weightSum_pos hθ hM
  rw [mem_closedBall, dist_eq_norm]
  change ‖(weightSum k.θ k.M)⁻¹ • (innerRun grad P k st.s (hgrad k.β P st.s) k.M (st.y, st.z) js
    (fun t => ξ (m + t))).2 - k.x0‖ ≤ k.ρ
  have he : (weightSum k.θ k.M)⁻¹ • (innerRun grad P k st.s (hgrad k.β P st.s) k.M (st.y, st.z) js
      (fun t => ξ (m + t))).2 - k.x0 = (weightSum k.θ k.M)⁻¹ • ((innerRun grad P k st.s
        (hgrad k.β P st.s) k.M (st.y, st.z) js (fun t => ξ (m + t))).2 -
          weightSum k.θ k.M • k.x0) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hw.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
  calc _ ≤ (weightSum k.θ k.M)⁻¹ * (weightSum k.θ k.M * k.ρ) := by gcongr
    _ = k.ρ := by field_simp

end LongTails.Proofs.ManyConstraintRun
