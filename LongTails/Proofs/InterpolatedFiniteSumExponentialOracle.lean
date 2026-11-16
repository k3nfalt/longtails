import LongTails.Proofs.InterpolatedFiniteSumExponentialFamily
import LongTails.Proofs.InterpolatedFiniteSumBlockOracle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open Classical OracleTemplate

namespace LongTails.Proofs.InterpolatedFiniteSumExponentialOracle

open InterpolatedFiniteSumExponential InterpolatedFiniteSumExponentialFamily
open InterpolatedFiniteSumPairs InterpolatedFiniteSumBlocks InterpolatedFiniteSumBlockOracle

noncomputable def transform {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (a : ℝ × EuclideanSpace ℝ (Fin d)) :
    ℝ × EuclideanSpace ℝ (Fin d) :=
  (C * (Real.exp (a.1 + ⟪v, x⟫) - 1) - C * ⟪v, x⟫,
    (C * Real.exp (a.1 + ⟪v, x⟫)) • (a.2 + v) - C • v)

lemma transform_full {d : ℕ} (m : EuclideanSpace ℝ (Fin d) → ℝ)
    (dm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) (C : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    transform v C x (m x, dm x) = (centeredValue m v C x, centeredField m dm v C x) := by
  simp only [transform, centeredValue, centeredField, value, field,
    InterpolatedFiniteSumCentering.centered, real_inner_smul_left]

noncomputable def reply {d n g k : ℕ} (h : 2 * g ≤ n)
    (v : EuclideanSpace ℝ (Fin d)) (C c σ r G W B : ℝ)
    (π : (Fin g × Fin (k + 1)) → Fin d) (q : Fin n × EuclideanSpace ℝ (Fin d)) (ℓ : ℕ) :
    ℝ × EuclideanSpace ℝ (Fin d) :=
  paired h (fun a x => transform (signed v a.2) C x
    (latentReply (fun j => π (a.1, j)) ℓ c σ r G W B x)) q.1 q.2

lemma reply_prefix {d n g k : ℕ} (hg : 0 < g) (h : 2 * g ≤ n)
    (v : EuclideanSpace ℝ (Fin d)) (C c σ r G W B : ℝ)
    (π ρ : (Fin g × Fin (k + 1)) → Fin d) (q : Fin n × EuclideanSpace ℝ (Fin d)) (ℓ : ℕ)
    (hp : ∀ j : Fin (k + 1), j.val < ℓ + 1 → π (which hg q.1, j) = ρ (which hg q.1, j)) :
    reply h v C c σ r G W B π q ℓ = reply h v C c σ r G W B ρ q ℓ := by
  rcases index_or_outside h q.1 with ⟨a, ha⟩ | hi
  · have hh : which hg q.1 = a.1 := by rw [← ha, which_index]
    have he := latentReply_prefix (fun j => π (a.1, j)) (fun j => ρ (a.1, j))
      ℓ c σ r G W B q.2 (by simpa only [hh] using hp)
    simp only [reply, ← ha, paired_at_index, he]
  · simp only [reply, paired_outside h _ q.1 hi]

noncomputable def fullReply {d n g k : ℕ} (h : 2 * g ≤ n)
    (π : (Fin g × Fin (k + 1)) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d))
    (C c σ r G W : ℝ) (q : Fin n × EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  (components h (fun i => shielded (block π i) c σ r G W) v C q.1 q.2,
    fields h (fun i => shielded (block π i) c σ r G W)
      (fun i => shieldedField (block π i) c σ r G W) v C q.1 q.2)

lemma reply_full {d n g k : ℕ} (hg : 0 < g) (h : 2 * g ≤ n)
    (π : (Fin g × Fin (k + 1)) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d))
    (C c σ r G W B : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hG : 0 < G) (hW : 0 < W)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (q : Fin n × EuclideanSpace ℝ (Fin d)) (ℓ : ℕ)
    (hp : ‖q.2‖ ≤ B → ∀ j : Fin (k + 1), ℓ ≤ j.val → |q.2 (π (which hg q.1, j))| ≤ σ / 8) :
    reply h v C c σ r G W B π q ℓ = fullReply h π v C c σ r G W q := by
  rcases index_or_outside h q.1 with ⟨a, ha⟩ | hi
  · have hh : which hg q.1 = a.1 := by rw [← ha, which_index]
    have he := latentReply_full (block π a.1) ℓ c σ r G W B hc hσ hG hW hgrad hB q.2
      (by
        intro hn j hj
        change |q.2 (π (a.1, j))| ≤ σ / 8
        simpa only [hh] using hp hn j hj)
    simp only [reply, fullReply, components, fields, ← ha, paired_at_index]
    rw [show (fun j => π (a.1, j)) = (block π a.1 : Fin (k + 1) → Fin d) from rfl, he]
    exact transform_full _ _ _ _ _
  · simp only [reply, fullReply, components, fields, paired_outside h _ q.1 hi]
    rfl

noncomputable def fullOracle {d n g k : ℕ} (h : 2 * g ≤ n)
    (π : (Fin g × Fin (k + 1)) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d)) (C c σ r G W : ℝ) :
    Oracle (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d)) where
  answer _ q _ := fullReply h π v C c σ r G W q.2

lemma coupled_execution {d n g k : ℕ} (hg : 0 < g) (h : 2 * g ≤ n)
    (π : (Fin g × Fin (k + 1)) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d))
    (C c σ r G W B θ : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hG : 0 < G) (hW : 0 < W)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B) (hθ : θ ≤ σ / 8)
    (A : Algorithm (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) (b : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (carrier : Fin d)
    (hgood : ¬InterpolatedFiniteSumBlockExecution.Bad A (fun q => which hg q.1)
      (reply h v C c σ r G W B) Prod.snd id (A.initial seed) b B θ carrier π) :
    execute (fullOracle h π v C c σ r G W) A (fun _ => b) seed ξ =
      A.output (InterpolatedFiniteSumBlockExecution.process A (fun q => which hg q.1)
        (reply h v C c σ r G W B) (A.initial seed) π b).1.1 := by
  rw [execute_eq_of_answer_eq (fullOracle h π v C c σ r G W)
    (fullReply h π v C c σ r G W) (by intros; rfl),
    execute_iterate (fullReply h π v C c σ r G W) A b seed]
  apply congrArg A.output
  apply InterpolatedFiniteSumBlockExecution.process_coupling
  intro t ht
  let s := (InterpolatedFiniteSumBlockExecution.process A (fun q => which hg q.1)
    (reply h v C c σ r G W B) (A.initial seed) π t).1
  let q := (A.query s.1).2
  apply (reply_full hg h π v C c σ r G W B hc hσ hG hW hgrad hB q
    (s.2 (which hg q.1)) _).symm
  intro hnear j hj
  have hh := InterpolatedFiniteSumBlockExecution.good_coordinate A (fun q => which hg q.1)
    (reply h v C c σ r G W B) Prod.snd id (A.initial seed) b B θ carrier π hgood
    ⟨t, by omega⟩ (which hg q.1, j) hj
    (by simpa only [InterpolatedFiniteSumBlockExecution.observation,
      ite_eq_right (ne_of_lt ht)] using hnear)
  have hsmall : |q.2 (π (which hg q.1, j))| ≤ θ := by
    simpa only [InterpolatedFiniteSumBlockExecution.observation,
      ite_eq_right (ne_of_lt ht)] using hh
  exact hsmall.trans hθ

lemma ideal_output_lower {d n g k : ℕ} (hg : 0 < g) (h : 2 * g ≤ n)
    (π : (Fin g × Fin (k + 1)) ↪ Fin d) (v : EuclideanSpace ℝ (Fin d))
    (C c σ r G W B θ : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c) (hσ : 0 < σ)
    (hr : 0 ≤ r) (hG : 0 < G) (hW : 0 < W) (hθ : 0 ≤ θ)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (A : Algorithm (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) (b : ℕ) (seed : A.Seed) (carrier : Fin d)
    (hgood : ¬InterpolatedFiniteSumBlockExecution.Bad A (fun q => which hg q.1)
      (reply h v C c σ r G W B) Prod.snd id (A.initial seed) b B θ carrier π) :
    let η := (k + 1 : ℕ) * c / 2
    let s := (InterpolatedFiniteSumBlockExecution.process A (fun q => which hg q.1)
      (reply h v C c σ r G W B) (A.initial seed) π b).1
    (2 * C * g / n) * (Real.exp η - 1 - Real.exp η * (c * θ / σ)) -
      (C * Real.exp η * c / n) * ∑ i, (s.2 i : ℝ) ≤
      (n : ℝ)⁻¹ * ∑ i, components h (fun j => shielded (block π j) c σ r G W) v C i (A.output s.1) := by
  dsimp only
  let s := (InterpolatedFiniteSumBlockExecution.process A (fun q => which hg q.1)
    (reply h v C c σ r G W B) (A.initial seed) π b).1
  have hcomp (i : Fin g) : (k + 1 : ℕ) * c / 2 - c * θ / σ - (c / 2) * s.2 i ≤
      shielded (block π i) c σ r G W (A.output s.1) := by
    have hh := shielded_output_lower (block π i) c σ r G W B θ hc hσ hr hG hW hθ hB
      (s.2 i) (InterpolatedFiniteSumBlockExecution.process_counts_le A (fun q => which hg q.1)
        (reply h v C c σ r G W B) (A.initial seed) π b i) (A.output s.1) (by
        intro hnear j hj
        have hz := InterpolatedFiniteSumBlockExecution.good_coordinate A (fun q => which hg q.1)
          (reply h v C c σ r G W B) Prod.snd id (A.initial seed) b B θ carrier π hgood
          (Fin.last b) (i, j) hj (by
            simpa only [InterpolatedFiniteSumBlockExecution.observation, Fin.val_last,
              ite_eq_left rfl, ite_true, id_eq] using hnear)
        simp only [InterpolatedFiniteSumBlockExecution.observation, Fin.val_last,
          ite_true, id_eq] at hz
        exact hz)
    nlinarith only [hh]
  have hh := components_sum_tangent h (fun i => shielded (block π i) c σ r G W)
    v C ((k + 1 : ℕ) * c / 2) (c * θ / σ) (c / 2) hC (fun i => (s.2 i : ℝ))
    (A.output s.1) hcomp
  have hb := mul_le_mul_of_nonneg_left hh (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  convert hb using 1
  ring

end LongTails.Proofs.InterpolatedFiniteSumExponentialOracle
