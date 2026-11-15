import LongTails.Proofs.InterpolatedFiniteSumBlocks
import LongTails.Proofs.InterpolatedFiniteSumChainLocality
import LongTails.Proofs.InterpolatedFiniteSumBlockExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open Classical OracleTemplate

namespace LongTails.Proofs.InterpolatedFiniteSumBlockOracle

open InterpolatedFiniteSumChains InterpolatedFiniteSumShield InterpolatedFiniteSumChainLocality
open InterpolatedFiniteSumBlocks

noncomputable def partialShift {d k : ℕ} (π : Fin (k + 1) → Fin d) (ℓ : ℕ) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := partialValue π ℓ c σ x + (k + 1 : ℕ) * c / 2

noncomputable def latentReply {d k : ℕ} (π : Fin (k + 1) → Fin d) (ℓ : ℕ)
    (c σ r G W B : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  if ‖x‖ ≤ B then
    (envelope (partialShift π ℓ c σ) (radialWall r G 0 W) W x,
      envelopeField (partialShift π ℓ c σ) (radialWall r G 0 W)
        (partialField π ℓ c σ) (radialField r G) W x)
  else (radialWall r G 0 W x, radialField r G x)

lemma latentReply_prefix {d k : ℕ} (π ρ : Fin (k + 1) → Fin d) (ℓ : ℕ)
    (c σ r G W B : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), j.val < ℓ + 1 → π j = ρ j) :
    latentReply π ℓ c σ r G W B x = latentReply ρ ℓ c σ r G W B x := by
  have hv := partialValue_prefix π ρ ℓ c σ h x
  have hg := partialField_prefix π ρ ℓ c σ h x
  simp only [latentReply, envelope, envelopeField, envelopeMix, partialShift, hv, hg]

lemma latentReply_near {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (ℓ : ℕ)
    (c σ r G W B : ℝ) (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ B)
    (h : ∀ j : Fin (k + 1), ℓ ≤ j.val → |x (π j)| ≤ σ / 8) :
    latentReply π ℓ c σ r G W B x = (shielded π c σ r G W x, shieldedField π c σ r G W x) := by
  have hv : partialValue π ℓ c σ x = rawChain π c σ x :=
    (partialValue_full π ℓ c σ hσ x h).trans (partialValue_raw π c σ x)
  have hg : partialField π ℓ c σ x = rawField π c σ x :=
    (partialField_full π ℓ c σ hσ x h).trans (partialField_raw π c σ x)
  simp only [latentReply, ite_eq_left hx, shielded, shieldedField, envelope, envelopeField,
    envelopeMix, partialShift, shifted, hv, hg]

lemma latentReply_far {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (ℓ : ℕ)
    (c σ r G W B : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hG : 0 < G) (hW : 0 < W)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) (hx : B < ‖x‖) :
    latentReply π ℓ c σ r G W B x = (shielded π c σ r G W x, shieldedField π c σ r G W x) := by
  have hgrowth := shifted_growth π c σ G hc hσ hgrad x
  have houter : 4 * r + (shifted π c σ 0 - 0 + W) / G ≤ ‖x‖ := by
    simp only [shifted, rawChain_zero, zero_add, sub_zero]
    exact hB.trans hx.le
  rw [latentReply, ite_eq_right (not_le.mpr hx), shielded, shieldedField,
    envelope_radial_exterior _ r G 0 W hG hW x hgrowth houter,
    envelopeField_radial_exterior _ _ r G 0 W hG hW x hgrowth houter]

lemma latentReply_full {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (ℓ : ℕ)
    (c σ r G W B : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hG : 0 < G) (hW : 0 < W)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (x : EuclideanSpace ℝ (Fin d))
    (h : ‖x‖ ≤ B → ∀ j : Fin (k + 1), ℓ ≤ j.val → |x (π j)| ≤ σ / 8) :
    latentReply π ℓ c σ r G W B x = (shielded π c σ r G W x, shieldedField π c σ r G W x) := by
  by_cases hx : ‖x‖ ≤ B
  · exact latentReply_near π ℓ c σ r G W B hσ x hx (h hx)
  · exact latentReply_far π ℓ c σ r G W B hc hσ hG hW hgrad hB x (lt_of_not_ge hx)

noncomputable def reply {d n k : ℕ} (c σ r G W B : ℝ)
    (π : (Fin n × Fin (k + 1)) → Fin d) (q : Fin n × EuclideanSpace ℝ (Fin d)) (ℓ : ℕ) :
    ℝ × EuclideanSpace ℝ (Fin d) := latentReply (fun j => π (q.1, j)) ℓ c σ r G W B q.2

lemma reply_prefix {d n k : ℕ} (c σ r G W B : ℝ)
    (π ρ : (Fin n × Fin (k + 1)) → Fin d) (q : Fin n × EuclideanSpace ℝ (Fin d)) (ℓ : ℕ)
    (h : ∀ j : Fin (k + 1), j.val < ℓ + 1 → π (q.1, j) = ρ (q.1, j)) :
    reply c σ r G W B π q ℓ = reply c σ r G W B ρ q ℓ :=
  latentReply_prefix _ _ ℓ c σ r G W B q.2 h

noncomputable def fullReply {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d)
    (c σ r G W : ℝ) (q : Fin n × EuclideanSpace ℝ (Fin d)) : ℝ × EuclideanSpace ℝ (Fin d) :=
  (shielded (block π q.1) c σ r G W q.2, shieldedField (block π q.1) c σ r G W q.2)

noncomputable def fullOracle {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d)
    (c σ r G W : ℝ) : Oracle (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d)) where
  answer _ q _ := fullReply π c σ r G W q.2

lemma execute_fullOracle {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d)
    (c σ r G W : ℝ)
    (A : Algorithm (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) (b : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (fullOracle π c σ r G W) A (fun _ => b) seed ξ =
      A.output ((fun s => A.update s (fullReply π c σ r G W (A.query s).2))^[b] (A.initial seed)) := by
  rw [execute_eq_of_answer_eq (fullOracle π c σ r G W) (fullReply π c σ r G W) (by intros; rfl)]
  exact execute_iterate (fullReply π c σ r G W) A b seed

lemma coupled_execution {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d)
    (c σ r G W B θ : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hG : 0 < G) (hW : 0 < W)
    (hgrad : (c / σ) * (1 + 2 * Real.sqrt (k + 1 : ℕ)) ≤ G)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B) (hθ : θ ≤ σ / 8)
    (A : Algorithm (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) (b : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) (carrier : Fin d)
    (hgood : ¬InterpolatedFiniteSumBlockExecution.Bad A Prod.fst (reply c σ r G W B)
      Prod.snd id (A.initial seed) b B θ carrier π) :
    execute (fullOracle π c σ r G W) A (fun _ => b) seed ξ =
      A.output (InterpolatedFiniteSumBlockExecution.process A Prod.fst (reply c σ r G W B)
        (A.initial seed) π b).1.1 := by
  rw [execute_fullOracle]
  apply congrArg A.output
  apply InterpolatedFiniteSumBlockExecution.process_coupling
  intro t ht
  let s := (InterpolatedFiniteSumBlockExecution.process A Prod.fst (reply c σ r G W B)
    (A.initial seed) π t).1
  let q := (A.query s.1).2
  change fullReply π c σ r G W q = latentReply (block π q.1) (s.2 q.1) c σ r G W B q.2
  apply (latentReply_full (block π q.1) (s.2 q.1) c σ r G W B hc hσ hG hW hgrad hB q.2 _).symm
  intro hnear j hj
  have hh := InterpolatedFiniteSumBlockExecution.good_coordinate A Prod.fst (reply c σ r G W B)
    Prod.snd id (A.initial seed) b B θ carrier π hgood ⟨t, by omega⟩ (q.1, j) hj
    (by simpa only [InterpolatedFiniteSumBlockExecution.observation,
      ite_eq_right (ne_of_lt ht)] using hnear)
  have hsmall : |q.2 (π (q.1, j))| ≤ θ := by
    simpa only [InterpolatedFiniteSumBlockExecution.observation,
      ite_eq_right (ne_of_lt ht)] using hh
  exact hsmall.trans hθ

lemma average_lower (n : ℕ) (hn : 0 < n) (f a : Fin n → ℝ) (A C : ℝ)
    (h : ∀ i, A - C * a i ≤ f i) :
    A - (C / n) * ∑ i, a i ≤ (n : ℝ)⁻¹ * ∑ i, f i := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  convert hh using 1
  field_simp

lemma ideal_output_lower {d n k : ℕ} (π : (Fin n × Fin (k + 1)) ↪ Fin d) (hn : 0 < n)
    (c σ r G W B θ : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hr : 0 ≤ r)
    (hG : 0 < G) (hW : 0 < W) (hθ : 0 ≤ θ)
    (hB : 4 * r + ((k + 1 : ℕ) * c / 2 + W) / G ≤ B)
    (A : Algorithm (Fin n × EuclideanSpace ℝ (Fin d)) (ℝ × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d))) (b : ℕ) (seed : A.Seed) (carrier : Fin d)
    (hgood : ¬InterpolatedFiniteSumBlockExecution.Bad A Prod.fst (reply c σ r G W B)
      Prod.snd id (A.initial seed) b B θ carrier π) :
    let s := (InterpolatedFiniteSumBlockExecution.process A Prod.fst (reply c σ r G W B)
      (A.initial seed) π b).1
    (k + 1 : ℕ) * c / 2 - c * θ / σ - (c / (2 * n)) * ∑ i, (s.2 i : ℝ) ≤
      (n : ℝ)⁻¹ * ∑ i, shielded (block π i) c σ r G W (A.output s.1) := by
  dsimp only
  let s := (InterpolatedFiniteSumBlockExecution.process A Prod.fst (reply c σ r G W B)
    (A.initial seed) π b).1
  have hcomp (i : Fin n) : (k + 1 : ℕ) * c / 2 - c * θ / σ - (c / 2) * s.2 i ≤
      shielded (block π i) c σ r G W (A.output s.1) := by
    have hh := shielded_output_lower (block π i) c σ r G W B θ hc hσ hr hG hW hθ hB
      (s.2 i) (InterpolatedFiniteSumBlockExecution.process_counts_le A Prod.fst
        (reply c σ r G W B) (A.initial seed) π b i) (A.output s.1) (by
        intro hnear j hj
        have hz := InterpolatedFiniteSumBlockExecution.good_coordinate A Prod.fst
          (reply c σ r G W B) Prod.snd id (A.initial seed) b B θ carrier π hgood
          (Fin.last b) (i, j) hj (by
            simpa only [InterpolatedFiniteSumBlockExecution.observation, Fin.val_last,
              ite_eq_left rfl, ite_true, id_eq] using hnear)
        simp only [InterpolatedFiniteSumBlockExecution.observation, Fin.val_last,
          ite_true, id_eq] at hz
        exact hz)
    nlinarith only [hh]
  have hav := average_lower n hn _ (fun i => (s.2 i : ℝ))
    ((k + 1 : ℕ) * c / 2 - c * θ / σ) (c / 2) hcomp
  convert hav using 1
  ring

noncomputable def safeEmbedding {I : Type*} [Fintype I] {d : ℕ} (fallback : I ↪ Fin d)
    (carrier : Fin d) (π : I → Fin d) : I ↪ Fin d :=
  if h : Function.Injective π ∧ ∀ i, π i ≠ carrier then ⟨π, h.1⟩ else fallback

lemma safeEmbedding_good {I : Type*} [Fintype I] {d : ℕ} (fallback : I ↪ Fin d)
    (carrier : Fin d) (π : I → Fin d) (hπ : Function.Injective π) (hc : ∀ i, π i ≠ carrier) :
    (safeEmbedding fallback carrier π : I → Fin d) = π := by
  have h : Function.Injective π ∧ ∀ i, π i ≠ carrier := ⟨hπ, hc⟩
  simp only [safeEmbedding, dite_eq_left h]
  rfl

lemma safeEmbedding_avoids {I : Type*} [Fintype I] {d : ℕ} (fallback : I ↪ Fin d)
    (carrier : Fin d) (hf : ∀ i, fallback i ≠ carrier) (π : I → Fin d) :
    ∀ i, safeEmbedding fallback carrier π i ≠ carrier := by
  unfold safeEmbedding
  split_ifs with h
  · exact h.2
  · exact hf

end LongTails.Proofs.InterpolatedFiniteSumBlockOracle
