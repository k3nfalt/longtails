import LongTails.Proofs.NcConcaveExecution
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveCounting

open Classical
open LongTails.Proofs.NcConcaveInstance LongTails.Proofs.NcConcaveModel
open LongTails.Proofs.NcConcaveLocality LongTails.Proofs.NcConcaveChainGrad
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveReply
open LongTails.Proofs.NcConcaveOracle LongTails.Proofs.NcConcaveExecution
open LongTails.Proofs.SmoothConvexFiniteHiding (largeSet not_largeSet_small bounded_prefix_bad_count)
open LongTails.Proofs.FiniteSumNondualLowerHiding (hits distinctWords)
open LongTails.Proofs.FiniteSumNondualLowerExposure (hits_drop_positive)
open LongTails.Proofs.FiniteSumNondualLowerAveraging (CoordinateWords coordinateEmbedding coordinateEmbedding_labels subtype_indicator_sum)
open LongTails.Setups.StochasticNonconvexConcaveMinimax

variable {d n m : ℕ} {St : Type*}

noncomputable def obsVec (s : ℝ) (z : Prim d × Dual d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (|z.1 (0, i)| + |z.1 (1, i)| + |z.2 i|) / s)

lemma obsVec_norm {s : ℝ} (hs : 0 < s) (z : Prim d × Dual d) :
    ‖obsVec s z‖ ^ 2 ≤ 3 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) / s ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, norm_sq_prim, EuclideanSpace.real_norm_sq_eq]
  simp only [obsVec, PiLp.toLp_apply, div_pow, ← Finset.sum_div, blockSq_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have h1 := sq_abs (z.1 (0, i)); have h2 := sq_abs (z.1 (1, i)); have h3 := sq_abs (z.2 i)
  nlinarith [sq_nonneg (|z.1 (0, i)| - |z.1 (1, i)|), sq_nonneg (|z.1 (0, i)| - |z.2 i|),
    sq_nonneg (|z.1 (1, i)| - |z.2 i|)]

lemma obs_U {s : ℝ} (hs : 0 < s) (z : Prim d × Dual d) (i : Fin d) :
    |z.1 (0, i)| / s ≤ |obsVec s z i| := by
  simp only [obsVec, PiLp.toLp_apply]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (|z.1 (0, i)| + |z.1 (1, i)| + |z.2 i|) / s by positivity)]
  exact div_le_div_of_nonneg_right (show |z.1 (0, i)| ≤ |z.1 (0, i)| + |z.1 (1, i)| + |z.2 i| by
    linarith [abs_nonneg (z.1 (1, i)), abs_nonneg (z.2 i)]) hs.le

lemma obs_AB {s : ℝ} (hs : 0 < s) (z : Prim d × Dual d) (i : Fin d) :
    |z.1 (1, i)| / s ≤ |obsVec s z i| := by
  simp only [obsVec, PiLp.toLp_apply]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (|z.1 (0, i)| + |z.1 (1, i)| + |z.2 i|) / s by positivity)]
  exact div_le_div_of_nonneg_right (show |z.1 (1, i)| ≤ |z.1 (0, i)| + |z.1 (1, i)| + |z.2 i| by
    linarith [abs_nonneg (z.1 (0, i)), abs_nonneg (z.2 i)]) hs.le

lemma obs_Y {s : ℝ} (hs : 0 < s) (z : Prim d × Dual d) (i : Fin d) :
    |z.2 i| / s ≤ |obsVec s z i| := by
  simp only [obsVec, PiLp.toLp_apply]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (|z.1 (0, i)| + |z.1 (1, i)| + |z.2 i|) / s by positivity)]
  exact div_le_div_of_nonneg_right (show |z.2 i| ≤ |z.1 (0, i)| + |z.1 (1, i)| + |z.2 i| by
    linarith [abs_nonneg (z.1 (0, i)), abs_nonneg (z.1 (1, i))]) hs.le

lemma small_of_obs {s θ' : ℝ} (hs : 0 < s) (W : Word d n m) (z : Prim d × Dual d) (r : ℕ)
    (h : ∀ k : Fin (K n m), r ≤ k.val → |obsVec s z (W.w k)| ≤ θ') :
    SmallFrom θ' r (selC W s z.1 z.2) where
  hu j hj := by
    simp only [selC, abs_div, abs_of_pos hs]
    exact (obs_U hs z _).trans (h (posU j) hj)
  ha i hi := by
    simp only [selC, abs_div, abs_of_pos hs]
    exact (obs_AB hs z _).trans (h (posA i) hi)
  hb i hi := by
    simp only [selC, abs_div, abs_of_pos hs]
    exact (obs_AB hs z _).trans (h (posB i) hi)
  hy i k hk := by
    simp only [selC, abs_div, abs_of_pos hs]
    exact (obs_Y hs z _).trans (h (posY i k) hk)

noncomputable def observation (θ τ p : ℝ) (s ℓ : ℝ) (qry : St → Prim d × Dual d) (out : St → Prim d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1))
    (π : Fin (K n m) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  if j.val < N then obsVec s (qry (simState θ τ p ⟨π⟩ s ℓ qry upd init ω j.val))
  else obsVec s (out (simState θ τ p ⟨π⟩ s ℓ qry upd init ω j.val), 0)

lemma observation_prefix (θ τ p : ℝ) (s ℓ : ℝ) (qry : St → Prim d × Dual d) (out : St → Prim d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1))
    (π ρ : Fin (K n m) ↪ Fin d) (h : ∀ k : Fin (K n m), k.val < levelSeq n m p ω j.val → π k = ρ k) :
    observation θ τ p s ℓ qry out upd init ω N j π = observation θ τ p s ℓ qry out upd init ω N j ρ := by
  unfold observation
  rw [simState_prefix θ τ p (W := ⟨π⟩) (W' := ⟨ρ⟩) s ℓ qry upd init ω j.val h]

def coordinateBad (θ τ p : ℝ) (s ℓ : ℝ) (qry : St → Prim d × Dual d) (out : St → Prim d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) (N : ℕ) (B θ' : ℝ)
    (π : Fin (K n m) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits (largeSet B θ' (observation θ τ p s ℓ qry out upd init ω N j π))
    ((List.ofFn π).drop (levelSeq n m p ω j.val))

lemma good_small (θ τ p : ℝ) (s ℓ : ℝ) (qry : St → Prim d × Dual d) (out : St → Prim d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) (N : ℕ) (B θ' : ℝ)
    (π : Fin (K n m) ↪ Fin d)
    (hgood : ¬ coordinateBad θ τ p s ℓ qry out upd init ω N B θ' π) (j : Fin (N + 1))
    (hj : ‖observation θ τ p s ℓ qry out upd init ω N j π‖ ≤ B)
    (k : Fin (K n m)) (hk : levelSeq n m p ω j.val ≤ k.val) :
    |observation θ τ p s ℓ qry out upd init ω N j π (π k)| ≤ θ' := by
  apply not_largeSet_small _ _ _ hj
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ k hk h⟩

lemma bad_sum_bound (θ τ p : ℝ) (s ℓ : ℝ) (qry : St → Prim d × Dual d) (out : St → Prim d)
    (upd : St → Prim d × Dual d → St) (init : St) (ω : ℕ → ℝ) (N : ℕ) (B θ' : ℝ)
    (hB : 0 ≤ B) (hθ' : 0 < θ') (Dm : ℝ) (hDm : 0 ≤ Dm) (hDs : Dm + (K n m : ℕ) ≤ d) :
    Dm * (∑ w : CoordinateWords d (n * (m + 4)), if coordinateBad θ τ p s ℓ qry out upd init ω N B θ'
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (K n m : ℕ) * (B ^ 2 / θ' ^ 2) * Fintype.card (CoordinateWords d (n * (m + 4))) := by
  let bad := fun π : Fin (K n m) ↪ Fin d => coordinateBad θ τ p s ℓ qry out upd init ω N B θ' π
  have he (w : CoordinateWords d (n * (m + 4))) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (K n m) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet B θ' (observation θ τ p s ℓ qry out upd init ω N j π))
          (w.val.drop (levelSeq n m p ω j.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w, ?_⟩
      rw [← coordinateEmbedding_labels w]
      exact hj
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro k
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) k
      subst hp
      rw [← hπ] at hj
      exact ⟨j, hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1), ∃ π : Fin (K n m) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet B θ' (observation θ τ p s ℓ qry out upd init ω N j π))
      (w.drop (levelSeq n m p ω j.val))
  have hs : (∑ w : CoordinateWords d (n * (m + 4)), if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (K n m) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change Dm * (∑ w : CoordinateWords d (n * (m + 4)), if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := K n m) B θ' Dm hB hθ' hDm hDs
    (fun j : Fin (N + 1) => levelSeq n m p ω j.val) (fun j => levelSeq_le p ω j.val)
    (observation θ τ p s ℓ qry out upd init ω N)
    (observation_prefix θ τ p s ℓ qry out upd init ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  all_goals first
    | rfl
    | (apply congrArg (fun t : Finset (List (Fin d)) => Dm * (t.card : ℝ))
       ext w
       simp only [Finset.mem_filter, P])

end LongTails.Proofs.NcConcaveCounting
