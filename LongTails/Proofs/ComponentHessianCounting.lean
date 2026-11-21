import LongTails.Proofs.ComponentHessianSimulation
import LongTails.Proofs.ComponentHessianGap

namespace LongTails.Proofs.ComponentHessianCounting

open Classical
open ComponentHessianFamily ComponentHessianTranscript ComponentHessianSimulation
open FiniteSumNondualLowerPolicy FiniteSumNondualLowerSearch FiniteSumNondualLowerHiding
open FiniteSumNondualLowerAveraging SmoothConvexFiniteHiding

variable {d k n : ℕ} {S : Type*}

def owner (anchor : Fin n) (w : List (Fin n)) (j : Fin (k + 1)) :=
  (anchor :: w)[j.val]?.getD anchor

lemma indices_full (anchor : Fin n) (w : List (Fin n)) (hw : w.length = k) (i : Fin n) :
    indices k (anchor :: w) i = owned (owner anchor w) i := by
  unfold indices owned
  apply Finset.filter_congr
  intro j _
  have hj : j.val < (anchor :: w).length := by simpa [hw] using j.isLt
  simp [owner, List.getElem?_eq_getElem hj]

variable (P : Policy d n S)

def complete (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (T : ℕ) (w : List (Fin n)) : Prop :=
  (P.simulate π anchor w T).2 = []

lemma owner_fraction (π : Fin (k + 1) ↪ Fin d) (anchor : Fin n) (T : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hT : 8 * T ≤ n * k) :
    4 * (∑ w : OwnerWords n k, if complete P π anchor T w.val then (1 : ℝ) else 0) ≤
      Fintype.card (OwnerWords n k) := by
  classical
  let q := policy P.component (P.step π) (P.initial, [anchor])
  rw [subtype_indicator_sum]
  have he : (words n k).filter (complete P π anchor T) =
      (words n k).filter (fun w => k ≤ discoveries n T q w) := by
    apply Finset.filter_congr
    intro w hw
    have h := wordAdvance_discoveries P.component (P.step π) T (P.initial, [anchor]) w
    change (P.simulate π anchor w T).2.length + discoveries n T q w = w.length at h
    rw [(mem_words n k w).mp hw] at h
    unfold complete
    rw [← List.length_eq_zero_iff]
    omega
  rw [he]
  simpa [OwnerWords, Fintype.card_coe, words_card] using completion_fraction n T k q hn hk hT

lemma coordinate_fraction (w : List (Fin n)) (hw : w.length = k) (anchor : Fin n) (T : ℕ)
    (D : ℝ) (hD : 0 < D) (hd : D + (k + 1 : ℕ) ≤ d)
    (hsize : 32 * (T + 1 : ℕ) * (k + 1 : ℕ) *
      ((2 * radius n (k + 1 : ℕ)) ^ 2 / (1 / 80 : ℝ)^2) ≤ D) :
    32 * (∑ v : CoordinateWords d k, if P.bad anchor w T (coordinateEmbedding v) then (1 : ℝ) else 0) ≤
      Fintype.card (CoordinateWords d k) := by
  classical
  let s := distinctWords (k+1) (Finset.univ : Finset (Fin d))
  let F := fun (j : Fin (T+1)) (π : Fin (k+1) ↪ Fin d) => P.exposure anchor w T j π
  let C := (2 * radius n (k+1 : ℕ))^2 / (1/80 : ℝ)^2
  have hB : ∀ j π, ((F j π).2.card : ℝ) ≤ C := fun _ _ =>
    largeSet_bound _ _ (by unfold radius; positivity) (by norm_num) _
  have hK : ∀ j π, (F j π).1 ≤ k+1 := fun j π => by
    simpa [F, Policy.exposure, hw] using P.prefix_length_le π anchor w j.val
  have hF : ∀ j π ρ, (∀ z : Fin (k+1), z.val < (F j π).1 → π z = ρ z) → F j π = F j ρ := by
    intro j π ρ h
    unfold F Policy.exposure
    rw [P.agreed π ρ anchor w j.val h]
  let event := fun l => ∃ j : Fin (T+1), ∃ π : Fin (k+1) ↪ Fin d, List.ofFn π = l ∧
    0 < hits (F j π).2 (l.drop (F j π).1)
  have hc := prefix_family_bad_count_bound F hB (by dsimp [C]; positivity) hK hF
    (Finset.univ : Finset (Fin d)) D hD.le (by simpa using hd)
  have hs : 32 * ((s.filter event).card : ℝ) ≤ s.card := by
    have hh := scaled_bad_fraction hD (by positivity) hc (by simpa [C, mul_assoc] using hsize)
    convert hh using 1
    apply congrArg (fun t : Finset (List (Fin d)) => (32 : ℝ) * t.card)
    ext w
    simp only [s, Finset.mem_filter, event]
  have he (v : CoordinateWords d k) : P.bad anchor w T (coordinateEmbedding v) ↔ event v.val := by
    constructor
    · rintro ⟨j, h⟩
      exact ⟨j, coordinateEmbedding v, coordinateEmbedding_labels v, by simpa [← coordinateEmbedding_labels v] using h⟩
    · rintro ⟨j, π, hπ, h⟩
      have hEq : π = coordinateEmbedding v := by
        apply Function.Embedding.ext
        intro z
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels v).symm)) z
      subst π
      exact ⟨j, by simpa only [F, coordinateEmbedding_labels] using h⟩
  calc
    _ = 32 * ∑ v : CoordinateWords d k, if event v.val then (1 : ℝ) else 0 := by
      congr 1
      exact Finset.sum_congr rfl (fun v _ => if_congr (he v) rfl rfl)
    _ = 32 * ((s.filter event).card : ℝ) := by rw [subtype_indicator_sum]
    _ ≤ _ := by simpa [s, CoordinateWords, Fintype.card_coe] using hs

lemma output_penalty (hn : 0 < n) (π : Fin (k+1) ↪ Fin d) (anchor : Fin n) (w : List (Fin n))
    (hw : w.length = k) (T : ℕ) (ho : ¬ complete P π anchor T w) (hc : ¬ P.bad anchor w T π) :
    (k + 1 : ℕ) / (n : ℝ) ≤
      ComponentHessianGap.mean π (owner anchor w) (P.output (P.actual π (anchor :: w) T)) -
      ComponentHessianGap.mean π (owner anchor w) (ComponentHessianGap.anchorPoint π) := by
  rw [P.coupled hn π anchor w T hc T le_rfl]
  apply ComponentHessianGap.mean_hidden_gap π _ hn
  intro hx
  let g := P.simulate π anchor w T
  have eq := congrArg List.length (P.preserved π anchor w T)
  simp only [List.length_append, List.length_cons, hw] at eq
  have hp : g.1.2.length ≤ k := by
    have hr : 0 < g.2.length := List.length_pos_iff.mpr ho
    change g.1.2.length + g.2.length = k+1 at eq
    omega
  let j := Fin.last T
  have hj : j.val = T := rfl
  have he : P.observation T j g = P.output g.1.1 := ite_eq_right (by omega)
  have hB : 0 ≤ radius n (k+1 : ℕ) := by unfold radius; positivity
  have h := P.small_of_good anchor w T π hc j (by rw [hj]; change ‖P.observation T j g‖ ≤ _; rw [he]; linarith)
    (Fin.last k) hp
  change |P.observation T j g _| ≤ _ at h
  rw [he] at h
  linarith

end LongTails.Proofs.ComponentHessianCounting
