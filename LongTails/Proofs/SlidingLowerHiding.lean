import LongTails.Proofs.SlidingLowerOracle
import LongTails.Proofs.SlidingLowerExposure
import LongTails.Proofs.SlidingLowerRun
import LongTails.Proofs.SmoothConvexFiniteHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerHiding

open OracleTemplate SlidingLowerChain SlidingLowerMask SlidingLowerInstance SlidingLowerOracle
open SlidingLowerSim SlidingLowerRun SoftRadialProjection
open SmoothConvexFiniteHiding FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure
open FiniteSumNondualLowerAveraging
open Classical

variable {d T : ℕ} {S : Type*}

structure Corner (T : ℕ) where
  lev : ℕ → ℕ
  rv : Fin 2 → Bool → ℕ
  mono : Monotone lev
  le : ∀ e, lev e ≤ 2 * T + 1
  fpos : ∀ e b, 0 < lev (e + rv 0 b)
  fodd : ∀ e b, lev (e + rv 0 b) = lev e → lev e < 2 * T + 1 → lev e % 2 = 1
  hcoin : ∀ e b, lev (e + rv 1 b) = lev e → lev e < 2 * T + 1 → lev e % 2 = 1 → b = false

structure Scale where
  p : ℝ
  a : ℝ
  s : ℝ
  R : ℝ

noncomputable def partialReply (C : Corner T) (Q : Scale) (x0 : Point d)
    (π : Fin (2 * T + 1) ↪ Fin d) (e : ℕ) (b : Bool) (q : Fin 2 × Point d) : Point d :=
  if q.1 = 0 then (Q.a / Q.s) • fpart Q.R π (C.lev (e + C.rv q.1 b)) (rescale Q.s x0 q.2)
  else (Q.a / Q.s) • hpart Q.p Q.R π (C.lev (e + C.rv q.1 b)) b (rescale Q.s x0 q.2)

noncomputable def trueReply (Q : Scale) (x0 : Point d) (π : Fin (2 * T + 1) ↪ Fin d) (b : Bool)
    (q : Fin 2 × Point d) : Point d :=
  if q.1 = 0 then (Q.a / Q.s) • fgrad Q.R π (rescale Q.s x0 q.2)
  else hO Q.p Q.a Q.s Q.R π x0 q.2 b

def good (Q : Scale) (x0 : Point d) (π : Fin (2 * T + 1) ↪ Fin d) (V : ℕ) (x : Point d) : Prop :=
  Good π V (project Q.R (rescale Q.s x0 x))

lemma fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

lemma partial_prefix (C : Corner T) (Q : Scale) (x0 : Point d) :
    ∀ π ρ e b q, (∀ j : Fin (2 * T + 1), j.val < C.lev (e + C.rv q.1 b) → π j = ρ j) →
      partialReply C Q x0 π e b q = partialReply C Q x0 ρ e b q := by
  intro π ρ e b q h
  unfold partialReply fpart hpart
  split_ifs
  · rw [gateV_congr π ρ _ _ h]
  · rw [coupV_congr Q.p π ρ _ b _ h]

lemma partial_eq (C : Corner T) (Q : Scale) (x0 : Point d) :
    ∀ π e b q, good Q x0 π (C.lev e) q.2 →
      partialReply C Q x0 π e b q = trueReply Q x0 π b q := by
  intro π e b q hg
  unfold partialReply trueReply good at *
  have hVV := C.mono (Nat.le_add_right e (C.rv q.1 b))
  rcases fin_two_cases q.1 with h0 | h1
  · rw [ite_eq_left h0, ite_eq_left h0]
    unfold fpart fgrad
    rw [gateV_eq π (C.lev e) _ _ hVV (by rw [h0]; exact C.fpos e b) hg
      (by rw [h0]; exact C.fodd e b), gateV_full]
  · have hn : q.1 ≠ 0 := by rw [h1]; decide
    rw [ite_eq_right hn, ite_eq_right hn]
    unfold hO hpart
    rw [coupV_eq Q.p π (C.lev e) _ b _ (C.le e) hVV hg (by rw [h1]; exact C.hcoin e b)]

noncomputable def toRun (A : Algorithm (Point d) (Point d) (Point d) 2)
    (seed : A.Seed) : Run A.State d :=
  ⟨A.query, A.update, A.output, A.initial seed⟩

noncomputable def observe (C : Corner T) (Q : Scale) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (j : ℕ × Fin 2) (π : Fin (2 * T + 1) ↪ Fin d) :
    Point d :=
  let st := (simSeq H C.rv (partialReply C Q x0) π β budget j.1).state
  project Q.R (rescale Q.s x0 (if j.2 = 0 then (H.query st).2 else H.output st))

def isBad (C : Corner T) (Q : Scale) (x0 : Point d) (H : Run S d) (β : ℕ → Bool)
    (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (2 * T + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1) × Fin 2, 0 < hits (largeSet Q.R (1 / 8) (observe C Q x0 H β budget
    (j.1.val, j.2) π)) ((List.ofFn π).drop
      (C.lev (simSeq H C.rv (partialReply C Q x0) π β budget j.1.val).exposure))

lemma observe_prefix (C : Corner T) (Q : Scale) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (j : ℕ × Fin 2) (π ρ : Fin (2 * T + 1) ↪ Fin d)
    (h : ∀ z : Fin (2 * T + 1),
      z.val < C.lev (simSeq H C.rv (partialReply C Q x0) π β budget j.1).exposure → π z = ρ z) :
    observe C Q x0 H β budget j π = observe C Q x0 H β budget j ρ ∧
      (simSeq H C.rv (partialReply C Q x0) π β budget j.1).exposure =
        (simSeq H C.rv (partialReply C Q x0) ρ β budget j.1).exposure := by
  have he := simSeq_prefix H C.rv C.lev C.mono (partialReply C Q x0) (partial_prefix C Q x0)
    π ρ β budget j.1 h
  unfold observe
  rw [he]
  exact ⟨rfl, rfl⟩

lemma bad_count (C : Corner T) (Q : Scale) (hR : 0 < Q.R) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hDs : D + (2 * T + 1 : ℕ) ≤ d) :
    D * (((distinctWords (2 * T + 1) (Finset.univ : Finset (Fin d))).filter
      (fun w => ∃ π : Fin (2 * T + 1) ↪ Fin d, List.ofFn π = w ∧
        isBad C Q x0 H β budget N π)).card : ℝ) ≤
      (2 * ((N : ℝ) + 1)) * (2 * T + 1 : ℕ) * (Q.R ^ 2 / (1 / 8) ^ 2) *
        (distinctWords (2 * T + 1) (Finset.univ : Finset (Fin d))).card := by
  let F : Fin (N + 1) × Fin 2 → (Fin (2 * T + 1) ↪ Fin d) → ℕ × Finset (Fin d) :=
    fun j π => (C.lev (simSeq H C.rv (partialReply C Q x0) π β budget j.1.val).exposure,
      largeSet Q.R (1 / 8) (observe C Q x0 H β budget (j.1.val, j.2) π))
  have hb : ∀ j π, ((F j π).2.card : ℝ) ≤ Q.R ^ 2 / (1 / 8) ^ 2 :=
    fun j π => largeSet_bound Q.R (1 / 8) hR.le (by norm_num) _
  have hk : ∀ j π, (F j π).1 ≤ 2 * T + 1 := fun j π => C.le _
  have hf : ∀ j π ρ, (∀ z : Fin (2 * T + 1), z.val < (F j π).1 → π z = ρ z) → F j π = F j ρ := by
    intro j π ρ h
    obtain ⟨h1, h2⟩ := observe_prefix C Q x0 H β budget (j.1.val, j.2) π ρ h
    simp only [F]
    rw [h1, h2]
  have hd : D + (2 * T + 1 : ℕ) ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) := by simpa using hDs
  have bound := prefix_family_bad_count_bound F hb (by positivity) hk hf Finset.univ D hD hd
  have hJ : (Fintype.card (Fin (N + 1) × Fin 2) : ℝ) = 2 * ((N : ℝ) + 1) := by
    simp [Fintype.card_prod]; ring
  rw [hJ] at bound
  have hset : ∀ w : List (Fin d), (∃ π : Fin (2 * T + 1) ↪ Fin d, List.ofFn π = w ∧
      isBad C Q x0 H β budget N π) ↔
      ∃ j : Fin (N + 1) × Fin 2, ∃ π : Fin (2 * T + 1) ↪ Fin d, List.ofFn π = w ∧
        0 < hits (F j π).2 (w.drop (F j π).1) := by
    intro w
    constructor
    · rintro ⟨π, hπ, j, hj⟩
      exact ⟨j, π, hπ, by rw [← hπ]; exact hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      exact ⟨π, hπ, j, by rw [hπ]; exact hj⟩
  refine le_trans ?_ bound
  apply mul_le_mul_of_nonneg_left _ hD
  exact_mod_cast Finset.card_le_card (fun w hw => by
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, (hset w).mp hw.2⟩)

lemma good_of_not_bad (C : Corner T) (Q : Scale) (hR : 0 < Q.R) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (2 * T + 1) ↪ Fin d)
    (hgood : ¬ isBad C Q x0 H β budget N π) (t : ℕ) (ht : t ≤ N) (i : Fin 2) :
    Good π (C.lev (simSeq H C.rv (partialReply C Q x0) π β budget t).exposure)
      (observe C Q x0 H β budget (t, i) π) := by
  intro j hj
  apply not_largeSet_small Q.R (1 / 8) _ (norm_project_le hR _)
  intro hm
  apply hgood
  exact ⟨(⟨t, by omega⟩, i), hits_drop_positive π _ _ j hj hm⟩

lemma coupled (C : Corner T) (Q : Scale) (hR : 0 < Q.R) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (2 * T + 1) ↪ Fin d)
    (hgood : ¬ isBad C Q x0 H β budget N π) :
    (simSeq H C.rv (partialReply C Q x0) π β budget N).state =
      (trueSeq H (fun π b q => trueReply Q x0 π b q) π β budget N).1 := by
  have h := coupling H C.rv C.lev (partialReply C Q x0) (fun π b q => trueReply Q x0 π b q)
    (good Q x0) (partial_eq C Q x0) π β budget N (fun t ht => by
      have := good_of_not_bad C Q hR x0 H β budget N π hgood t ht.le 0
      simpa [observe, good] using this)
  rw [← h]

lemma output_small (C : Corner T) (Q : Scale) (hR : 0 < Q.R) (x0 : Point d) (H : Run S d)
    (β : ℕ → Bool) (budget : Fin 2 → ℕ) (N : ℕ) (π : Fin (2 * T + 1) ↪ Fin d)
    (hgood : ¬ isBad C Q x0 H β budget N π)
    (hlev : C.lev (simSeq H C.rv (partialReply C Q x0) π β budget N).exposure ≤ 2 * T) :
    |project Q.R (rescale Q.s x0
      (H.output (trueSeq H (fun π b q => trueReply Q x0 π b q) π β budget N).1))
        (π (xi (Fin.last T)))| ≤ 1 / 8 := by
  have h := good_of_not_bad C Q hR x0 H β budget N π hgood N le_rfl 1 (xi (Fin.last T))
    (by simp [xi]; omega)
  rw [← coupled C Q hR x0 H β budget N π hgood]
  simpa [observe] using h

end LongTails.Proofs.SlidingLowerHiding
