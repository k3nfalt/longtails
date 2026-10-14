import LongTails.Algorithms.ScalarNoisySearch
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.ScalarNoisySearch

open Classical

noncomputable def invalid (g : ℝ → ℝ) (ε : ℝ) : Node → Prop
  | .interval lo hi _ => ¬ (g lo < 0 ∧ 0 < g hi)
  | .candidate x _ _ => 17 * ε / 32 < |g x|

noncomputable def potential (g : ℝ → ℝ) (ε : ℝ) (path : List Node) : ℤ := by
  classical
  exact (path.map fun n => if invalid g ε n then (-1 : ℤ) else 1).sum - 1

lemma potential_nil (g : ℝ → ℝ) (ε : ℝ) : potential g ε [] = -1 := by
  simp [potential]

lemma potential_cons (g : ℝ → ℝ) (ε : ℝ) (n : Node) (path : List Node) :
    potential g ε (n :: path) = potential g ε path +
      (if invalid g ε n then (-1 : ℤ) else 1) := by
  classical
  simp only [potential, List.map_cons, List.sum_cons]
  omega

lemma potential_le_length (g : ℝ → ℝ) (ε : ℝ) (path : List Node) :
    potential g ε path ≤ (path.length : ℤ) - 1 := by
  induction path with
  | nil => simp [potential]
  | cons n path ih =>
    rw [potential_cons]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    split_ifs <;> omega

lemma sum_increment_lower (φ : ℕ → ℤ) (bad acceptable : ℕ → ℕ)
    (N : ℕ)
    (hstep : ∀ k < N, 1 - 2 * (bad k : ℤ) - 2 * (acceptable k : ℤ) ≤ φ (k + 1) - φ k) :
    (N : ℤ) - 2 * (∑ k ∈ Finset.range N, (bad k : ℤ)) -
      2 * (∑ k ∈ Finset.range N, (acceptable k : ℤ)) ≤ φ N - φ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun k hk => hstep k (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    linarith [hstep N (by omega)]

lemma occupation_lower (φ : ℕ → ℤ) (bad acceptable : ℕ → ℕ)
    (D : ℕ) (hzero : φ 0 = 0)
    (hstep : ∀ k < 16 * D, 1 - 2 * (bad k : ℤ) - 2 * (acceptable k : ℤ) ≤ φ (k + 1) - φ k)
    (hbad : (∑ k ∈ Finset.range (16 * D), (bad k : ℤ)) ≤ D)
    (hcap : φ (16 * D) ≤ 4 * D) :
    5 * (D : ℤ) ≤ ∑ k ∈ Finset.range (16 * D), (acceptable k : ℤ) := by
  have h := sum_increment_lower φ bad acceptable (16 * D) hstep
  rw [hzero] at h
  push_cast at h
  linarith

lemma entry_strong {ε estimate value : ℝ} (hε : 0 ≤ ε)
    (he : |estimate - value| ≤ ε / 32) (hsmall : |estimate| ≤ ε / 4) :
    |value| ≤ 15 * ε / 32 := by
  rw [abs_le] at he hsmall ⊢
  constructor <;> linarith

lemma strong_validates {ε estimate value : ℝ}
    (he : |estimate - value| ≤ ε / 32) (hsmall : |value| ≤ 15 * ε / 32) :
    |estimate| ≤ ε / 2 := by
  rw [abs_le] at he hsmall ⊢
  constructor <;> linarith

lemma bad_rejects {ε estimate value : ℝ}
    (he : |estimate - value| ≤ ε / 32) (hbad : 17 * ε / 32 < |value|) :
    ε / 2 < |estimate| := by
  by_contra hn
  have hs : |estimate| ≤ ε / 2 := le_of_not_gt hn
  have hv : |value| ≤ 17 * ε / 32 := by
    rw [abs_le] at he hs ⊢
    constructor <;> linarith
  exact (not_le_of_gt hbad) hv

lemma potential_push_lower (g : ℝ → ℝ) (ε : ℝ) (n : Node) (path : List Node) :
    potential g ε path - 1 ≤ potential g ε (n :: path) := by
  rw [potential_cons]
  split_ifs <;> omega

lemma potential_retreat_lower (g : ℝ → ℝ) (ε : ℝ) (path : List Node) :
    potential g ε path - 1 ≤ potential g ε (retreat path) := by
  cases path with
  | nil => simp [retreat]
  | cons n rest =>
    cases rest with
    | nil => simp [retreat]
    | cons m rest =>
      simp only [retreat, potential_cons]
      split_ifs <;> omega

lemma advance_lower (g : ℝ → ℝ) (ε : ℝ) (D ℓ : ℕ)
    (reply : Fin 3 → ℝ) (path : List Node) :
    potential g ε path - 1 ≤ potential g ε (advance ε D ℓ reply path) := by
  classical
  cases path with
  | nil => simp [advance]
  | cons n rest =>
    cases n with
    | interval lo hi d =>
      simp only [advance]
      split_ifs <;> first
        | exact potential_push_lower g ε _ _
        | exact potential_retreat_lower g ε _
    | candidate x d k =>
      simp only [advance]
      split_ifs <;> first
        | omega
        | exact potential_push_lower g ε _ _
        | exact potential_retreat_lower g ε _

lemma negative_sign {ε estimate value : ℝ}
    (he : |estimate - value| ≤ ε / 32)
    (hn : ¬ |estimate| ≤ ε / 4) (hs : estimate < 0) : value < 0 := by
  rw [abs_of_neg hs] at hn
  rw [abs_le] at he
  linarith

lemma positive_sign {ε estimate value : ℝ} (hε : 0 < ε)
    (he : |estimate - value| ≤ ε / 32)
    (hn : ¬ |estimate| ≤ ε / 4) (hs : 0 ≤ estimate) : 0 < value := by
  rw [abs_of_nonneg hs] at hn
  rw [abs_le] at he
  linarith

lemma sign_of_negative_value {ε estimate value : ℝ} (hε : 0 < ε)
    (he : |estimate - value| ≤ ε / 32)
    (hn : ¬ |estimate| ≤ ε / 4) (hv : value < 0) : estimate < 0 := by
  by_contra hs
  have h := positive_sign hε he hn (le_of_not_gt hs)
  linarith

lemma sign_of_positive_value {ε estimate value : ℝ} (hε : 0 < ε)
    (he : |estimate - value| ≤ ε / 32)
    (hn : ¬ |estimate| ≤ ε / 4) (hv : 0 < value) : 0 < estimate := by
  rcases lt_or_ge estimate 0 with hs | hs
  · have h := negative_sign he hn hs
    linarith
  · by_contra hn'
    have hz : estimate = 0 := le_antisymm (le_of_not_gt hn') hs
    simp only [hz, abs_zero] at hn
    linarith

lemma small_endpoint_detected {ε estimate value : ℝ} (hε : 0 ≤ ε)
    (he : |estimate - value| ≤ ε / 32) (hv : |value| ≤ ε / 8) :
    |estimate| ≤ ε / 4 := by
  rw [abs_le] at he hv ⊢
  constructor <;> linarith

def Reliable (g : ℝ → ℝ) (ε : ℝ) (n : Node) (reply : Fin 3 → ℝ) : Prop :=
  ∀ i, |reply i - g (queries n i)| ≤ ε / 32

noncomputable def acceptable (g : ℝ → ℝ) (ε : ℝ) : Node → Prop
  | .interval _ _ _ => False
  | .candidate x _ _ => |g x| ≤ 17 * ε / 32

lemma potential_push_valid {g : ℝ → ℝ} {ε : ℝ} {n : Node} (path : List Node)
    (h : ¬ invalid g ε n) :
    potential g ε (n :: path) = potential g ε path + 1 := by
  classical
  rw [potential_cons, ite_eq_right h]

lemma potential_retreat_invalid {g : ℝ → ℝ} {ε : ℝ} {n : Node} {rest : List Node}
    (hn : invalid g ε n) (hr : rest ≠ []) :
    potential g ε (retreat (n :: rest)) = potential g ε (n :: rest) + 1 := by
  classical
  cases rest with
  | nil => exact False.elim (hr rfl)
  | cons m rest =>
    simp only [retreat, potential_cons, ite_eq_left hn]
    omega

lemma entry_valid {g : ℝ → ℝ} {ε x : ℝ} {d : ℕ} (hε : 0 < ε)
    {v : ℝ} (he : |v - g x| ≤ ε / 32) (hv : |v| ≤ ε / 4) :
    ¬ invalid g ε (.candidate x d 0) := by
  have h := entry_strong hε.le he hv
  simp only [invalid, not_lt]
  linarith

lemma reliable_advance_improves {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (D ℓ : ℕ) (reply : Fin 3 → ℝ) (n : Node) (rest : List Node)
    (hr : Reliable g ε n reply) (hn : ¬ acceptable g ε n)
    (hroot : rest = [] → ¬ invalid g ε n)
    (hleaf : ∀ lo hi d, n = .interval lo hi d → D ≤ d →
      g lo < 0 → 0 < g hi → |g lo| ≤ ε / 8)
    (htail : ∀ x d k, n = .candidate x d k → ℓ ≤ k → acceptable g ε n) :
    potential g ε (n :: rest) + 1 ≤
      potential g ε (advance ε D ℓ reply (n :: rest)) := by
  classical
  cases n with
  | interval lo hi d =>
    have he0 : |reply 0 - g lo| ≤ ε / 32 := by simpa [Reliable, queries] using hr 0
    have he1 : |reply 1 - g hi| ≤ ε / 32 := by simpa [Reliable, queries] using hr 1
    have he2 : |reply 2 - g ((lo + hi) / 2)| ≤ ε / 32 := by
      simpa [Reliable, queries] using hr 2
    simp only [advance]
    split_ifs with h0 h1 h2 hb hm
    · rw [potential_push_valid _ (entry_valid hε he0 h0)]
    · rw [potential_push_valid _ (entry_valid hε he1 h1)]
    · rw [potential_push_valid _ (entry_valid hε he2 h2)]
    · have hv : ¬ invalid g ε (.interval ((lo + hi) / 2) hi (d + 1)) := by
        simpa only [invalid, not_not] using
          And.intro (negative_sign he2 h2 hm)
            (positive_sign hε he1 h1 hb.2.1.le)
      rw [potential_push_valid _ hv]
    · have hv : ¬ invalid g ε (.interval lo ((lo + hi) / 2) (d + 1)) := by
        simpa only [invalid, not_not] using
          And.intro (negative_sign he0 h0 hb.1)
            (positive_sign hε he2 h2 (le_of_not_gt hm))
      rw [potential_push_valid _ hv]
    · have hinvalid : invalid g ε (.interval lo hi d) := by
        intro hv
        apply hb
        refine ⟨sign_of_negative_value hε he0 h0 hv.1,
          sign_of_positive_value hε he1 h1 hv.2, ?_⟩
        by_contra hd
        exact h0 (small_endpoint_detected hε.le he0
          (hleaf lo hi d rfl (le_of_not_gt hd) hv.1 hv.2))
      have hrest : rest ≠ [] := fun h => hroot h hinvalid
      rw [potential_retreat_invalid hinvalid hrest]
  | candidate x d k =>
    have he0 : |reply 0 - g x| ≤ ε / 32 := by simpa [Reliable, queries] using hr 0
    have hb : 17 * ε / 32 < |g x| := lt_of_not_ge hn
    have hk : ¬ ℓ ≤ k := fun hk => hn (htail x d k rfl hk)
    have hrj : ¬ |reply 0| ≤ ε / 2 := not_le_of_gt (bad_rejects he0 hb)
    simp only [advance, ite_eq_right hk, ite_eq_right hrj]
    have hinvalid : invalid g ε (.candidate x d k) := hb
    have hrest : rest ≠ [] := fun h => hroot h hinvalid
    rw [potential_retreat_invalid hinvalid hrest]

def Levels (path : List Node) : Prop :=
  path.map Node.level = (List.range path.length).reverse

lemma levels_cons_iff (n : Node) (rest : List Node) :
    Levels (n :: rest) ↔ n.level = rest.length ∧ Levels rest := by
  simp [Levels, List.range_succ, List.reverse_append]

lemma levels_push {n child : Node} {rest : List Node}
    (h : Levels (n :: rest)) (hc : child.level = n.level + 1) :
    Levels (child :: n :: rest) := by
  obtain ⟨hn, _⟩ := (levels_cons_iff n rest).mp h
  apply (levels_cons_iff child (n :: rest)).mpr
  exact ⟨by simp only [List.length_cons]; omega, h⟩

lemma levels_retreat {path : List Node} (h : Levels path) : Levels (retreat path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases rest with
    | nil => exact h
    | cons m rest => exact ((levels_cons_iff n (m :: rest)).mp h).2

lemma advance_levels (ε : ℝ) (D ℓ : ℕ) (reply : Fin 3 → ℝ)
    (path : List Node) (h : Levels path) : Levels (advance ε D ℓ reply path) := by
  classical
  cases path with
  | nil => exact h
  | cons n rest =>
    cases n with
    | interval lo hi d =>
      simp only [advance]
      split_ifs <;> first
        | exact levels_push h (by simp [Node.level])
        | exact levels_retreat h
    | candidate x d k =>
      simp only [advance]
      split_ifs <;> first
        | exact h
        | exact levels_push h (by simp [Node.level, Nat.add_assoc])
        | exact levels_retreat h

def Bounded (D ℓ : ℕ) (path : List Node) : Prop :=
  ∀ n ∈ path, match n with
    | .interval _ _ d => d ≤ D
    | .candidate _ d k => d ≤ D ∧ k ≤ ℓ

lemma bounded_retreat {D ℓ : ℕ} {path : List Node} (h : Bounded D ℓ path) :
    Bounded D ℓ (retreat path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases rest with
    | nil => exact h
    | cons m rest =>
      intro a ha
      exact h a (List.mem_cons_of_mem n ha)

lemma bounded_cons_iff (D ℓ : ℕ) (n : Node) (rest : List Node) :
    Bounded D ℓ (n :: rest) ↔
      (match n with | .interval _ _ d => d ≤ D
                    | .candidate _ d k => d ≤ D ∧ k ≤ ℓ) ∧ Bounded D ℓ rest := by
  simp only [Bounded, List.mem_cons, forall_eq_or_imp]

lemma advance_bounded (ε : ℝ) (D ℓ : ℕ) (reply : Fin 3 → ℝ)
    (path : List Node) (h : Bounded D ℓ path) :
    Bounded D ℓ (advance ε D ℓ reply path) := by
  classical
  cases path with
  | nil => exact h
  | cons n rest =>
    have hn := h n (List.mem_cons_self)
    cases n with
    | interval lo hi d =>
      simp only [advance]
      split_ifs with h0 h1 h2 hb hm <;> first
        | exact bounded_retreat h
        | apply (bounded_cons_iff _ _ _ _).mpr; exact ⟨by simp_all, h⟩
    | candidate x d k =>
      simp only [advance]
      split_ifs with hk hv <;> first
        | exact h
        | exact bounded_retreat h
        | apply (bounded_cons_iff _ _ _ _).mpr; exact ⟨by simp_all, h⟩

lemma potential_bounded {g : ℝ → ℝ} {ε : ℝ} {D ℓ : ℕ} {n : Node} {rest : List Node}
    (hl : Levels (n :: rest)) (hb : Bounded D ℓ (n :: rest)) :
    potential g ε (n :: rest) ≤ (D : ℤ) + ℓ + 1 := by
  have hp := potential_le_length g ε (n :: rest)
  have he := ((levels_cons_iff n rest).mp hl).1
  have hn := hb n (List.mem_cons_self)
  cases n <;> simp only [Node.level] at he <;>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hp <;> omega

def BadDepth (g : ℝ → ℝ) (ε : ℝ) (B : ℕ) (path : List Node) : Prop :=
  ∀ x d k, Node.candidate x d k ∈ path → 17 * ε / 32 < |g x| → k + 1 ≤ B

lemma badDepth_mono {g : ℝ → ℝ} {ε : ℝ} {B C : ℕ} {path : List Node}
    (h : BadDepth g ε B path) (hBC : B ≤ C) : BadDepth g ε C path := by
  intro x d k hn hb
  exact (h x d k hn hb).trans hBC

lemma badDepth_retreat {g : ℝ → ℝ} {ε : ℝ} {B : ℕ} {path : List Node}
    (h : BadDepth g ε B path) : BadDepth g ε B (retreat path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases rest with
    | nil => exact h
    | cons m rest =>
      intro x d k hn hb
      exact h x d k (List.mem_cons_of_mem n hn) hb

lemma badDepth_push_interval {g : ℝ → ℝ} {ε lo hi : ℝ} {B d : ℕ}
    {path : List Node} (h : BadDepth g ε B path) :
    BadDepth g ε B (.interval lo hi d :: path) := by
  intro x b k hn hb
  simp only [List.mem_cons, reduceCtorEq, false_or] at hn
  exact h x b k hn hb

lemma badDepth_push_candidate {g : ℝ → ℝ} {ε x : ℝ} {B d k : ℕ}
    {path : List Node} (h : BadDepth g ε B path)
    (hk : 17 * ε / 32 < |g x| → k + 1 ≤ B) :
    BadDepth g ε B (.candidate x d k :: path) := by
  intro y b j hn hb
  rcases List.mem_cons.mp hn with he | hm
  · cases he
    exact hk hb
  · exact h y b j hm hb

lemma advance_badDepth {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (D ℓ : ℕ)
    (reply : Fin 3 → ℝ) (n : Node) (rest : List Node) (B : ℕ)
    (h : BadDepth g ε B (n :: rest)) :
    BadDepth g ε (B + if Reliable g ε n reply then 0 else 1)
      (advance ε D ℓ reply (n :: rest)) := by
  have hmono : BadDepth g ε (B + if Reliable g ε n reply then 0 else 1) (n :: rest) :=
    badDepth_mono h (Nat.le_add_right _ _)
  cases n with
  | interval lo hi d =>
    have entry (i : Fin 3) (hs : |reply i| ≤ ε / 4) :
        17 * ε / 32 < |g (queries (.interval lo hi d) i)| →
          1 ≤ B + if Reliable g ε (.interval lo hi d) reply then 0 else 1 := by
      intro hb
      split_ifs with hr
      · have he := entry_strong hε.le (hr i) hs
        linarith
      · omega
    generalize heB : (B + if Reliable g ε (.interval lo hi d) reply then 0 else 1) = C at hmono entry ⊢
    simp only [advance]
    split_ifs with h0 h1 h2 hb hm
    · apply badDepth_push_candidate hmono
      simpa [queries] using entry 0 h0
    · apply badDepth_push_candidate hmono
      simpa [queries] using entry 1 h1
    · apply badDepth_push_candidate hmono
      simpa [queries] using entry 2 h2
    · exact badDepth_push_interval hmono
    · exact badDepth_push_interval hmono
    · exact badDepth_retreat hmono
  | candidate x d k =>
    generalize heB : (B + if Reliable g ε (.candidate x d k) reply then 0 else 1) = C at hmono ⊢
    simp only [advance]
    split_ifs with hk hv
    · exact hmono
    · apply badDepth_push_candidate hmono
      intro hb
      have hold := h x d k List.mem_cons_self hb
      rw [← heB]
      split_ifs with hr
      · have he : |reply 0 - g x| ≤ ε / 32 := by simpa [queries] using hr 0
        exact False.elim ((not_le_of_gt (bad_rejects he hb)) hv)
      · omega
    · exact badDepth_retreat hmono

noncomputable def badStep (g : ℝ → ℝ) (ε : ℝ) (reply : Fin 3 → ℝ) : List Node → ℕ
  | [] => 0
  | n :: _ => if Reliable g ε n reply then 0 else 1

lemma trace_badDepth {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε) (D ℓ : ℕ)
    (replies : ℕ → List Node → Fin 3 → ℝ) (initial : List Node)
    (hinit : BadDepth g ε 0 initial) (N : ℕ) :
    BadDepth g ε (∑ k ∈ Finset.range N,
      badStep g ε (replies k (trace ε D ℓ replies initial k))
        (trace ε D ℓ replies initial k)) (trace ε D ℓ replies initial N) := by
  induction N with
  | zero => simpa [trace] using hinit
  | succ N ih =>
    rw [Finset.sum_range_succ, trace]
    cases he : trace ε D ℓ replies initial N with
    | nil => simp [advance, BadDepth]
    | cons n rest =>
      simp only [he] at ih ⊢
      exact advance_badDepth hε D ℓ _ n rest _ ih

def Rooted (root : Node) (path : List Node) : Prop := path.getLast? = some root

lemma rooted_push {root n : Node} {path : List Node} (h : Rooted root path) :
    Rooted root (n :: path) := by
  cases path with
  | nil => simp [Rooted] at h
  | cons a rest => simpa [Rooted] using h

lemma rooted_retreat {root : Node} {path : List Node} (h : Rooted root path) :
    Rooted root (retreat path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases rest with
    | nil => exact h
    | cons a rest => simpa [Rooted, retreat] using h

lemma advance_rooted (ε : ℝ) (D ℓ : ℕ) (reply : Fin 3 → ℝ)
    {root : Node} {path : List Node} (h : Rooted root path) :
    Rooted root (advance ε D ℓ reply path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases n <;> simp only [advance] <;> split_ifs <;> first
      | exact h
      | exact rooted_push h
      | exact rooted_retreat h

lemma trace_invariants (ε : ℝ) (D ℓ : ℕ)
    (replies : ℕ → List Node → Fin 3 → ℝ) (lo hi : ℝ) (N : ℕ) :
    Levels (trace ε D ℓ replies [.interval lo hi 0] N) ∧
    Bounded D ℓ (trace ε D ℓ replies [.interval lo hi 0] N) ∧
    Rooted (.interval lo hi 0) (trace ε D ℓ replies [.interval lo hi 0] N) := by
  induction N with
  | zero => simp [trace, Levels, Node.level, Bounded, Rooted]
  | succ N ih =>
    exact ⟨advance_levels ε D ℓ _ _ ih.1,
      advance_bounded ε D ℓ _ _ ih.2.1, advance_rooted ε D ℓ _ ih.2.2⟩

noncomputable def acceptableStep (g : ℝ → ℝ) (ε : ℝ) : List Node → ℕ
  | [] => 0
  | n :: _ => if acceptable g ε n then 1 else 0

lemma step_drift {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (D ℓ : ℕ) (reply : Fin 3 → ℝ) (n : Node) (rest : List Node)
    (hroot : rest = [] → ¬ invalid g ε n)
    (hleaf : ∀ lo hi d, n = .interval lo hi d → D ≤ d →
      g lo < 0 → 0 < g hi → |g lo| ≤ ε / 8)
    (htail : ∀ x d k, n = .candidate x d k → ℓ ≤ k → acceptable g ε n) :
    1 - 2 * (badStep g ε reply (n :: rest) : ℤ) -
      2 * (acceptableStep g ε (n :: rest) : ℤ) ≤
      potential g ε (advance ε D ℓ reply (n :: rest)) - potential g ε (n :: rest) := by
  have hlow := advance_lower g ε D ℓ reply (n :: rest)
  by_cases hr : Reliable g ε n reply
  · by_cases ha : acceptable g ε n
    · simp only [badStep, acceptableStep, hr, ha, ite_true, Nat.cast_zero, Nat.cast_one]
      omega
    · have h := reliable_advance_improves hε D ℓ reply n rest hr ha hroot hleaf htail
      simp only [badStep, acceptableStep, hr, ha, ite_true, ite_false, Nat.cast_zero]
      omega
  · simp only [badStep, hr, ite_false, acceptableStep]
    split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> omega

lemma trace_occupation {g : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (D : ℕ) (hD : 0 < D) (lo hi : ℝ) (hlo : g lo < 0) (hhi : 0 < g hi)
    (replies : ℕ → List Node → Fin 3 → ℝ)
    (hleaf : ∀ t < 16 * D, ∀ a b d,
      Node.interval a b d ∈ trace ε D (2 * D) replies [.interval lo hi 0] t →
      D ≤ d → g a < 0 → 0 < g b → |g a| ≤ ε / 8)
    (hbad : (∑ t ∈ Finset.range (16 * D),
      badStep g ε (replies t (trace ε D (2 * D) replies [.interval lo hi 0] t))
        (trace ε D (2 * D) replies [.interval lo hi 0] t)) ≤ D) :
    5 * D ≤ ∑ t ∈ Finset.range (16 * D),
      acceptableStep g ε (trace ε D (2 * D) replies [.interval lo hi 0] t) := by
  let path := trace ε D (2 * D) replies [.interval lo hi 0]
  let bad := fun t => badStep g ε (replies t (path t)) (path t)
  have hinv t := trace_invariants ε D (2 * D) replies lo hi t
  have hnonempty (t : ℕ) : path t ≠ [] := by
    intro he
    have h := (hinv t).2.2
    change Rooted (.interval lo hi 0) (path t) at h
    simp [he, Rooted] at h
  have hdepth (t : ℕ) : BadDepth g ε (∑ k ∈ Finset.range t, bad k) (path t) :=
    trace_badDepth hε D (2 * D) replies [.interval lo hi 0]
      (by simp [BadDepth]) t
  have hsum (t : ℕ) (ht : t ≤ 16 * D) : (∑ k ∈ Finset.range t, bad k) ≤ D := by
    apply le_trans _ hbad
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht) (by intros; omega)
  have hd (t : ℕ) (ht : t < 16 * D) :
      1 - 2 * (bad t : ℤ) - 2 * (acceptableStep g ε (path t) : ℤ) ≤
        potential g ε (path (t + 1)) - potential g ε (path t) := by
    cases he : path t with
    | nil => exact False.elim (hnonempty t he)
    | cons n rest =>
      change 1 - 2 * (badStep g ε (replies t (path t)) (path t) : ℤ) - _ ≤ _
      change _ ≤ potential g ε (advance ε D (2 * D) (replies t (path t)) (path t)) - _
      rw [he]
      apply step_drift hε
      · intro hr
        have hroot := (hinv t).2.2
        change Rooted (.interval lo hi 0) (path t) at hroot
        rw [he, hr] at hroot
        have hn : n = .interval lo hi 0 := by simpa [Rooted] using hroot
        simp [hn, invalid, hlo, hhi]
      · intro a b d hn hlevel ha hb
        apply hleaf t ht a b d _ hlevel ha hb
        rw [show trace ε D (2 * D) replies [.interval lo hi 0] t = path t from rfl, he, hn]
        exact List.mem_cons_self
      · intro x d k hn hk
        by_contra ha
        rw [hn] at ha
        have hb : 17 * ε / 32 < |g x| := lt_of_not_ge ha
        have hd := hdepth t x d k (by rw [he, hn]; exact List.mem_cons_self) hb
        have hs := hsum t ht.le
        omega
  have hz : potential g ε (path 0) = 0 := by
    simp [path, trace, potential, invalid, hlo, not_le_of_gt hhi]
  have hc : potential g ε (path (16 * D)) ≤ 4 * (D : ℤ) := by
    cases he : path (16 * D) with
    | nil => exact False.elim (hnonempty _ he)
    | cons n rest =>
      have h := hinv (16 * D)
      change Levels (path (16 * D)) ∧ Bounded D (2 * D) (path (16 * D)) ∧ _ at h
      rw [he] at h
      have hp := potential_bounded h.1 h.2.1 (g := g) (ε := ε)
      push_cast at hp
      omega
  have hb : (∑ k ∈ Finset.range (16 * D), (bad k : ℤ)) ≤ D := by
    exact_mod_cast hbad
  have h := occupation_lower (fun t => potential g ε (path t)) bad
    (fun t => acceptableStep g ε (path t)) D hz hd hb hc
  exact_mod_cast h

def Geometry (R : ℝ) (path : List Node) : Prop :=
  ∀ a b d, Node.interval a b d ∈ path →
    0 ≤ a ∧ a ≤ b ∧ b ≤ R ∧ (2 : ℝ) ^ d * (b - a) ≤ R

lemma geometry_retreat {R : ℝ} {path : List Node} (h : Geometry R path) :
    Geometry R (retreat path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases rest with
    | nil => exact h
    | cons a rest =>
      intro x y d hm
      exact h x y d (List.mem_cons_of_mem n hm)

lemma geometry_candidate {R x : ℝ} {d k : ℕ} {path : List Node}
    (h : Geometry R path) : Geometry R (.candidate x d k :: path) := by
  intro a b j hm
  simp only [List.mem_cons, reduceCtorEq, false_or] at hm
  exact h a b j hm

lemma geometry_interval {R a b : ℝ} {d : ℕ} {path : List Node}
    (h : Geometry R path) (hn : 0 ≤ a ∧ a ≤ b ∧ b ≤ R ∧ (2 : ℝ) ^ d * (b - a) ≤ R) :
    Geometry R (.interval a b d :: path) := by
  intro x y j hm
  rcases List.mem_cons.mp hm with he | ht
  · cases he
    exact hn
  · exact h x y j ht

lemma advance_geometry (ε : ℝ) (D ℓ : ℕ) (reply : Fin 3 → ℝ)
    {R : ℝ} {path : List Node} (h : Geometry R path) :
    Geometry R (advance ε D ℓ reply path) := by
  cases path with
  | nil => exact h
  | cons n rest =>
    cases n with
    | interval a b d =>
      obtain ⟨ha, hab, hb, hw⟩ := h a b d List.mem_cons_self
      simp only [advance]
      split_ifs <;> first
        | exact geometry_candidate h
        | exact geometry_retreat h
        | apply geometry_interval h
          refine ⟨by linarith, by linarith, by linarith, ?_⟩
          rw [pow_succ]
          nlinarith
    | candidate x d k =>
      simp only [advance]
      split_ifs <;> first
        | exact h
        | exact geometry_candidate h
        | exact geometry_retreat h

lemma trace_geometry (ε : ℝ) (D ℓ : ℕ)
    (replies : ℕ → List Node → Fin 3 → ℝ) {R hi : ℝ} (hh : 0 ≤ hi) (hR : hi ≤ R)
    (N : ℕ) : Geometry R (trace ε D ℓ replies [.interval 0 hi 0] N) := by
  induction N with
  | zero =>
    simp only [trace]
    apply geometry_interval (by simp [Geometry])
    simpa using And.intro (le_refl (0 : ℝ)) (And.intro hh (And.intro hR hR))
  | succ N ih => exact advance_geometry ε D ℓ _ ih

lemma leaf_accuracy {g : ℝ → ℝ} {ε H ν R a b : ℝ} {D d : ℕ}
    (hH : 0 ≤ H) (hν : 0 ≤ ν)
    (hholder : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν)
    (hab : a ≤ b) (hw : (2 : ℝ) ^ d * (b - a) ≤ R) (hd : D ≤ d)
    (hsmall : H * (R / (2 : ℝ) ^ D) ^ ν ≤ ε / 8)
    (ha : g a < 0) (hb : 0 < g b) : |g a| ≤ ε / 8 := by
  have hp : (2 : ℝ) ^ D ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hdist : |a - b| ≤ R / (2 : ℝ) ^ D := by
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ D)).mpr
    have hmul := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hab)
    nlinarith
  have h := (hholder a b).trans ((mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) hdist hν) hH).trans hsmall)
  rw [abs_of_neg ha]
  rw [abs_of_neg (show g a - g b < 0 by linarith)] at h
  linarith

lemma holder_trace_occupation {g : ℝ → ℝ} {ε H ν R hi : ℝ}
    (hε : 0 < ε) (hH : 0 ≤ H) (hν : 0 ≤ ν)
    (hholder : ∀ x y, |g x - g y| ≤ H * |x - y| ^ ν)
    (D : ℕ) (hD : 0 < D) (hhi : 0 ≤ hi) (hR : hi ≤ R)
    (hlo : g 0 < 0) (hgHi : 0 < g hi)
    (hsmall : H * (R / (2 : ℝ) ^ D) ^ ν ≤ ε / 8)
    (replies : ℕ → List Node → Fin 3 → ℝ)
    (hbad : (∑ t ∈ Finset.range (16 * D),
      badStep g ε (replies t (trace ε D (2 * D) replies [.interval 0 hi 0] t))
        (trace ε D (2 * D) replies [.interval 0 hi 0] t)) ≤ D) :
    5 * D ≤ ∑ t ∈ Finset.range (16 * D),
      acceptableStep g ε (trace ε D (2 * D) replies [.interval 0 hi 0] t) := by
  apply trace_occupation hε D hD 0 hi hlo hgHi replies _ hbad
  intro t ht a b d hm hd ha hb
  have hg := trace_geometry ε D (2 * D) replies hhi hR t a b d hm
  exact leaf_accuracy hH hν hholder hg.2.1 hg.2.2.2 hd hsmall ha hb

end OracleTemplate.ScalarNoisySearch
