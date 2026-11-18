import Mathlib.Tactic

namespace LongTails.Proofs.StrongGrowthThinning

variable {S V : Type*} [Zero V]

def heads (c : ℕ → Bool) (n : ℕ) : ℕ := ((Finset.range n).filter (fun j => c j = true)).card

lemma heads_succ (c : ℕ → Bool) (n : ℕ) :
    heads c (n + 1) = heads c n + if c n = true then 1 else 0 := by
  unfold heads
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma heads_mono (c : ℕ → Bool) {m n : ℕ} (h : m ≤ n) : heads c m ≤ heads c n := by
  unfold heads
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

def skip (update : S → V → S) (c : ℕ → Bool) (b : ℕ) : ℕ → S × ℕ → S × ℕ
  | 0, z => z
  | n + 1, z => if z.2 < b ∧ c z.2 = false then skip update c b n (update z.1 0, z.2 + 1) else z

def realStep (update : S → V → S) (c : ℕ → Bool) (reply : S → V) (z : S × ℕ) : S × ℕ :=
  (update z.1 (if c z.2 = true then reply z.1 else 0), z.2 + 1)

lemma realStep_iterate_snd (update : S → V → S) (c : ℕ → Bool) (reply : S → V) (s : S) (j : ℕ) :
    ((realStep update c reply)^[j] (s, 0)).2 = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      simp [realStep, ih]

lemma skip_spec (update : S → V → S) (c : ℕ → Bool) (reply : S → V) (s0 : S) (b : ℕ) :
    ∀ n j, j ≤ b → b ≤ n + j →
      ∃ j', j ≤ j' ∧ j' ≤ b ∧ heads c j' = heads c j ∧ (j' = b ∨ c j' = true) ∧
        skip update c b n ((realStep update c reply)^[j] (s0, 0)) =
          (realStep update c reply)^[j'] (s0, 0) := by
  intro n
  induction n with
  | zero =>
      intro j hj hb
      have hjb : j = b := by omega
      subst hjb
      exact ⟨j, le_rfl, le_rfl, rfl, Or.inl rfl, rfl⟩
  | succ n ih =>
      intro j hj hb
      have hsnd := realStep_iterate_snd update c reply s0 j
      by_cases hcase : j < b ∧ c j = false
      · obtain ⟨j', h1, h2, h3, h4, h5⟩ := ih (j + 1) (by omega) (by omega)
        refine ⟨j', by omega, h2, ?_, h4, ?_⟩
        · rw [h3, heads_succ]
          simp [hcase.2]
        · have hstep : (update ((realStep update c reply)^[j] (s0, 0)).1 0,
              ((realStep update c reply)^[j] (s0, 0)).2 + 1) =
              (realStep update c reply)^[j + 1] (s0, 0) := by
            rw [Function.iterate_succ_apply']
            simp only [realStep, hsnd, hcase.2]
            rfl
          rw [← h5, ← hstep]
          simp only [skip, hsnd, hcase, and_self, ↓reduceIte]
      · refine ⟨j, le_rfl, hj, rfl, ?_, ?_⟩
        · by_cases hjb : j = b
          · exact Or.inl hjb
          · right
            have : j < b := by omega
            simpa [this] using hcase
        · simp only [skip, hsnd, hcase, ↓reduceIte]

section Pair

variable {X W : Type*}

def pairQuery (qx qy : S → X) (z : S × ℕ × Option W) : X :=
  match z.2.2 with
  | none => qx z.1
  | some _ => qy z.1

def pairUpdate (update : S → V → S) (c : ℕ → Bool) (b : ℕ) (T : W → W → V)
    (z : S × ℕ × Option W) (v : W) : S × ℕ × Option W :=
  match z.2.2 with
  | none => (z.1, z.2.1, some v)
  | some v1 =>
      if z.2.1 < b then
        ((skip update c b b (update z.1 (T v1 v), z.2.1 + 1)).1,
          (skip update c b b (update z.1 (T v1 v), z.2.1 + 1)).2, none)
      else (z.1, z.2.1, none)

def pairInit (update : S → V → S) (c : ℕ → Bool) (b : ℕ) (s0 : S) : S × ℕ × Option W :=
  ((skip update c b b (s0, 0)).1, (skip update c b b (s0, 0)).2, none)

lemma pair_invariant (update : S → V → S) (c : ℕ → Bool) (b : ℕ) (s0 : S)
    (qx qy : S → X) (F : X → W) (T : W → W → V) (m : ℕ) :
    ∃ j, j ≤ b ∧ (j = b ∨ (c j = true ∧ heads c j = m)) ∧
      (fun z => pairUpdate update c b T z (F (pairQuery qx qy z)))^[2 * m]
          (pairInit update c b s0) =
        (((realStep update c (fun s => T (F (qx s)) (F (qy s))))^[j] (s0, 0)).1, j, none) := by
  set reply : S → V := fun s => T (F (qx s)) (F (qy s)) with hreply
  induction m with
  | zero =>
      obtain ⟨j', _, h2, h3, h4, h5⟩ :=
        skip_spec update c reply s0 b b 0 (Nat.zero_le b) (by omega)
      refine ⟨j', h2, ?_, ?_⟩
      · rcases h4 with h4 | h4
        · exact Or.inl h4
        · exact Or.inr ⟨h4, by simpa [heads] using h3⟩
      · have hs : skip update c b b (s0, 0) = (realStep update c reply)^[j'] (s0, 0) := by
          simpa using h5
        have hsnd := realStep_iterate_snd update c reply s0 j'
        simp only [Nat.mul_zero, Function.iterate_zero, id_eq, pairInit, hs, hsnd]
  | succ m ih =>
      obtain ⟨j, hjb, hcase, hz⟩ := ih
      rw [show 2 * (m + 1) = 2 + 2 * m by ring, Function.iterate_add_apply, hz]
      have hsnd := realStep_iterate_snd update c reply s0 j
      by_cases hj : j = b
      · refine ⟨j, hjb, Or.inl hj, ?_⟩
        subst hj
        simp [pairUpdate, pairQuery]
      · have hlt : j < b := by omega
        rcases hcase with hcase | ⟨hc, hh⟩
        · exact absurd hcase hj
        obtain ⟨j', h1, h2, h3, h4, h5⟩ :=
          skip_spec update c reply s0 b b (j + 1) (by omega) (by omega)
        have hstep : (update ((realStep update c reply)^[j] (s0, 0)).1
              (reply ((realStep update c reply)^[j] (s0, 0)).1),
              ((realStep update c reply)^[j] (s0, 0)).2 + 1) =
              (realStep update c reply)^[j + 1] (s0, 0) := by
          rw [Function.iterate_succ_apply']
          simp only [realStep, hsnd, hc, ↓reduceIte]
        rw [hsnd] at hstep
        have hsk : skip update c b b (update ((realStep update c reply)^[j] (s0, 0)).1
            (reply ((realStep update c reply)^[j] (s0, 0)).1), j + 1) =
            (realStep update c reply)^[j'] (s0, 0) := by
          rw [hstep]; exact h5
        have hsnd' := realStep_iterate_snd update c reply s0 j'
        refine ⟨j', h2, ?_, ?_⟩
        · rcases h4 with h4 | h4
          · exact Or.inl h4
          · refine Or.inr ⟨h4, ?_⟩
            rw [h3, heads_succ, hh]
            simp [hc]
        · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
            pairUpdate, pairQuery, hlt, ↓reduceIte]
          rw [show T (F (qx ((realStep update c reply)^[j] (s0, 0)).1))
              (F (qy ((realStep update c reply)^[j] (s0, 0)).1)) =
              reply ((realStep update c reply)^[j] (s0, 0)).1 from rfl, hsk, hsnd']

lemma pair_eq_real (update : S → V → S) (c : ℕ → Bool) (b k : ℕ) (s0 : S)
    (qx qy : S → X) (F : X → W) (T : W → W → V) (hk : heads c b ≤ k) :
    ((fun z => pairUpdate update c b T z (F (pairQuery qx qy z)))^[2 * k]
        (pairInit update c b s0)).1 =
      ((realStep update c (fun s => T (F (qx s)) (F (qy s))))^[b] (s0, 0)).1 := by
  obtain ⟨j, hjb, hcase, hz⟩ := pair_invariant update c b s0 qx qy F T k
  rw [hz]
  by_cases hj : j = b
  · rw [hj]
  · exfalso
    have hjlt : j < b := by omega
    rcases hcase with hcase | ⟨hc, hh⟩
    · exact hj hcase
    have h1 := heads_succ c j
    have h2 := heads_mono c (show j + 1 ≤ b by omega)
    simp [hc] at h1
    omega

end Pair

end LongTails.Proofs.StrongGrowthThinning
