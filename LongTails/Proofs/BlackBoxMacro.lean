import LongTails.Proofs.BlackBoxPhase
import LongTails.Proofs.BlackBoxProbe

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

noncomputable def cost (j : ℕ) : ℕ := 2 * len j + 1

section Macro

variable (f : Vec d → ℝ) (x0 : Vec d)

noncomputable def ms : ℕ → St d
  | 0 => startSt f x0
  | n + 1 => endPhase (ms n) (Hrep f (ms n) (2 * (ms n).N + 1))

noncomputable def bt : ℕ → ℕ
  | 0 => 0
  | n + 1 => bt n + cost (ms f x0 n).lvl

lemma endPhase_shape (st : St d) (H : ℕ → ℝ × Vec d) :
    (endPhase st H).probing = st.probing ∧ (endPhase st H).s = 0 ∧ (endPhase st H).J = st.J := by
  unfold endPhase
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

lemma ms_shape (n : ℕ) :
    (ms f x0 n).probing = false ∧ (ms f x0 n).s = 0 ∧ (ms f x0 n).J = sec f x0 := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := endPhase_shape (ms f x0 n) (Hrep f (ms f x0 n) (2 * (ms f x0 n).N + 1))
    exact ⟨h1.trans ih.1, h2, h3.trans ih.2.2⟩

lemma iterate_bt (n : ℕ) : (stepOf f x0)^[bt f x0 n] (startSt f x0) = ms f x0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bt, cost]
    rw [add_comm, Function.iterate_add_apply, ih]
    obtain ⟨h1, h2, _⟩ := ms_shape f x0 n
    have := phase_end f x0 (ms f x0 n) h1 h2
    simp only [St.N] at this
    rw [this]
    rfl

lemma base_within (n r : ℕ) (hr : r ≤ 2 * (ms f x0 n).N) :
    ((stepOf f x0)^[bt f x0 n + r] (startSt f x0)).base = (ms f x0 n).base := by
  rw [add_comm, Function.iterate_add_apply, iterate_bt]
  obtain ⟨h1, h2, _⟩ := ms_shape f x0 n
  rw [phase_iterate f x0 (ms f x0 n) h1 h2 r hr]

lemma bt_ge (n : ℕ) : n ≤ bt f x0 n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [bt, cost]; omega

lemma base_at (t : ℕ) : ∃ n, bt f x0 n ≤ t ∧ t < bt f x0 (n + 1) ∧
    ((stepOf f x0)^[t] (startSt f x0)).base = (ms f x0 n).base := by
  classical
  have hex : ∃ n, t < bt f x0 (n + 1) := ⟨t, by have := bt_ge f x0 (t + 1); omega⟩
  let n := Nat.find hex
  have hn : t < bt f x0 (n + 1) := Nat.find_spec hex
  have hle : bt f x0 n ≤ t := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have := Nat.find_min hex (show n - 1 < n by omega)
      rw [show n - 1 + 1 = n by omega] at this
      omega
  refine ⟨n, hle, hn, ?_⟩
  have hr : t - bt f x0 n ≤ 2 * (ms f x0 n).N := by
    simp only [bt, cost, St.N] at hn ⊢
    omega
  have := base_within f x0 n (t - bt f x0 n) hr
  rwa [show bt f x0 n + (t - bt f x0 n) = t by omega] at this

end Macro

end OracleTemplate.BlackBoxDiagonal
