import LongTails.Template

namespace OracleTemplate

noncomputable def batched {Q V W U : Type} {n : ℕ} (hn : 0 < n)
    (A : Algorithm Q V U) (queries : A.State → Fin n → Q)
    (decode : A.State → (Fin n → W) → V) (zero : W) : Algorithm Q W U where
  Seed := A.Seed
  law := A.law
  State := ℕ × A.State × (Fin n → W)
  initial seed := (0, A.initial seed, fun _ => zero)
  query state := (0, queries state.2.1 ⟨state.1 % n, Nat.mod_lt _ hn⟩)
  update state reply :=
    let replies := Function.update state.2.2 ⟨state.1 % n, Nat.mod_lt _ hn⟩ reply
    if state.1 + 1 < n then (state.1 + 1, state.2.1, replies)
    else (0, A.update state.2.1 (decode state.2.1 replies), fun _ => zero)
  output state := A.output state.2.1

end OracleTemplate
