import LongTails.Setups.SphericalRandomUtility
import LongTails.TemplateLowerBound
import LongTails.Proofs.SphericalPreferenceLower

namespace LongTails.Theorems.SphericalPreferenceLowerBound

open OracleTemplate LongTails.Setups.SphericalRandomUtility
open LongTails.Proofs.SphericalPreferenceHypercube LongTails.Proofs.SphericalPreferenceLower

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌊(p.d : ℝ) * (p.B * p.R / p.ε) ^ 2 / 524288⌋₊

theorem result : NonConvergence LongTails.Setups.SphericalRandomUtility.spec budget := by
  rintro p ⟨hd,hR,hB,he,hacc⟩ A _ b hb
  have : NeZero p.d := ⟨by omega⟩
  have hk : (b 0 : ℝ) ≤ (p.d : ℝ)*(p.B*p.R/p.ε)^2/524288 :=
    (Nat.cast_le.mpr (hb 0)).trans (Nat.floor_le (by positivity))
  obtain ⟨v,hv⟩ := hard_vertex p hR hB he hacc A (b 0) hk
  refine ⟨linear p v,oracle p v,admissible p v hR hB he hacc,?_⟩
  have heq : b = (fun _ => b 0) := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  exact hv

end LongTails.Theorems.SphericalPreferenceLowerBound
