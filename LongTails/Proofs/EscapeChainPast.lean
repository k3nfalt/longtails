import LongTails.Proofs.EscapeChainMeasurable

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainPast

open scoped RealInnerProductSpace BigOperators
open EscapeChainFunction EscapeChainOracle EscapeChainSimulator EscapeChainFamily EscapeChainSmooth
open EscapeChainCounting EscapeChainRun EscapeChainInvariance

variable {d : ℕ} (c : Ctx d) (alg : Algorithm (Sp d) (Sp d) (Sp d))

def Agree (θ θ' : Hid c.n c.b) (j : ℕ) : Prop := ∀ m < j, U c θ' m = U c θ m ∧ V c θ' m = V c θ m

lemma ans_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) : ans c θ' j = ans c θ j := by
  funext x w
  unfold ans
  rw [answerS_congr c.K c.A (fun m hm => (h m hm).1) (fun m hm => (h m hm).2)]

lemma runJ_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) :
    runJ c alg θ' j = runJ c alg θ j := by
  funext z t; unfold runJ; rw [ans_agree c h]

lemma yq_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) :
    yq c alg θ' j = yq c alg θ j := by
  funext z t; unfold yq; rw [runJ_agree c alg h]

lemma yo_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) :
    yo c alg θ' j = yo c alg θ j := by
  funext z; unfold yo; rw [runJ_agree c alg h]

lemma rev_agree {θ θ' : Hid c.n c.b} {j l : ℕ} (h : Agree c θ θ' j) (hl : l < j) (z) (t : ℕ) :
    rev c alg θ' j l z t ↔ rev c alg θ j l z t := by
  unfold rev
  rw [yq_agree c alg h, reveals_congr c.K c.A (fun m hm => (h m (by omega)).1)
    (fun m hm => (h m (by omega)).2)]

lemma win_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) (z) (t : ℕ) :
    Win c alg θ' j z t ↔ Win c alg θ j z t := by
  unfold Win
  constructor
  · rintro (h0 | ⟨h0, s, hs, hst, hr, hmin⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨h0, s, hs, hst, (rev_agree c alg h (by omega) z s).1 hr, fun s' hs' => ?_⟩
      rw [← rev_agree c alg h (by omega) z s']; exact hmin s' hs'
  · rintro (h0 | ⟨h0, s, hs, hst, hr, hmin⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨h0, s, hs, hst, (rev_agree c alg h (by omega) z s).2 hr, fun s' hs' => ?_⟩
      rw [rev_agree c alg h (by omega) z s']; exact hmin s' hs'

lemma agree_swap (θ : Hid c.n c.b) {j : ℕ} {i k : Fin c.n} (hik : i ≤ k) (hi : 2 * j ≤ i) :
    Agree c θ (θ.1 * Equiv.swap i k, θ.2) j := by
  intro m hm
  exact ⟨uOf_swap c.hnb θ hik (by omega), vOf_swap c.hnb θ hik (by omega)⟩

lemma agree_sign (θ : Hid c.n c.b) {j : ℕ} {k : Fin c.n} (hk : 2 * j ≤ k) (σs : Fin c.b → Bool) :
    Agree c θ (θ.1, Function.update θ.2 (θ.1 k) σs) j := by
  intro m hm
  exact ⟨uOf_sign c.hnb θ (by omega) σs, vOf_sign c.hnb θ (by omega) σs⟩

lemma projL_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) :
    projL (U c θ') (V c θ') j = projL (U c θ) (V c θ) j :=
  projL_congr (fun m hm => (h m hm).1) (fun m hm => (h m hm).2)

lemma resid_agree {θ θ' : Hid c.n c.b} {j : ℕ} (h : Agree c θ θ' j) :
    resid (U c θ') (V c θ') j = resid (U c θ) (V c θ) j :=
  resid_congr (fun m hm => (h m hm).1) (fun m hm => (h m hm).2)

end LongTails.Proofs.EscapeChainPast
