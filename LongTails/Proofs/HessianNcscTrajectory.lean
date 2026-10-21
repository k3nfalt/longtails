import LongTails.Algorithms.HessianNcscIgt
import LongTails.Proofs.SgdExecution

namespace OracleTemplate.HessianNcsc

variable {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def yA (cfg : IgtConfig) (x0 : E) (y0 : F) (oy : E × F → Ω → F) (ξ : ℕ → Ω) : ℕ → F
  | 0 => y0
  | j + 1 => yA cfg x0 y0 oy ξ j + cfg.γ • oy (x0, yA cfg x0 y0 oy ξ j) (ξ j)

def accB (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (ξ : ℕ → Ω) : ℕ → E
  | 0 => 0
  | j + 1 => accB cfg x0 y0 ox oy ξ j + ox (x0, yA cfg x0 y0 oy ξ cfg.NA) (ξ (cfg.NA + j))

noncomputable def mInit (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (ξ : ℕ → Ω) : E :=
  mzero cfg (accB cfg x0 y0 ox oy ξ cfg.NB)

noncomputable def wOne (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (ξ : ℕ → Ω) : E :=
  x0 + nphi cfg.η cfg.lam (mInit cfg x0 y0 ox oy ξ)

noncomputable def xtOne (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (ξ : ℕ → Ω) : E :=
  lead cfg (wOne cfg x0 y0 ox oy ξ) (mInit cfg x0 y0 ox oy ξ)

noncomputable def yC (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (ξ : ℕ → Ω) : ℕ → F
  | 0 => yA cfg x0 y0 oy ξ cfg.NA
  | j + 1 => yC cfg x0 y0 ox oy ξ j +
      cfg.γ • oy (xtOne cfg x0 y0 ox oy ξ, yC cfg x0 y0 ox oy ξ j) (ξ (cfg.NA + cfg.NB + j))

def off (cfg : IgtConfig) : ℕ := cfg.NA + cfg.NB + cfg.NC

noncomputable def mainS (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (ξ : ℕ → Ω) : ℕ → E × E × F
  | 0 => (wOne cfg x0 y0 ox oy ξ, mInit cfg x0 y0 ox oy ξ, yC cfg x0 y0 ox oy ξ cfg.NC)
  | k + 1 =>
    ((mainS cfg x0 y0 ox oy ξ k).1 + nphi cfg.η cfg.lam ((1 - cfg.α) • (mainS cfg x0 y0 ox oy ξ k).2.1 +
        cfg.α • ox (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
          (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k))),
     (1 - cfg.α) • (mainS cfg x0 y0 ox oy ξ k).2.1 +
        cfg.α • ox (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
          (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k)),
     (mainS cfg x0 y0 ox oy ξ k).2.2 +
        cfg.γ • oy (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
          (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k)))

noncomputable def outRec (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (ξ : ℕ → Ω) (τ k : ℕ) : E :=
  if 1 ≤ τ ∧ τ ≤ k then (mainS cfg x0 y0 ox oy ξ (τ - 1)).1 else x0

noncomputable def igtStep (cfg : IgtConfig) (x0 : E) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (ξ : ℕ → Ω) (k : ℕ) (s : IgtState E F) : IgtState E F :=
  igtUpdate cfg x0 s (ox (igtQuery cfg x0 s) (ξ k), oy (igtQuery cfg x0 s) (ξ k))

lemma advance_succ {S : Type*} (step : ℕ → S → S) :
    ∀ (n c : ℕ) (s : S), StochasticGradient.advance step (n + 1) c s =
      step (c + n) (StochasticGradient.advance step n c s)
  | 0, c, s => by simp [StochasticGradient.advance]
  | n + 1, c, s => by
      rw [StochasticGradient.advance, advance_succ step n (c + 1) (step c s)]
      rw [StochasticGradient.advance]
      congr 1; omega

section
variable (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
  (ξ : ℕ → Ω) (τ : ℕ)

noncomputable def st (n : ℕ) : IgtState E F :=
  StochasticGradient.advance (igtStep cfg x0 ox oy ξ) n 0
    { c := 0, tau := τ, y := y0, w := x0, u := 0, acc := 0, out := x0 }

lemma st_succ (n : ℕ) : st cfg x0 y0 ox oy ξ τ (n + 1) = igtStep cfg x0 ox oy ξ n (st cfg x0 y0 ox oy ξ τ n) := by
  simp only [st]; rw [advance_succ]; simp

lemma st_phaseA : ∀ n, n ≤ cfg.NA → st cfg x0 y0 ox oy ξ τ n =
    { c := n, tau := τ, y := yA cfg x0 y0 oy ξ n, w := x0, u := 0, acc := 0, out := x0 }
  | 0, _ => rfl
  | n + 1, h => by
      rw [st_succ, st_phaseA n (by omega)]
      have h1 : n < cfg.NA := by omega
      simp [igtStep, igtUpdate, igtQuery, h1, yA, show n < cfg.NA + cfg.NB by omega]

lemma st_phaseB (hNB : 1 ≤ cfg.NB) : ∀ j, j < cfg.NB → st cfg x0 y0 ox oy ξ τ (cfg.NA + j) =
    { c := cfg.NA + j, tau := τ, y := yA cfg x0 y0 oy ξ cfg.NA, w := x0, u := 0,
      acc := accB cfg x0 y0 ox oy ξ j, out := x0 }
  | 0, _ => by simpa [accB] using st_phaseA cfg x0 y0 ox oy ξ τ cfg.NA le_rfl
  | j + 1, h => by
      rw [show cfg.NA + (j + 1) = (cfg.NA + j) + 1 by omega, st_succ, st_phaseB hNB j (by omega)]
      have h1 : ¬ (cfg.NA + j < cfg.NA) := by omega
      have h2 : cfg.NA + j + 1 < cfg.NA + cfg.NB := by omega
      simp [igtStep, igtUpdate, igtQuery, h1, h2, accB, show cfg.NA + j < cfg.NA + cfg.NB by omega]

lemma st_afterB (hNB : 1 ≤ cfg.NB) : st cfg x0 y0 ox oy ξ τ (cfg.NA + cfg.NB) =
    { c := cfg.NA + cfg.NB, tau := τ, y := yA cfg x0 y0 oy ξ cfg.NA,
      w := wOne cfg x0 y0 ox oy ξ, u := mInit cfg x0 y0 ox oy ξ,
      acc := accB cfg x0 y0 ox oy ξ cfg.NB, out := x0 } := by
  obtain ⟨j, hj⟩ : ∃ j, cfg.NB = j + 1 := ⟨cfg.NB - 1, by omega⟩
  rw [show cfg.NA + cfg.NB = (cfg.NA + j) + 1 by omega, st_succ, st_phaseB cfg x0 y0 ox oy ξ τ hNB j (by omega)]
  have h1 : ¬ (cfg.NA + j < cfg.NA) := by omega
  have h2 : ¬ (cfg.NA + j + 1 < cfg.NA + cfg.NB) := by omega
  have h3 : cfg.NA + j + 1 = cfg.NA + cfg.NB := by omega
  simp [igtStep, igtUpdate, igtQuery, h1, h3, accB, wOne, mInit, hj]


lemma st_phaseC (hNB : 1 ≤ cfg.NB) : ∀ j, j ≤ cfg.NC → st cfg x0 y0 ox oy ξ τ (cfg.NA + cfg.NB + j) =
    { c := cfg.NA + cfg.NB + j, tau := τ, y := yC cfg x0 y0 ox oy ξ j,
      w := wOne cfg x0 y0 ox oy ξ, u := mInit cfg x0 y0 ox oy ξ,
      acc := accB cfg x0 y0 ox oy ξ cfg.NB, out := x0 }
  | 0, _ => by simpa [yC] using st_afterB cfg x0 y0 ox oy ξ τ hNB
  | j + 1, h => by
      rw [show cfg.NA + cfg.NB + (j + 1) = (cfg.NA + cfg.NB + j) + 1 by omega, st_succ,
        st_phaseC hNB j (by omega)]
      have h1 : ¬ (cfg.NA + cfg.NB + j < cfg.NA) := by omega
      have h2 : ¬ (cfg.NA + cfg.NB + j + 1 < cfg.NA + cfg.NB) := by omega
      have h3 : ¬ (cfg.NA + cfg.NB + j + 1 = cfg.NA + cfg.NB) := by omega
      have h4 : cfg.NA + cfg.NB + j < cfg.NA + cfg.NB + cfg.NC := by omega
      have h5 : ¬ (cfg.NA + cfg.NB + j < cfg.NA + cfg.NB) := by omega
      simp [igtStep, igtUpdate, igtQuery, h1, h2, h3, h4, h5, yC, xtOne]

lemma outRec_succ (k : ℕ) : outRec cfg x0 y0 ox oy ξ τ (k + 1) =
    if k + 1 = τ then (mainS cfg x0 y0 ox oy ξ k).1 else outRec cfg x0 y0 ox oy ξ τ k := by
  unfold outRec
  by_cases hk : k + 1 = τ
  · subst hk; simp
  · simp only [hk, ite_false]
    by_cases h1 : 1 ≤ τ ∧ τ ≤ k
    · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

lemma st_main (hNB : 1 ≤ cfg.NB) : ∀ k, k ≤ cfg.T → st cfg x0 y0 ox oy ξ τ (off cfg + k) =
    { c := off cfg + k, tau := τ, y := (mainS cfg x0 y0 ox oy ξ k).2.2,
      w := (mainS cfg x0 y0 ox oy ξ k).1, u := (mainS cfg x0 y0 ox oy ξ k).2.1,
      acc := accB cfg x0 y0 ox oy ξ cfg.NB, out := outRec cfg x0 y0 ox oy ξ τ k }
  | 0, _ => by
      have := st_phaseC cfg x0 y0 ox oy ξ τ hNB cfg.NC le_rfl
      simp only [off, add_zero]
      rw [this]
      simp only [mainS, outRec]
      congr 1
      rw [ite_eq_right (by omega)]
  | k + 1, h => by
      rw [show off cfg + (k + 1) = (off cfg + k) + 1 by omega, st_succ, st_main hNB k (by omega),
        outRec_succ]
      have h1 : ¬ (off cfg + k < cfg.NA) := by simp only [off]; omega
      have h2 : ¬ (off cfg + k + 1 < cfg.NA + cfg.NB) := by simp only [off]; omega
      have h3 : ¬ (off cfg + k + 1 = cfg.NA + cfg.NB) := by simp only [off]; omega
      have h4 : ¬ (off cfg + k < cfg.NA + cfg.NB + cfg.NC) := by simp only [off]; omega
      have h5 : off cfg + k < cfg.NA + cfg.NB + cfg.NC + cfg.T := by simp only [off]; omega
      have h6 : ¬ (off cfg + k < cfg.NA + cfg.NB) := by simp only [off]; omega
      have h7 : off cfg + k - (cfg.NA + cfg.NB + cfg.NC) + 1 = k + 1 := by simp only [off]; omega
      simp only [igtStep, igtUpdate, igtQuery, h1, h2, h3, h4, h5, h6, h7, ite_false, ite_true]
      simp [mainS]

end

lemma igt_execute (cfg : IgtConfig) (x0 : E) (y0 : F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    [MeasurableSpace Ω] (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (hNB : 1 ≤ cfg.NB)
    (τ : Fin (cfg.T + 1)) (ξ : ℕ → Ω) :
    execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (ox z ω, oy z ω) } : Oracle (E × F) (E × F))
      (igtSgda cfg x0 y0) (fun _ => (off cfg + cfg.T)) (show (igtSgda cfg x0 y0).Seed from τ) ξ =
      outRec cfg x0 y0 ox oy ξ τ.val cfg.T := by
  erw [StochasticGradient.execute_advance P (fun z ω => (ox z ω, oy z ω))
    (igtSgda cfg x0 y0) (off cfg + cfg.T) (show (igtSgda cfg x0 y0).Seed from τ) ξ]
  have h := st_main cfg x0 y0 ox oy ξ τ.val hNB cfg.T le_rfl
  simp only [st] at h
  simp only [igtSgda]
  change (StochasticGradient.advance (igtStep cfg x0 ox oy ξ) (off cfg + cfg.T) 0
    { c := 0, tau := τ.val, y := y0, w := x0, u := 0, acc := 0, out := x0 }).out = _
  rw [h]

end OracleTemplate.HessianNcsc
