import LongTails.Algorithms.DyadicVarianceReduction
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.DyadicHolder

open OracleTemplate.NormalizedStorm

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Process

variable (cfg : DyadicConfig) (g : E → Ω → E)

def off : ℕ → ℕ
  | 0 => 0
  | k + 1 => off k + cfg.batch k

noncomputable def contrib (s : DyadicState E) (ω : Ω) : E :=
  if cfg.pos s.k = 0 then g (s.xs s.k) ω else g (s.xs s.k) ω - g (s.xs (cfg.pred s.k)) ω

noncomputable def accum (s : DyadicState E) (ξ : ℕ → Ω) (c0 : ℕ) (i : ℕ) : E :=
  ∑ i' ∈ Finset.range i, contrib cfg g s (ξ (c0 + i'))

noncomputable def boundary (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) : ℕ → DyadicState E
  | 0 => { k := 0, i := 0, acc := 0, xs := fun _ => x0, ds := fun _ => 0, tau := τ }
  | k + 1 =>
      let s := boundary x0 τ ξ k
      let d := dyadicEstimate cfg s.ds k (accum cfg g s ξ (off cfg k) (cfg.batch k))
      { k := k + 1, i := 0, acc := 0,
        xs := Function.update s.xs (k + 1) (stormStep cfg.η (s.xs k) d),
        ds := Function.update s.ds k d, tau := τ }

noncomputable def callState (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) : ℕ → DyadicState E
  | 0 => { k := 0, i := 0, acc := 0, xs := fun _ => x0, ds := fun _ => 0, tau := τ }
  | c + 1 =>
      let s := callState x0 τ ξ c
      dyadicUpdate cfg s (g (dyadicQuery cfg s).1 (ξ c), g (dyadicQuery cfg s).2 (ξ c))

variable {cfg g}

lemma boundary_k (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) : ∀ k, (boundary cfg g x0 τ ξ k).k = k
  | 0 => rfl
  | _ + 1 => rfl

lemma boundary_i (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) : ∀ k, (boundary cfg g x0 τ ξ k).i = 0
  | 0 => rfl
  | _ + 1 => rfl

lemma boundary_acc (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) : ∀ k, (boundary cfg g x0 τ ξ k).acc = 0
  | 0 => rfl
  | _ + 1 => rfl

lemma boundary_tau (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) : ∀ k, (boundary cfg g x0 τ ξ k).tau = τ
  | 0 => rfl
  | _ + 1 => rfl

omit [InnerProductSpace ℝ E] in
lemma contrib_eq_query (s : DyadicState E) (ω : Ω) :
    contrib cfg g s ω = (if cfg.pos s.k = 0 then g (dyadicQuery cfg s).1 ω
      else g (dyadicQuery cfg s).1 ω - g (dyadicQuery cfg s).2 ω) := by
  unfold contrib dyadicQuery
  split_ifs <;> rfl

lemma callState_inner (hb : ∀ k, 1 ≤ cfg.batch k) (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) (k : ℕ)
    (hk : k ≤ cfg.K) (hbd : callState cfg g x0 τ ξ (off cfg k) = boundary cfg g x0 τ ξ k) :
    ∀ i, i < cfg.batch k →
      callState cfg g x0 τ ξ (off cfg k + i) =
        { boundary cfg g x0 τ ξ k with
          i := i, acc := accum cfg g (boundary cfg g x0 τ ξ k) ξ (off cfg k) i }
  | 0, _ => by
      rw [Nat.add_zero, hbd]
      cases hB : boundary cfg g x0 τ ξ k
      have h1 := boundary_i (cfg := cfg) (g := g) x0 τ ξ k
      have h2 := boundary_acc (cfg := cfg) (g := g) x0 τ ξ k
      rw [hB] at h1 h2
      simp only at h1 h2
      subst h1; subst h2
      simp [accum]
  | i + 1, hi => by
      have ih := callState_inner hb x0 τ ξ k hk hbd i (by omega)
      rw [← Nat.add_assoc, callState, ih]
      set B := boundary cfg g x0 τ ξ k with hB
      have hBk : B.k = k := boundary_k x0 τ ξ k
      unfold dyadicUpdate
      have hnot : ¬ (cfg.K + 1 ≤ B.k) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)]
      simp only
      have hlt : i + 1 < cfg.batch B.k := by rw [hBk]; exact hi
      rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)]
      simp only [accum, Finset.sum_range_succ]
      congr 1
      rw [contrib_eq_query]
      rfl

lemma callState_boundary (hb : ∀ k, 1 ≤ cfg.batch k) (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) :
    ∀ k, k ≤ cfg.K + 1 → callState cfg g x0 τ ξ (off cfg k) = boundary cfg g x0 τ ξ k
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := callState_boundary hb x0 τ ξ k (by omega)
      have hlast := callState_inner hb x0 τ ξ k (by omega) ih (cfg.batch k - 1)
        (by have := hb k; omega)
      have e : off cfg (k + 1) = off cfg k + (cfg.batch k - 1) + 1 := by
        simp only [off]; have := hb k; omega
      rw [e, callState, hlast]
      set B := boundary cfg g x0 τ ξ k with hB
      have hBk : B.k = k := boundary_k x0 τ ξ k
      unfold dyadicUpdate
      have hnot : ¬ (cfg.K + 1 ≤ B.k) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot)]
      simp only
      have hge : ¬ (cfg.batch k - 1 + 1 < cfg.batch B.k) := by rw [hBk]; omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hge)]
      have hq : dyadicQuery cfg
          { B with i := cfg.batch k - 1, acc := accum cfg g B ξ (off cfg k) (cfg.batch k - 1) } =
          dyadicQuery cfg B := rfl
      have hsum : accum cfg g B ξ (off cfg k) (cfg.batch k - 1) +
          (if cfg.pos k = 0 then g (dyadicQuery cfg B).1 (ξ (off cfg k + (cfg.batch k - 1)))
            else g (dyadicQuery cfg B).1 (ξ (off cfg k + (cfg.batch k - 1))) -
              g (dyadicQuery cfg B).2 (ξ (off cfg k + (cfg.batch k - 1)))) =
          accum cfg g B ξ (off cfg k) (cfg.batch k) := by
        have h1 : cfg.batch k = (cfg.batch k - 1) + 1 := by have := hb k; omega
        conv_rhs => rw [h1]
        simp only [accum, Finset.sum_range_succ, contrib_eq_query, hBk]
      simp only [hBk] at hq ⊢
      rw [hq, hsum]
      rw [boundary]
      simp only [hB.symm]
      rw [hB, boundary_tau]

lemma callState_frozen (x0 : E) (τ : ℕ) (ξ : ℕ → Ω) (c : ℕ)
    (hc : cfg.K + 1 ≤ (callState cfg g x0 τ ξ c).k) :
    ∀ m, callState cfg g x0 τ ξ (c + m) = callState cfg g x0 τ ξ c
  | 0 => rfl
  | m + 1 => by
      rw [← Nat.add_assoc, callState, callState_frozen x0 τ ξ c hc m]
      unfold dyadicUpdate
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]

end Process

end OracleTemplate.DyadicHolder
