import LongTails.Setups.QuasarSignedBias
import LongTails.Algorithms.BestValueDescent
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient

namespace OracleTemplate.QuasarSignedBias

open LongTails.Setups.QuasarSignedBias

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma shifted_step (f : E → ℝ) (x u b : E) (η M B τ : ℝ)
    (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hg : ‖gradient f x‖ ≤ M) (hb : ‖b‖ ≤ B)
    (hs : τ * (f x - f u) ≤ ⟪gradient f x, x - u⟫) :
    ‖x + η • b - η • gradient f x - u‖ ^ 2 + 2 * η * τ * (f x - f u) ≤
      ‖x + η • b - u‖ ^ 2 + η ^ 2 * (M ^ 2 + 2 * M * B) := by
  have hgb : -M * B ≤ ⟪b, gradient f x⟫ := by
    have hi := real_inner_le_norm (-b) (gradient f x)
    simp only [inner_neg_left, norm_neg] at hi
    have hm := mul_le_mul hb hg (norm_nonneg _) hB
    nlinarith
  have hgn : ‖gradient f x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have he : x + η • b - η • gradient f x - u = (x + η • b - u) - η • gradient f x := by module
  rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
  have hi : ⟪x + η • b - u, gradient f x⟫ = ⟪gradient f x, x - u⟫ + η * ⟪b, gradient f x⟫ := by
    rw [show x + η • b - u = (x - u) + η • b by module, inner_add_left,
      real_inner_smul_left, ← real_inner_comm (x - u) (gradient f x)]
  rw [hi]
  have h1 := mul_le_mul_of_nonneg_left hs hη
  have h2 := mul_le_mul_of_nonneg_left hgb (sq_nonneg η)
  have h3 := mul_le_mul_of_nonneg_left hgn (sq_nonneg η)
  nlinarith

lemma execute_accuracy (p : Params) (f : p.E → ℝ) (O : Oracle p.E (ℝ × p.E))
    (hp : spec.valid p) (ho : spec.admissible p f O)
    (ξ : (k : ℕ) → O.Seed k) :
    let C := p.M ^ 2 + 2 * p.M * p.B
    let η := p.τ * p.ε / C
    let K := max 1 ⌈p.R ^ 2 * C / (p.τ ^ 2 * p.ε ^ 2)⌉₊
    let output := execute O (bestValueDescent η p.x0) (fun _ => K) () ξ
    ∃ xstar, IsMinOn f Set.univ xstar ∧ f output - f xstar ≤ p.ε := by
  rcases hp with ⟨hM, hB, hR, hτ, hτ1, hε⟩
  rcases ho with ⟨hg, hbound, ⟨b, hb0, hb, hans⟩, u, hmin, hdist, hsupport⟩
  let C := p.M ^ 2 + 2 * p.M * p.B
  let η := p.τ * p.ε / C
  let K := max 1 ⌈p.R ^ 2 * C / (p.τ ^ 2 * p.ε ^ 2)⌉₊
  have hC : 0 < C := by dsimp [C]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  let A := bestValueDescent η p.x0
  let step := fun k s => A.update s (O.answer k (A.query s) (ξ k))
  let s := fun k => advance step k 0 (A.initial ())
  let x := fun k => (s k).2.1
  have hs (k : ℕ) : s (k + 1) = step k (s k) := by
    dsimp [s]
    rw [advance_add, Nat.zero_add]
    rfl
  have hindex : ∀ k, (s k).1 = k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [hs]; exact congrArg (· + 1) ih
  have hx (k : ℕ) : x (k + 1) = x k - η • (gradient f (x k) + b (k + 1) - b k) := by
    simp only [x, hs, step, A, bestValueDescent, hans]
  have hbest : ∀ k, 0 < k →
      f (s k).2.2.1 = (s k).2.2.2 ∧ ∀ j < k, f (s k).2.2.1 ≤ f (x j) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        constructor
        · simp [hs, step, A, bestValueDescent, hans, hindex]
        · intro j hj
          have : j = 0 := by omega
          subst j
          simp [hs, step, A, bestValueDescent, hans, hindex, x]
      · have hi := ih (Nat.pos_of_ne_zero hk0)
        rw [hs]
        simp only [step, A, bestValueDescent, hans, hindex, hk0, false_or]
        change f (if f (x k) ≤ (s k).2.2.2 then (x k, f (x k)) else (s k).2.2).1 =
          (if f (x k) ≤ (s k).2.2.2 then (x k, f (x k)) else (s k).2.2).2 ∧
          ∀ j < k + 1, f (if f (x k) ≤ (s k).2.2.2 then (x k, f (x k)) else (s k).2.2).1 ≤ f (x j)
        split_ifs with hh
        · refine ⟨rfl, ?_⟩
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
          · have hh' : f (x k) ≤ f (s k).2.2.1 := by simpa only [hi.1] using hh
            exact hh'.trans (hi.2 j h)
          · subst j; exact le_rfl
        · refine ⟨hi.1, ?_⟩
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
          · exact hi.2 j h
          · subst j; rw [hi.1]; exact le_of_lt (lt_of_not_ge hh)
  have henergy : ∀ k, ‖x k + η • b k - u‖ ^ 2 +
      2 * η * p.τ * (∑ j ∈ Finset.range k, (f (x j) - f u)) ≤
      ‖p.x0 - u‖ ^ 2 + (k : ℝ) * η ^ 2 * C := by
    intro k
    induction k with
    | zero => simp [x, s, A, bestValueDescent, advance, hb0]
    | succ k ih =>
      have hstep := shifted_step f (x k) u (b k) η p.M p.B p.τ hη.le hB
        (hbound _) (hb k) (hsupport _)
      have he : x (k + 1) + η • b (k + 1) - u = x k + η • b k - η • gradient f (x k) - u := by
        rw [hx]; module
      rw [he, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      dsimp only [C] at *
      nlinarith
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun j hj =>
    sub_le_sub_right ((hbest K hK).2 j (Finset.mem_range.mp hj)) (f u))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * η * p.τ by positivity)
  have hen := henergy K
  have hR2 : ‖p.x0 - u‖ ^ 2 ≤ p.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hceil : p.R ^ 2 * C / (p.τ ^ 2 * p.ε ^ 2) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
  have hbud := (div_le_iff₀ (show 0 < p.τ ^ 2 * p.ε ^ 2 by positivity)).mp hceil
  have hid : η * C = p.τ * p.ε := by dsimp [η]; field_simp
  have hinit : p.R ^ 2 ≤ η * p.τ * p.ε * (K : ℝ) := by
    calc
      p.R ^ 2 ≤ (K : ℝ) * (p.τ ^ 2 * p.ε ^ 2) / C := (le_div_iff₀ hC).mpr hbud
      _ = η * p.τ * p.ε * (K : ℝ) := by dsimp [η]; ring
  have hnoise : (K : ℝ) * η ^ 2 * C = η * p.τ * (K : ℝ) * p.ε := by
    calc
      _ = η * (K : ℝ) * (η * C) := by ring
      _ = _ := by rw [hid]; ring
  rw [hnoise] at hen
  have hacc : f (s K).2.2.1 - f u ≤ p.ε := by
    have hn := sq_nonneg ‖x K + η • b K - u‖
    have hrate : 2 * η * p.τ * (K : ℝ) * (f (s K).2.2.1 - f u) ≤
        2 * η * p.τ * (K : ℝ) * p.ε := by nlinarith only [hen, hsum', hR2, hinit, hn]
    exact (mul_le_mul_iff_right₀ (show 0 < 2 * η * p.τ * (K : ℝ) by positivity)).mp hrate
  dsimp only
  erw [execute_advance]
  exact ⟨u, hmin, hacc⟩

end OracleTemplate.QuasarSignedBias
