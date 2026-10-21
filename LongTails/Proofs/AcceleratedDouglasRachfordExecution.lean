import LongTails.Proofs.ExecutionHistory
import LongTails.Proofs.AcceleratedDouglasRachfordPotential
import LongTails.Proofs.SgdExecution

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.DouglasRachford

open LongTails.Setups.DouglasRachfordSmoothConvex

open StochasticGradient (advance execute_advance)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def tt (i : ℕ) : ℝ := max 1 ((i : ℝ) / 2)

lemma tt_ge_one (i : ℕ) : 1 ≤ tt i := le_max_left _ _

lemma tt_ge_half (i : ℕ) : (i : ℝ) / 2 ≤ tt i := le_max_right _ _

lemma tt_one : tt 1 = 1 := by
  rw [tt, max_eq_left]
  norm_num

lemma tt_succ {i : ℕ} (hi : 1 ≤ i) : tt (i + 1) = ((i : ℝ) + 1) / 2 := by
  have h : (1 : ℝ) ≤ i := by exact_mod_cast hi
  rw [tt, Nat.cast_add, Nat.cast_one, max_eq_right (by linarith)]

lemma tt_sq_ge {i : ℕ} (hi : 1 ≤ i) :
    ((i : ℝ) + 1) / 2 * (((i : ℝ) + 1) / 2 - 1) ≤ tt i ^ 2 := by
  have h : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have h2 := tt_ge_half i
  have h3 : ((i : ℝ) / 2) ^ 2 ≤ tt i ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  nlinarith

lemma tt_mom {i : ℕ} (hi : 1 ≤ i) :
    ((i : ℝ) + 1) / 2 * (((i - 2 : ℕ) : ℝ) / ((i : ℝ) + 1)) = tt i - 1 := by
  rcases Nat.lt_or_ge i 2 with h | h
  · have h1 : i = 1 := by omega
    subst h1
    rw [tt_one]
    norm_num
  · have hc : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by
      rw [Nat.cast_sub h]
      norm_num
    have h2 : (2 : ℝ) ≤ i := by exact_mod_cast h
    rw [hc, tt, max_eq_right (by linarith)]
    field_simp

noncomputable def reserve (γ L lam : ℝ) (i : ℕ) : ℝ :=
  tt (i + 1) * (tt (i + 1) - 1) * (γ / 2 * (lam - 2 * γ * L))
    + (tt i ^ 2 - tt (i + 1) * (tt (i + 1) - 1)) * (γ / 2 * (1 - γ * L))

lemma reserve_succ (γ L lam : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    reserve γ L lam (i + 1) =
      (tt (i + 1) ^ 2 - 1 / 4) * (γ / 2 * (lam - 2 * γ * L)) + 1 / 4 * (γ / 2 * (1 - γ * L)) := by
  have h1 : tt (i + 1 + 1) = ((i : ℝ) + 1 + 1) / 2 := by
    have := tt_succ (i := i + 1) (by omega)
    rw [this]
    push_cast
    ring
  have h2 : tt (i + 1 + 1) * (tt (i + 1 + 1) - 1) = tt (i + 1) ^ 2 - 1 / 4 := by
    rw [h1, tt_succ hi]
    ring
  rw [reserve, h2]
  ring

structure Hyp (f g : E → ℝ) (grad : E → E) (C : Set E) (γ L lam : ℝ) (xs : E) : Prop where
  hL : 0 < L
  hγ : 0 < γ
  hlam0 : 0 < lam
  hlam : lam ≤ 1
  hstep : 4 * γ * L ≤ lam
  hlow : ∀ x y, f x + ⟪grad x, y - x⟫ ≤ f y
  hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2
  hC : Convex ℝ C
  hg : ConvexOn ℝ C g
  hxs : xs ∈ C
  hmin : IsMinOn (fun x => f x + g x) C xs

section

variable {f g : E → ℝ} {grad : E → E} {C : Set E} {γ L lam : ℝ} {xs : E}

lemma star_ineq (H : Hyp f g grad C γ L lam xs) {w x y : E} (P : DRPoint f g grad C γ w x y) :
    env f g grad γ x y - (f xs + g xs) ≤
      ⟪res γ x y, w - (xs + γ • grad xs)⟫ - γ / 2 * (1 - γ * L) * ‖res γ x y‖ ^ 2 := by
  have h := env_ineq H.hL H.hγ H.hlow H.hup (drPoint_star (γ := γ) H.hL H.hC H.hg H.hup H.hxs H.hmin) P
  have e1 : res γ xs xs = 0 := by simp [res]
  have e2 : env f g grad γ xs xs = f xs + g xs := by simp [env]
  have e3 : ⟪res γ x y, xs + γ • grad xs - w⟫ = -⟪res γ x y, w - (xs + γ • grad xs)⟫ := by
    rw [← neg_sub w (xs + γ • grad xs), inner_neg_right]
  rw [e1, e2, e3, zero_sub, zero_add, norm_neg] at h
  nlinarith [h]

lemma gap_lower (H : Hyp f g grad C γ L lam xs) {w x y : E} (P : DRPoint f g grad C γ w x y) :
    γ / 2 * (1 - γ * L) * ‖res γ x y‖ ^ 2 ≤ env f g grad γ x y - (f xs + g xs) := by
  have h1 := env_upper (g := g) H.hγ H.hup x y
  have h2 : f xs + g xs ≤ f y + g y := H.hmin P.hyC
  linarith

structure Good (f g : E → ℝ) (grad : E → E) (C : Set E) (γ L lam : ℝ) (ws : E) (Fs B : ℝ)
    (i : ℕ) (s : State E) : Prop where
  hx : s.x = none
  hk : s.k = i + 1
  data : ∃ wi xi up : E, DRPoint f g grad C γ wi xi s.y ∧ s.u = wi + lam • (s.y - xi) ∧
    s.w = s.u + (((i - 2 : ℕ) : ℝ) / ((i : ℝ) + 1)) • (s.u - up) ∧
    tt i ^ 2 * (env f g grad γ xi s.y - Fs)
      + ‖tt i • s.u - (tt i - 1) • up - ws‖ ^ 2 / (2 * (lam * γ))
      - reserve γ L lam i * ‖res γ xi s.y‖ ^ 2 ≤ B

lemma relax_eq (hγ : 0 < γ) (w x y : E) :
    w + lam • (y - x) = w - (lam * γ) • res γ x y := by
  have h : (lam * γ) • res γ x y = lam • (x - y) := by
    rw [res, smul_smul, mul_assoc, mul_one_div_cancel hγ.ne', mul_one]
  rw [h]
  module

lemma good_first (H : Hyp f g grad C γ L lam xs) {w1 x1 y1 : E}
    (P : DRPoint f g grad C γ w1 x1 y1) :
    Good f g grad C γ L lam (xs + γ • grad xs) (f xs + g xs)
      (‖w1 - (xs + γ • grad xs)‖ ^ 2 / (2 * (lam * γ))) 1
      (advanceState lam ⟨1, w1, w1, none, w1⟩ x1 y1) := by
  refine ⟨rfl, rfl, w1, x1, w1, P, rfl, rfl, ?_⟩
  have hB := star_ineq H P
  have h := first_step H.hγ H.hlam0 H.hlam H.hstep hB
  have hr : reserve γ L lam 1 = γ / 2 * (1 - γ * L) := by
    have h2 : tt (1 + 1) = 1 := by
      rw [tt_succ le_rfl]
      norm_num
    rw [reserve, h2, tt_one]
    ring
  change tt 1 ^ 2 * (env f g grad γ x1 y1 - (f xs + g xs))
      + ‖tt 1 • (w1 + lam • (y1 - x1)) - (tt 1 - 1) • w1 - (xs + γ • grad xs)‖ ^ 2
        / (2 * (lam * γ))
      - reserve γ L lam 1 * ‖res γ x1 y1‖ ^ 2 ≤ _
  rw [hr, tt_one, relax_eq H.hγ]
  have e : (1 : ℝ) • (w1 - (lam * γ) • res γ x1 y1) - ((1 : ℝ) - 1) • w1 - (xs + γ • grad xs) =
      w1 - (lam * γ) • res γ x1 y1 - (xs + γ • grad xs) := by
    rw [one_smul, sub_self, zero_smul, sub_zero]
  rw [e]
  linarith

lemma good_step (H : Hyp f g grad C γ L lam xs) {B : ℝ} {i : ℕ} (hi : 1 ≤ i) {s : State E}
    (hG : Good f g grad C γ L lam (xs + γ • grad xs) (f xs + g xs) B i s) {x' y' : E}
    (P' : DRPoint f g grad C γ s.w x' y') :
    Good f g grad C γ L lam (xs + γ • grad xs) (f xs + g xs) B (i + 1)
      (advanceState lam s x' y') := by
  obtain ⟨wi, xi, up, P, hu, hw, hΦ⟩ := hG.data
  refine ⟨rfl, by simp [advanceState, hG.hk], s.w, x', s.u, P', rfl, ?_, ?_⟩
  · simp [advanceState, hG.hk]
  · have hwi : wi = s.u + (lam * γ) • res γ xi s.y := by
      rw [hu, relax_eq H.hγ]
      abel
    have hA0 := env_ineq H.hL H.hγ H.hlow H.hup P P'
    have e3 : ⟪res γ x' y', wi - s.w⟫ = -⟪res γ x' y', s.w - (s.u + (lam * γ) • res γ xi s.y)⟫ := by
      rw [hwi, ← neg_sub s.w (s.u + (lam * γ) • res γ xi s.y), inner_neg_right]
    rw [e3] at hA0
    have hA : (env f g grad γ x' y' - (f xs + g xs)) - (env f g grad γ xi s.y - (f xs + g xs)) ≤
        ⟪res γ x' y', s.w - (s.u + (lam * γ) • res γ xi s.y)⟫
          - γ / 2 * ‖res γ xi s.y - res γ x' y'‖ ^ 2
          + L * γ ^ 2 / 2 * ‖res γ xi s.y + res γ x' y'‖ ^ 2 := by linarith
    have hB := star_ineq H P'
    have hδp := gap_lower H P
    have hs : tt (i + 1) * (tt (i + 1) - 1) ≤ tt i ^ 2 := by
      rw [tt_succ hi]
      exact tt_sq_ge hi
    have key := potential_step H.hγ H.hL H.hlam0 H.hlam H.hstep (tt_ge_one (i + 1)) hs hδp hA hB
    have hv : tt (i + 1) • s.w - (tt (i + 1) - 1) • s.u = tt i • s.u - (tt i - 1) • up := by
      have hm := tt_mom hi
      rw [← tt_succ hi] at hm
      rw [hw, smul_add, smul_smul, hm]
      module
    rw [hv] at key
    change tt (i + 1) ^ 2 * (env f g grad γ x' y' - (f xs + g xs))
        + ‖tt (i + 1) • (s.w + lam • (y' - x')) - (tt (i + 1) - 1) • s.u - (xs + γ • grad xs)‖ ^ 2
          / (2 * (lam * γ))
        - reserve γ L lam (i + 1) * ‖res γ x' y'‖ ^ 2 ≤ B
    have hv' : tt (i + 1) • (s.w + lam • (y' - x')) - (tt (i + 1) - 1) • s.u =
        tt i • s.u - (tt i - 1) • up - (tt (i + 1) * (lam * γ)) • res γ x' y' := by
      rw [relax_eq H.hγ, ← hv, smul_sub, smul_smul]
      abel
    rw [hv', reserve_succ γ L lam hi]
    have hres : reserve γ L lam i = tt (i + 1) * (tt (i + 1) - 1) * (γ / 2 * (lam - 2 * γ * L))
        + (tt i ^ 2 - tt (i + 1) * (tt (i + 1) - 1)) * (γ / 2 * (1 - γ * L)) := rfl
    rw [hres] at hΦ
    linarith

lemma good_final (H : Hyp f g grad C γ L lam xs) {B : ℝ} {i : ℕ} {s : State E}
    (hG : Good f g grad C γ L lam (xs + γ • grad xs) (f xs + g xs) B i s) :
    s.y ∈ C ∧ tt i ^ 2 * (f s.y + g s.y - (f xs + g xs)) ≤ B := by
  obtain ⟨wi, xi, up, P, -, -, hΦ⟩ := hG.data
  refine ⟨P.hyC, ?_⟩
  have h1 := env_upper (g := g) H.hγ H.hup xi s.y
  have hn := sq_nonneg ‖res γ xi s.y‖
  have ht := tt_ge_one (i + 1)
  have ht2 : 0 ≤ tt i ^ 2 := sq_nonneg _
  have hc : 0 ≤ tt (i + 1) * (tt (i + 1) - 1) := mul_nonneg (by linarith) (by linarith)
  have hab : 0 ≤ γ / 2 * (1 - γ * L) - γ / 2 * (lam - 2 * γ * L) := by
    have := mul_pos H.hγ H.hL
    have h2 : γ / 2 * (1 - γ * L) - γ / 2 * (lam - 2 * γ * L) = γ / 2 * (1 - lam + γ * L) := by ring
    rw [h2]
    exact mul_nonneg (by linarith [H.hγ]) (by linarith [H.hlam])
  have hres : reserve γ L lam i * ‖res γ xi s.y‖ ^ 2 ≤
      tt i ^ 2 * (γ / 2 * (1 - γ * L)) * ‖res γ xi s.y‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hn
    rw [reserve]
    nlinarith [mul_nonneg hc hab]
  have hd : 0 ≤ ‖tt i • s.u - (tt i - 1) • up - (xs + γ • grad xs)‖ ^ 2 / (2 * (lam * γ)) :=
    div_nonneg (sq_nonneg _) (by linarith [mul_pos H.hlam0 H.hγ])
  have h3 := mul_le_mul_of_nonneg_left h1 ht2
  nlinarith [h3]

end

lemma advance_add {State : Type*} (step : ℕ → State → State) (K1 K2 call : ℕ) (s : State) :
    advance step (K1 + K2) call s = advance step K2 (call + K1) (advance step K1 call s) := by
  induction K1 generalizing call s with
  | zero => simp [advance]
  | succ K1 ih =>
    rw [Nat.succ_add, advance, advance, ih]
    congr 1
    omega

noncomputable def drStep (p : Public) (O : Oracle (Query p) p.E) (ξ : (k : ℕ) → O.Seed k) :
    ℕ → State p.E → State p.E :=
  fun k st => (acceleratedDouglasRachford p).update st
    (executeAnswerAt O (acceleratedDouglasRachford p) () ξ k ((acceleratedDouglasRachford p).query st))

lemma two_calls (p : Public) (O : Oracle (Query p) p.E) (ξ : (k : ℕ) → O.Seed k) (c : ℕ)
    (s : State p.E) (hx : s.x = none) :
    advance (drStep p O ξ) 2 c s =
      advanceState p.lam s (executeAnswerAt O (acceleratedDouglasRachford p) () ξ c (0, (.proxF s.w)))
        (executeAnswerAt O (acceleratedDouglasRachford p) () ξ (c + 1) (0, (.proxG ((2 : ℝ) • executeAnswerAt O (acceleratedDouglasRachford p) () ξ c (0, (.proxF s.w)) - s.w)))) := by
  obtain ⟨k, u, w, x, y⟩ := s
  simp only at hx
  subst hx
  rfl

lemma run_good (q : Params) (I : Instance q.toPublic) (O : Oracle (Query q.toPublic) q.E)
    (ξ : (k : ℕ) → O.Seed k) {xs : q.E}
    (H : Hyp I.f I.g (gradient I.f) I.C q.γ q.L q.lam xs)
    (hpf : ∀ k seed w, IsMinOn (fun x => I.f x + ‖x - w‖ ^ 2 / (2 * q.γ)) univ
      (O.answer k (0, (.proxF w)) seed))
    (hpg : ∀ k seed v, O.answer k (0, (.proxG v)) seed ∈ I.C ∧
      IsMinOn (fun y => I.g y + ‖y - v‖ ^ 2 / (2 * q.γ)) I.C (O.answer k (0, (.proxG v)) seed))
    (n : ℕ) :
    Good I.f I.g (gradient I.f) I.C q.γ q.L q.lam (xs + q.γ • gradient I.f xs) (I.f xs + I.g xs)
      (‖q.w1 - (xs + q.γ • gradient I.f xs)‖ ^ 2 / (2 * (q.lam * q.γ))) (n + 1)
      (advance (drStep q.toPublic O ξ) (2 * (n + 1)) 0 ⟨1, q.w1, q.w1, none, q.w1⟩) := by
  induction n with
  | zero =>
    rw [show 2 * (0 + 1) = 2 from rfl,
      two_calls q.toPublic O ξ 0 (⟨1, q.w1, q.w1, none, q.w1⟩ : State q.E) rfl]
    exact good_first H (drPoint_of_prox H.hL H.hγ H.hup H.hC H.hg (hpf _ _ _) (hpg _ _ _).1
      (hpg _ _ _).2)
  | succ n ih =>
    rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by ring, advance_add,
      two_calls q.toPublic O ξ _ _ ih.hx]
    exact good_step H (Nat.succ_le_succ (Nat.zero_le n)) ih
      (drPoint_of_prox H.hL H.hγ H.hup H.hC H.hg (hpf _ _ _) (hpg _ _ _).1 (hpg _ _ _).2)

lemma execute_accuracy (q : Params) (I : Instance q.toPublic) (O : Oracle (Query q.toPublic) q.E)
    {xs : q.E} (H : Hyp I.f I.g (gradient I.f) I.C q.γ q.L q.lam xs) (hR : 0 < q.R) (hε : 0 < q.ε)
    (hpf : ∀ k seed w, IsMinOn (fun x => I.f x + ‖x - w‖ ^ 2 / (2 * q.γ)) univ
      (O.answer k (0, (.proxF w)) seed))
    (hpg : ∀ k seed v, O.answer k (0, (.proxG v)) seed ∈ I.C ∧
      IsMinOn (fun y => I.g y + ‖y - v‖ ^ 2 / (2 * q.γ)) I.C (O.answer k (0, (.proxG v)) seed))
    (hdist : ‖q.w1 - (xs + q.γ • gradient I.f xs)‖ ≤ q.R)
    (seed : (acceleratedDouglasRachford q.toPublic).Seed) (ξ : (k : ℕ) → O.Seed k) (N : ℕ)
    (hbudget : ⌈Real.sqrt (2 * q.R ^ 2 / (q.lam * q.γ * q.ε))⌉₊ ≤ N) :
    (execute O (acceleratedDouglasRachford q.toPublic)
        (fun _ => (2 * N)) seed ξ) ∈ I.C ∧
      objective I (execute O (acceleratedDouglasRachford q.toPublic)
        (fun _ => (2 * N)) seed ξ) - objective I xs ≤ q.ε := by
  have hlg : 0 < q.lam * q.γ := mul_pos H.hlam0 H.hγ
  have hlge : 0 < q.lam * q.γ * q.ε := mul_pos hlg hε
  have hX : 0 < 2 * q.R ^ 2 / (q.lam * q.γ * q.ε) := div_pos (mul_pos two_pos (pow_pos hR 2)) hlge
  have hNpos : 0 < N := (Nat.ceil_pos.mpr (Real.sqrt_pos.mpr hX)).trans_le hbudget
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hceil : Real.sqrt (2 * q.R ^ 2 / (q.lam * q.γ * q.ε)) ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hbudget)
  have hsq : 2 * q.R ^ 2 / (q.lam * q.γ * q.ε) ≤ (N : ℝ) ^ 2 := (Real.sqrt_le_left (by positivity)).mp hceil
  cases seed
  erw [execute_advance_history]
  have hG := run_good q I O ξ H hpf hpg n
  rw [← hn] at hG
  obtain ⟨hyC, hfin⟩ := good_final H hG
  change (advance (drStep q.toPublic O ξ) (2 * N) 0 ⟨1, q.w1, q.w1, none, q.w1⟩).y ∈ I.C ∧
    I.f (advance (drStep q.toPublic O ξ) (2 * N) 0 ⟨1, q.w1, q.w1, none, q.w1⟩).y
      + I.g (advance (drStep q.toPublic O ξ) (2 * N) 0 ⟨1, q.w1, q.w1, none, q.w1⟩).y
      - (I.f xs + I.g xs) ≤ q.ε
  refine ⟨hyC, ?_⟩
  generalize (advance (drStep q.toPublic O ξ) (2 * N) 0 ⟨1, q.w1, q.w1, none, q.w1⟩).y = y at hfin ⊢
  by_contra hgap
  push Not at hgap
  have hB : ‖q.w1 - (xs + q.γ • gradient I.f xs)‖ ^ 2 / (2 * (q.lam * q.γ)) ≤
      q.R ^ 2 / (2 * (q.lam * q.γ)) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hdist 2) (by linarith)
  have ht : ((N : ℝ) / 2) ^ 2 ≤ tt N ^ 2 := pow_le_pow_left₀ (by positivity) (tt_ge_half N) 2
  have hpos : 0 < I.f y + I.g y - (I.f xs + I.g xs) := lt_trans hε hgap
  have hNr : (0 : ℝ) < ((N : ℝ) / 2) ^ 2 := by
    have : (0 : ℝ) < N := by exact_mod_cast hNpos
    positivity
  have h1 : ((N : ℝ) / 2) ^ 2 * q.ε < tt N ^ 2 * (I.f y + I.g y - (I.f xs + I.g xs)) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hgap hNr) (mul_le_mul_of_nonneg_right ht hpos.le)
  have h2 : q.R ^ 2 / (2 * (q.lam * q.γ)) ≤ ((N : ℝ) / 2) ^ 2 * q.ε := by
    rw [div_le_iff₀ hlge] at hsq
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

end OracleTemplate.DouglasRachford
