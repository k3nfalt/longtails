import LongTails.Algorithms.WeaklyConvexSilver
import LongTails.Proofs.WeaklyConvexSilverInduction
import LongTails.Proofs.GdConvex
import Mathlib.Data.List.GetD

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeaklyConvexSilverExecution

open OracleTemplate
open LongTails.Setups.SmoothWeaklyConvex
open LongTails.Algorithms.SilverSchedule
open LongTails.Algorithms.WeaklyConvexSilver
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace
open LongTails.Proofs.WeaklyConvexSilverBasic
open LongTails.Proofs.WeaklyConvexSilverCertificate
open LongTails.Proofs.WeaklyConvexSilverJoin
open LongTails.Proofs.WeaklyConvexSilverInduction

section Normalized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma normalized_facts {f : E → ℝ} {L ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hc : ConvexOn ℝ univ (fun x => f x + ρ / 2 * ‖x‖ ^ 2)) :
    (∀ x y, ‖(1 / L) • gradient f x - (1 / L) • gradient f y‖ ≤ ‖x - y‖) ∧
    (∀ u v, -(ρ / L) * ‖(u - (1 / L) • gradient f u) - (v - (1 / L) • gradient f v)‖ ^ 2 ≤
      defect (1 / L * f u) (1 / L * f v) u v ((1 / L) • gradient f u) ((1 / L) • gradient f v)) := by
  have hl : ∀ x y, ‖(1 / L) • gradient f x - (1 / L) • gradient f y‖ ≤ ‖x - y‖ := by
    intro x y
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h := hlip x y
    calc 1 / L * ‖gradient f x - gradient f y‖ ≤ 1 / L * (L * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ‖x - y‖ := by field_simp
  have hG : ∀ x, HasGradientAt (fun z => 1 / L * f z) ((1 / L) • gradient f x) x := by
    intro x
    rw [hasGradientAt_iff_hasFDerivAt]
    convert ((hg x).hasFDerivAt.const_mul (1 / L)) using 1
    ext v
    simp
  have hc' : ConvexOn ℝ univ (fun z => 1 / L * f z + ρ / L / 2 * ‖z‖ ^ 2) := by
    have h := hc.smul (show (0 : ℝ) ≤ 1 / L by positivity)
    convert h using 1
    funext z
    simp only [smul_eq_mul]
    ring
  refine ⟨hl, fun u v => ?_⟩
  exact weak_defect (f := fun z => 1 / L * f z) (g := fun z => (1 / L) • gradient f z)
    (by positivity) hc' hG hl u v

end Normalized

section Trajectory

variable (p : Params) (f : p.E → ℝ)

noncomputable def traj (t : ℕ) : State p.E :=
  (fun s => (method p).update s (gradient f ((method p).query s).2))^[t] ((method p).initial ())

lemma traj_zero : traj p f 0 = ⟨p.x0, 0, p.x0, 0⟩ := rfl

lemma traj_succ (t : ℕ) :
    traj p f (t + 1) = (method p).update (traj p f t) (gradient f (traj p f t).point) := by
  unfold traj
  rw [Function.iterate_succ_apply']
  rfl

lemma traj_count (t : ℕ) : (traj p f t).count = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [traj_succ]; simp [method, ih]

lemma traj_point (t : ℕ) :
    (traj p f (t + 1)).point = (traj p f t).point - stepSize p t • gradient f (traj p f t).point := by
  rw [traj_succ]
  simp [method, traj_count]

lemma traj_best (t : ℕ) (ht : 1 ≤ t) :
    ‖gradient f (traj p f t).best‖ ^ 2 = (traj p f t).bestNorm ∧
      ∀ i < t, (traj p f t).bestNorm ≤ ‖gradient f (traj p f i).point‖ ^ 2 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [traj_succ]
    rcases Nat.eq_zero_or_pos t with rfl | ht'
    · simp only [method, traj_zero, true_or, ite_true]
      refine ⟨trivial, fun i hi => ?_⟩
      have : i = 0 := by omega
      subst this
      simp [traj_zero]
    · obtain ⟨h1, h2⟩ := ih ht'
      have hc : (traj p f t).count ≠ 0 := by rw [traj_count]; omega
      simp only [method, hc, false_or]
      split_ifs with hle
      · refine ⟨rfl, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hle.trans (h2 i hi)
        · exact le_rfl
      · refine ⟨h1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · exact (lt_of_not_ge hle).le

lemma run_from (hL : 0 < p.L) :
    ∀ (l : List ℝ) (t0 : ℕ), (∀ i < l.length, stepSize p (t0 + i) = l.getD i 1 / p.L) →
      (traj p f (t0 + l.length)).point =
        run (fun z => (1 / p.L) • gradient f z) l (traj p f t0).point
  | [], t0, _ => by simp [run]
  | h :: l, t0, hst => by
    have h0 := hst 0 (by simp)
    simp only [List.getD_cons_zero, add_zero] at h0
    have ih := run_from hL l (t0 + 1) (fun i hi => by
      have := hst (i + 1) (by simp only [List.length_cons]; omega)
      simpa [List.getD_cons_succ, add_assoc, add_comm 1 i] using this)
    have hlen : t0 + (h :: l).length = t0 + 1 + l.length := by
      simp only [List.length_cons]; ring
    rw [hlen, ih, traj_point, h0]
    simp only [run]
    congr 1
    rw [smul_smul, div_eq_mul_one_div]

end Trajectory

section Accuracy

variable {p : Params} {f : p.E → ℝ}

lemma length_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ (steps k).length := by
  have h := steps_length k
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

lemma step_periodic (j i : ℕ) (hi : i < (steps (level p)).length) :
    stepSize p (j * (steps (level p)).length + i) = (steps (level p)).getD i 1 / p.L := by
  unfold stepSize
  rw [show j * (steps (level p)).length + i = i + j * (steps (level p)).length by ring,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

lemma best_le (B : ℕ) (hB : 1 ≤ B) (i : ℕ) (hi : i < B) :
    ‖gradient f (traj p f B).best‖ ^ 2 ≤ ‖gradient f (traj p f i).point‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := traj_best p f B hB
  rw [h1]
  exact h2 i hi

lemma accuracy_blocks (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hc : ConvexOn ℝ univ (fun x => f x + p.ρ / 2 * ‖x‖ ^ 2))
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (hK : 2 ≤ level p) (hsmall : 250000 * p.ρ * (7 / 2) ^ level p ≤ p.L)
    (J : ℕ) (hJ : 1 ≤ J) (hJε : 4 * p.L * p.Δ ≤ ratio ^ level p * J * p.ε ^ 2)
    (B : ℕ) (hB : J * (steps (level p)).length + 1 ≤ B) :
    ‖gradient f (traj p f B).best‖ ^ 2 ≤ p.ε ^ 2 := by
  set K := level p with hKdef
  set n := (steps K).length with hn
  have hn1 : 1 ≤ n := length_pos K (by omega)
  obtain ⟨hl, hD⟩ := normalized_facts hL hρ hg hlip hc
  set G := fun z => (1 / p.L) • gradient f z with hG
  set F := fun z => 1 / p.L * f z with hF
  have hρ' : 0 ≤ p.ρ / p.L := div_nonneg hρ hL.le
  have hsm : p.ρ / p.L * (7 / 2) ^ K ≤ 1 / 250000 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    linarith
  have hdesc := fun x => block_descent (f := F) (g := G) hρ' hl hD hK hsm x
  have hblock : ∀ j, (traj p f ((j + 1) * n)).point = run G (steps K) (traj p f (j * n)).point := by
    intro j
    have h := run_from p f hL (steps K) (j * n) (fun i hi => step_periodic j i hi)
    rw [show j * n + (steps K).length = (j + 1) * n by rw [← hn]; ring] at h
    exact h
  have htele : ∀ m, ∑ j ∈ Finset.range m,
      ((steps K).sum + 1) * ‖G (traj p f ((j + 1) * n)).point‖ ^ 2 ≤
        4 * (F p.x0 - F (traj p f (m * n)).point) := by
    intro m
    induction m with
    | zero => simp [traj_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h := hdesc (traj p f (m * n)).point
      rw [← hblock m] at h
      linarith
  have hS1 : (steps K).sum + 1 = ratio ^ K := pow_steps_sum K
  have hlowF : ∀ x, lower / p.L ≤ F x := by
    intro x
    simp only [hF]
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (hlower x) (by positivity)
  have hsum := htele J
  have hF0 : F p.x0 - F (traj p f (J * n)).point ≤ p.Δ / p.L := by
    have h1 := hlowF (traj p f (J * n)).point
    have h2 : F p.x0 = f p.x0 / p.L := by simp only [hF]; ring
    rw [h2]
    have h3 : f p.x0 / p.L - lower / p.L ≤ p.Δ / p.L := by
      rw [← sub_div]; gcongr
    linarith
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJc : (J : ℝ) * (4 * (p.Δ / p.L) / J) = 4 * (p.Δ / p.L) := by
    field_simp
  obtain ⟨j, hj, hjb⟩ := Finset.exists_le_of_sum_le (s := Finset.range J)
    (f := fun j => ((steps K).sum + 1) * ‖G (traj p f ((j + 1) * n)).point‖ ^ 2)
    (g := fun _ => 4 * (p.Δ / p.L) / J) (Finset.nonempty_range_iff.mpr (by omega)) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hJc]
      linarith)
  have hjJ : j < J := Finset.mem_range.mp hj
  have hidx : (j + 1) * n < B := by
    have : (j + 1) * n ≤ J * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hout := best_le (p := p) (f := f) B (by omega) ((j + 1) * n) hidx
  have hGn : ‖G (traj p f ((j + 1) * n)).point‖ ^ 2 =
      ‖gradient f (traj p f ((j + 1) * n)).point‖ ^ 2 / p.L ^ 2 := by
    simp only [hG, norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / p.L), mul_pow]
    ring
  rw [hGn, hS1] at hjb
  have hrK : 0 < ratio ^ K := pow_pos (by have := ratio_bounds; linarith) K
  have key : ‖gradient f (traj p f ((j + 1) * n)).point‖ ^ 2 ≤ 4 * p.L * p.Δ / (ratio ^ K * J) := by
    rw [le_div_iff₀ (mul_pos hrK hJpos)]
    have h1 : ratio ^ K * (‖gradient f (traj p f ((j + 1) * n)).point‖ ^ 2 / p.L ^ 2) ≤
        4 * (p.Δ / p.L) / J := hjb
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ p.L ^ 2 * J)
    have e1 : p.L ^ 2 * J * (ratio ^ K * (‖gradient f (traj p f ((j + 1) * n)).point‖ ^ 2 / p.L ^ 2)) =
        ‖gradient f (traj p f ((j + 1) * n)).point‖ ^ 2 * (ratio ^ K * J) := by
      field_simp
    have e2 : p.L ^ 2 * J * (4 * (p.Δ / p.L) / J) = 4 * p.L * p.Δ := by
      field_simp
    linarith
  have key2 : 4 * p.L * p.Δ / (ratio ^ K * J) ≤ p.ε ^ 2 := by
    rw [div_le_iff₀ (mul_pos hrK hJpos)]
    linarith
  linarith

lemma level_one_steps (h1 : level p = 1) (t : ℕ) : stepSize p t = (ratio - 1) / p.L := by
  unfold stepSize
  rw [h1, steps_one]
  simp [Nat.mod_one]

lemma accuracy_single (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (hK : level p = 1) (T : ℕ) (hT : 1 ≤ T) (hTε : ratio * p.L * p.Δ ≤ T * p.ε ^ 2)
    (B : ℕ) (hB : T ≤ B) :
    ‖gradient f (traj p f B).best‖ ^ 2 ≤ p.ε ^ 2 := by
  have hb := ratio_bounds
  have hsq := ratio_square
  have hdesc : ∀ t, (ratio - 2) / p.L * ‖gradient f (traj p f t).point‖ ^ 2 ≤
      f (traj p f t).point - f (traj p f (t + 1)).point := by
    intro t
    have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip (traj p f t).point
      (traj p f (t + 1)).point
    rw [traj_point, level_one_steps hK] at h
    have e1 : (traj p f t).point - ((ratio - 1) / p.L) • gradient f (traj p f t).point -
        (traj p f t).point = -((ratio - 1) / p.L) • gradient f (traj p f t).point := by module
    rw [e1, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by apply div_pos; linarith; exact hL), mul_pow] at h
    rw [traj_point, level_one_steps hK]
    have e2 : p.L / 2 * (((ratio - 1) / p.L) ^ 2 * ‖gradient f (traj p f t).point‖ ^ 2) =
        (ratio - 1) ^ 2 / (2 * p.L) * ‖gradient f (traj p f t).point‖ ^ 2 := by
      field_simp
    have e3 : (ratio - 1) ^ 2 = 2 := by linear_combination hsq
    rw [e2, e3] at h
    have e4 : (ratio - 2) / p.L * ‖gradient f (traj p f t).point‖ ^ 2 =
        (ratio - 1) / p.L * ‖gradient f (traj p f t).point‖ ^ 2 -
          2 / (2 * p.L) * ‖gradient f (traj p f t).point‖ ^ 2 := by
      field_simp
      ring
    rw [e4]
    linarith
  have htele : ∀ m, ∑ t ∈ Finset.range m, (ratio - 2) / p.L * ‖gradient f (traj p f t).point‖ ^ 2 ≤
      f p.x0 - f (traj p f m).point := by
    intro m
    induction m with
    | zero => simp [traj_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have := hdesc m
      linarith
  have hsum := htele T
  have hlow := hlower (traj p f T).point
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hTc : (T : ℝ) * (p.Δ / T) = p.Δ := by field_simp
  obtain ⟨t, ht, htb⟩ := Finset.exists_le_of_sum_le (s := Finset.range T)
    (f := fun t => (ratio - 2) / p.L * ‖gradient f (traj p f t).point‖ ^ 2)
    (g := fun _ => p.Δ / T) (Finset.nonempty_range_iff.mpr (by omega)) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hTc]
      linarith)
  have htT : t < T := Finset.mem_range.mp ht
  have hout := best_le (p := p) (f := f) B (by omega) t (by omega)
  have hr2 : 0 < ratio - 2 := by linarith
  have h1 : (ratio - 2) * ‖gradient f (traj p f t).point‖ ^ 2 ≤ p.L * (p.Δ / T) := by
    have h0 := mul_le_mul_of_nonneg_left htb hL.le
    have e : p.L * ((ratio - 2) / p.L * ‖gradient f (traj p f t).point‖ ^ 2) =
        (ratio - 2) * ‖gradient f (traj p f t).point‖ ^ 2 := by
      field_simp
    linarith
  have hinv : ratio * (ratio - 2) = 1 := by linear_combination hsq
  have h2 : ‖gradient f (traj p f t).point‖ ^ 2 =
      ratio * ((ratio - 2) * ‖gradient f (traj p f t).point‖ ^ 2) := by
    rw [← mul_assoc, hinv, one_mul]
  have h3 : ratio * (p.L * (p.Δ / T)) ≤ p.ε ^ 2 := by
    have e : ratio * (p.L * (p.Δ / T)) = ratio * p.L * p.Δ / T := by ring
    rw [e, div_le_iff₀ hTpos]
    linarith
  have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ ratio)
  linarith

lemma stepSize_pos (p : Params) (hL : 0 < p.L) (t : ℕ) : 0 < stepSize p t := by
  unfold stepSize
  apply div_pos _ hL
  have hlen := length_pos (level p) (le_max_left _ _)
  have hi : t % (steps (level p)).length < (steps (level p)).length := Nat.mod_lt _ (by omega)
  rw [List.getD_eq_getElem (steps (level p)) 1 hi]
  exact steps_positive _ _ (List.getElem_mem hi)

lemma allowed (p : Params) (hL : 0 < p.L) : gdFamily p (method p) :=
  ⟨State.point, State.best, State.bestNorm, State.count, stepSize p, stepSize_pos p hL,
    fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩

end Accuracy

end LongTails.Proofs.WeaklyConvexSilverExecution
