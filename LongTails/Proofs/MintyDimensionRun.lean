import LongTails.Proofs.MintyCutPotential
import LongTails.Proofs.MintySeparatingCut
import LongTails.Proofs.MintyDimensionBudget
import LongTails.Proofs.Execution

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyDimensionRun

open LongTails.Setups.FiniteDimensionalWeakMinty LongTails.Algorithms.DimensionAdaptiveMinty
open MintyCutPotential MintySeparatingCut

def trajectory (p : Params) (F : E p → E p) : ℕ → Round p
  | 0 => start p
  | n+1 =>
    let r := trajectory p F n
    let g := F (output p r)
    advance p r g (F (look p r g))

lemma execute_eq (p : Params) (F : E p → E p) (O : Oracle (E p) (E p))
    (ho : ∀ k v x, O.answer k (0,x) v = F x) (n : ℕ) (seed : (algorithm p).Seed)
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => 2*n) seed ξ = output p (trajectory p F n) := by
  rw [execute_eq_of_answer_eq O F (fun k x v => ho k v x), execute_iterate]
  let step := fun s : (algorithm p).State =>
    (algorithm p).update s (F ((algorithm p).query s).2)
  have he : step^[2*n] ((algorithm p).initial seed) = (trajectory p F n, none) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 2*(n+1) = 2*n+1+1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      rfl
  exact congrArg (algorithm p).output he

def progress (p : Params) (z : E p) (n : ℕ) (r : Round p) : Prop :=
  if localized p then
    r.x = center p r.cuts ∧ n/8 + potential p z r.cuts ≤ potential p z []
  else ‖r.x-z‖^2 + n * margin p ^ 2 ≤ p.R^2

lemma invariant (p : Params) (hp : spec.valid p) (F : E p → E p)
    (hlip : ∀ x y, ‖F x-F y‖ ≤ p.L * ‖x-y‖) (z : E p)
    (hz : ‖z-p.x0‖ ≤ p.R) (hm : ∀ x, -p.ρ*‖F x‖^2 ≤ ⟪F x,x-z⟫) (n : ℕ) :
    let r := trajectory p F n
    (r.done = true ∧ ‖F (output p r)‖ ≤ p.ε) ∨
      (r.done = false ∧ progress p (z-p.x0) n r) := by
  have hα := margin_pos p hp
  have hR := pos_of_mul_pos_right (hp.2.2.2.2.1.trans hp.2.2.2.2.2) hp.2.1.le
  induction n with
  | zero =>
    right
    constructor
    · rfl
    · by_cases hb : localized p
      · simp [progress, trajectory, start, hb]
      · simpa [progress, trajectory, start, hb, norm_sub_rev p.x0 z] using pow_le_pow_left₀ (norm_nonneg _) hz 2
  | succ n ih =>
    let r := trajectory p F n
    let g := F (output p r)
    let h := F (look p r g)
    change ((advance p r g h).done = true ∧ ‖F (output p (advance p r g h))‖ ≤ p.ε) ∨ _
    rcases ih with ⟨hd, hgood⟩ | ⟨hd, hprog⟩
    · left
      change r.done = true at hd
      simpa [advance, hd, output] using hgood
    · change r.done = false at hd
      by_cases hg : ‖g‖ ≤ p.ε
      · left
        have he : advance p r g h = {r with done := true} := by simp [advance, hd, hg]
        rw [he]
        exact ⟨rfl, hg⟩
      · right
        let u := ‖h‖⁻¹ • h
        obtain ⟨hu, hcut⟩ := separation p hp F hlip z hm r (lt_of_not_ge hg)
        change ‖u‖ = 1 at hu
        change margin p ≤ ⟪u,r.x-(z-p.x0)⟫ at hcut
        change (advance p r g h).done = false ∧ progress p (z-p.x0) (n+1) (advance p r g h)
        by_cases hb : localized p
        · change progress p (z-p.x0) n r at hprog
          simp only [progress, ite_eq_left hb] at hprog
          have hdec := decrease p hp.1 hR hα (z-p.x0) u hu r.cuts (hprog.1 ▸ hcut)
          rw [← hprog.1] at hdec
          simp [advance, hd, hg, hb, progress]
          change ((n:ℝ)+1)/8 + potential p (z-p.x0) (r.cuts ++ [(u,r.x)]) ≤ _
          linarith only [hdec, hprog.2]
        · change progress p (z-p.x0) n r at hprog
          simp only [progress, ite_eq_right hb] at hprog
          have he : ‖(r.x - margin p • u) - (z-p.x0)‖^2 =
              ‖r.x-(z-p.x0)‖^2 - 2*margin p*⟪u,r.x-(z-p.x0)⟫ + (margin p)^2 := by
            rw [show r.x - margin p • u - (z-p.x0) = (r.x-(z-p.x0)) - margin p • u by abel,
              norm_sub_sq_real, real_inner_smul_right, real_inner_comm (r.x-(z-p.x0)) u,
              norm_smul, Real.norm_eq_abs, abs_of_pos hα, hu, mul_one]
            ring
          simp [advance, hd, hg, hb, progress]
          change ‖r.x-margin p • u-(z-p.x0)‖^2 + _ ≤ _
          rw [he]
          nlinarith only [hprog, mul_le_mul_of_nonneg_left hcut hα.le]

lemma accuracy (p : Params) (hp : spec.valid p) (F : E p → E p)
    (hlip : ∀ x y, ‖F x-F y‖ ≤ p.L * ‖x-y‖) (z : E p)
    (hz : ‖z-p.x0‖ ≤ p.R) (hm : ∀ x, -p.ρ*‖F x‖^2 ≤ ⟪F x,x-z⟫) (n : ℕ)
    (hn : 1024*p.d*Real.log (1+(p.L*p.R/p.ε)^2/p.d) ≤ n) :
    ‖F (output p (trajectory p F n))‖ ≤ p.ε := by
  have hL := hp.2.1
  have hε := hp.2.2.2.2.1
  have hR := pos_of_mul_pos_right (hε.trans hp.2.2.2.2.2) hL.le
  have ht := div_pos (mul_pos hL hR) hε
  have hd : (0:ℝ) < p.d := by exact_mod_cast hp.1
  have hs := Real.sqrt_pos.mpr hd
  have hα := margin_pos p hp
  have hh := MintyDimensionBudget.rounds_suffice hp.1 ht n hn
  obtain h | ⟨_,h⟩ := invariant p hp F hlip z hz hm n
  · exact h.2
  · by_cases hc : localized p
    · simp only [progress, ite_eq_left hc] at h
      have hd' : (p.d : ℝ) ≤ (p.L*p.R/p.ε)^2 := hc
      have hs' : Real.sqrt p.d ≤ p.L*p.R/p.ε := by nlinarith [Real.sq_sqrt hd.le]
      have hsmall : margin p ≤ (geometry p).L * p.R := by
        change p.ε / (16*p.L) ≤ 4/Real.sqrt p.d * p.R
        apply (div_le_iff₀ (by positivity : 0 < 16*p.L)).mpr
        apply (mul_le_mul_iff_left₀ hs).mp
        field_simp
        nlinarith only [(le_div_iff₀ hε).mp hs', mul_pos hL hR]
      have hh' := cumulative_bound p hp.1 hR hα hsmall (z-p.x0) hz (trajectory p F n).cuts
      have he : 8*(geometry p).L*p.R/margin p = 512*(p.L*p.R/p.ε)/Real.sqrt p.d := by
        change 8*(4/Real.sqrt p.d)*p.R/(p.ε/(16*p.L)) = _
        field_simp
        ring
      rw [he] at hh'
      linarith only [hh.1 hd', h.2, hh']
    · simp only [progress, ite_eq_right hc] at h
      have hb := hh.2 (le_of_not_ge hc)
      have he : p.R^2 < (n:ℝ) * margin p ^ 2 := by
        unfold margin
        field_simp [hL.ne', hε.ne'] at hb ⊢
        nlinarith only [hb]
      linarith only [h, he, sq_nonneg ‖(trajectory p F n).x-(z-p.x0)‖]

lemma constant_output {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    (P : ProbabilityMeasure Ω) (F : E → E) (out : Ω → E) (x : E) (ε : ℝ)
    (he : ∀ w, out w = x) (hx : ‖F x‖ ≤ ε) :
    Integrable (fun w => ‖F (out w)‖) (P : Measure Ω) ∧
      (∫ w, ‖F (out w)‖ ∂(P : Measure Ω)) ≤ ε := by
  have h : (fun w => ‖F (out w)‖) = fun _ : Ω => ‖F x‖ := funext fun w => by rw [he]
  rw [h, integral_const, probReal_univ, one_smul]
  exact ⟨integrable_const _, hx⟩

end LongTails.Proofs.MintyDimensionRun
