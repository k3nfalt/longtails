import LongTails.Algorithms.AdaptiveSilverGd
import LongTails.Proofs.AdaptiveSilverLocal
import LongTails.Proofs.GdConvex
import Mathlib.Data.List.GetD
import LongTails.Proofs.AdaptiveSilverParams

namespace LongTails.Proofs.AdaptiveSilverExecution

open scoped RealInnerProductSpace
open OracleTemplate
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.SilverSchedule
open LongTails.Algorithms.AdaptiveSilverGd
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace
open LongTails.Proofs.AdaptiveSilverDynamics
open LongTails.Proofs.AdaptiveSilverLocal
open LongTails.Proofs.AdaptiveSilverParams

section Trajectory

variable (p : Params) (f : p.E → ℝ)

noncomputable def traj (t : ℕ) : State p.E :=
  (fun s => (method p).update s (gradient f ((method p).query s).2))^[t] ((method p).initial ())

lemma traj_succ (t : ℕ) :
    traj p f (t + 1) = (method p).update (traj p f t) (gradient f (traj p f t).point) := by
  unfold traj
  rw [Function.iterate_succ_apply']
  rfl

lemma traj_count (t : ℕ) : (traj p f t).count = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [traj_succ]; simp [method, ih]

lemma traj_zero : traj p f 0 = ⟨p.x0, 0, 0, p.x0, 0⟩ := rfl

lemma traj_zero_point : (traj p f 0).point = p.x0 := rfl

lemma traj_zero_phase : (traj p f 0).phase = 0 := rfl

lemma traj_point (t : ℕ) :
    (traj p f (t + 1)).point = (traj p f t).point -
      (rule p (traj p f t).phase (gradient f (traj p f t).point)).1 •
        gradient f (traj p f t).point := by
  rw [traj_succ]; rfl

lemma traj_phase (t : ℕ) :
    (traj p f (t + 1)).phase = (rule p (traj p f t).phase (gradient f (traj p f t).point)).2 := by
  rw [traj_succ]; rfl

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

end Trajectory

lemma blockLength_ge (p : Params) : 3 ≤ blockLength p := by
  unfold blockLength
  have h := steps_length (level p)
  have hK : 2 ≤ level p := le_max_left _ _
  have : 4 ≤ 2 ^ level p := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ level p := Nat.pow_le_pow_right (by norm_num) hK
  omega

lemma cyc_getElem (p : Params) (i : ℕ) (hi : i < (steps (level p) ++ steps (level p)).length) :
    (steps (level p) ++ steps (level p))[i] = (steps (level p)).getD (i % blockLength p) 1 := by
  have hn : blockLength p = (steps (level p)).length := rfl
  rw [List.length_append] at hi
  rw [List.getElem_append]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega), List.getD_eq_getElem _ _ (by omega)]
  · rw [hn, show i % (steps (level p)).length = i - (steps (level p)).length by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]
    rw [List.getD_eq_getElem _ _ (by omega)]

section Cycle

variable {p : Params} {f : p.E → ℝ}

lemma cycle_track (T : ℕ) (h0 : (traj p f T).phase = 0)
    (hG : ‖gradient f (traj p f T).point‖ ≤ threshold p) :
    ∀ k, k + 1 ≤ 2 * blockLength p →
      (∀ j, 1 ≤ j → j < k + 1 → ‖gradient f (traj p f (T + j)).point‖ ≤ abortThreshold p) →
      (traj p f (T + (k + 1))).point = run (fun y => (1 / p.L) • gradient f y)
        ((steps (level p) ++ steps (level p)).take (k + 1)) (traj p f T).point ∧
      (traj p f (T + (k + 1))).phase = (if k + 1 < 2 * blockLength p then k + 1 else 0) := by
  have hn3 := blockLength_ge p
  have hlen : (steps (level p) ++ steps (level p)).length = 2 * blockLength p := by
    rw [List.length_append]; unfold blockLength; ring
  intro k
  induction k with
  | zero =>
    intro hk _
    have hr : rule p (traj p f T).phase (gradient f (traj p f T).point) = (silverStep p 0, 1) := by
      rw [h0]; simp [rule, not_lt.mpr hG]
    have hx : (traj p f (T + 1)).point = (traj p f T).point -
        silverStep p 0 • gradient f (traj p f T).point := by
      rw [traj_point, hr]
    refine ⟨?_, ?_⟩
    · rw [show T + (0 + 1) = T + 1 by ring, hx,
        run_take_succ (fun y => (1 / p.L) • gradient f y) (steps (level p) ++ steps (level p))
          (traj p f T).point 0 (by omega), cyc_getElem p 0 (by omega)]
      simp only [List.take_zero, run, silverStep, smul_smul]
      congr 2
      ring
    · rw [show T + (0 + 1) = T + 1 by ring, traj_phase, hr]
      simp [show 0 + 1 < 2 * blockLength p by omega]
  | succ k ih =>
    intro hk hj
    obtain ⟨ihp, ihφ⟩ := ih (by omega) (fun j h1 h2 => hj j h1 (by omega))
    have hphase : (traj p f (T + (k + 1))).phase = k + 1 := by
      rw [ihφ]; simp [show k + 1 < 2 * blockLength p by omega]
    have hb := hj (k + 1) (by omega) (by omega)
    have hr : rule p (traj p f (T + (k + 1))).phase (gradient f (traj p f (T + (k + 1))).point) =
        (silverStep p (k + 1), if k + 1 + 1 < 2 * blockLength p then k + 1 + 1 else 0) := by
      rw [hphase]; simp [rule, not_lt.mpr hb]
    have hx : (traj p f (T + (k + 1) + 1)).point = (traj p f (T + (k + 1))).point -
        silverStep p (k + 1) • gradient f (traj p f (T + (k + 1))).point := by
      rw [traj_point, hr]
    refine ⟨?_, ?_⟩
    · rw [show T + (k + 1 + 1) = T + (k + 1) + 1 by ring, hx, ihp,
        run_take_succ (fun y => (1 / p.L) • gradient f y) (steps (level p) ++ steps (level p))
          (traj p f T).point (k + 1) (by omega), cyc_getElem p (k + 1) (by omega)]
      simp only [silverStep, smul_smul]
      congr 2
      ring
    · rw [show T + (k + 1 + 1) = T + (k + 1) + 1 by ring, traj_phase, hr]

end Cycle

section Episode

structure Adm (p : Params) (f : p.E → ℝ) : Prop where
  hL : 0 < p.L
  hρ : 0 ≤ p.ρ
  hε : 0 < p.ε
  hf : ContDiff ℝ 2 f
  lip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖
  hA : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖

variable {p : Params} {f : p.E → ℝ}

lemma hasGrad (h : Adm p f) (x : p.E) : HasGradientAt f (gradient f x) x :=
  ((h.hf.differentiable (by norm_num)) x).hasGradientAt

lemma hyp_of (h : Adm p f) (x0 : p.E) : Hyp f p.L p.ρ x0 where
  hL := h.hL
  hρ := h.hρ
  hf := fun x => by
    have := (hasGrad h x).hasFDerivAt
    convert this using 1
    ext v
    simp
  hg := fun x => ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one h.hf).differentiable
    (by norm_num) x).hasFDerivAt
  hA := h.hA
  hsym := fun u v => OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric h.hf x0 u v
  hH := by
    have hl : LipschitzWith ⟨p.L, h.hL.le⟩ (gradient f) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact h.lip x y
    exact norm_fderiv_le_of_lipschitz ℝ hl (x₀ := x0)

lemma spectral (h : Adm p f) (x0 : p.E) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ p.E)) ℝ p.E) (eig : Fin (Module.finrank ℝ p.E) → ℝ),
      ∀ j v, ⟪b j, fderiv ℝ (gradient f) x0 v⟫ = eig j * ⟪b j, v⟫ := by
  have hs := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric h.hf x0
  refine ⟨hs.eigenvectorBasis rfl, hs.eigenvalues rfl, fun j v => ?_⟩
  simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq,
    ContinuousLinearMap.coe_coe] using hs.eigenvectorBasis_apply_self_apply rfl v j

lemma descent_step (h : Adm p f) (x : p.E) :
    f (x - (1 / p.L) • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * p.L) :=
  OracleTemplate.Gradient.descent h.hL (hasGrad h) h.lip x

lemma probe_rule (T : ℕ) (hφ : (traj p f T).phase = 0)
    (hg : threshold p < ‖gradient f (traj p f T).point‖) :
    rule p (traj p f T).phase (gradient f (traj p f T).point) = (1 / p.L, 0) := by
  rw [hφ]; simp [rule, hg]

lemma abort_rule (T : ℕ) {m : ℕ} (hφ : (traj p f T).phase = m) (hm : m ≠ 0)
    (hg : abortThreshold p < ‖gradient f (traj p f T).point‖) :
    rule p (traj p f T).phase (gradient f (traj p f T).point) = (1 / p.L, 0) := by
  rw [hφ]; simp [rule, hm, hg]

lemma episode (h : Adm p f) (T : ℕ) (hφ : (traj p f T).phase = 0)
    (hno : ∀ t, T ≤ t → t < T + 2 * blockLength p → p.ε < ‖gradient f (traj p f t).point‖) :
    ∃ T', T < T' ∧ T' ≤ T + 2 * blockLength p ∧ (traj p f T').phase = 0 ∧
      ((T' - T : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L)) ≤
        f (traj p f T).point - f (traj p f T').point := by
  have hL := h.hL
  have hε := h.hε
  have hn3 := blockLength_ge p
  have hG0 : 0 ≤ threshold p := hε.le.trans (threshold_ge p hε)
  have hεT := hno T le_rfl (by omega)
  by_cases hgT : threshold p < ‖gradient f (traj p f T).point‖
  · refine ⟨T + 1, by omega, by omega, ?_, ?_⟩
    · rw [traj_phase, probe_rule T hφ hgT]
    · have hx : (traj p f (T + 1)).point = (traj p f T).point -
          (1 / p.L) • gradient f (traj p f T).point := by
        rw [traj_point, probe_rule T hφ hgT]
      rw [hx, show T + 1 - T = 1 by omega]
      have hd := descent_step h (traj p f T).point
      have hsq : threshold p ^ 2 ≤ ‖gradient f (traj p f T).point‖ ^ 2 :=
        pow_le_pow_left₀ hG0 hgT.le 2
      have : threshold p ^ 2 / (2 * p.L) ≤ ‖gradient f (traj p f T).point‖ ^ 2 / (2 * p.L) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      push_cast
      linarith
  · have hgT' : ‖gradient f (traj p f T).point‖ ≤ threshold p := not_lt.mp hgT
    have hGε : p.ε < threshold p := lt_of_lt_of_le hεT hgT'
    obtain ⟨hgood, hG2⟩ : good p ∧ threshold p ^ 2 =
        p.ε ^ 2 * blockSum p / (25 * blockLength p) := by
      rcases threshold_cases p with h' | h'
      · exact absurd h' (ne_of_gt hGε)
      · exact h'
    have hσ4 := blockSum_ge p
    have hn3r := blockLength_three p
    have hRge := ratio_pow_ge p
    have hsq := ratio_square
    have hrat := ratio_gt_two
    have hlc := lc_level p hgood
    rw [pow_mul'] at hlc
    have hMg0 : 0 ≤ abortThreshold p := by unfold abortThreshold; positivity
    obtain ⟨c1, c2, c3, b1, b2, b3⟩ := constraints (σ := blockSum p) (R := ratio ^ level p)
      (n := blockLength p) (ρ := p.ρ) (ε := p.ε) (L := p.L) (G := threshold p)
      (Mg := abortThreshold p) (by linarith) (by rw [blockSum_eq]; linarith) (by nlinarith)
      hn3r (by nlinarith) h.hρ hε hL hG0 hMg0 hlc hG2 (abort_sq p)
    have hGM : threshold p ≤ abortThreshold p := by linarith
    have hσdef : blockSum p = (steps (level p)).sum := rfl
    have hndef : blockLength p = (steps (level p)).length := rfl
    have hlen : (steps (level p) ++ steps (level p)).length = 2 * blockLength p := by
      rw [List.length_append, hndef]; ring
    obtain ⟨b, eig, hc⟩ := spectral h (traj p f T).point
    have hyp := hyp_of h (traj p f T).point
    have hK := level_ge p
    classical
    by_cases hab : ∃ j, 1 ≤ j ∧ j < 2 * blockLength p ∧
        abortThreshold p < ‖gradient f (traj p f (T + j)).point‖
    · let m := Nat.find hab
      have hm : 1 ≤ m ∧ m < 2 * blockLength p ∧
          abortThreshold p < ‖gradient f (traj p f (T + m)).point‖ := Nat.find_spec hab
      have hmin : ∀ j, 1 ≤ j → j < m → ‖gradient f (traj p f (T + j)).point‖ ≤ abortThreshold p := by
        intro j h1 h2
        have := Nat.find_min hab h2
        push Not at this
        exact this h1 (by omega)
      obtain ⟨hpt, hph⟩ := cycle_track (f := f) T hφ hgT' (m - 1) (by omega)
        (fun j h1 h2 => hmin j h1 (by omega))
      rw [show m - 1 + 1 = m by omega] at hpt hph
      simp only [hm.2.1, ↓reduceIte] at hph
      have habort := aborted hyp b eig hc hK (G := threshold p) (Mg := abortThreshold p) hgT'
        (m := m) (by omega) (fun t ht => by
          rcases Nat.eq_zero_or_pos t with rfl | htp
          · simpa [run] using hgT'.trans hGM
          · obtain ⟨hp', -⟩ := cycle_track (f := f) T hφ hgT' (t - 1) (by omega)
              (fun j h1 h2 => hmin j h1 (by omega))
            rw [show t - 1 + 1 = t by omega] at hp'
            rw [← hp']
            exact hmin t htp ht)
        (by rw [← hσdef]; exact b1) b2 (by rw [← hσdef]; exact b3)
      rw [← hpt] at habort
      have hr := abort_rule (f := f) (T + m) hph (by omega) hm.2.2
      refine ⟨T + m + 1, by omega, by omega, ?_, ?_⟩
      · rw [traj_phase, hr]
      · have hx : (traj p f (T + m + 1)).point = (traj p f (T + m)).point -
            (1 / p.L) • gradient f (traj p f (T + m)).point := by
          rw [traj_point, hr]
        rw [hx, show T + m + 1 - T = m + 1 by omega]
        have hd := descent_step h (traj p f (T + m)).point
        have hsq' : abortThreshold p ^ 2 ≤ ‖gradient f (traj p f (T + m)).point‖ ^ 2 :=
          pow_le_pow_left₀ hMg0 hm.2.2.le 2
        have hA2 := abort_sq p
        have hmr : ((m + 1 : ℕ) : ℝ) ≤ 2 * blockLength p := by
          have : m + 1 ≤ 2 * blockLength p := by omega
          exact_mod_cast this
        have hkey : ((m + 1 : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L)) ≤
            3 * abortThreshold p ^ 2 / (8 * p.L) := by
          rw [hA2]
          have hG2' : 0 ≤ threshold p ^ 2 := sq_nonneg _
          rw [show ((m + 1 : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L)) =
              ((m + 1 : ℕ) : ℝ) * threshold p ^ 2 / (2 * p.L) by ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hmr hG2', hL]
        have : abortThreshold p ^ 2 / (2 * p.L) ≤
            ‖gradient f (traj p f (T + m)).point‖ ^ 2 / (2 * p.L) :=
          div_le_div_of_nonneg_right hsq' (by positivity)
        have h8 : abortThreshold p ^ 2 / (2 * p.L) - abortThreshold p ^ 2 / (8 * p.L) =
            3 * abortThreshold p ^ 2 / (8 * p.L) := by field_simp; ring
        linarith
    · push Not at hab
      obtain ⟨hpt, hph⟩ := cycle_track (f := f) T hφ hgT' (2 * blockLength p - 1) (by omega)
        (fun j h1 h2 => hab j h1 (by omega))
      rw [show 2 * blockLength p - 1 + 1 = 2 * blockLength p by omega] at hpt hph
      simp only [lt_irrefl, ↓reduceIte] at hph
      rw [← hlen, List.take_length] at hpt
      obtain ⟨hpn, -⟩ := cycle_track (f := f) T hφ hgT' (blockLength p - 1) (by omega)
        (fun j h1 h2 => hab j h1 (by omega))
      rw [show blockLength p - 1 + 1 = blockLength p by omega, hndef,
        List.take_left' rfl] at hpn
      have hcomp := completed hyp b eig hc hK (G := threshold p) (Mg := abortThreshold p)
        (ε := p.ε) hε.le hgT' (fun t ht => by
          rcases Nat.eq_zero_or_pos t with rfl | htp
          · simpa [run] using hgT'.trans hGM
          · obtain ⟨hp', -⟩ := cycle_track (f := f) T hφ hgT' (t - 1) (by omega)
              (fun j h1 h2 => hab j h1 (by omega))
            rw [show t - 1 + 1 = t by omega] at hp'
            rw [← hp']
            exact hab t htp (by omega))
        (by rw [← hpn]; exact (hno _ (by omega) (by omega)).le)
        (by rw [← hσdef]; exact c1) (by rw [← hσdef]; exact c2) (by rw [← hσdef]; exact c3)
      rw [← hpt, hlen] at hcomp
      refine ⟨T + 2 * blockLength p, by omega, le_rfl, hph, ?_⟩
      rw [show T + 2 * blockLength p - T = 2 * blockLength p by omega]
      have heq : ((2 * blockLength p : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L)) =
          (steps (level p)).sum * p.ε ^ 2 / (25 * p.L) := by
        rw [hG2, ← hσdef]
        push_cast
        field_simp
      rw [heq]
      exact hcomp

lemma reach (h : Adm p f) (hΔ : ∀ x, f p.x0 - f x ≤ p.Δ) (B : ℕ)
    (hB : p.Δ < ((B - 2 * blockLength p : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L))) :
    ∃ t < B, ‖gradient f (traj p f t).point‖ ≤ p.ε := by
  by_contra hcon
  push Not at hcon
  have hr0 : 0 ≤ threshold p ^ 2 / (2 * p.L) := by
    have := h.hL; positivity
  have key : ∀ k, ∃ T, (traj p f T).phase = 0 ∧
      (T : ℝ) * (threshold p ^ 2 / (2 * p.L)) ≤ f p.x0 - f (traj p f T).point ∧
      min k (B - 2 * blockLength p) ≤ T := by
    intro k
    induction k with
    | zero => exact ⟨0, rfl, by simp [traj_zero_point], by simp⟩
    | succ k ih =>
      obtain ⟨T, hφ, hgood, hT⟩ := ih
      by_cases hdone : min (k + 1) (B - 2 * blockLength p) ≤ T
      · exact ⟨T, hφ, hgood, hdone⟩
      · push Not at hdone
        have hTB : T + 2 * blockLength p ≤ B := by omega
        obtain ⟨T', h1, h2, h3, h4⟩ := episode h T hφ (fun t ht1 ht2 => hcon t (by omega))
        refine ⟨T', h3, ?_, by omega⟩
        have : ((T' - T : ℕ) : ℝ) = (T' : ℝ) - T := by
          rw [Nat.cast_sub h1.le]
        rw [this] at h4
        nlinarith
  obtain ⟨T, -, hgood, hT⟩ := key B
  have hBT : B - 2 * blockLength p ≤ T := by omega
  have h1 : ((B - 2 * blockLength p : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L)) ≤
      (T : ℝ) * (threshold p ^ 2 / (2 * p.L)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hBT) hr0
  have h2 := hΔ (traj p f T).point
  linarith

end Episode

section Allowed

lemma rule_pos (p : Params) (hL : 0 < p.L) (phase : ℕ) (r : p.E) : 0 < (rule p phase r).1 := by
  have hs : ∀ i, 0 < silverStep p i := by
    intro i
    unfold silverStep
    apply div_pos _ hL
    have hn := blockLength_ge p
    have hi : i % blockLength p < (steps (level p)).length := Nat.mod_lt _ (by omega)
    rw [List.getD_eq_getElem (steps (level p)) 1 hi]
    exact steps_positive _ _ (List.getElem_mem hi)
  unfold rule
  split_ifs <;> simp [hs, hL]

lemma allowed (p : Params) (hL : 0 < p.L) : adaptiveGdFamily p (method p) :=
  ⟨State.point, State.best, State.bestNorm, State.count, fun s r => (rule p s.phase r).1,
    fun s r => rule_pos p hL s.phase r, fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl,
    fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩

end Allowed

end LongTails.Proofs.AdaptiveSilverExecution
