import LongTails.Proofs.SelfConcordantBFGSRate
import Mathlib.Algebra.Order.Chebyshev

open Set Matrix Finset

namespace LongTails.Proofs.SelfConcordantBFGSAccuracy

open OracleTemplate LongTails.Setups.SelfConcordantBFGS LongTails.Proofs.SelfConcordantBFGSExecution
open LongTails.Proofs.SelfConcordantSegment LongTails.Proofs.SelfConcordantCalculus
open LongTails.Proofs.BFGSLogPotential LongTails.Proofs.BFGSLogDet LongTails.Proofs.BFGSLogStep
open LongTails.Proofs.BFGSMatrix
open LongTails.Setups.LinearPredictorBFGS (bfgsUpdate)
open LongTails.Proofs.SelfConcordantBFGSRate

variable {q : Params} {I : Instance q.toPublic} {O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1}
  {ξ : (k : ℕ) → O.Seed k}

noncomputable def sv (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
    (ξ : (k : ℕ) → O.Seed k) (n : ℕ) : Vec q.d :=
  (answer q O ξ n).1 • direction (run q O ξ n).B (run q O ξ n).g

noncomputable def rv (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
    (ξ : (k : ℕ) → O.Seed k) (D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ) (n : ℕ) : ℝ :=
  √(D2f (run q O ξ n).x (sv q O ξ n) (sv q O ξ n))

noncomputable def av (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
    (ξ : (k : ℕ) → O.Seed k) (D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ) (n : ℕ) : ℝ :=
  if rv q O ξ D2f n ≤ q.c1 / 32 then 8 * rv q O ξ D2f n else 6 * q.Δ + 6

noncomputable def Qv (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
    (ξ : (k : ℕ) → O.Seed k) (D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ) (n : ℕ) :
    Matrix (Fin q.d) (Fin q.d) ℝ :=
  segQ D2f (run q O ξ n).x (sv q O ξ n)

noncomputable def QP (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
    (ξ : (k : ℕ) → O.Seed k) (D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ) (n : ℕ) :
    Matrix (Fin q.d) (Fin q.d) ℝ :=
  if n = 0 then hessMatrix (D2f q.x0) else Qv q O ξ D2f (n - 1)

lemma av_nonneg (q : Params) (O : Oracle (Vec q.d × Vec q.d) (ℝ × Vec q.d) 1)
    (ξ : (k : ℕ) → O.Seed k) (D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ) (hΔ : 0 ≤ q.Δ)
    (n : ℕ) : 0 ≤ av q O ξ D2f n := by
  unfold av; split_ifs
  · have := Real.sqrt_nonneg (D2f (run q O ξ n).x (sv q O ξ n) (sv q O ξ n))
    unfold rv; linarith
  · linarith

lemma quad_comp {Df : Vec q.d → Vec q.d →L[ℝ] ℝ} {D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ}
    {D3f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ}
    (hSC : SelfConcordantOn I.D I.f Df D2f D3f) {x s : Vec q.d}
    (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, x + τ • s ∈ I.D) {a : ℝ} (hb : SegBound D2f x s a)
    {τ' : ℝ} (hτ' : τ' ∈ Icc (0 : ℝ) 1) (v : Vec q.d) :
    v ⬝ᵥ (segQ D2f x s *ᵥ v) ≤ Real.exp a * (v ⬝ᵥ (hessMatrix (D2f (x + τ' • s)) *ᵥ v)) ∧
      v ⬝ᵥ (hessMatrix (D2f (x + τ' • s)) *ᵥ v) ≤ Real.exp a * (v ⬝ᵥ (segQ D2f x s *ᵥ v)) := by
  rw [← quad_eq (D2f := D2f) v]
  exact ⟨segQ_le hSC hseg hb hτ' v, le_segQ hSC hseg hb hτ' v⟩

set_option maxHeartbeats 4000000 in
theorem accuracy {Df : Vec q.d → Vec q.d →L[ℝ] ℝ}
    {D2f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ}
    {D3f : Vec q.d → Vec q.d →L[ℝ] Vec q.d →L[ℝ] Vec q.d →L[ℝ] ℝ}
    (hc1 : 0 < q.c1) (hc12 : q.c1 < q.c2) (hc2 : q.c2 < 1) (hB0 : Matrix.PosDef q.B0)
    (hΔ0 : 0 ≤ q.Δ)
    (hΦ0 : 0 ≤ q.Φ0) (hε : 0 < q.ε) (hD : IsOpen I.D) (hconv : Convex ℝ I.D)
    (hx0 : q.x0 ∈ I.D) (hSC : SelfConcordantOn I.D I.f Df D2f D3f)
    (hlow : ∀ x ∈ I.D, I.f q.x0 - q.Δ ≤ I.f x)
    (hmis : mismatch q.B0 (hessMatrix (D2f q.x0)) ≤ q.Φ0) (horc : OracleOK q I O Df)
    {xstar : Vec q.d} (hxs : xstar ∈ I.D) (K : ℕ)
    (hK : 2 ^ 21 * (q.d + 1) * (q.Δ + 1) * ((q.Δ + 1) / (q.c1 ^ 3 * min q.c1 (1 - q.c2) ^ 2) +
      (q.d + 1) / (q.c1 * min q.c1 (1 - q.c2) ^ 4)) + 10 * q.Φ0 / min q.c1 (1 - q.c2) ^ 2 +
      4 * Real.log (64 + 2 / q.ε) / min q.c1 (1 - q.c2) < K) :
    (run q O ξ K).x ∈ I.D ∧ I.f (run q O ξ K).x - I.f xstar ≤ q.ε := by
  have hinv := inv_run (ξ := ξ) hB0 hc1 hc2 hx0 horc
  refine ⟨(hinv K).1, ?_⟩
  by_cases hz : ∃ n ≤ K, (run q O ξ n).g = 0
  · obtain ⟨n, hnK, hg⟩ := hz
    have hpers : ∀ m, n ≤ m → (run q O ξ m).x = (run q O ξ n).x ∧ (run q O ξ m).g = 0 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact ⟨rfl, hg⟩
      | succ m hm ih =>
        obtain ⟨hx, hrep, -, -⟩ := hinv m
        have := zero_persist horc hx hrep ih.2
        exact ⟨this.1.trans ih.1, this.2⟩
    obtain ⟨hxK, -⟩ := hpers K hnK
    obtain ⟨hxn, hrepn, -, -⟩ := hinv n
    have hfo := first_order hSC hconv hxn hxs
    rw [hrepn, hg, zero_dotProduct, add_zero] at hfo
    rw [hxK]
    linarith
  push Not at hz
  set α := q.c1 with hα
  set Δ := q.Δ with hΔ
  set δ := min α (1 - q.c2) with hδ
  set k : ℕ := ⌈1 / δ⌉₊ + 2 with hk
  have hδ0 : 0 < δ := lt_min hc1 (by linarith)
  have hδ2 : δ ≤ 1 / 2 := by
    by_contra h; push Not at h
    have h1 : 1 / 2 < α := lt_of_lt_of_le h (min_le_left _ _)
    have h2 : 1 / 2 < 1 - q.c2 := lt_of_lt_of_le h (min_le_right _ _)
    linarith
  have hδα : δ ≤ α := min_le_left _ _
  have hk1 : 1 ≤ k := by omega
  have hkR : (k : ℝ) ≤ 1 / δ + 3 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / δ)
    simp only [hk]; push_cast; linarith
  have hlg0 : 0 ≤ Real.log (64 + 2 / q.ε) := Real.log_nonneg (by
    have : 0 ≤ 2 / q.ε := by positivity
    linarith)
  have hBud0 : 0 ≤ 2 ^ 21 * (q.d + 1) * (q.Δ + 1) * ((q.Δ + 1) / (q.c1 ^ 3 * δ ^ 2) +
      (q.d + 1) / (q.c1 * δ ^ 4)) + 10 * q.Φ0 / δ ^ 2 + 4 * Real.log (64 + 2 / q.ε) / δ := by
    have h1 : 0 ≤ 2 ^ 21 * (q.d + 1) * (q.Δ + 1) * ((q.Δ + 1) / (q.c1 ^ 3 * δ ^ 2) +
        (q.d + 1) / (q.c1 * δ ^ 4)) := by positivity
    have h2 : 0 ≤ 10 * q.Φ0 / δ ^ 2 := by positivity
    have h3 : 0 ≤ 4 * Real.log (64 + 2 / q.ε) / δ := div_nonneg (by linarith) hδ0.le
    linarith
  have hKpos : 0 < K := by
    have : (0 : ℝ) < K := lt_of_le_of_lt hBud0 hK
    exact_mod_cast this
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  have hfacts : ∀ n < m + 1,
      SegBound D2f (run q O ξ n).x (sv q O ξ n) (av q O ξ D2f n) ∧ (Qv q O ξ D2f n).PosDef ∧
      U k (bfgsUpdate (run q O ξ n).B (sv q O ξ n) ((answer q O ξ n).2 - (run q O ξ n).g))
          (Qv q O ξ D2f n) (answer q O ξ n).2 ≤
        U k (run q O ξ n).B (Qv q O ξ D2f n) (run q O ξ n).g +
          (if rv q O ξ D2f n ≤ α / 32 then -(δ / 2) else 24 * Δ + 37) ∧
      (if rv q O ξ D2f n ≤ α / 32 then α * rv q O ξ D2f n ^ 2 / 4 else α ^ 3 / 4096) ≤
        I.f (run q O ξ n).x - I.f (run q O ξ (n + 1)).x := by
    intro n hn
    obtain ⟨hx, hrep, hB, hf⟩ := hinv n
    have hg0 := hz n hn.le
    have h := answer_spec q O ξ (fun r x v => x ∈ I.D → Df x v ≤ 0 →
      x + r.1 • v ∈ I.D ∧ (∀ w, Df (x + r.1 • v) w = r.2 ⬝ᵥ w) ∧ (Df x v < 0 → 0 < r.1 ∧
        I.f (x + r.1 • v) ≤ I.f x + q.c1 * r.1 * Df x v ∧ q.c2 * Df x v ≤ Df (x + r.1 • v) v))
      (fun hist x v seed => horc hist x v seed) n
    have hdesc : Df (run q O ξ n).x (direction (run q O ξ n).B (run q O ξ n).g) < 0 := by
      rw [hrep, dir_pairing]
      have := posDef_quad_pos hB.inv hg0
      linarith
    obtain ⟨hmem, hrep', hwolfe⟩ := h hx hdesc.le
    obtain ⟨hη, harm, hcurv⟩ := hwolfe hdesc
    have hg'0 : (answer q O ξ n).2 ≠ 0 := by
      rw [← run_g_succ n]; exact hz (n + 1) (by omega)
    have hps := pure_step hSC hD hconv hc1 hc12 hc2 hΔ0 hlow hx hf hB hrep hg0 hη hmem hrep'
      hg'0 harm hcurv
    obtain ⟨h1, h2, -, h4, h5⟩ := hps
    have hxs : (run q O ξ (n + 1)).x = (run q O ξ n).x + sv q O ξ n := run_x_succ n
    refine ⟨h1, h2, h4, ?_⟩
    rw [hxs]; exact h5
  have hsegs : ∀ n < m + 1, ∀ τ ∈ Icc (0 : ℝ) 1, (run q O ξ n).x + τ • sv q O ξ n ∈ I.D := by
    intro n hn
    have hxn := (hinv n).1
    have hxn1 := (hinv (n + 1)).1
    rw [run_x_succ n] at hxn1
    intro τ hτ
    have := seg_mem hconv hxn hxn1 τ hτ
    simpa [sv] using this
  have hend1 : ∀ n, (run q O ξ n).x + (1 : ℝ) • sv q O ξ n = (run q O ξ (n + 1)).x := fun n => by
    rw [one_smul, run_x_succ n]; rfl
  have hend0 : ∀ n, (run q O ξ n).x + (0 : ℝ) • sv q O ξ n = (run q O ξ n).x := fun n => by simp
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hH : ∀ n, (hessMatrix (D2f (run q O ξ n).x)).PosDef := fun n =>
    hessMatrix_posDef hSC hD (hinv n).1
  set Kc : ℝ := 3 * (k : ℝ) * q.d + 1 with hKc
  set ℓv : ℕ → ℝ := fun n => (if n = 0 then 0 else av q O ξ D2f (n - 1)) + av q O ξ D2f n
    with hℓv
  have hswitch : ∀ n < m + 1, U k (run q O ξ n).B (Qv q O ξ D2f n) (run q O ξ n).g ≤
      U k (run q O ξ n).B (QP q O ξ D2f n) (run q O ξ n).g + Kc * ℓv n := by
    intro n hn
    obtain ⟨hSBn, hQn, -, -⟩ := hfacts n hn
    have hB := (hinv n).2.2.1
    have hg0 := hz n hn.le
    rcases n with _ | n
    · have hx0' : (run q O ξ 0).x = q.x0 := by rw [run_zero]
      have hc := fun v => quad_comp hSC (hsegs 0 hn) hSBn h0mem v
      rw [hend0, hx0'] at hc
      have hQP : QP q O ξ D2f 0 = hessMatrix (D2f q.x0) := by simp [QP]
      rw [hQP]
      have := U_switch hB (hx0' ▸ hH 0) hQn (av_nonneg q O ξ D2f hΔ0 0)
        (fun v => (hc v).1) (fun v => (hc v).2) k hg0
      simp only [hℓv]
      simpa [hKc] using this
    · have hQP : QP q O ξ D2f (n + 1) = Qv q O ξ D2f n := by simp [QP]
      rw [hQP]
      obtain ⟨hSBp, hQp, -, -⟩ := hfacts n (by omega)
      have hcp := fun v => quad_comp hSC (hsegs n (by omega)) hSBp h1mem v
      have hcn := fun v => quad_comp hSC (hsegs (n + 1) hn) hSBn h0mem v
      rw [hend1] at hcp
      rw [hend0] at hcn
      have hℓ0 : 0 ≤ av q O ξ D2f n + av q O ξ D2f (n + 1) :=
        add_nonneg (av_nonneg q O ξ D2f hΔ0 n) (av_nonneg q O ξ D2f hΔ0 (n + 1))
      have hexp : Real.exp (av q O ξ D2f n + av q O ξ D2f (n + 1)) =
          Real.exp (av q O ξ D2f n) * Real.exp (av q O ξ D2f (n + 1)) := Real.exp_add _ _
      have := U_switch hB hQp hQn hℓ0
        (fun v => by
          rw [hexp]
          calc v ⬝ᵥ (Qv q O ξ D2f (n + 1) *ᵥ v) ≤ Real.exp (av q O ξ D2f (n + 1)) *
                (v ⬝ᵥ (hessMatrix (D2f (run q O ξ (n + 1)).x) *ᵥ v)) := (hcn v).1
            _ ≤ Real.exp (av q O ξ D2f (n + 1)) * (Real.exp (av q O ξ D2f n) *
                (v ⬝ᵥ (Qv q O ξ D2f n *ᵥ v))) :=
                mul_le_mul_of_nonneg_left (hcp v).2 (Real.exp_pos _).le
            _ = _ := by ring)
        (fun v => by
          rw [hexp]
          calc v ⬝ᵥ (Qv q O ξ D2f n *ᵥ v) ≤ Real.exp (av q O ξ D2f n) *
                (v ⬝ᵥ (hessMatrix (D2f (run q O ξ (n + 1)).x) *ᵥ v)) := (hcp v).1
            _ ≤ Real.exp (av q O ξ D2f n) * (Real.exp (av q O ξ D2f (n + 1)) *
                (v ⬝ᵥ (Qv q O ξ D2f (n + 1) *ᵥ v))) :=
                mul_le_mul_of_nonneg_left (hcn v).2 (Real.exp_pos _).le
            _ = _ := by ring) k hg0
      simp only [hℓv, Nat.add_sub_cancel, ite_eq_right (Nat.succ_ne_zero n)]
      simpa [hKc] using this
  set incv : ℕ → ℝ := fun n => if rv q O ξ D2f n ≤ α / 32 then -(δ / 2) else 24 * Δ + 37
    with hincv
  set P : ℕ → ℝ := fun n => U k (run q O ξ n).B (QP q O ξ D2f n) (run q O ξ n).g with hP
  have hPstep : ∀ n < m + 1, P (n + 1) ≤ P n + incv n + Kc * ℓv n := by
    intro n hn
    obtain ⟨-, -, hpot, -⟩ := hfacts n hn
    have hsw := hswitch n hn
    have hQP : QP q O ξ D2f (n + 1) = Qv q O ξ D2f n := by simp [QP]
    simp only [hP, hincv]
    rw [hQP, run_B_succ, run_g_succ]
    exact (hpot.trans (by linarith [hsw]))
  have hPsum : ∀ j ≤ m + 1, P j ≤ P 0 + ∑ n ∈ range j, (incv n + Kc * ℓv n) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ]
      have := hPstep j (by omega)
      have := ih (by omega)
      linarith
  have hPK := hPsum (m + 1) le_rfl
  have hsumℓ : ∑ n ∈ range (m + 1), ℓv n ≤ 2 * ∑ n ∈ range (m + 1), av q O ξ D2f n := by
    simp only [hℓv, sum_add_distrib, sum_shift]
    have : ∑ j ∈ range m, av q O ξ D2f j ≤ ∑ j ∈ range (m + 1), av q O ξ D2f j := by
      rw [sum_range_succ]; linarith [av_nonneg q O ξ D2f hΔ0 m]
    linarith
  obtain ⟨hxK, hrepK, hBK, -⟩ := hinv (m + 1)
  have hgK := hz (m + 1) le_rfl
  obtain ⟨hSBm, hQm, -, -⟩ := hfacts m (by omega)
  have hlowU := U_lower hBK hQm k hk1 hgK
  have hQPK : QP q O ξ D2f (m + 1) = Qv q O ξ D2f m := by simp [QP]
  have hPKdef : P (m + 1) = U k (run q O ξ (m + 1)).B (Qv q O ξ D2f m) (run q O ξ (m + 1)).g := by
    simp only [hP, hQPK]
  set lam2 := (run q O ξ (m + 1)).g ⬝ᵥ ((hessMatrix (D2f (run q O ξ (m + 1)).x))⁻¹ *ᵥ
    (run q O ξ (m + 1)).g) with hlam2
  have hlam2pos : 0 < lam2 := posDef_quad_pos (hH (m + 1)).inv hgK
  have hcm := fun v => quad_comp hSC (hsegs m (by omega)) hSBm h1mem v
  rw [hend1] at hcm
  have hinvQ : Real.exp (-(av q O ξ D2f m)) * lam2 ≤
      (run q O ξ (m + 1)).g ⬝ᵥ ((Qv q O ξ D2f m)⁻¹ *ᵥ (run q O ξ (m + 1)).g) := by
    have hle : LeQ (Qv q O ξ D2f m) (Real.exp (av q O ξ D2f m) •
        hessMatrix (D2f (run q O ξ (m + 1)).x)) := fun v => by
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul]; exact (hcm v).1
    have := inv_anti hQm ((hH (m + 1)).smul (Real.exp_pos _)) hle (run q O ξ (m + 1)).g
    rw [inv_smul_mulVec (hH (m + 1)) (Real.exp_pos _), dotProduct_smul, smul_eq_mul,
      ← Real.exp_neg] at this
    exact this
  have hlogQ : -(av q O ξ D2f m) + Real.log lam2 ≤
      Real.log ((run q O ξ (m + 1)).g ⬝ᵥ ((Qv q O ξ D2f m)⁻¹ *ᵥ (run q O ξ (m + 1)).g)) := by
    have := Real.log_le_log (by positivity) hinvQ
    rwa [Real.log_mul (Real.exp_pos _).ne' hlam2pos.ne', Real.log_exp] at this
  have hP0 : P 0 ≤ k * (q.Φ0 + 2 * q.d * Real.log 2) + 2 * Real.log (2 * Δ + 1) := by
    have hx0' : (run q O ξ 0).x = q.x0 := by rw [run_zero]
    have hB0' : (run q O ξ 0).B = q.B0 := by rw [run_zero]
    have hQP0 : QP q O ξ D2f 0 = hessMatrix (D2f q.x0) := by simp [QP]
    have hH0 := hessMatrix_posDef hSC hD hx0
    have hg00 := hz 0 (by omega)
    have hrep0 := (hinv 0).2.1
    rw [hx0'] at hrep0
    simp only [hP, hQP0, hB0']
    unfold U
    have hPsi : Psi q.B0 (hessMatrix (D2f q.x0)) = mismatch q.B0 (hessMatrix (D2f q.x0)) +
        2 * q.d * Real.log 2 := by simp only [Psi, mismatch]; ring
    have hpit : pit q.B0 (hessMatrix (D2f q.x0)) (run q O ξ 0).g ≤ (2 * Δ + 1) ^ 2 := by
      have hle : LeQ (hessMatrix (D2f q.x0)) (q.B0 + hessMatrix (D2f q.x0)) := fun v => by
        rw [add_mulVec, dotProduct_add]; linarith [posDef_quad_nonneg hB0 v]
      have h1 := inv_anti hH0 (hB0.add hH0) hle (run q O ξ 0).g
      have h2 := decrement_bound hSC hD hx0 hrep0 (fun y hy => hlow y hy)
      exact h1.trans h2
    have hpitpos := pit_pos hB0 hH0 hg00
    have hlogpit : Real.log (pit q.B0 (hessMatrix (D2f q.x0)) (run q O ξ 0).g) ≤
        2 * Real.log (2 * Δ + 1) := by
      have := Real.log_le_log hpitpos hpit
      rwa [Real.log_pow] at this
    rw [hPsi]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_le_mul_of_nonneg_left hmis hk0]
  have hcomb : Real.log lam2 ≤ k * q.Φ0 + Real.log 4 + 2 * Real.log (2 * Δ + 1) +
      ∑ n ∈ range (m + 1), incv n + (2 * Kc + 1) * ∑ n ∈ range (m + 1), av q O ξ D2f n := by
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have ham : av q O ξ D2f m ≤ ∑ n ∈ range (m + 1), av q O ξ D2f n := by
      apply single_le_sum (fun i _ => av_nonneg q O ξ D2f hΔ0 i) (mem_range.mpr (by omega))
    have hKc0 : 0 ≤ Kc := by positivity
    have hsplit : ∑ n ∈ range (m + 1), (incv n + Kc * ℓv n) =
        ∑ n ∈ range (m + 1), incv n + Kc * ∑ n ∈ range (m + 1), ℓv n := by
      rw [sum_add_distrib, mul_sum]
    rw [hPKdef, hsplit] at hPK
    have := mul_le_mul_of_nonneg_left hsumℓ hKc0
    nlinarith
  set ε' := min (q.ε / 2) (1 / 64) with hε'
  have hε'pos : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hlamle : lam2 ≤ ε' := by
    by_contra hcon
    push Not at hcon
    set sh := (range (m + 1)).filter (fun n => rv q O ξ D2f n ≤ α / 32) with hsh
    set lg := (range (m + 1)).filter (fun n => ¬ rv q O ξ D2f n ≤ α / 32) with hlg
    have hinc : ∑ n ∈ range (m + 1), incv n =
        -(δ / 2) * (sh.card : ℝ) + (24 * Δ + 37) * lg.card := by
      simp only [hincv]
      rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
      ring
    have hav : ∑ n ∈ range (m + 1), av q O ξ D2f n =
        8 * ∑ n ∈ sh, rv q O ξ D2f n + (6 * Δ + 6) * lg.card := by
      simp only [av]
      rw [sum_ite, sum_const, nsmul_eq_mul, ← mul_sum]
      ring
    have hdecsum : ∑ n ∈ range (m + 1),
        (if rv q O ξ D2f n ≤ α / 32 then α * rv q O ξ D2f n ^ 2 / 4 else α ^ 3 / 4096) ≤ Δ := by
      have h1 : ∑ n ∈ range (m + 1),
          (if rv q O ξ D2f n ≤ α / 32 then α * rv q O ξ D2f n ^ 2 / 4 else α ^ 3 / 4096) ≤
          ∑ n ∈ range (m + 1), (I.f (run q O ξ n).x - I.f (run q O ξ (n + 1)).x) :=
        sum_le_sum fun n hn => (hfacts n (mem_range.mp hn)).2.2.2
      rw [sum_range_sub'] at h1
      have h2 := hlow _ hxK
      have h3 : (run q O ξ 0).x = q.x0 := by rw [run_zero]
      rw [h3] at h1
      linarith
    have hdec2 : ∑ n ∈ range (m + 1),
        (if rv q O ξ D2f n ≤ α / 32 then α * rv q O ξ D2f n ^ 2 / 4 else α ^ 3 / 4096) =
        α * (∑ n ∈ sh, rv q O ξ D2f n ^ 2) / 4 + (lg.card : ℝ) * (α ^ 3 / 4096) := by
      rw [sum_ite, sum_const, nsmul_eq_mul, ← sum_div, ← mul_sum]
    have hcard : (sh.card : ℝ) + lg.card = (m + 1 : ℕ) := by
      have := card_filter_add_card_filter_not (s := range (m + 1))
        (fun n => rv q O ξ D2f n ≤ α / 32)
      rw [card_range] at this
      exact_mod_cast this
    have hXY := sq_sum_le_card_mul_sum_sq (s := sh) (f := fun n => rv q O ξ D2f n)
    have hX0 : 0 ≤ ∑ n ∈ sh, rv q O ξ D2f n := sum_nonneg fun n _ => Real.sqrt_nonneg _
    have hY0 : 0 ≤ ∑ n ∈ sh, rv q O ξ D2f n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hlogΔ : Real.log (2 * Δ + 1) ≤ 2 * Δ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 2 * Δ + 1); linarith
    have hpot : Real.log lam2 ≤ k * q.Φ0 + 3 + 4 * Δ +
        (-(δ / 2) * (sh.card : ℝ) + (24 * Δ + 37) * lg.card) +
        (2 * (3 * (k : ℝ) * q.d + 1) + 1) *
          (8 * ∑ n ∈ sh, rv q O ξ D2f n + (6 * Δ + 6) * lg.card) := by
      rw [← hinc, ← hav]
      have : (2 * Kc + 1) = 2 * (3 * (k : ℝ) * q.d + 1) + 1 := by rw [hKc]
      rw [this] at hcomb
      linarith
    have hlε : Real.log ε' < Real.log lam2 := Real.log_lt_log hε'pos hcon
    have hlgε : -Real.log ε' ≤ Real.log (64 + 2 / q.ε) := by
      rw [← Real.log_inv]
      apply Real.log_le_log (by positivity)
      rw [hε']
      rcases le_total (q.ε / 2) (1 / 64) with h | h
      · rw [min_eq_left h]
        have : (q.ε / 2)⁻¹ = 2 / q.ε := by field_simp
        rw [this]; linarith
      · rw [min_eq_right h]
        have : 0 ≤ 2 / q.ε := by positivity
        norm_num; linarith
    have hcb := count_bound hc1 (by linarith) hδ0 hδ2 (Nat.cast_nonneg q.d) hΔ0 hΦ0
      (Nat.cast_nonneg k) hkR (Nat.cast_nonneg _) (Nat.cast_nonneg _) hX0 hY0
      (by rw [← hdec2]; exact hdecsum) (by simpa using hXY) hpot hlε hlgε
    have : ((m + 1 : ℕ) : ℝ) ≤ _ := hcard ▸ hcb
    linarith
  have hgap := gap_of_decrement hSC hD hconv hxK hxs hrepK (Real.sqrt_nonneg ε')
    (by rw [Real.sq_sqrt hε'pos.le]; exact hlamle)
    (by
      rw [show (1 / 8 : ℝ) = √(1 / 64) by
        rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (min_le_right _ _))
  rw [Real.sq_sqrt hε'pos.le] at hgap
  have : 2 * ε' ≤ q.ε := by
    have := min_le_left (q.ε / 2) (1 / 64); rw [← hε'] at this; linarith
  linarith

end LongTails.Proofs.SelfConcordantBFGSAccuracy
