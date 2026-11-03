import LongTails.Proofs.AuxiliaryAppa

namespace LongTails.Proofs.AuxiliaryEpoch

open scoped RealInnerProductSpace
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.GuardedMetricAcceleration LongTails.Proofs.GuardedAcceleratedGeometry
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryEval
open LongTails.Proofs.AuxiliaryCertificates LongTails.Proofs.AuxiliaryInner
open LongTails.Proofs.AuxiliaryDane LongTails.Proofs.AuxiliaryDaneRun LongTails.Proofs.AuxiliaryAppa

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {t : Tuning} {f h : E → ℝ} {L δ ρ Δ : ℝ}

def Valid (f : E → ℝ) (bk : Book E) : Prop := bk.best.2 = f bk.best.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma valid_note {bk : Book E} (hb : Valid f bk) (x : E) : Valid f (bk.note x (f x)) :=
  Book.note_valid bk hb x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma valid_flag {bk : Book E} (hb : Valid f bk) (c : Option (E × E)) : Valid f (bk.flag c) := hb

lemma valid_daneBook (y v s : E) {bk : Book E} (hb : Valid f bk) (k : ℕ) :
    Valid f (daneBook t y v (Fo f) (Fo h) s bk k) := by
  induction k with
  | zero => exact valid_note hb s
  | succ k ih => exact valid_note (valid_flag ih _) _

lemma valid_P (y : E) (k : ℕ) : Valid f (P t f h y k).2.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [book_succ]
      exact valid_flag (valid_flag (valid_flag (valid_daneBook _ _ _ ih _) _) _) _

lemma exploit_eval (y : E) (bk : Book E) :
    eval (orc (Fo f) (Fo h)) (exploit t y bk) =
      match bk.cert with
      | none => bk
      | some (u, w) =>
          (((bk.note u (f u)).note w (f w)).note (y + t.η • (‖u - w‖⁻¹ • (u - w)))
            (f (y + t.η • (‖u - w‖⁻¹ • (u - w))))).note (y - t.η • (‖u - w‖⁻¹ • (u - w)))
            (f (y - t.η • (‖u - w‖⁻¹ • (u - w)))) := by
  unfold exploit
  cases bk.cert with
  | none => rfl
  | some p =>
      obtain ⟨u, w⟩ := p
      simp only [eval_bind', eval_call, eval_pure, orc_zero, Fo]

lemma exploit_best_le (y : E) (bk : Book E) :
    (eval (orc (Fo f) (Fo h)) (exploit t y bk)).best.2 ≤ bk.best.2 := by
  rw [exploit_eval]
  cases bk.cert with
  | none => exact le_rfl
  | some p =>
      obtain ⟨u, w⟩ := p
      simp only
      refine (Book.note_le_left _ _ _).trans ((Book.note_le_left _ _ _).trans
        ((Book.note_le_left _ _ _).trans (Book.note_le_left _ _ _)))

lemma exploit_valid (y : E) {bk : Book E} (hb : Valid f bk) :
    Valid f (eval (orc (Fo f) (Fo h)) (exploit t y bk)) := by
  rw [exploit_eval]
  cases bk.cert with
  | none => exact hb
  | some p =>
      obtain ⟨u, w⟩ := p
      exact valid_note (valid_note (valid_note (valid_note hb _) _) _) _

lemma exploit_some (y : E) (bk : Book E) {u w : E} (hc : bk.cert = some (u, w)) :
    let r := eval (orc (Fo f) (Fo h)) (exploit t y bk)
    r.best.2 ≤ f u ∧ r.best.2 ≤ f w ∧ r.best.2 ≤ f (y + t.η • (‖u - w‖⁻¹ • (u - w))) ∧
      r.best.2 ≤ f (y - t.η • (‖u - w‖⁻¹ • (u - w))) := by
  intro r
  have hr : r = (((bk.note u (f u)).note w (f w)).note (y + t.η • (‖u - w‖⁻¹ • (u - w)))
            (f (y + t.η • (‖u - w‖⁻¹ • (u - w))))).note (y - t.η • (‖u - w‖⁻¹ • (u - w)))
            (f (y - t.η • (‖u - w‖⁻¹ • (u - w)))) := by
    simp only [r, exploit_eval, hc]
  rw [hr]
  refine ⟨?_, ?_, ?_, Book.note_le_right _ _ _⟩
  · exact (Book.note_le_left _ _ _).trans ((Book.note_le_left _ _ _).trans
      ((Book.note_le_left _ _ _).trans (Book.note_le_right _ _ _)))
  · exact (Book.note_le_left _ _ _).trans ((Book.note_le_left _ _ _).trans
      (Book.note_le_right _ _ _))
  · exact (Book.note_le_left _ _ _).trans (Book.note_le_right _ _ _)

section Final

variable (t f h) (y : E)

noncomputable def xT : E := (P t f h y t.T).1

noncomputable def xF : E := daneX t y (xT t f h y) (Fo f) (Fo h) (xT t f h y) t.J

noncomputable def bk1 : Book E :=
  (daneBook t y (xT t f h y) (Fo f) (Fo h) (xT t f h y) (P t f h y t.T).2.2 (t.J + 1)).flag
    (daneCert t y (xT t f h y) (Fo f) (Fo h) (xT t f h y))

noncomputable def cF : Option (E × E) :=
  (firstBad t.T (fun i => recBreg (gRecY t y (Fo f) (xF t f h y))
      (gRecY t y (Fo f) (P t f h y (i + 1)).1) <
    t.α / 2 * ‖xF t f h y - (P t f h y (i + 1)).1‖ ^ 2)).map (fun i => (xF t f h y, (P t f h y (i + 1)).1))

end Final

lemma inv_all (hyp : Hyp t f h L δ ρ Δ) (y : E) (hGy : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ)
    (β : ℝ) (hβ : f y - t.α * tau t ρ ^ 2 < β) (hβT : β ≤ (P t f h y t.T).2.2.best.2) :
    ∀ k ≤ t.T, Inv t f h ρ y β k := by
  have hβy : β ≤ f y := hβT.trans (best_mono t f h y 0 t.T (Nat.zero_le _))
  intro k
  induction k with
  | zero => intro _; exact ⟨fun p hp => (by cases hp), fun _ s hs => absurd hs (Nat.not_lt_zero _)⟩
  | succ k ih =>
      intro hk
      exact inv_step hyp y hGy β hβ hβy k (hβT.trans (best_mono t f h y (k + 1) t.T hk))
        (ih (by omega))

lemma final_phase (hyp : Hyp t f h L δ ρ Δ) (y : E) (hGy : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ)
    (β : ℝ) (hβ : f y - t.α * tau t ρ ^ 2 < β) (hβ1 : β ≤ (bk1 t f h y).best.2) :
    β ≤ f (xF t f h y) ∧
      (∀ p, ((bk1 t f h y).flag (cF t f h y)).cert = some p → Good t f ρ y β p) ∧
      (((bk1 t f h y).flag (cF t f h y)).cert = none → ‖gradient f (xF t f h y)‖ ≤ t.ε) := by
  have hdb_best := daneBook_best (t := t) (f := f) (h := h) y (xT t f h y) (xT t f h y)
    (P t f h y t.T).2.2 (t.J + 1)
  have hβT : β ≤ (P t f h y t.T).2.2.best.2 := hβ1.trans hdb_best.1
  have hβy : β ≤ f y := hβT.trans (best_mono t f h y 0 t.T (Nat.zero_le _))
  have hI := inv_all hyp y hGy β hβ hβT t.T le_rfl
  have hfx : β ≤ f (xF t f h y) := hβ1.trans (hdb_best.2 t.J (by omega))
  have hdc := daneBook_cert (t := t) (f := f) (h := h) y (xT t f h y) (xT t f h y)
    (P t f h y t.T).2.2 (t.J + 1)
  have hcert1 : (bk1 t f h y).cert = ((daneBook t y (xT t f h y) (Fo f) (Fo h) (xT t f h y)
      (P t f h y t.T).2.2 (t.J + 1)).flag (daneCert t y (xT t f h y) (Fo f) (Fo h) (xT t f h y))).cert :=
    rfl
  cases hTc : (P t f h y t.T).2.2.cert with
  | some p0 =>
      have hp0 : ((bk1 t f h y).flag (cF t f h y)).cert = some p0 :=
        Book.flag_some _ _ (by rw [hcert1]; exact Book.flag_some _ _ (hdc.1 p0 hTc))
      refine ⟨hfx, fun q hq => ?_, fun hn => ?_⟩
      · rw [hp0] at hq; cases hq; exact hI.1 p0 hTc
      · rw [hp0] at hn; cases hn
  | none =>
      have hok := hI.2 hTc
      obtain ⟨hB1, hxl, _, _, _⟩ := bounds_of_steps hyp y β hβ hβy t.T hok
      have hE := e_small hyp
      have hτ := hyp.tau_pos
      have hα := hyp.hα
      have hdb := hyp.db_pos
      have hgxT : gval t f y (xT t f h y) ≤ f y + t.α * tau t ρ ^ 2 := by
        have : 0 ≤ t.α / 2 / 2 * ‖y - (P t f h y t.T).2.1‖ ^ 2 := by positivity
        unfold xT; linarith
      have hTs : tval t y (xT t f h y) f (xT t f h y) ≤ f y + 8 * t.α * tau t ρ ^ 2 := by
        have he : tval t y (xT t f h y) f (xT t f h y) = gval t f y (xT t f h y) := by
          simp [tval, gval]
        rw [he]
        have : 0 ≤ t.α * tau t ρ ^ 2 := by positivity
        linarith
      have hnote : β ≤ (daneBook t y (xT t f h y) (Fo f) (Fo h) (xT t f h y) (P t f h y t.T).2.2
          (t.J + 1)).best.2 := hβ1
      obtain ⟨DA1, DA2, DA3, DA4⟩ := dane_analysis hyp y (xT t f h y) (xT t f h y)
        (P t f h y t.T).2.2 hGy hxl hTs β hβ hnote
      have hxFl : ‖xF t f h y - y‖ ≤ 3 * tau t ρ := (DA1 t.J (by omega)).2.2
      refine ⟨hfx, fun q hq => ?_, fun hn => ?_⟩
      · rcases Book.flag_cases _ _ hq with hq | ⟨_, hq⟩
        · rw [hcert1] at hq
          rcases Book.flag_cases _ _ hq with hq | ⟨_, hq⟩
          · rcases hdc.2.1 q hq with hq | ⟨j, hj, hq⟩
            · rw [hTc] at hq; cases hq
            · exact good_of_cand hyp y _ _ β hβ hTs (DA2 j (by omega) q hq)
          · exact good_of_cand hyp y _ _ β hβ hTs (DA3 q hq)
        · unfold cF at hq
          simp only [Option.map_eq_some_iff] at hq
          obtain ⟨i, hi, rfl⟩ := hq
          obtain ⟨hiT, hbad⟩ := firstBad_some hi
          rw [recBreg_g] at hbad
          have hc := transfer_g rfl hbad
          exact ⟨hc, ne_of_breg_neg hc, fun _ _ => ⟨hxFl, (hok i hiT).2.1⟩⟩
      · obtain ⟨hn1, hcF⟩ := Book.flag_none _ _ hn
        rw [hcert1] at hn1
        obtain ⟨hn2, hdc0⟩ := Book.flag_none _ _ hn1
        have hcheap := hdc.2.2 hn2
        have hacc := DA4 (fun j hj => hcheap j (by omega)) hdc0
        unfold cF at hcF
        simp only [Option.map_eq_none_iff] at hcF
        have hguards := firstBad_none hcF
        have hsupp : ∀ s < t.T, Supp t f h y s (xF t f h y) (6 * vartheta t ρ * tau t ρ) := by
          intro s hs
          have hg := hguards s hs
          push Not at hg
          rw [recBreg_gRecY] at hg
          exact supp_of_guard hyp y s _ (hok s hs).1 hxFl (hok s hs).2.1 hg
        have hpot := potential_of_steps hyp y (xF t f h y) β t.T hok _
          (by have := hyp.vartheta_nonneg; positivity) hsupp le_rfl
        have hQ : gval t f y y - gval t f y (xF t f h y) + t.α / 2 / 2 * ‖xF t f h y - y‖ ^ 2 ≤
            t.α * tau t ρ ^ 2 := by
          have : 0 ≤ ‖xF t f h y - y‖ ^ 2 := sq_nonneg _
          simp only [gval, sub_self, norm_zero]
          nlinarith
        have ha0 : 0 ≤ (1 - t.a) ^ t.T := pow_nonneg (sub_nonneg.mpr hyp.ha1) _
        have hQ' := mul_le_mul_of_nonneg_left hQ ha0
        have hdec : gval t f y (xF t f h y) + t.db * ‖xF t f h y - xT t f h y‖ ^ 2 ≤
            gval t f y (xT t f h y) := by
          have := (DA1 t.J (by omega)).1
          simp only [tval, sub_self, norm_zero] at this
          unfold xF gval
          nlinarith
        have hD : gval t f y (xT t f h y) - gval t f y (xF t f h y) ≤
            (1 - t.a) ^ t.T * (t.α * tau t ρ ^ 2) + 6 * vartheta t ρ * tau t ρ / t.a := by
          have : 0 ≤ t.α / 2 / 2 * ‖xF t f h y - (P t f h y t.T).2.1‖ ^ 2 := by positivity
          unfold xT at *
          linarith
        have hfg := final_gradient (g := gval t f y) (dg := ggrad t f y) hdb (xT t f h y)
          (xF t f h y) hacc hdec hD
        have hgg : ‖ggrad t f y (xF t f h y)‖ ^ 2 ≤ t.ε ^ 2 / 4 := hfg.trans hyp.hCT
        have hgg' : ‖ggrad t f y (xF t f h y)‖ ≤ t.ε / 2 := by
          apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith [hyp.hε]) two_ne_zero).mp
          nlinarith
        by_contra hbig
        push Not at hbig
        have hsplit : gradient f (xF t f h y) =
            ggrad t f y (xF t f h y) - (2 * t.α) • (xF t f h y - y) := by
          unfold ggrad; abel
        have hlow : t.ε / 2 < 2 * t.α * ‖xF t f h y - y‖ := by
          have h1 : ‖gradient f (xF t f h y)‖ ≤ ‖ggrad t f y (xF t f h y)‖ +
              ‖(2 * t.α) • (xF t f h y - y)‖ := by
            rw [hsplit]; exact norm_sub_le _ _
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
          linarith
        have hsq : t.ε ^ 2 / (16 * t.α) < t.α * ‖xF t f h y - y‖ ^ 2 := by
          have hε := hyp.hε
          have hpw := pow_lt_pow_left₀ hlow (by positivity) two_ne_zero
          have e1 : (t.ε / 2) ^ 2 = t.ε ^ 2 / 4 := by ring
          have e2 : (2 * t.α * ‖xF t f h y - y‖) ^ 2 = 4 * (t.α * (t.α * ‖xF t f h y - y‖ ^ 2)) := by
            ring
          rw [e1, e2] at hpw
          rw [div_lt_iff₀ (by positivity)]
          linarith only [hpw]
        have hfxF : f (xF t f h y) ≤ f y + t.α * tau t ρ ^ 2 - t.α * ‖xF t f h y - y‖ ^ 2 := by
          have h0 : 0 ≤ t.db * ‖xF t f h y - xT t f h y‖ ^ 2 := by positivity
          simp only [gval] at hdec hgxT
          linarith only [hdec, hgxT, h0]
        have hCε := hyp.hCε
        linarith only [hfxF, hsq, hCε, hfx, hβ]

lemma eval_epoch (y : E) :
    eval (orc (Fo f) (Fo h)) (epoch t y) =
      if ‖gradient f y‖ ≤ t.ε then y else
        if ‖gradient f (xF t f h y)‖ ≤ t.ε then xF t f h y else
          (eval (orc (Fo f) (Fo h)) (exploit t y ((bk1 t f h y).flag (cF t f h y)))).best.1 := by
  obtain ⟨_, hx, _, hb, hr⟩ := appaRun_spec t y (Fo f) (Fo h) (bk0 f y) t.T
  have hloop : eval (orc (Fo f) (Fo h)) (TwoPlan.loop t.T (appaStep t y (y, f y, gradient f y))
      ⟨0, y, y, fun _ => (y, f y, gradient f y), { best := (y, f y), cert := none }⟩) =
      appaRun t y (Fo f) (Fo h) (bk0 f y) t.T := by
    rw [eval_loop]; rfl
  unfold epoch
  rw [eval_bind', eval_call, orc_zero]
  by_cases h1 : ‖gradient f y‖ ≤ t.ε
  · simp only [Fo, h1, ↓reduceIte, eval_pure]
  · simp only [Fo, h1, ↓reduceIte]
    rw [eval_bind', hloop, eval_bind', eval_dane, hx, hb, eval_bind', eval_call, orc_zero]
    simp only [gRec_tRec]
    simp only [gRecY, Fo]
    simp only [xF, xT, P]
    by_cases h2 : ‖gradient f (daneX t y (appaP t y (Fo f) (Fo h) (bk0 f y) t.T).1 (Fo f) (Fo h)
        (appaP t y (Fo f) (Fo h) (bk0 f y) t.T).1 t.J)‖ ≤ t.ε
    · simp only [h2, ↓reduceIte, eval_pure]
    · simp only [h2, ↓reduceIte]
      rw [eval_bind', eval_pure]
      refine congrArg (fun bk => (eval (orc (Fo f) (Fo h)) (exploit t y bk)).best.1) ?_
      unfold bk1 cF xF xT P
      congr 1
      apply firstBad_map_congr
      · intro i hi
        rw [hr (i + 1) hi]
        rfl
      · intro i hi
        rw [hr (i + 1) hi]
        rfl

lemma epoch_progress [FiniteDimensional ℝ E] (hyp : Hyp t f h L δ ρ Δ) (y : E)
    (hGy : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ) :
    ‖gradient f (eval (orc (Fo f) (Fo h)) (epoch t y))‖ ≤ t.ε ∨
      f (eval (orc (Fo f) (Fo h)) (epoch t y)) ≤ f y - t.α * tau t ρ ^ 2 := by
  rw [eval_epoch]
  by_cases h1 : ‖gradient f y‖ ≤ t.ε
  · rw [ite_eq_left h1]; exact Or.inl h1
  rw [ite_eq_right h1]
  by_cases h2 : ‖gradient f (xF t f h y)‖ ≤ t.ε
  · rw [ite_eq_left h2]; exact Or.inl h2
  rw [ite_eq_right h2]
  right
  set bkE := eval (orc (Fo f) (Fo h)) (exploit t y ((bk1 t f h y).flag (cF t f h y)))
  have hval : Valid f bkE := exploit_valid y (valid_flag (valid_flag
    (valid_daneBook _ _ _ (valid_P y t.T) _) _) _)
  rw [← hval]
  by_contra hcon
  push Not at hcon
  set β := bkE.best.2
  have hβ1 : β ≤ (bk1 t f h y).best.2 := exploit_best_le y _
  obtain ⟨hfx, hgood, hstat⟩ := final_phase hyp y hGy β hcon hβ1
  cases hc : ((bk1 t f h y).flag (cF t f h y)).cert with
  | none => exact h2 (hstat hc)
  | some p =>
      obtain ⟨u, w⟩ := p
      obtain ⟨hcert, hne, hloc⟩ := hgood (u, w) hc
      obtain ⟨hu, hw, hp1, hp2⟩ := exploit_some y _ hc
      obtain ⟨hlu, hlw⟩ := hloc hu hw
      have hR : 3 * tau t ρ ≤ t.α / (4 * ρ) := by
        have hx : 0 ≤ t.α / (4 * ρ) := by have := hyp.hα; have := hyp.hρ; positivity
        have e : 3 * tau t ρ = 3 / 8 * (t.α / (4 * ρ)) := by unfold tau; ring
        rw [e]; linarith
      have hprog := certificate_progress hyp.hf hyp.hρ hyp.hHess hyp.hα.le hyp.hη y u w hne
        (hlu.trans hR) (hlw.trans hR) hcert
      have h2τ : t.α ^ 3 / (512 * ρ ^ 2) = 2 * (t.α * tau t ρ ^ 2) := by
        unfold tau; ring
      have hpos : 0 < t.α * tau t ρ ^ 2 := by have := hyp.hα; have := hyp.tau_pos; positivity
      rcases hprog with hp | hp <;> linarith

end LongTails.Proofs.AuxiliaryEpoch
