import LongTails.Proofs.AuxiliaryDane

namespace LongTails.Proofs.AuxiliaryDaneRun

open scoped RealInnerProductSpace
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryEval
open LongTails.Proofs.AuxiliaryCertificates LongTails.Proofs.AuxiliaryInner
open LongTails.Proofs.AuxiliaryDane

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {t : Tuning} {f h : E → ℝ} {L δ ρ Δ : ℝ}

noncomputable def psiF (t : Tuning) (y v : E) (h : E → ℝ) (xb b : E) (z : E) : ℝ :=
  ⟪b, z⟫ + pval t y v h z - pval t y v h xb - ⟪pgrad t y v h xb, z - xb⟫

noncomputable def psiG (t : Tuning) (y v : E) (h : E → ℝ) (xb b : E) (z : E) : E :=
  b + pgrad t y v h z - pgrad t y v h xb

lemma psi_has (hyp : Hyp t f h L δ ρ Δ) (y v xb b z : E) :
    HasGradientAt (psiF t y v h xb b) (psiG t y v h xb b z) z := by
  have hlin : ∀ c : E, HasGradientAt (fun z => ⟪c, z⟫) c z := by
    intro c
    rw [hasGradientAt_iff_hasFDerivAt]
    exact ((InnerProductSpace.toDual ℝ E) c).hasFDerivAt
  have h1 := hlin b
  have h2 := hyp.pgrad_has y v z
  have h3 : HasGradientAt (fun z => ⟪pgrad t y v h xb, z - xb⟫) (pgrad t y v h xb) z := by
    have hf : (fun z => ⟪pgrad t y v h xb, z - xb⟫) =
        fun z => ⟪pgrad t y v h xb, z⟫ - ⟪pgrad t y v h xb, xb⟫ := by
      funext w; rw [inner_sub_right]
    rw [hf]
    exact grad_sub_const (hlin _) _
  exact grad_sub (grad_sub_const (grad_add h1 h2) (pval t y v h xb)) h3

lemma psi_lip (hyp : Hyp t f h L δ ρ Δ) (y v xb b : E) (a c : E) :
    ‖psiG t y v h xb b a - psiG t y v h xb b c‖ ≤ t.M * ‖a - c‖ := by
  have he : psiG t y v h xb b a - psiG t y v h xb b c = pgrad t y v h a - pgrad t y v h c := by
    simp only [psiG]; abel
  rw [he]
  exact hyp.pgrad_lip y v a c

lemma psi_breg (t : Tuning) (y v : E) (h : E → ℝ) (xb b u w : E) :
    breg (psiF t y v h xb b) (psiG t y v h xb b) u w =
      recBreg (psiRec t y v u (Fo h u)) (psiRec t y v w (Fo h w)) := by
  simp only [breg, psiF, psiG, recBreg, psiRec_eq, inner_add_left, inner_sub_left,
    inner_sub_right]
  ring

lemma cheapZ_succ (t : Tuning) (y v : E) (h : E → ℝ) (xb b : E) (i : ℕ) :
    cheapZ t y v (Fo h) xb b (i + 1) =
      cheapZ t y v (Fo h) xb b i - (1 / t.M) • psiG t y v h xb b (cheapZ t y v (Fo h) xb b i) := by
  simp only [cheapZ, psiG, psiRec_eq]

lemma cheapZ_zero (t : Tuning) (y v : E) (h : E → ℝ) (xb b : E) :
    cheapZ t y v (Fo h) xb b 0 = xb := rfl

lemma tval_le_psiF (hyp : Hyp t f h L δ ρ Δ) (y v xb z : E) :
    tval t y v f z ≤ tval t y v f xb + psiF t y v h xb (tgrad t y v f xb) z -
      psiF t y v h xb (tgrad t y v f xb) xb := by
  have hr := hyp.T_le_psi y v z xb
  rw [tRec_eq, tRec_eq, psiRec_eq, psiRec_eq] at hr
  simp only [recBreg, psiF, inner_sub_right] at hr ⊢
  linarith

section Locality

variable (t ρ) in
noncomputable def R3 : ℝ := 3 * tau t ρ

lemma local_of_tval (hyp : Hyp t f h L δ ρ Δ) (y v p : E) (β : ℝ)
    (hβ : f y - t.α * tau t ρ ^ 2 < β) (hfp : β ≤ f p)
    (hT : tval t y v f p ≤ f y + 8 * t.α * tau t ρ ^ 2) : ‖p - y‖ ≤ 3 * tau t ρ := by
  have hα := hyp.hα
  have hτ := hyp.tau_pos
  have h1 : t.α * ‖p - y‖ ^ 2 ≤ t.α * (3 * tau t ρ) ^ 2 := by
    have : 0 ≤ t.db * ‖p - v‖ ^ 2 := by have := hyp.db_pos; positivity
    simp only [tval] at hT
    nlinarith
  have h2 : ‖p - y‖ ^ 2 ≤ (3 * tau t ρ) ^ 2 := le_of_mul_le_mul_left h1 hα
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

end Locality

section Run

variable (t) in
def Cand (f : E → ℝ) (y v s : E) (p : E × E) : Prop :=
  breg f (gradient f) p.1 p.2 < -(t.α / 2) * ‖p.1 - p.2‖ ^ 2 ∧ p.1 ≠ p.2 ∧
    tval t y v f p.1 ≤ tval t y v f s ∧ tval t y v f p.2 ≤ tval t y v f s

lemma cheap_facts (hyp : Hyp t f h L δ ρ Δ) (y v xb : E) :
    let b := tgrad t y v f xb
    let z := cheapZ t y v (Fo h) xb b
    (∀ k, tval t y v f (z k) ≤ tval t y v f xb) ∧
      (⟪b, z (t.N - 1) - xb⟫ + breg (pval t y v h) (pgrad t y v h) (z (t.N - 1)) xb ≤
        -(‖b‖ ^ 2 / (2 * t.M))) := by
  intro b z
  have hM := hyp.M_pos
  have hz : ∀ i, z (i + 1) = z i - (1 / t.M) • psiG t y v h xb b (z i) :=
    cheapZ_succ t y v h xb b
  have hg := psi_has hyp y v xb b
  have hl := psi_lip hyp y v xb b
  have hz0 : z 0 = xb := rfl
  constructor
  · intro k
    have h1 := cheap_mono hM hg hl z hz 0 k
    have h2 := tval_le_psiF hyp y v xb (z k)
    rw [zero_add, hz0] at h1
    linarith
  · have hN := hyp.hN
    obtain ⟨k, hk⟩ : ∃ k, t.N - 1 = k + 1 := ⟨t.N - 2, by omega⟩
    have h1 := cheap_first hM hg hl z hz k
    rw [← hk, hz0] at h1
    have hg0 : psiG t y v h xb b xb = b := by simp [psiG]
    rw [hg0] at h1
    simp only [psiF, breg, sub_self, inner_zero_right, inner_sub_right] at h1 ⊢
    linarith

lemma cheap_cert (hyp : Hyp t f h L δ ρ Δ) (y v xb : E) {p : E × E}
    (hp : (cheapOut t y v (Fo f) (Fo h) xb).2.1 = some p) :
    Cand t f y v xb p := by
  unfold cheapOut at hp
  rw [eval_cheapGD] at hp
  simp only [Option.map_eq_some_iff] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨hiN, hbad⟩ := firstBad_some hi
  have hcert := hyp.cert_psi y v _ _ hbad
  have hfacts := (cheap_facts hyp y v xb).1
  exact ⟨hcert, ne_of_breg_neg hcert, hfacts _, hfacts _⟩

lemma cheap_accuracy (hyp : Hyp t f h L δ ρ Δ) (y v xb : E)
    (hnone : (cheapOut t y v (Fo f) (Fo h) xb).2.1 = none) :
    ‖psiG t y v h xb (tgrad t y v f xb) (cheapZ t y v (Fo h) xb (tgrad t y v f xb) (t.N - 1))‖ ^ 2 ≤
      2 * t.M * ((1 - 3 * t.db / t.M) ^ (t.N - 1) * (‖tgrad t y v f xb‖ ^ 2 / (6 * t.db))) := by
  unfold cheapOut at hnone
  rw [eval_cheapGD] at hnone
  simp only [Option.map_eq_none_iff] at hnone
  have hgood := firstBad_none hnone
  have hM := hyp.M_pos
  have hdb := hyp.db_pos
  set b := tgrad t y v f xb
  set z := cheapZ t y v (Fo h) xb b
  have hz : ∀ i, z (i + 1) = z i - (1 / t.M) • psiG t y v h xb b (z i) :=
    cheapZ_succ t y v h xb b
  have hcM : 2 * (3 * t.db / 2) ≤ t.M := by rw [hyp.hM]; have := hyp.hα; linarith [hyp.hL]
  have hr := cheap_rate hM (by positivity : 0 < 3 * t.db / 2) hcM (psi_has hyp y v xb b)
    (psi_lip hyp y v xb b) z hz t.N (fun i hi => by
      have := hgood i hi
      push Not at this
      rw [psi_breg]
      exact this) (t.N - 1) (by have := hyp.hN; omega)
  have hg0 : psiG t y v h xb b (z 0) = b := by simp [psiG, z, cheapZ_zero]
  rw [hg0] at hr
  have he : 2 * (3 * t.db / 2) / t.M = 3 * t.db / t.M := by ring
  have he2 : 4 * (3 * t.db / 2) = 6 * t.db := by ring
  rw [he, he2] at hr
  exact hr

end Run

section Dane

lemma daneX_succ (y v s : E) (j : ℕ) :
    daneX t y v (Fo f) (Fo h) s (j + 1) =
      cheapZ t y v (Fo h) (daneX t y v (Fo f) (Fo h) s j)
        (tgrad t y v f (daneX t y v (Fo f) (Fo h) s j)) (t.N - 1) := by
  simp only [daneX, cheapOut, eval_cheapGD]
  rfl

lemma prec_eq (y v x : E) : (cheapOut t y v (Fo f) (Fo h) x).2.2 = psiRec t y v x (Fo h x) := by
  simp only [cheapOut, eval_cheapGD]

lemma dane_tval (hyp : Hyp t f h L δ ρ Δ) (y v s : E) (j : ℕ) :
    tval t y v f (daneX t y v (Fo f) (Fo h) s j) ≤ tval t y v f s := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [daneX_succ]
      exact ((cheap_facts hyp y v _).1 _).trans ih

lemma daneBook_best (y v s : E) (bk : Book E) (k : ℕ) :
    (daneBook t y v (Fo f) (Fo h) s bk k).best.2 ≤ bk.best.2 ∧
      ∀ j ≤ k, (daneBook t y v (Fo f) (Fo h) s bk k).best.2 ≤ f (daneX t y v (Fo f) (Fo h) s j) := by
  induction k with
  | zero =>
      refine ⟨Book.note_le_left _ _ _, fun j hj => ?_⟩
      obtain rfl : j = 0 := by omega
      exact Book.note_le_right _ _ _
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      have hstep : (daneBook t y v (Fo f) (Fo h) s bk (k + 1)).best.2 ≤
          (daneBook t y v (Fo f) (Fo h) s bk k).best.2 := Book.note_le_left _ _ _
      refine ⟨hstep.trans h1, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact hstep.trans (h2 j (by omega))
      · obtain rfl : j = k + 1 := by omega
        exact Book.note_le_right _ _ _

lemma daneBook_cert (y v s : E) (bk : Book E) (k : ℕ) :
    (∀ p, bk.cert = some p → (daneBook t y v (Fo f) (Fo h) s bk k).cert = some p) ∧
      (∀ p, (daneBook t y v (Fo f) (Fo h) s bk k).cert = some p →
        bk.cert = some p ∨ ∃ j < k,
          (cheapOut t y v (Fo f) (Fo h) (daneX t y v (Fo f) (Fo h) s j)).2.1 = some p) ∧
      ((daneBook t y v (Fo f) (Fo h) s bk k).cert = none →
        ∀ j < k, (cheapOut t y v (Fo f) (Fo h) (daneX t y v (Fo f) (Fo h) s j)).2.1 = none) := by
  induction k with
  | zero =>
      refine ⟨fun p hp => hp, fun p hp => Or.inl hp, fun _ j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hc : (daneBook t y v (Fo f) (Fo h) s bk (k + 1)).cert =
          ((daneBook t y v (Fo f) (Fo h) s bk k).flag
            (cheapOut t y v (Fo f) (Fo h) (daneX t y v (Fo f) (Fo h) s k)).2.1).cert := rfl
      refine ⟨fun p hp => ?_, fun p hp => ?_, fun hn j hj => ?_⟩
      · rw [hc]; exact Book.flag_some _ _ (h1 p hp)
      · rw [hc] at hp
        rcases Book.flag_cases _ _ hp with hq | ⟨_, hq⟩
        · rcases h2 p hq with hr | ⟨j, hj, hr⟩
          · exact Or.inl hr
          · exact Or.inr ⟨j, by omega, hr⟩
        · exact Or.inr ⟨k, by omega, hq⟩
      · rw [hc] at hn
        obtain ⟨hn1, hn2⟩ := Book.flag_none _ _ hn
        rcases Nat.lt_or_ge j k with hj' | hj'
        · exact h3 hn1 j hj'
        · obtain rfl : j = k := by omega
          exact hn2

lemma tgrad_bound (hyp : Hyp t f h L δ ρ Δ) (y v x : E)
    (hGy : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ) (hx : ‖x - y‖ ≤ 3 * tau t ρ)
    (hv : ‖v - y‖ ≤ 3 * tau t ρ) :
    ‖tgrad t y v f x‖ ^ 2 ≤ 4 * (L + δ) * Δ + 18 * tau t ρ ^ 2 * (t.M + δ) ^ 2 := by
  have hα := hyp.hα
  have hdb := hyp.db_pos
  have hτ := hyp.tau_pos
  have hxv : ‖x - v‖ ≤ 6 * tau t ρ := by
    calc ‖x - v‖ = ‖(x - y) - (v - y)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖v - y‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have h1 : ‖gradient f x‖ ≤ ‖gradient f y‖ + (L + δ) * (3 * tau t ρ) := by
    have := hyp.gradf_lip x y
    have h2 : ‖gradient f x‖ ≤ ‖gradient f y‖ + ‖gradient f x - gradient f y‖ := by
      have := norm_add_le (gradient f y) (gradient f x - gradient f y)
      simpa using this
    have hLd : 0 ≤ L + δ := by linarith [hyp.hL, hyp.hδ]
    nlinarith [mul_le_mul_of_nonneg_left hx hLd]
  have h2 : ‖tgrad t y v f x‖ ≤ ‖gradient f y‖ + 3 * tau t ρ * (t.M + δ) := by
    unfold tgrad
    calc _ ≤ ‖gradient f x + (2 * t.α) • (x - y)‖ + ‖(2 * t.db) • (x - v)‖ := norm_add_le _ _
      _ ≤ ‖gradient f x‖ + ‖(2 * t.α) • (x - y)‖ + ‖(2 * t.db) • (x - v)‖ := by
          gcongr; exact norm_add_le _ _
      _ = ‖gradient f x‖ + 2 * t.α * ‖x - y‖ + 2 * t.db * ‖x - v‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < 2 * t.α), abs_of_pos (by positivity : 0 < 2 * t.db)]
      _ ≤ ‖gradient f y‖ + (L + δ) * (3 * tau t ρ) + 2 * t.α * (3 * tau t ρ) +
            2 * t.db * (6 * tau t ρ) := by gcongr
      _ = _ := by rw [hyp.hM]; ring
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 := sq_nonneg (‖gradient f y‖ - 3 * tau t ρ * (t.M + δ))
  nlinarith

end Dane

section Main

lemma dane_analysis (hyp : Hyp t f h L δ ρ Δ) (y v s : E) (bk : Book E)
    (hGy : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ) (hv : ‖v - y‖ ≤ 3 * tau t ρ)
    (hTs : tval t y v f s ≤ f y + 8 * t.α * tau t ρ ^ 2) (β : ℝ)
    (hβ : f y - t.α * tau t ρ ^ 2 < β)
    (hnote : β ≤ (daneBook t y v (Fo f) (Fo h) s bk (t.J + 1)).best.2) :
    (∀ j ≤ t.J + 1, tval t y v f (daneX t y v (Fo f) (Fo h) s j) ≤ tval t y v f s ∧
        β ≤ f (daneX t y v (Fo f) (Fo h) s j) ∧
        ‖daneX t y v (Fo f) (Fo h) s j - y‖ ≤ 3 * tau t ρ) ∧
      (∀ j ≤ t.J, ∀ p,
        (cheapOut t y v (Fo f) (Fo h) (daneX t y v (Fo f) (Fo h) s j)).2.1 = some p →
          Cand t f y v s p) ∧
      (∀ p, daneCert t y v (Fo f) (Fo h) s = some p → Cand t f y v s p) ∧
      ((∀ j ≤ t.J, (cheapOut t y v (Fo f) (Fo h) (daneX t y v (Fo f) (Fo h) s j)).2.1 = none) →
        daneCert t y v (Fo f) (Fo h) s = none →
          ‖tgrad t y v f (daneX t y v (Fo f) (Fo h) s t.J)‖ ≤ vartheta t ρ) := by
  set x := daneX t y v (Fo f) (Fo h) s
  have hτ := hyp.tau_pos
  have hM := hyp.M_pos
  have hdb := hyp.db_pos
  have hbest := (daneBook_best (t := t) (f := f) (h := h) y v s bk (t.J + 1)).2
  have hloc : ∀ j ≤ t.J + 1, tval t y v f (x j) ≤ tval t y v f s ∧ β ≤ f (x j) ∧
      ‖x j - y‖ ≤ 3 * tau t ρ := by
    intro j hj
    have h1 := dane_tval hyp y v s j
    have h2 := hnote.trans (hbest j hj)
    exact ⟨h1, h2, local_of_tval hyp y v (x j) β hβ h2 (h1.trans hTs)⟩
  refine ⟨hloc, ?_, ?_, ?_⟩
  · intro j hj p hp
    obtain ⟨c1, c2, c3, c4⟩ := cheap_cert hyp y v (x j) hp
    exact ⟨c1, c2, c3.trans (hloc j (by omega)).1, c4.trans (hloc j (by omega)).1⟩
  · intro p hp
    unfold daneCert at hp
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    obtain ⟨hjJ, hbad⟩ := firstBad_some hj
    rw [prec_eq] at hbad
    have hc := hyp.cert_T y v _ _ hbad
    exact ⟨hc, ne_of_breg_neg hc, (hloc (t.J + 1) le_rfl).1, (hloc j (by omega)).1⟩
  · intro hcheap hdane
    unfold daneCert at hdane
    simp only [Option.map_eq_none_iff] at hdane
    have hgood := firstBad_none hdane
    set ζ := vartheta t ρ ^ 2 / (60 * t.M * tau t ρ)
    have hζ : 0 ≤ ζ := by have := hyp.vartheta_nonneg; positivity
    have hpair : ∀ i j, i ≤ t.J + 1 → j ≤ t.J + 1 → ‖x i - x j‖ ≤ 6 * tau t ρ := by
      intro i j hi hj
      calc ‖x i - x j‖ = ‖(x i - y) - (x j - y)‖ := by congr 1; abel
        _ ≤ ‖x i - y‖ + ‖x j - y‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [(hloc i hi).2.2, (hloc j hj).2.2]
    have hrate := dane_rate (T := tval t y v f) (dT := tgrad t y v f) (ψ := pval t y v h)
      (dψ := pgrad t y v h) (Rd := 6 * tau t ρ) hM hζ x t.J hyp.hJ
      (fun u w => by
        have := hyp.T_le_psi y v u w
        rw [tRec_eq, tRec_eq, psiRec_eq, psiRec_eq] at this
        exact this)
      (by
        have hb := breg_abs_le (hyp.pgrad_has y v) (hyp.pgrad_lip y v) (x (t.J + 1)) (x 0)
        have hd := hpair (t.J + 1) 0 le_rfl (by omega)
        have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
        have := (abs_le.mp hb).2
        nlinarith)
      (fun j hj => by
        have := (cheap_facts hyp y v (x j)).2
        rw [← daneX_succ] at this
        exact this)
      (fun j hj => by
        have hacc := cheap_accuracy hyp y v (x j) (hcheap j hj)
        rw [← daneX_succ] at hacc
        have hG := tgrad_bound hyp y v (x j) hGy (hloc j (by omega)).2.2 hv
        have hk : 0 ≤ (1 - 3 * t.db / t.M) ^ (t.N - 1) := by
          apply pow_nonneg
          rw [sub_nonneg, div_le_one hM, hyp.hM]
          linarith [hyp.hL, hyp.hα]
        have h1 : ‖psiG t y v h (x j) (tgrad t y v f (x j)) (x (j + 1))‖ ^ 2 ≤ ζ ^ 2 := by
          refine hacc.trans (le_trans ?_ hyp.hCN)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hG (by positivity)) hk) (by positivity)
        have h2 := (pow_le_pow_iff_left₀ (norm_nonneg _) hζ two_ne_zero).mp h1
        simpa [psiG] using h2)
      (fun j hj => hpair (j + 1) (t.J + 1) (by omega) le_rfl)
      (fun j hj => by
        have := hgood j (by omega)
        push Not at this
        rw [prec_eq, tRec_eq, tRec_eq, psiRec_eq] at this
        exact this)
    have hfin : ‖tgrad t y v f (x t.J)‖ ^ 2 ≤ vartheta t ρ ^ 2 := hrate.trans hyp.hCJ
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hyp.vartheta_nonneg two_ne_zero).mp hfin

end Main

end LongTails.Proofs.AuxiliaryDaneRun
