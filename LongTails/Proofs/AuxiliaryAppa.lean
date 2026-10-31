import LongTails.Proofs.AuxiliaryDaneRun

namespace LongTails.Proofs.AuxiliaryAppa

open scoped RealInnerProductSpace
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.GuardedMetricAcceleration LongTails.Proofs.GuardedAcceleratedGeometry
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryEval
open LongTails.Proofs.AuxiliaryCertificates LongTails.Proofs.AuxiliaryInner
open LongTails.Proofs.AuxiliaryDane LongTails.Proofs.AuxiliaryDaneRun

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {t : Tuning} {f h : E → ℝ} {L δ ρ Δ : ℝ}

noncomputable def gval (t : Tuning) (f : E → ℝ) (y x : E) : ℝ := f x + t.α * ‖x - y‖ ^ 2

noncomputable def ggrad (t : Tuning) (f : E → ℝ) (y x : E) : E :=
  gradient f x + (2 * t.α) • (x - y)

lemma recBreg_gRecY (t : Tuning) (f : E → ℝ) (y u w : E) :
    recBreg (gRecY t y (Fo f) u) (gRecY t y (Fo f) w) = breg (gval t f y) (ggrad t f y) u w := rfl

noncomputable def bk0 (f : E → ℝ) (y : E) : Book E := { best := (y, f y), cert := none }

section Seq

variable (t f h) (y : E)

noncomputable def P (k : ℕ) : E × E × Book E := appaP t y (Fo f) (Fo h) (bk0 f y) k

noncomputable def vk (k : ℕ) : E := extrapolate t.a (P t f h y k).1 (P t f h y k).2.1

noncomputable def dbook (k : ℕ) : Book E :=
  daneBook t y (vk t f h y k) (Fo f) (Fo h) (P t f h y k).1 (P t f h y k).2.2 (t.J + 1)

lemma P_succ (k : ℕ) : P t f h y (k + 1) = appaNext t y (Fo f) (Fo h) (P t f h y k) :=
  Function.iterate_succ_apply' _ _ _

lemma P_zero : P t f h y 0 = (y, y, bk0 f y) := rfl

lemma x_succ (k : ℕ) :
    (P t f h y (k + 1)).1 = daneX t y (vk t f h y k) (Fo f) (Fo h) (P t f h y k).1 t.J := by
  rw [P_succ]; rfl

lemma z_succ (k : ℕ) :
    (P t f h y (k + 1)).2.1 = centerStep t.a (t.α / 2) (vk t f h y k) (P t f h y k).2.1
      ((2 * t.db) • (vk t f h y k - (P t f h y (k + 1)).1)) := by
  rw [x_succ, P_succ]; rfl

lemma book_succ (k : ℕ) :
    (P t f h y (k + 1)).2.2 =
      (((dbook t f h y k).flag (daneCert t y (vk t f h y k) (Fo f) (Fo h) (P t f h y k).1)).flag
        (guardPair t (gRecY t y (Fo f) (P t f h y k).1) (gRecY t y (Fo f) (P t f h y (k + 1)).1))).flag
        (guardPair t (gRecY t y (Fo f) y) (gRecY t y (Fo f) (P t f h y (k + 1)).1)) := by
  rw [x_succ, P_succ]; rfl

lemma best_succ (k : ℕ) : (P t f h y (k + 1)).2.2.best = (dbook t f h y k).best := by
  rw [book_succ]; rfl

lemma best_mono (k m : ℕ) (hkm : k ≤ m) :
    (P t f h y m).2.2.best.2 ≤ (P t f h y k).2.2.best.2 := by
  induction m with
  | zero => obtain rfl : k = 0 := by omega
            exact le_rfl
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hk | hk
      · rw [best_succ]
        exact ((daneBook_best (t := t) (f := f) (h := h) _ _ _ _ _).1).trans (ih (by omega))
      · obtain rfl : k = m + 1 := by omega
        exact le_rfl

end Seq

lemma e_small (hyp : Hyp t f h L δ ρ Δ) :
    6 * vartheta t ρ * tau t ρ / t.a ≤ t.α * tau t ρ ^ 2 := by
  have hα := hyp.hα
  have hρ := hyp.hρ
  have hdb := hyp.db_pos
  have ha := hyp.ha0
  unfold vartheta tau
  rw [div_le_iff₀ ha]
  have key : t.α * t.α ^ 3 ≤ t.α ^ 3 * t.db := by
    have := mul_le_mul_of_nonneg_left hyp.hαdb (by positivity : 0 ≤ t.α ^ 3)
    nlinarith
  have e1 : 6 * (t.a * t.α ^ 3 / (192 * ρ * t.db)) * (t.α / (32 * ρ)) =
      t.a * (t.α * t.α ^ 3) / (1024 * ρ ^ 2 * t.db) := by field_simp; ring
  have e2 : t.α * (t.α / (32 * ρ)) ^ 2 * t.a = t.a * (t.α ^ 3 * t.db) / (1024 * ρ ^ 2 * t.db) := by
    field_simp; ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left key ha.le

section Inv

variable (t f h) (ρ) (y : E)

def Good (β : ℝ) (p : E × E) : Prop :=
  breg f (gradient f) p.1 p.2 < -(t.α / 2) * ‖p.1 - p.2‖ ^ 2 ∧ p.1 ≠ p.2 ∧
    (β ≤ f p.1 → β ≤ f p.2 → ‖p.1 - y‖ ≤ 3 * tau t ρ ∧ ‖p.2 - y‖ ≤ 3 * tau t ρ)

noncomputable def Gk (k : ℕ) : E := (2 * t.db) • (vk t f h y k - (P t f h y (k + 1)).1)

def Supp (k : ℕ) (u : E) (e : ℝ) : Prop :=
  gval t f y (P t f h y (k + 1)).1 + ‖Gk t f h y k‖ ^ 2 / (2 * (2 * t.db)) +
      ⟪Gk t f h y k, u - vk t f h y k⟫ + t.α / 2 / 2 * ‖u - vk t f h y k‖ ^ 2 ≤ gval t f y u + e

def StepOK (β : ℝ) (k : ℕ) : Prop :=
  ‖ggrad t f y (P t f h y (k + 1)).1 - Gk t f h y k‖ ≤ vartheta t ρ ∧
    ‖(P t f h y (k + 1)).1 - y‖ ≤ 3 * tau t ρ ∧ β ≤ f (P t f h y (k + 1)).1 ∧
    Supp t f h y k (P t f h y k).1 (6 * vartheta t ρ * tau t ρ) ∧
    Supp t f h y k y (6 * vartheta t ρ * tau t ρ)

def Bounds (k : ℕ) : Prop :=
  gval t f y (P t f h y k).1 + t.α / 2 / 2 * ‖y - (P t f h y k).2.1‖ ^ 2 ≤
      f y + 6 * vartheta t ρ * tau t ρ / t.a ∧
    ‖(P t f h y k).1 - y‖ ≤ 3 * tau t ρ ∧ ‖(P t f h y k).2.1 - y‖ ≤ 3 * tau t ρ ∧
    ‖vk t f h y k - y‖ ≤ 3 * tau t ρ ∧
    tval t y (vk t f h y k) f (P t f h y k).1 ≤ f y + 8 * t.α * tau t ρ ^ 2

end Inv

lemma x_gradientStep (hyp : Hyp t f h L δ ρ Δ) (y : E) (k : ℕ) :
    (P t f h y (k + 1)).1 = gradientStep (2 * t.db) (vk t f h y k) (Gk t f h y k) := by
  have hdb := hyp.db_pos
  unfold gradientStep Gk
  rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  abel

lemma potential_of_steps (hyp : Hyp t f h L δ ρ Δ) (y c : E) (β : ℝ) (n : ℕ)
    (hok : ∀ s < n, StepOK t f h ρ y β s) (e : ℝ) (he : 0 ≤ e)
    (hsc : ∀ s < n, Supp t f h y s c e) (hle : 6 * vartheta t ρ * tau t ρ ≤ e) :
    gval t f y (P t f h y n).1 + t.α / 2 / 2 * ‖c - (P t f h y n).2.1‖ ^ 2 ≤
      gval t f y c + (1 - t.a) ^ n * (gval t f y y - gval t f y c + t.α / 2 / 2 * ‖c - y‖ ^ 2) +
        e / t.a := by
  have hdb := hyp.db_pos
  have hα := hyp.hα
  have htune : t.a ^ 2 * (2 * t.db) = t.α / 2 := by have := hyp.ha; linarith
  have := appa_potential (g := gval t f y) (a := t.a) (μ := t.α / 2) (L := 2 * t.db) (e := e)
    hyp.ha0 hyp.ha1 (by positivity) (by positivity) htune he
    (fun k => (P t f h y k).1) (fun k => (P t f h y k).2.1) (Gk t f h y) y c rfl rfl
    (fun k => by rw [z_succ]; rfl) n
    (fun s hs => by
      have := (hok s hs).2.2.2.1
      unfold Supp at this
      unfold vk at this
      linarith)
    (fun s hs => by
      have := hsc s hs
      unfold Supp vk at this
      exact this)
  exact this

omit [CompleteSpace E] in
lemma guardPair_some {w u : Rec E} {q : E × E} (hq : guardPair t w u = some q) :
    q = (w.1, u.1) ∧ recBreg w u < t.α / 2 * ‖w.1 - u.1‖ ^ 2 := by
  unfold guardPair at hq
  split_ifs at hq with hc
  · exact ⟨(Option.some.inj hq).symm, hc⟩

omit [CompleteSpace E] in
lemma guardPair_none {w u : Rec E} (hq : guardPair t w u = none) :
    t.α / 2 * ‖w.1 - u.1‖ ^ 2 ≤ recBreg w u := by
  unfold guardPair at hq
  split_ifs at hq with hc
  exact not_lt.mp hc

omit [CompleteSpace E] in
lemma xv_bound {a : ℝ} (ha : 0 ≤ a) (x z : E) : ‖x - extrapolate a x z‖ ≤ a * ‖x - z‖ := by
  have he : x - extrapolate a x z = (a / (1 + a)) • (x - z) := by
    unfold extrapolate
    have h1 : (1 + a) ≠ 0 := by positivity
    rw [smul_sub, smul_add]
    module_nf
    field_simp
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma bounds_of_steps (hyp : Hyp t f h L δ ρ Δ) (y : E) (β : ℝ)
    (hβ : f y - t.α * tau t ρ ^ 2 < β) (hβy : β ≤ f y) (k : ℕ)
    (hok : ∀ s < k, StepOK t f h ρ y β s) : Bounds t f h ρ y k := by
  have hα := hyp.hα
  have hτ := hyp.tau_pos
  have hdb := hyp.db_pos
  have hE := e_small hyp
  have hp := potential_of_steps hyp y y β k hok (6 * vartheta t ρ * tau t ρ)
    (by have := hyp.vartheta_nonneg; positivity) (fun s hs => (hok s hs).2.2.2.2) le_rfl
  have hgy : gval t f y y = f y := by simp [gval]
  simp only [hgy, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero] at hp
  have hfx : β ≤ f (P t f h y k).1 := by
    cases k with
    | zero => simpa [P_zero] using hβy
    | succ s => exact (hok s (by omega)).2.2.1
  set X := ‖(P t f h y k).1 - y‖ ^ 2 with hXdef
  set Z := ‖y - (P t f h y k).2.1‖ ^ 2 with hZdef
  have hsum : t.α * X + t.α / 2 / 2 * Z < 2 * t.α * tau t ρ ^ 2 := by
    simp only [gval] at hp
    linarith
  have hX0 : 0 ≤ X := sq_nonneg _
  have hZ0 : 0 ≤ Z := sq_nonneg _
  have hXZ : X + Z / 4 < 2 * tau t ρ ^ 2 := by
    have : t.α * (X + Z / 4) < t.α * (2 * tau t ρ ^ 2) := by linarith
    exact lt_of_mul_lt_mul_left this hα.le
  have h3 : (3 * tau t ρ) ^ 2 = 9 * tau t ρ ^ 2 := by ring
  have hxl : ‖(P t f h y k).1 - y‖ ≤ 3 * tau t ρ := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    rw [h3]; linarith
  have hzl : ‖(P t f h y k).2.1 - y‖ ≤ 3 * tau t ρ := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    rw [h3, norm_sub_rev]; linarith
  have hvl := extrapolate_radius hyp.ha0.le y _ _ hxl hzl
  refine ⟨hp, hxl, hzl, hvl, ?_⟩
  have hxv := xv_bound hyp.ha0.le (P t f h y k).1 (P t f h y k).2.1
  have hxz : ‖(P t f h y k).1 - (P t f h y k).2.1‖ ^ 2 ≤ 2 * X + 2 * Z := by
    have he : (P t f h y k).1 - (P t f h y k).2.1 =
        ((P t f h y k).1 - y) - ((P t f h y k).2.1 - y) := by abel
    rw [he]
    have := norm_sub_sq_le ((P t f h y k).1 - y) ((P t f h y k).2.1 - y)
    rw [norm_sub_rev ((P t f h y k).2.1) y] at this
    exact this
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hxv 2
  rw [mul_pow] at hsq
  have hdbv : t.db * ‖(P t f h y k).1 - vk t f h y k‖ ^ 2 ≤ t.α / 4 * (2 * X + 2 * Z) := by
    have h1 : t.db * ‖(P t f h y k).1 - vk t f h y k‖ ^ 2 ≤
        t.db * (t.a ^ 2 * ‖(P t f h y k).1 - (P t f h y k).2.1‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hdb.le
    have h2 : t.db * (t.a ^ 2 * ‖(P t f h y k).1 - (P t f h y k).2.1‖ ^ 2) =
        t.α / 4 * ‖(P t f h y k).1 - (P t f h y k).2.1‖ ^ 2 := by
      have := hyp.ha; field_simp; nlinarith
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hxz (by positivity))
  have hXZα := mul_le_mul_of_nonneg_left hXZ.le hα.le
  have hαX := mul_nonneg hα.le hX0
  have hαZ := mul_nonneg hα.le hZ0
  unfold tval
  simp only [gval] at hp
  rw [← hXdef]
  linarith

section Step

variable (t f h) (ρ) (y : E)

def Inv (β : ℝ) (k : ℕ) : Prop :=
  (∀ p, (P t f h y k).2.2.cert = some p → Good t f ρ y β p) ∧
    ((P t f h y k).2.2.cert = none → ∀ s < k, StepOK t f h ρ y β s)

end Step

lemma ggrad_sub_G (y : E) (k : ℕ) :
    ggrad t f y (P t f h y (k + 1)).1 - Gk t f h y k =
      tgrad t y (vk t f h y k) f (P t f h y (k + 1)).1 := by
  unfold ggrad Gk tgrad
  module

lemma good_of_cand (hyp : Hyp t f h L δ ρ Δ) (y v s : E) (β : ℝ)
    (hβ : f y - t.α * tau t ρ ^ 2 < β) (hTs : tval t y v f s ≤ f y + 8 * t.α * tau t ρ ^ 2)
    {p : E × E} (hp : Cand t f y v s p) : Good t f ρ y β p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨h1, h2, fun hf1 hf2 => ⟨local_of_tval hyp y v p.1 β hβ hf1 (h3.trans hTs),
    local_of_tval hyp y v p.2 β hβ hf2 (h4.trans hTs)⟩⟩

lemma supp_of_guard (hyp : Hyp t f h L δ ρ Δ) (y : E) (k : ℕ) (u : E)
    (hacc : ‖ggrad t f y (P t f h y (k + 1)).1 - Gk t f h y k‖ ≤ vartheta t ρ)
    (hu : ‖u - y‖ ≤ 3 * tau t ρ) (hx : ‖(P t f h y (k + 1)).1 - y‖ ≤ 3 * tau t ρ)
    (hg : t.α / 2 * ‖u - (P t f h y (k + 1)).1‖ ^ 2 ≤
      breg (gval t f y) (ggrad t f y) u (P t f h y (k + 1)).1) :
    Supp t f h y k u (6 * vartheta t ρ * tau t ρ) := by
  have hdb := hyp.db_pos
  have hs := support_of_guard (g := gval t f y) (dg := ggrad t f y) hyp.hα.le
    (by linarith [hyp.hαdb, hyp.hα]) hdb u (vk t f h y k) (P t f h y (k + 1)).1 (Gk t f h y k)
    (by rw [x_gradientStep hyp y k]; rfl) hacc hg
  have hd : ‖u - (P t f h y (k + 1)).1‖ ≤ 6 * tau t ρ := by
    calc ‖u - (P t f h y (k + 1)).1‖ = ‖(u - y) - ((P t f h y (k + 1)).1 - y)‖ := by
          congr 1; abel
      _ ≤ ‖u - y‖ + ‖(P t f h y (k + 1)).1 - y‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have he := mul_le_mul_of_nonneg_left hd hyp.vartheta_nonneg
  unfold Supp
  linarith

lemma inv_step (hyp : Hyp t f h L δ ρ Δ) (y : E) (hGy : ‖gradient f y‖ ^ 2 ≤ 2 * (L + δ) * Δ)
    (β : ℝ) (hβ : f y - t.α * tau t ρ ^ 2 < β) (hβy : β ≤ f y) (k : ℕ)
    (hβk : β ≤ (P t f h y (k + 1)).2.2.best.2) (hI : Inv t f h ρ y β k) :
    Inv t f h ρ y β (k + 1) := by
  obtain ⟨hI1, hI2⟩ := hI
  have hcert := book_succ t f h y k
  set dc := daneCert t y (vk t f h y k) (Fo f) (Fo h) (P t f h y k).1
  set c1 := guardPair t (gRecY t y (Fo f) (P t f h y k).1) (gRecY t y (Fo f) (P t f h y (k + 1)).1)
  set c2 := guardPair t (gRecY t y (Fo f) y) (gRecY t y (Fo f) (P t f h y (k + 1)).1)
  have hdc := daneBook_cert (t := t) (f := f) (h := h) y (vk t f h y k) (P t f h y k).1
    (P t f h y k).2.2 (t.J + 1)
  cases hk : (P t f h y k).2.2.cert with
  | some p =>
      have hp1 := Book.flag_some _ c2 (Book.flag_some _ c1 (Book.flag_some _ dc (hdc.1 p hk)))
      have hpk : (P t f h y (k + 1)).2.2.cert = some p := by rw [hcert]; exact hp1
      refine ⟨fun q hq => ?_, fun hn => ?_⟩
      · rw [hpk] at hq
        cases hq
        exact hI1 p hk
      · rw [hpk] at hn
        cases hn
  | none =>
      have hok := hI2 hk
      have hB := bounds_of_steps hyp y β hβ hβy k hok
      obtain ⟨_, hxl, _, hvl, hTl⟩ := hB
      have hnote : β ≤ (dbook t f h y k).best.2 := by rw [← best_succ]; exact hβk
      have DA := dane_analysis hyp y (vk t f h y k) (P t f h y k).1 (P t f h y k).2.2 hGy hvl hTl β
        hβ hnote
      obtain ⟨DA1, DA2, DA3, DA4⟩ := DA
      have hx1 : (P t f h y (k + 1)).1 = daneX t y (vk t f h y k) (Fo f) (Fo h) (P t f h y k).1 t.J :=
        x_succ t f h y k
      have hloc1 : ‖(P t f h y (k + 1)).1 - y‖ ≤ 3 * tau t ρ := by
        rw [hx1]; exact (DA1 t.J (by omega)).2.2
      have hfx1 : β ≤ f (P t f h y (k + 1)).1 := by
        rw [hx1]; exact (DA1 t.J (by omega)).2.1
      refine ⟨fun q hq => ?_, fun hn => ?_⟩
      · rw [hcert] at hq
        rcases Book.flag_cases _ _ hq with hq | ⟨_, hq⟩
        · rcases Book.flag_cases _ _ hq with hq | ⟨_, hq⟩
          · rcases Book.flag_cases _ _ hq with hq | ⟨_, hq⟩
            · rcases hdc.2.1 q hq with hq | ⟨j, hj, hq⟩
              · rw [hk] at hq; cases hq
              · exact good_of_cand hyp y _ _ β hβ hTl (DA2 j (by omega) q hq)
            · exact good_of_cand hyp y _ _ β hβ hTl (DA3 q hq)
          · obtain ⟨rfl, hb⟩ := guardPair_some hq
            rw [recBreg_g] at hb
            have hc := transfer_g rfl hb
            exact ⟨hc, ne_of_breg_neg hc, fun _ _ => ⟨hxl, hloc1⟩⟩
        · obtain ⟨rfl, hb⟩ := guardPair_some hq
          rw [recBreg_g] at hb
          have hc := transfer_g rfl hb
          exact ⟨hc, ne_of_breg_neg hc, fun _ _ => ⟨by show ‖y - y‖ ≤ 3 * tau t ρ; rw [sub_self, norm_zero]; have := hyp.tau_pos; positivity,
            hloc1⟩⟩
      · rw [hcert] at hn
        obtain ⟨hn, hc2⟩ := Book.flag_none _ _ hn
        obtain ⟨hn, hc1⟩ := Book.flag_none _ _ hn
        obtain ⟨hn, hdc0⟩ := Book.flag_none _ _ hn
        have hcheap := hdc.2.2 hn
        have hacc := DA4 (fun j hj => hcheap j (by omega)) hdc0
        rw [← hx1, ← ggrad_sub_G] at hacc
        intro s hs
        rcases Nat.lt_or_ge s k with hs' | hs'
        · exact hok s hs'
        · obtain rfl : s = k := by omega
          exact ⟨hacc, hloc1, hfx1, supp_of_guard hyp y _ _ hacc hxl hloc1
            (by have := guardPair_none hc1; rwa [recBreg_gRecY] at this),
            supp_of_guard hyp y _ _ hacc (by rw [sub_self, norm_zero]; have := hyp.tau_pos; positivity) hloc1
            (by have := guardPair_none hc2; rwa [recBreg_gRecY] at this)⟩

end LongTails.Proofs.AuxiliaryAppa
