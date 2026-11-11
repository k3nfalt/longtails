import LongTails.Proofs.LogFreeInvariant
import LongTails.Proofs.LogFreeModes

namespace LongTails.Proofs.LogFreeStepGood

open OracleTemplate LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LogFreeProxNewton
open LongTails.Proofs.LogFreeGeometry LongTails.Proofs.LogFreeTail
  LongTails.Proofs.LogFreeTransition LongTails.Proofs.LogFreeParameters
  LongTails.Proofs.LogFreeLinearAlgebra LongTails.Proofs.LogFreeInvariant
  LongTails.Proofs.LogFreeModes LongTails.Proofs.LogFreeSteps LongTails.Proofs.LogFreeEscape
open scoped RealInnerProductSpace

variable (p : Params) (f : p.E → ℝ)

lemma exact_x (x : p.E) : (exact p f x).x = x := rfl

lemma moved_exact (st : State p.E) (H : p.E →L[ℝ] p.E) :
    (⟨candidates p st H (choose p st H (values p f st H)),
      (values p f st H (choose p st H (values p f st H))).1,
      (values p f st H (choose p st H (values p f st H))).2,
      fderiv ℝ (gradient f) (landing p st H (values p f st H))⟩ : Data p.E) =
      exact p f (landing p st H (values p f st H)) := rfl

lemma landing_key (st : State p.E) (H : p.E →L[ℝ] p.E) (i : Fin 5) :
    key p st H (landing p st H (values p f st H)) (f (landing p st H (values p f st H))) ≤
      key p st H (candidates p st H i) (f (candidates p st H i)) :=
  choose_le p st H (values p f st H) i

lemma base_nonneg (hp : spec.valid p) (ha : Admissible p f) (c : p.E) :
    0 ≤ phaseWeight * (f c - (f p.x0 - p.Δ)) / threshold p := by
  have hq : 0 < threshold p := by unfold threshold; have := unit_pos p hp; positivity
  have := ha.gap c
  unfold phaseWeight
  apply div_nonneg _ hq.le
  apply mul_nonneg (by norm_num); linarith

lemma measure_nonneg (hp : spec.valid p) (ha : Admissible p f) {n : ℕ} {st : State p.E}
    (hg : Good p f n st) : 0 ≤ potential p f st := by
  unfold potential
  split_ifs with hd ht
  · exact le_rfl
  · have hb := base_nonneg p f hp ha st.center
    have hl := (hg.tailInv ht).lev
    have : (st.level : ℝ) ≤ finalLevel p := by exact_mod_cast hl
    linarith
  · have hb := base_nonneg p f hp ha st.center
    have : (0 : ℝ) ≤ finalLevel p := Nat.cast_nonneg _
    have := le_max_left (0 : ℝ) (64 * (regF f (weight p) st.center st.cur.x - f st.center +
      threshold p) / tailLevel p + 1)
    linarith

lemma tailLevel_pos (hp : spec.valid p) : 0 < tailLevel p := by
  unfold tailLevel; have := unit_pos p hp; positivity

lemma threshold_pos (hp : spec.valid p) : 0 < threshold p := by
  unfold threshold; have := unit_pos p hp; positivity

lemma newPhase_measure (hp : spec.valid p) {c b : p.E} {D : ℝ} {extra : ℝ}
    (hD : D * threshold p ≤ f c - f b) (hextra : extra + 1 ≤ phaseWeight * D - 2 ^ 14 - 3) :
    phaseWeight * (f b - (f p.x0 - p.Δ)) / threshold p + 2 ^ 14 + 3 + extra + 1 ≤
      phaseWeight * (f c - (f p.x0 - p.Δ)) / threshold p := by
  have hq := threshold_pos p hp
  have hw : (0 : ℝ) < phaseWeight := by unfold phaseWeight; norm_num
  have : phaseWeight * (f c - (f p.x0 - p.Δ)) / threshold p -
      phaseWeight * (f b - (f p.x0 - p.Δ)) / threshold p = phaseWeight * (f c - f b) / threshold p := by
    ring
  have h2 : phaseWeight * D ≤ phaseWeight * (f c - f b) / threshold p := by
    rw [le_div_iff₀ hq]; nlinarith
  linarith

def Progress (n : ℕ) (st st' : State p.E) : Prop :=
  Good p f (n + 1) st' ∧ (st'.done = true ∨ potential p f st' ≤ potential p f st - 1)

lemma data_of_good {n : ℕ} {st : State p.E} (hg : Good p f n st) :
    st.cur.value = f st.cur.x ∧ st.cur.grad = gradient f st.cur.x ∧
      st.cur.hess = fderiv ℝ (gradient f) st.cur.x :=
  ⟨congrArg Data.value hg.cur, congrArg Data.grad hg.cur, congrArg Data.hess hg.cur⟩

lemma global_measure {st : State p.E} (hd : st.done = false) (ht : st.tail = false) :
    potential p f st = phaseWeight * (f st.center - (f p.x0 - p.Δ)) / threshold p + finalLevel p +
      (2 + max 0 (64 * (regF f (weight p) st.center st.cur.x - f st.center + threshold p) /
        tailLevel p + 1)) := by
  unfold potential; simp [hd, ht]

lemma tail_measure {st : State p.E} (hd : st.done = false) (ht : st.tail = true) :
    potential p f st = phaseWeight * (f st.center - (f p.x0 - p.Δ)) / threshold p + finalLevel p +
      (1 - st.level) := by
  unfold potential; simp [hd, ht]

lemma restart_term (hp : spec.valid p) (b : p.E) :
    max 0 (64 * (regF f (weight p) b b - f b + threshold p) / tailLevel p + 1) = 2 ^ 14 + 1 := by
  have hreg : regF f (weight p) b b = f b := by simp [regF]
  rw [hreg]
  have hu := unit_pos p hp
  have : 64 * (f b - f b + threshold p) / tailLevel p + 1 = 2 ^ 14 + 1 := by
    unfold threshold tailLevel; field_simp; ring
  rw [this]; exact max_eq_right (by norm_num)

lemma no_curvature {γ : ℝ} {d : Data p.E} (h : (curvature γ d).isSome = false) :
    ∀ v, -(γ / 4) * ‖v‖ ^ 2 ≤ ⟪d.hess v, v⟫ := by
  classical
  intro v
  by_cases hv : v = 0
  · subst hv; simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnot : ¬ ∃ w : p.E, ‖w‖ = 1 ∧ ⟪d.hess w, w⟫ ≤ -(γ / 4) := by
    intro hex
    unfold curvature at h
    rw [dite_eq_left hex] at h
    simp at h
  have hw : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hlt : -(γ / 4) < ⟪d.hess (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫ := by
    by_contra hle
    exact hnot ⟨_, hw, le_of_not_gt hle⟩
  rw [map_smul, real_inner_smul_left, real_inner_smul_right] at hlt
  have h2 : ⟪d.hess v, v⟫ = ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * ⟪d.hess v, v⟫)) := by
    field_simp
  rw [h2]
  nlinarith [sq_nonneg ‖v‖]

lemma curvature_spec {γ : ℝ} {d : Data p.E} (h : (curvature γ d).isSome = true) :
    ‖(curvature γ d).getD 0‖ = 1 ∧ ⟪d.hess ((curvature γ d).getD 0), (curvature γ d).getD 0⟫ ≤
      -(γ / 4) := by
  classical
  unfold curvature at h ⊢
  split_ifs with hex
  · simpa using hex.choose_spec
  · rw [dite_eq_right hex] at h; simp at h


section Modes

variable (hp : spec.valid p) (ha : Admissible p f)
include hp ha

omit ha in
lemma step_stop {n : ℕ} {st : State p.E} (hg : Good p f n st) (hnd : st.done = false)
    (hgrad : ‖st.cur.grad‖ ≤ p.ε) : Progress p f n st (transition p f st) := by
  have hm := mode_stop p st (fderiv ℝ (gradient f) (probe p st)) hnd hgrad
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  rw [transition_eq]
  simp only [next, hm]
  refine ⟨⟨hg.cur, hg.center, hg.mono, hg.top, ?_, fun h => ?_, fun _ => ?_⟩, Or.inl rfl⟩
  · have := scale_pos p hp
    exact hg.path.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) (by positivity))
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hg.tailInv h
    exact ⟨h1, h2, h3, h4, h5⟩
  · simpa [hgr] using hgrad

omit ha in
lemma step_success {n : ℕ} {st : State p.E} (hg : Good p f n st) (hnd : st.done = false)
    (hgrad : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : st.cur.value ≤ st.centerValue - threshold p) :
    Progress p f n st (transition p f st) := by
  have hm : mode p st (fderiv ℝ (gradient f) (probe p st)) = .success := by
    exact mode_success p st _ hnd hgrad ht hs
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  have hq := threshold_pos p hp
  rw [transition_eq]
  simp only [next, hm]
  have hcv := hg.center
  have hfy : f st.cur.x ≤ f st.center - threshold p := by rw [← hval, ← hcv]; exact hs
  refine ⟨⟨hg.cur, hval, ?_, ?_, ?_, fun h => by simp [ht] at h, fun h => by simp [hnd] at h⟩, ?_⟩
  · simp [regF]
  · linarith [hg.top]
  · have := scale_pos p hp
    exact hg.path.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) (by positivity))
  · right
    rw [global_measure p f (st := { st with center := st.cur.x, centerValue := st.cur.value })
      hnd ht, global_measure p f hnd ht]
    simp only
    rw [restart_term p f hp]
    have hmax := le_max_left (0 : ℝ) (64 * (regF f (weight p) st.center st.cur.x - f st.center +
      threshold p) / tailLevel p + 1)
    have hnew := newPhase_measure p f hp (c := st.center) (b := st.cur.x) (D := 1) (extra := -1)
      (by linarith) (by unfold phaseWeight; norm_num)
    linarith

omit hp ha in
lemma path_step {n : ℕ} {st : State p.E} (hg : Good p f n st) {b : p.E}
    (hb : ‖b - st.cur.x‖ ≤ 2 * scale p) : ‖b - p.x0‖ ≤ 2 * scale p * (n + 1 : ℕ) := by
  have h := hg.path
  calc ‖b - p.x0‖ = ‖(b - st.cur.x) + (st.cur.x - p.x0)‖ := by congr 1; abel
    _ ≤ ‖b - st.cur.x‖ + ‖st.cur.x - p.x0‖ := norm_add_le _ _
    _ ≤ 2 * scale p + 2 * scale p * n := add_le_add hb h
    _ = 2 * scale p * (n + 1 : ℕ) := by push_cast; ring

lemma step_escape {n : ℕ} {st : State p.E} (hg : Good p f n st) (hnd : st.done = false)
    (hgrad : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : ¬ st.cur.value ≤ st.centerValue - threshold p)
    (hc : (curvature (weight p) st.cur).isSome = true) :
    Progress p f n st (transition p f st) := by
  set Hp := fderiv ℝ (gradient f) (probe p st) with hHp
  have hm : mode p st Hp = .escape := by
    exact mode_escape p st _ hnd hgrad ht hs hc
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  obtain ⟨hv1, hvneg⟩ := curvature_spec p hc
  set v := (curvature (weight p) st.cur).getD 0 with hv
  set y := st.cur.x with hy
  set b := landing p st Hp (values p f st Hp) with hb
  have hL := hp.1
  have hr := scale_pos p hp
  have hu := unit_eq p hp
  have hesc := plain_escape ha.smooth hL.le ha.lip (weight p) (scale p) y v hv1
    (by rw [← hhe]; exact hvneg)
  have hcand : candidates p st Hp = ![y + scale p • v, y - scale p • v, y + scale p • v,
      y + scale p • v, y + scale p • v] := by
    unfold candidates; rw [hm]
  have hkey : ∀ x w, key p st Hp x w = w := by intro x w; unfold key; simp [hm]
  have hb0 := landing_key p f st Hp 0
  have hb1 := landing_key p f st Hp 1
  rw [hkey, hkey, hcand] at hb0 hb1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb0 hb1
  have hfb : f b ≤ f y - weight p * scale p ^ 2 / 8 + p.L₃ * scale p ^ 4 := by
    have hmin : f b ≤ min (f (y + scale p • v)) (f (y - scale p • v)) := le_min hb0 hb1
    exact hmin.trans hesc
  have hws := weight_scale p hp
  have hmono := hg.mono
  have hreg : f y ≤ regF f (weight p) st.center y := by
    have := weight_pos p hp
    have : 0 ≤ weight p / 2 * ‖y - st.center‖ ^ 2 := by positivity
    unfold regF; linarith
  have hfc : f b ≤ f st.center - 31 * unit p := by
    have : weight p * scale p ^ 2 / 8 = 32 * unit p := by linarith
    rw [← hu] at hfb
    have := hreg.trans hmono
    nlinarith
  have hbdist : ‖b - y‖ ≤ 2 * scale p := by
    have hbin : b ∈ Set.range (candidates p st Hp) := ⟨_, rfl⟩
    rw [hcand] at hbin
    obtain ⟨i, hi⟩ := hbin
    rw [← hi]
    fin_cases i <;> simp [norm_smul, hv1, abs_of_pos hr] <;> linarith
  have htr : transition p f st = { st with center := b, centerValue := f b, cur := exact p f b } := by
    rw [transition_eq, ← hHp]; simp only [next, hm]; rfl
  rw [htr]
  have hq := threshold_pos p hp
  have hu0 := unit_pos p hp
  refine ⟨⟨rfl, rfl, by simp [regF, exact], ?_, path_step p f hg hbdist, fun h => by simp [ht] at h,
    fun h => by simp [hnd] at h⟩, ?_⟩
  · have := hg.top; nlinarith
  · right
    rw [global_measure p f (st := { st with center := b, centerValue := f b, cur := exact p f b })
      hnd ht, global_measure p f hnd ht]
    simp only [exact_x]
    rw [restart_term p f hp]
    have hmax := le_max_left (0 : ℝ) (64 * (regF f (weight p) st.center st.cur.x - f st.center +
      threshold p) / tailLevel p + 1)
    have hnew := newPhase_measure p f hp (c := st.center) (b := b) (D := 1) (extra := -1)
      (by unfold threshold; nlinarith) (by unfold phaseWeight; norm_num)
    linarith

omit hp ha in
lemma coercive_global {st : State p.E} (hhe : st.cur.hess = fderiv ℝ (gradient f) st.cur.x)
    (hc : (curvature (weight p) st.cur).isSome = false) :
    ∀ v, 3 * weight p / 4 * ‖v‖ ^ 2 ≤ ⟪sys f (weight p) st.cur.x v, v⟫ := by
  intro v
  have h := no_curvature p hc v
  rw [hhe] at h
  rw [sys_inner]
  nlinarith [sq_nonneg ‖v‖]

omit hp ha in
lemma system_eq_sys {st : State p.E} (hhe : st.cur.hess = fderiv ℝ (gradient f) st.cur.x) :
    system (weight p) st.cur = sys f (weight p) st.cur.x := by
  unfold system sys; rw [hhe]

omit ha in
lemma step_enter {n : ℕ} {st : State p.E} (hg : Good p f n st) (hnd : st.done = false)
    (hgrad : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : ¬ st.cur.value ≤ st.centerValue - threshold p)
    (hc : (curvature (weight p) st.cur).isSome = false)
    (hdec : decrement (weight p) st.center st.cur ≤ tailLevel p) :
    Progress p f n st (transition p f st) := by
  set Hp := fderiv ℝ (gradient f) (probe p st) with hHp
  have hm : mode p st Hp = .enter := by
    exact mode_enter p st _ hnd hgrad ht hs hc hdec
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  have htr : transition p f st = { st with tail := true, level := 0 } := by
    rw [transition_eq, ← hHp]; simp only [next, hm]
  rw [htr]
  have hw := weight_pos p hp
  have hq := threshold_pos p hp
  have hcoer := coercive_global p f hhe hc
  refine ⟨⟨hg.cur, hg.center, hg.mono, hg.top, ?_, fun _ => ?_, fun h => by simp [hnd] at h⟩, ?_⟩
  · have := scale_pos p hp
    exact hg.path.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) (by positivity))
  · refine ⟨?_, ?_, fun h => by simp at h, ?_, by simp⟩
    · intro v
      have : coerciveLevel p 0 = 3 * weight p / 4 := by unfold coerciveLevel; simp
      show coerciveLevel p 0 * ‖v‖ ^ 2 ≤ _
      rw [this]; exact hcoer v
    · simpa using hdec
    · show ‖st.cur.x - st.center‖ ≤ radius p 0
      unfold radius
      simp only [pow_zero, div_one, sub_self, mul_zero, zero_mul, add_zero]
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      have hfy : f st.center - threshold p < f st.cur.x := by
        rw [← hval, ← hg.center]; exact lt_of_not_ge hs
      have hm' := hg.mono
      unfold regF at hm'
      rw [le_div_iff₀ hw]
      nlinarith
  · right
    rw [tail_measure p f (st := { st with tail := true, level := 0 }) hnd rfl,
      global_measure p f hnd ht]
    simp only [Nat.cast_zero, sub_zero]
    have := le_max_left (0 : ℝ) (64 * (regF f (weight p) st.center st.cur.x - f st.center +
      threshold p) / tailLevel p + 1)
    linarith

lemma step_newton {n : ℕ} {st : State p.E} (hg : Good p f n st) (hnd : st.done = false)
    (hgrad : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : ¬ st.cur.value ≤ st.centerValue - threshold p)
    (hc : (curvature (weight p) st.cur).isSome = false)
    (hdec : ¬ decrement (weight p) st.center st.cur ≤ tailLevel p) :
    Progress p f n st (transition p f st) := by
  set Hp := fderiv ℝ (gradient f) (probe p st) with hHp
  have hm : mode p st Hp = .newton := by
    exact mode_newton p st _ hnd hgrad ht hs hc hdec
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  have hw := weight_pos p hp
  have hq := threshold_pos p hp
  have hr := scale_pos p hp
  have hu := unit_eq p hp
  have hL := hp.1
  have hcoer := coercive_global p f hhe hc
  have hsys := system_eq_sys p f hhe
  have hμ : 0 < 3 * weight p / 4 := by positivity
  have hcoer' : ∀ v, 3 * weight p / 4 * ‖v‖ ^ 2 ≤ ⟪system (weight p) st.cur v, v⟫ := by
    rw [hsys]; exact hcoer
  set y := st.cur.x with hy
  set c := st.center with hcdef
  set d := direction (weight p) c st.cur with hd
  have hspec := direction_spec p hμ c st.cur hcoer'
  have hdeq := decrement_eq p hμ c st.cur hcoer'
  have hd' : fderiv ℝ (gradient f) y d + weight p • d = -(gradient f y + weight p • (y - c)) := by
    have := hspec; rw [hsys] at this
    simpa [sys, LongTails.Algorithms.LogFreeProxNewton.residual, hgr] using this
  have hΛ : decrement (weight p) c st.cur = ⟪fderiv ℝ (gradient f) y d, d⟫ + weight p * ‖d‖ ^ 2 := by
    rw [hdeq, hsys, sys_inner]
  have hΛgt : tailLevel p < ⟪fderiv ℝ (gradient f) y d, d⟫ + weight p * ‖d‖ ^ 2 := by
    rw [← hΛ]; exact lt_of_not_ge hdec
  have hd0 : d ≠ 0 := by
    intro h; rw [h] at hΛgt; simp at hΛgt; linarith [tailLevel_pos p hp]
  obtain ⟨t, htmem, hdesc⟩ := newton_grid ha.smooth hL.le ha.lip (γ := weight p) (r := scale p)
    (weight_eq p).symm.le hr c y d (fun v => (hcoer v).trans_eq (sys_inner f _ _ v)) hd' hd0
  have hcand : ∀ i, candidates p st Hp i = y + (grid i * stepLength p c st.cur) • d := by
    intro i; unfold candidates; rw [hm]
  have hkey : ∀ x w, key p st Hp x w = regularized (weight p) c x w := by
    intro x w; unfold key; simp [hm]; rfl
  have hregF : ∀ x, regularized (weight p) c x (f x) = regF f (weight p) c x := by
    intro x; rfl
  set b := landing p st Hp (values p f st Hp) with hb
  have hidx : ∃ i, grid i = t := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at htmem
    rcases htmem with h | h | h | h | h
    · exact ⟨0, by simp [grid, h]⟩
    · exact ⟨1, by simp [grid, h]⟩
    · exact ⟨2, by simp [grid, h]⟩
    · exact ⟨3, by simp [grid, h]⟩
    · exact ⟨4, by simp [grid, h]⟩
  obtain ⟨i, hi⟩ := hidx
  have hbk := landing_key p f st Hp i
  rw [hkey, hkey, hregF, hregF, hcand i, hi] at hbk
  have hstep : stepLength p c st.cur = min 1 (scale p / ‖d‖) := rfl
  rw [hstep] at hbk
  have hmin : tailLevel p / 64 ≤ min ((⟪fderiv ℝ (gradient f) y d, d⟫ + weight p * ‖d‖ ^ 2) / 64)
      (weight p * scale p ^ 2 / 64 - p.L₃ * scale p ^ 4) := by
    apply le_min
    · linarith
    · have hws := weight_scale p hp
      have : weight p * scale p ^ 2 / 64 - p.L₃ * scale p ^ 4 = 3 * unit p := by
        rw [← hu]; linarith
      rw [this]; unfold tailLevel; have := unit_pos p hp; nlinarith
  have hFb : regF f (weight p) c b ≤ regF f (weight p) c y - tailLevel p / 64 := by
    linarith
  have hbdist : ‖b - y‖ ≤ 2 * scale p := by
    have hbin : b ∈ Set.range (candidates p st Hp) := ⟨_, rfl⟩
    obtain ⟨k, hk⟩ := hbin
    rw [← hk, hcand k, hstep, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hgk : |grid k| ≤ 1 := by fin_cases k <;> norm_num [grid]
    have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
    have hτ0 : 0 ≤ min 1 (scale p / ‖d‖) := le_min zero_le_one (div_nonneg hr.le hdn.le)
    have hτ : min 1 (scale p / ‖d‖) * ‖d‖ ≤ scale p := by
      calc min 1 (scale p / ‖d‖) * ‖d‖ ≤ scale p / ‖d‖ * ‖d‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hdn.le
        _ = scale p := by field_simp
    rw [abs_mul, abs_of_nonneg hτ0]
    calc |grid k| * min 1 (scale p / ‖d‖) * ‖d‖ ≤ 1 * min 1 (scale p / ‖d‖) * ‖d‖ := by gcongr
      _ ≤ 2 * scale p := by linarith
  have htr : transition p f st = { st with cur := exact p f b } := by
    rw [transition_eq, ← hHp]; simp only [next, hm]; rfl
  rw [htr]
  refine ⟨⟨rfl, hg.center, ?_, hg.top, path_step p f hg hbdist, fun h => by simp [ht] at h,
    fun h => by simp [hnd] at h⟩, ?_⟩
  · simp only [exact_x]; have := hg.mono; have := tailLevel_pos p hp; linarith
  · right
    rw [global_measure p f (st := { st with cur := exact p f b }) hnd ht, global_measure p f hnd ht]
    simp only [exact_x]
    have hfy : f c - threshold p < f y := by rw [← hval, ← hg.center]; exact lt_of_not_ge hs
    have hregy : f y ≤ regF f (weight p) c y := by
      have : 0 ≤ weight p / 2 * ‖y - c‖ ^ 2 := by positivity
      unfold regF; linarith
    have hlam := tailLevel_pos p hp
    set X := 64 * (regF f (weight p) c y - f c + threshold p) / tailLevel p with hX
    set X' := 64 * (regF f (weight p) c b - f c + threshold p) / tailLevel p with hX'
    have hX0 : 0 ≤ X := by rw [hX]; apply div_nonneg _ hlam.le; nlinarith
    have hXX : X' ≤ X - 1 := by
      rw [hX, hX', le_sub_iff_add_le, div_add_one hlam.ne', div_le_div_iff_of_pos_right hlam]
      nlinarith
    have h1 : max 0 (X' + 1) ≤ X := max_le hX0 (by linarith)
    have h2 : max 0 (X + 1) = X + 1 := max_eq_right (by linarith)
    rw [h2]
    linarith

omit hp ha in
lemma probe_tail {st : State p.E} (ht : st.tail = true) :
    probe p st = st.cur.x + direction (weight p) st.center st.cur := by
  unfold probe; simp [ht]

omit ha in
lemma tail_data {n : ℕ} {st : State p.E} (hg : Good p f n st) (ht : st.tail = true) :
    let d := direction (weight p) st.center st.cur
    fderiv ℝ (gradient f) st.cur.x d + weight p • d =
        -(gradient f st.cur.x + weight p • (st.cur.x - st.center)) ∧
      decrement (weight p) st.center st.cur = ⟪sys f (weight p) st.cur.x d, d⟫ := by
  intro d
  have TG := hg.tailInv ht
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  have hw := weight_pos p hp
  have hμ : 0 < weight p / 2 := by positivity
  have hcoer := tail_coercive p f hp hg.cur TG
  have hspec := direction_spec p hμ st.center st.cur hcoer
  have hdec := decrement_eq p hμ st.center st.cur hcoer
  have hsys := system_eq_sys p f hhe
  rw [hsys] at hspec hdec
  refine ⟨?_, hdec⟩
  simpa [sys, LongTails.Algorithms.LogFreeProxNewton.residual, hgr] using hspec

omit ha in
lemma tail_small {n : ℕ} {st : State p.E} (hg : Good p f n st) (ht : st.tail = true) :
    decrement (weight p) st.center st.cur ≤ tailLevel p := by
  have TG := hg.tailInv ht
  have h1 : (1 : ℝ) ≤ 16 ^ st.level := one_le_pow₀ (by norm_num)
  have h0 : 0 ≤ decrement (weight p) st.center st.cur := by
    rw [(tail_data p f hp hg ht).2]
    exact le_trans (by have := weight_pos p hp; positivity)
      ((tail_coercive p f hp hg.cur TG _).trans_eq (by rw [system_eq_sys p f (data_of_good p f hg).2.2]))
  nlinarith [TG.dec]

set_option maxHeartbeats 1000000 in
lemma step_advance {n : ℕ} (hn : n < steps p) {st : State p.E} (hg : Good p f n st)
    (hnd : st.done = false) (hgrad : p.ε < ‖st.cur.grad‖) (ht : st.tail = true)
    (hst : stable (weight p) (tolerance st.level) st.cur
      (fderiv ℝ (gradient f) (probe p st))) :
    Progress p f n st (transition p f st) := by
  set Hp := fderiv ℝ (gradient f) (probe p st) with hHp
  have hm : mode p st Hp = .advance := mode_advance p st _ hnd hgrad ht hst
  have TG := hg.tailInv ht
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  obtain ⟨hd', hΛeq⟩ := tail_data p f hp hg ht
  have hw := weight_pos p hp
  have hr := scale_pos p hp
  have hL := hp.1
  have hu := unit_eq p hp
  set y := st.cur.x with hy
  set c := st.center with hcdef
  set j := st.level with hj
  set d := direction (weight p) c st.cur with hd
  set Λ := ⟪sys f (weight p) y d, d⟫ with hΛ
  have hpr : probe p st = y + d := probe_tail p ht
  have hsys := system_eq_sys p f hhe
  have hμj := coerciveLevel_ge p hp j
  have hμpos : 0 < coerciveLevel p j := lt_of_lt_of_le (by positivity) hμj
  have hstab : ∀ v, |⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫| ≤
      tolerance j * ⟪sys f (weight p) y v, v⟫ := by
    intro v; have := hst v; rw [hsys, hhe, hHp, hpr] at this; exact this
  have hζ0 : 0 ≤ tolerance j := by unfold tolerance; positivity
  have hζ : tolerance j ≤ 1 / 16 := by
    unfold tolerance
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (16 : ℝ) ≤ 2 ^ (j + 4) := by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (j + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hsmallΛ : Λ ≤ tailLevel p := by rw [← hΛeq]; exact tail_small p f hp hg ht
  have hsmall : p.L₃ * Λ ≤ coerciveLevel p j ^ 2 / 2 ^ 20 := by
    have h1 : weight p / 2 = 128 * p.L₃ * scale p ^ 2 := by rw [weight_eq]; ring
    have h2 : p.L₃ * tailLevel p ≤ (weight p / 2) ^ 2 / 2 ^ 20 := by
      rw [h1]; unfold tailLevel; rw [hu]
      have : 0 ≤ p.L₃ ^ 2 * scale p ^ 4 := by positivity
      nlinarith
    have h3 : (weight p / 2) ^ 2 ≤ coerciveLevel p j ^ 2 :=
      pow_le_pow_left₀ (by positivity) hμj 2
    have h4 : p.L₃ * Λ ≤ p.L₃ * tailLevel p := mul_le_mul_of_nonneg_left hsmallΛ hL.le
    linarith [div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 2 ^ 20)]
  have hcoer2 : ∀ v, coerciveLevel p (j + 1) * ‖v‖ ^ 2 ≤ ⟪sys f (weight p) (y + d) v, v⟫ := by
    intro v
    have h1 := TG.coer v
    have h2 := hstab v
    have h3 : ⟪sys f (weight p) (y + d) v, v⟫ = ⟪sys f (weight p) y v, v⟫ +
        ⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫ := by
      rw [sys_inner, sys_inner]
      simp [inner_sub_left]
      ring
    have h4 := coerciveLevel_succ p hp j
    have h5 := neg_abs_le (⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫)
    have h6 : 0 ≤ ⟪sys f (weight p) y v, v⟫ := le_trans (by positivity) h1
    nlinarith [sq_nonneg ‖v‖]
  have hcoer2' : ∀ v, weight p / 2 * ‖v‖ ^ 2 ≤ ⟪system (weight p) (exact p f (y + d)) v, v⟫ := by
    intro v; rw [system_exact]
    exact (mul_le_mul_of_nonneg_right (coerciveLevel_ge p hp (j + 1)) (sq_nonneg _)).trans
      (hcoer2 v)
  have hμ2 : 0 < weight p / 2 := by positivity
  set d2 := direction (weight p) c (exact p f (y + d)) with hd2
  have hspec2 := direction_spec p hμ2 c (exact p f (y + d)) hcoer2'
  have hdec2 := decrement_eq p hμ2 c (exact p f (y + d)) hcoer2'
  rw [system_exact] at hspec2 hdec2
  have hd2' : fderiv ℝ (gradient f) (y + d) d2 + weight p • d2 =
      -(gradient f (y + d) + weight p • (y + d - c)) := by
    rw [hd2]; simpa [sys, LongTails.Algorithms.LogFreeProxNewton.residual, exact] using hspec2
  obtain ⟨hcontr, hFdec⟩ := tail_contraction ha.smooth hL.le ha.lip hμpos hζ0 hζ c y d d2 TG.coer
    hd' hsmall hstab hd2'
  have htr : transition p f st = { st with cur := exact p f (y + d), level := j + 1 } := by
    rw [transition_eq, ← hHp]; simp only [next, hm]; rw [hHp, hpr]; rfl
  rw [htr]
  have hlev : j < finalLevel p := by
    by_contra hcon
    have := tail_final p f hp ha hn.le hg ht (le_of_not_gt hcon)
    rw [← hgr] at this; linarith
  have hdnorm : ‖d‖ ^ 2 ≤ tailLevel p / 16 ^ j / (weight p / 2) := by
    have h1 := tail_coercive p f hp hg.cur TG d
    rw [hsys] at h1
    have h2 : Λ * 16 ^ j ≤ tailLevel p := by rw [← hΛeq]; exact TG.dec
    have h16 : (0 : ℝ) < 16 ^ j := by positivity
    rw [le_div_iff₀ hμ2, le_div_iff₀ h16]
    have := mul_le_mul_of_nonneg_right h1 h16.le
    linarith
  have hdr : ‖d‖ ≤ 2 * scale p := by
    have : tailLevel p / 16 ^ j / (weight p / 2) ≤ (2 * scale p) ^ 2 := by
      have h16 : (1 : ℝ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
      have hτ : tailLevel p / 16 ^ j ≤ tailLevel p := div_le_self (tailLevel_pos p hp).le h16
      rw [div_le_iff₀ hμ2]
      unfold tailLevel at hτ ⊢; rw [hu] at hτ ⊢; rw [weight_eq]
      nlinarith [pow_pos hr 4]
    nlinarith [norm_nonneg d, sq_nonneg (‖d‖ - 2 * scale p)]
  refine ⟨⟨rfl, hg.center, ?_, hg.top, path_step p f hg (by show ‖y + d - y‖ ≤ 2 * scale p; rw [add_sub_cancel_left]; exact hdr), fun _ => ?_,
    fun h => by simp [hnd] at h⟩, ?_⟩
  · simp only [exact_x]
    have hΛ0 : 0 ≤ Λ := le_trans (by positivity) (TG.coer d)
    have := hg.mono; linarith
  · have hΛ0 : 0 ≤ Λ := le_trans (by positivity) (TG.coer d)
    have hnew : decrement (weight p) c (exact p f (y + d)) = ⟪sys f (weight p) (y + d) d2, d2⟫ :=
      hdec2
    have hΛ16 : decrement (weight p) c (exact p f (y + d)) * 16 ^ (j + 1) ≤ Λ * 16 ^ j := by
      rw [hnew, pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 16) j]
    have hΛ3 : Λ ≤ 3 * p.Δ := by
      have h1 : f (y + d) ≤ regF f (weight p) c (y + d) := by
        have : 0 ≤ weight p / 2 * ‖y + d - c‖ ^ 2 := by positivity
        unfold regF; linarith
      have h2 := ha.gap (y + d)
      have h3 := hg.mono
      have h4 := hg.top
      linarith
    refine ⟨hcoer2, ?_, ?_, ?_, ?_⟩
    · have h2 : Λ * 16 ^ j ≤ tailLevel p := by rw [← hΛeq]; exact TG.dec
      exact hΛ16.trans h2
    · intro _
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · rw [hj0, pow_zero, mul_one] at hΛ16; rw [hj0]; linarith
      · have h2 : Λ * 16 ^ j ≤ 3 * p.Δ := by rw [← hΛeq]; exact TG.dec3 hj0
        exact hΛ16.trans h2
    · show ‖y + d - c‖ ≤ radius p (j + 1)
      have hsq : 0 ≤ Real.sqrt (tailLevel p / (weight p / 2)) := Real.sqrt_nonneg _
      have hdle : ‖d‖ ≤ Real.sqrt (tailLevel p / (weight p / 2)) / 4 ^ j := by
        rw [le_div_iff₀ (by positivity)]
        have key : (‖d‖ * 4 ^ j) ^ 2 ≤ tailLevel p / (weight p / 2) := by
          have h4 : ((4 : ℝ) ^ j) ^ 2 = 16 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [mul_pow, h4]
          have h16 : (0 : ℝ) < 16 ^ j := by positivity
          rw [div_div, le_div_iff₀ (by positivity)] at hdnorm
          rw [le_div_iff₀ hμ2]
          nlinarith
        exact (le_abs_self _).trans (Real.abs_le_sqrt key)
      have hrad : radius p (j + 1) = radius p j + Real.sqrt (tailLevel p / (weight p / 2)) / 4 ^ j := by
        unfold radius
        generalize Real.sqrt (2 * threshold p / weight p) = A
        generalize Real.sqrt (tailLevel p / (weight p / 2)) = R
        have h4 : (0 : ℝ) < 4 ^ j := by positivity
        rw [pow_succ]; field_simp; ring
      rw [hrad]
      calc ‖y + d - c‖ = ‖(y - c) + d‖ := by congr 1; abel
        _ ≤ ‖y - c‖ + ‖d‖ := norm_add_le _ _
        _ ≤ _ := add_le_add TG.loc hdle
    · exact hlev
  · right
    rw [tail_measure p f (st := { st with cur := exact p f (y + d), level := j + 1 }) hnd ht,
      tail_measure p f hnd ht]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

omit hp ha in
lemma witness_spec {γ ζ μ : ℝ} (hμ : 0 < μ) {d : Data p.E} {H : p.E →L[ℝ] p.E}
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪system γ d v, v⟫) (hns : ¬ stable γ ζ d H) :
    ⟪system γ d (witness γ ζ d H), witness γ ζ d H⟫ = 1 ∧
      ζ < |⟪(H - d.hess) (witness γ ζ d H), witness γ ζ d H⟫| := by
  classical
  have hex : ∃ v, ⟪system γ d v, v⟫ = 1 ∧ ζ < |⟪(H - d.hess) v, v⟫| := by
    unfold stable at hns
    push Not at hns
    obtain ⟨v, hv⟩ := hns
    have hv0 : v ≠ 0 := by
      intro h; rw [h] at hv; simp at hv
    have hpos : 0 < ⟪system γ d v, v⟫ :=
      lt_of_lt_of_le (by have := norm_pos_iff.mpr hv0; positivity) (hcoer v)
    set a := ⟪system γ d v, v⟫
    refine ⟨(Real.sqrt a)⁻¹ • v, ?_, ?_⟩
    · have h2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt hpos.le
      rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← mul_inv, ← sq, h2]
      exact inv_mul_cancel₀ hpos.ne'
    · have h2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt hpos.le
      rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← mul_inv, ← sq, h2,
        abs_mul, abs_inv, abs_of_pos hpos, inv_mul_eq_div, lt_div_iff₀ hpos]
      exact hv
  unfold witness
  rw [dite_eq_left hex]
  exact hex.choose_spec

omit hp ha in
lemma orientation_mul (st : State p.E) (H : p.E →L[ℝ] p.E) :
    orientation p st H * ⟪(H - st.cur.hess) (witness (weight p) (tolerance st.level) st.cur H),
      witness (weight p) (tolerance st.level) st.cur H⟫ =
      |⟪(H - st.cur.hess) (witness (weight p) (tolerance st.level) st.cur H),
        witness (weight p) (tolerance st.level) st.cur H⟫| := by
  unfold orientation
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]; ring

omit hp ha in
lemma orientation_sign (st : State p.E) (H : p.E →L[ℝ] p.E) :
    orientation p st H = 1 ∨ orientation p st H = -1 := by
  unfold orientation; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

set_option maxHeartbeats 1000000 in
lemma step_magnify {n : ℕ} {st : State p.E} (hg : Good p f n st)
    (hnd : st.done = false) (hgrad : p.ε < ‖st.cur.grad‖) (ht : st.tail = true)
    (hst : ¬ stable (weight p) (tolerance st.level) st.cur
      (fderiv ℝ (gradient f) (probe p st))) :
    Progress p f n st (transition p f st) := by
  set Hp := fderiv ℝ (gradient f) (probe p st) with hHp
  have hm : mode p st Hp = .magnify := mode_magnify p st _ hnd hgrad ht hst
  have TG := hg.tailInv ht
  obtain ⟨hval, hgr, hhe⟩ := data_of_good p f hg
  obtain ⟨hd', hΛeq⟩ := tail_data p f hp hg ht
  have hw := weight_pos p hp
  have hr := scale_pos p hp
  have hL := hp.1
  have hu := unit_eq p hp
  have hu0 := unit_pos p hp
  have hq := threshold_pos p hp
  set y := st.cur.x with hy
  set c := st.center with hcdef
  set j := st.level with hj
  set d := direction (weight p) c st.cur with hd
  set Λ := ⟪sys f (weight p) y d, d⟫ with hΛ
  have hpr : probe p st = y + d := probe_tail p ht
  have hsys := system_eq_sys p f hhe
  have hμ2 : 0 < weight p / 2 := by positivity
  have hcoerS := tail_coercive p f hp hg.cur TG
  obtain ⟨hw1, hwgap⟩ := witness_spec p hμ2 hcoerS hst
  have ho := orientation_mul p st Hp
  set w := witness (weight p) (tolerance j) st.cur Hp with hwdef
  set σ := orientation p st Hp with hσdef
  have hσ : σ = 1 ∨ σ = -1 := orientation_sign p st Hp
  have hgap0 : tolerance j < σ * ⟪(Hp - st.cur.hess) w, w⟫ := by rw [ho]; exact hwgap
  have hgap : tolerance j < σ * ⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) w, w⟫ := by
    have := hgap0; rw [hHp, hpr, hhe] at this; exact this
  have hv : ⟪sys f (weight p) y w, w⟫ = 1 := by rw [← hsys]; exact hw1
  have hcoerμ : ∀ v, 128 * p.L₃ * scale p ^ 2 * ‖v‖ ^ 2 ≤ ⟪sys f (weight p) y v, v⟫ := by
    intro v; have := hcoerS v; rw [hsys] at this
    have e : weight p / 2 = 128 * p.L₃ * scale p ^ 2 := by rw [weight_eq]; ring
    rwa [e] at this
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) (hcoerμ d)
  have hΛpos : 0 < Λ := by
    rcases hΛ0.lt_or_eq with h | h
    · exact h
    exfalso
    have hd0 : d = 0 := by
      have := hcoerμ d; rw [← hΛ, ← h] at this
      have : ‖d‖ ^ 2 ≤ 0 := by nlinarith [pow_pos hr 2]
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg d])
    apply hst
    intro v
    rw [hHp, hpr, hd0, add_zero, hhe, sub_self]
    have h0 : ((0 : p.E →L[ℝ] p.E) v) = 0 := rfl
    rw [h0, inner_zero_left, abs_zero]
    have hz : 0 ≤ tolerance j := by unfold tolerance; positivity
    exact mul_nonneg hz (le_trans (by positivity) (hcoerS v))
  have hΛdec : Λ * 16 ^ j ≤ tailLevel p := by rw [← hΛeq]; exact TG.dec
  have hΛu : Λ ≤ unit p / 2 ^ 20 := by
    have : (1 : ℝ) ≤ 16 ^ j := one_le_pow₀ (by norm_num)
    unfold tailLevel at hΛdec; nlinarith
  set s := magnifier p st with hsdef
  have hs : s = 8 * Real.sqrt (unit p / Λ) := by rw [hsdef]; unfold magnifier; rw [hΛeq]
  have hsmall : p.L₃ * Λ ≤ tolerance j * (128 * p.L₃ * scale p ^ 2) ^ 2 := by
    have h16 : (0 : ℝ) < 16 ^ j := by positivity
    have hΛj : Λ ≤ unit p / 2 ^ 20 / 16 ^ j := by
      rw [le_div_iff₀ h16]; unfold tailLevel at hΛdec; linarith
    unfold tolerance
    have h2j : (2 : ℝ) ^ (j + 4) ≤ 2 ^ 20 * 16 ^ j * 2 ^ 14 := by
      have : (2 : ℝ) ^ (j + 4) = 2 ^ j * 16 := by rw [pow_add]; norm_num
      have h2 : (2 : ℝ) ^ j ≤ 16 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      rw [this]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
    rw [hu] at hΛj
    have hpos : 0 < p.L₃ ^ 2 * scale p ^ 4 := by positivity
    calc p.L₃ * Λ ≤ p.L₃ * (p.L₃ * scale p ^ 4 / 2 ^ 20 / 16 ^ j) :=
          mul_le_mul_of_nonneg_left hΛj hL.le
      _ = p.L₃ ^ 2 * scale p ^ 4 / (2 ^ 20 * 16 ^ j) := by ring
      _ ≤ p.L₃ ^ 2 * scale p ^ 4 * 2 ^ 14 / 2 ^ (j + 4) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      _ = 1 / 2 ^ (j + 4) * (128 * p.L₃ * scale p ^ 2) ^ 2 := by ring
  have hdist : weight p * ‖y - c‖ * scale p ≤ unit p / 2 := by
    have h1 := radius_bound p hp j
    have h2 : weight p * ‖y - c‖ ≤ 2 / 5 * p.ε := (mul_le_mul_of_nonneg_left TG.loc hw.le).trans h1
    have : unit p = p.ε * scale p := rfl
    rw [this]; nlinarith
  have hbig2 : 2 ^ 9 * 2 ^ j ≤ s * tolerance j := by
    have h4' : ((4 : ℝ) ^ j) ^ 2 = 16 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e : ((2 : ℝ) ^ 10 * 4 ^ j) ^ 2 = 2 ^ 20 * 16 ^ j := by rw [mul_pow, h4']; norm_num
    have hsq : 2 ^ 10 * 4 ^ j ≤ Real.sqrt (unit p / Λ) := by
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      rw [e, le_div_iff₀ hΛpos]
      unfold tailLevel at hΛdec
      linarith
    have h2j4 : (2 : ℝ) ^ (j + 4) = 2 ^ j * 16 := by rw [pow_add]; norm_num
    have h4j : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    rw [hs]; unfold tolerance
    rw [mul_one_div, le_div_iff₀ (by positivity), h2j4]
    linarith
  have hbig : 18 ≤ s * tolerance j := by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have hesc := magnified_escape ha.smooth hL.le ha.lip hr hu (μ := 128 * p.L₃ * scale p ^ 2) rfl
    (weight_eq p) hL c y d w hcoerμ hd' hΛpos hΛu hs hv hσ hgap hsmall hdist hbig
  have hcand : candidates p st Hp = ![y - (σ * s) • d + scale p • (‖w‖⁻¹ • w),
      y - (σ * s) • d - scale p • (‖w‖⁻¹ • w), y + (σ * s) • d, y + (σ * s) • d,
      y + (σ * s) • d] := by
    unfold candidates; rw [hm]
  have hkey : ∀ x v, key p st Hp x v = v := by intro x v; unfold key; simp [hm]
  set b := landing p st Hp (values p f st Hp) with hb
  have hb0 := landing_key p f st Hp 0
  have hb1 := landing_key p f st Hp 1
  have hb2 := landing_key p f st Hp 2
  rw [hkey, hkey, hcand] at hb0 hb1 hb2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hb0 hb1 hb2
  have hfb : f b ≤ f y - s * tolerance j * unit p := by
    refine le_trans ?_ hesc
    exact le_min (le_min hb0 hb1) hb2
  have hfy : f y ≤ f c := by
    have h1 : f y ≤ regF f (weight p) c y := by
      have : 0 ≤ weight p / 2 * ‖y - c‖ ^ 2 := by positivity
      unfold regF; linarith
    exact h1.trans hg.mono
  have hsd : s * ‖d‖ ≤ scale p := by
    have hd2 : ‖d‖ ^ 2 ≤ Λ / (128 * p.L₃ * scale p ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; linarith [hcoerμ d]
    have hs2 : s ^ 2 * Λ = 64 * unit p := by
      rw [hs, mul_pow, Real.sq_sqrt (div_nonneg hu0.le hΛpos.le)]; field_simp; ring
    have : (s * ‖d‖) ^ 2 ≤ scale p ^ 2 := by
      have h1 : (s * ‖d‖) ^ 2 ≤ s ^ 2 * (Λ / (128 * p.L₃ * scale p ^ 2)) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
      have h2 : s ^ 2 * (Λ / (128 * p.L₃ * scale p ^ 2)) = scale p ^ 2 / 2 := by
        rw [show s ^ 2 * (Λ / (128 * p.L₃ * scale p ^ 2)) = s ^ 2 * Λ / (128 * p.L₃ * scale p ^ 2)
          by ring, hs2, hu]; field_simp; ring
      nlinarith [pow_pos hr 2]
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    nlinarith [sq_nonneg (s * ‖d‖ - scale p), mul_nonneg hs0 (norm_nonneg d)]
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hbdist : ‖b - y‖ ≤ 2 * scale p := by
    have hbin : b ∈ Set.range (candidates p st Hp) := ⟨_, rfl⟩
    rw [hcand] at hbin
    obtain ⟨i, hi⟩ := hbin
    rw [← hi]
    have hn1 : ‖(σ * s) • d‖ = s * ‖d‖ := by
      have hs0 : 0 ≤ s := by rw [hs]; positivity
      rw [norm_smul, Real.norm_eq_abs, abs_mul, hσabs, one_mul, abs_of_nonneg hs0]
    have hwv : ‖w‖ ≠ 0 := by
      intro h; rw [norm_eq_zero.mp h] at hv; simp at hv
    have hn2 : ‖scale p • (‖w‖⁻¹ • w)‖ = scale p := by
      rw [norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwv, mul_one,
        Real.norm_eq_abs, abs_of_pos hr]
    fin_cases i
    · calc ‖y - (σ * s) • d + scale p • (‖w‖⁻¹ • w) - y‖ =
            ‖-((σ * s) • d) + scale p • (‖w‖⁻¹ • w)‖ := by congr 1; abel
        _ ≤ ‖(σ * s) • d‖ + ‖scale p • (‖w‖⁻¹ • w)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_neg]
        _ ≤ 2 * scale p := by rw [hn1, hn2]; linarith
    · calc ‖y - (σ * s) • d - scale p • (‖w‖⁻¹ • w) - y‖ =
            ‖-((σ * s) • d) - scale p • (‖w‖⁻¹ • w)‖ := by congr 1; abel
        _ ≤ ‖(σ * s) • d‖ + ‖scale p • (‖w‖⁻¹ • w)‖ := by
            refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
        _ ≤ 2 * scale p := by rw [hn1, hn2]; linarith
    all_goals
      show ‖y + (σ * s) • d - y‖ ≤ 2 * scale p
      rw [add_sub_cancel_left, hn1]; linarith
  have htr : transition p f st =
      { st with
        center := b, centerValue := f b, cur := exact p f b, tail := false, level := 0 } := by
    rw [transition_eq, ← hHp]; simp only [next, hm]; rfl
  rw [htr]
  refine ⟨⟨rfl, rfl, by simp [regF, exact], ?_, path_step p f hg hbdist, fun h => by simp at h,
    fun h => by simp [hnd] at h⟩, ?_⟩
  · have := hg.top
    have : 0 ≤ s * tolerance j * unit p := by
      have : 0 ≤ tolerance j := by unfold tolerance; positivity
      have hs0 : 0 ≤ s := by rw [hs]; positivity
      positivity
    linarith
  · right
    rw [global_measure p f (st := { st with
        center := b, centerValue := f b, cur := exact p f b, tail := false, level := 0 }) hnd rfl,
      tail_measure p f hnd ht]
    simp only [exact_x]
    rw [restart_term p f hp]
    have hD : (j + 2 : ℝ) ≤ s * tolerance j * unit p / threshold p := by
      unfold threshold
      rw [show s * tolerance j * unit p / (unit p / 4096) = 4096 * (s * tolerance j) by
        field_simp]
      have hj2 : (j : ℝ) + 2 ≤ 2 ^ j * 2 := by
        have := Nat.lt_two_pow_self (n := j)
        have h : ((j : ℕ) : ℝ) + 1 ≤ 2 ^ j := by exact_mod_cast this
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        linarith
      linarith
    have hnew := newPhase_measure p f hp (c := c) (b := b) (D := s * tolerance j * unit p / threshold p)
      (extra := j) (by rw [div_mul_cancel₀ _ hq.ne']; linarith)
      (by unfold phaseWeight; nlinarith)
    linarith

lemma step_progress {n : ℕ} (hn : n < steps p) {st : State p.E} (hg : Good p f n st)
    (hnd : st.done = false) : Progress p f n st (transition p f st) := by
  by_cases hgrad : ‖st.cur.grad‖ ≤ p.ε
  · exact step_stop p f hp hg hnd hgrad
  have hgrad' : p.ε < ‖st.cur.grad‖ := lt_of_not_ge hgrad
  cases ht : st.tail
  · by_cases hs : st.cur.value ≤ st.centerValue - threshold p
    · exact step_success p f hp hg hnd hgrad' ht hs
    cases hc : (curvature (weight p) st.cur).isSome
    · by_cases hdec : decrement (weight p) st.center st.cur ≤ tailLevel p
      · exact step_enter p f hp hg hnd hgrad' ht hs hc hdec
      · exact step_newton p f hp ha hg hnd hgrad' ht hs hc hdec
    · exact step_escape p f hp ha hg hnd hgrad' ht hs hc
  · by_cases hst : stable (weight p) (tolerance st.level) st.cur
        (fderiv ℝ (gradient f) (probe p st))
    · exact step_advance p f hp ha hn hg hnd hgrad' ht hst
    · exact step_magnify p f hp ha hg hnd hgrad' ht hst

omit ha in
lemma step_done {n : ℕ} {st : State p.E} (hg : Good p f n st) (hd : st.done = true) :
    transition p f st = st ∧ Good p f (n + 1) st := by
  have hm := mode_idle p st (fderiv ℝ (gradient f) (probe p st)) hd
  refine ⟨?_, ⟨hg.cur, hg.center, hg.mono, hg.top, ?_, hg.tailInv, hg.out⟩⟩
  · rw [transition_eq]; simp only [next, hm]
  · have := scale_pos p hp
    exact hg.path.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) (by positivity))

end Modes

end LongTails.Proofs.LogFreeStepGood
