import LongTails.Proofs.FullRangeWeakMintyHalpernResidual
import LongTails.Proofs.FullRangeWeakMintyHalpernGeometry
import LongTails.Proofs.WeakMintyHybridExecution

open scoped RealInnerProductSpace
namespace OracleTemplate.FullRangeWeakMintyHalpern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def step (G : E → E) (δ e : ℝ) (st : State E) :=
  update δ e st (G (point st))

private def Within {S : Type*} (f : S → S) (a : S) (m : ℕ) (b : S) :=
  ∃ n ≤ m, f^[n] a = b

private lemma Within.trans {S : Type*} {f : S → S} {a b c : S} {m n : ℕ}
    (ha : Within f a m b) (hb : Within f b n c) : Within f a (m+n) c := by
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  exact ⟨j+i, by omega, Function.iterate_add_apply ..⟩

private lemma solve_steps (G : E → E) (δ e : ℝ) (w b c : E) (s : Bool) (j n : ℕ) :
    (step G δ e)^[n] (.solve w b c (endpoint G c j) s j n) =
      .solve w b c (endpoint G c (j+n)) s (j+n) 0 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (step G δ e)^[n] (.solve w b c (endpoint G c (j+1)) s (j+1) n) = _
    simpa only [Nat.succ_add, Nat.add_succ] using ih (j+1)

private lemma solve_end (G : E → E) (δ e : ℝ) (w b c : E) (s : Bool) :
    let k := count δ
    let y := endpoint G c k
    Within (step G δ e) (.solve w b c c s 0 k) (k+1)
      (update δ e (.solve w b c y s k 0) (G y)) := by
  dsimp only
  refine ⟨_, le_rfl, ?_⟩
  rw [Function.iterate_succ_apply']
  have h := solve_steps G δ e w b c s 0 (count δ)
  simp only [Nat.zero_add] at h
  exact congrArg (step G δ e) h

private lemma block (G : E → E) (lip : ∀ x y, ‖G x-G y‖ ≤ ‖x-y‖)
    {z : E} {δ e : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) (he : 0 < e)
    (hm : ∀ u, -(1-δ)*‖G u‖^2 ≤ ⟪G u,u-z⟫) (w : E) :
    let B := 2 * count δ + 3
    (∃ y, Within (step G δ e) (.anchor w) B (.done y) ∧ ‖G y‖ ≤ e) ∨
    (∃ w', Within (step G δ e) (.anchor w) B (.anchor w') ∧
      ‖w'-z‖^2 ≤ ‖w-z‖^2 - Real.sqrt δ*e^2/256) := by
  let t := Real.sqrt (Real.sqrt δ)
  have ht : 0 < t := Real.sqrt_pos.2 (Real.sqrt_pos.2 hd)
  have ht1 : t ≤ 1 := Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hd1)
  have ht2 : t^2 = Real.sqrt δ := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht4 : (t^2)^2 = δ := by rw [ht2, Real.sq_sqrt hd.le]
  let b := G w
  let c := center w b
  let k := count δ
  let y := endpoint G c k
  let v := G y
  by_cases hbw : ‖b‖ ≤ e
  · refine Or.inl ⟨w, ⟨1, by omega, ?_⟩, hbw⟩
    change (if ‖b‖ ≤ e then State.done w else _) = _
    exact ite_eq_left hbw
  have ha : Within (step G δ e) (.anchor w) 1 (.solve w b c c false 0 k) :=
    ⟨1, le_rfl, by change (if ‖b‖ ≤ e then _ else _) = _; exact ite_eq_right hbw⟩
  obtain ⟨n, hn, hs⟩ := ha.trans (solve_end G δ e w b c false)
  change (step G δ e)^[n] (.anchor w) = (if ‖v‖ ≤ e then .done y else
    if false = false ∧ ‖b‖ < t*‖v‖ then .solve w b (average w y) (average w y) true 0 k
    else .anchor (project δ w y v)) at hs
  change n ≤ 1+(k+1) at hn
  change (∃ _, Within _ _ (2*k+3) _ ∧ _) ∨ _
  by_cases hy : ‖v‖ ≤ e
  · rw [ite_eq_left hy] at hs
    exact Or.inl ⟨y, ⟨n, by omega, hs⟩, hy⟩
  rw [ite_eq_right hy] at hs
  have hr := relative_error G lip c hd
  change ‖y-c+v‖ ≤ _ * ‖v‖ at hr
  rw [← ht2] at hr
  have htb : t*e/16 < t*‖b‖/16 := by gcongr; exact lt_of_not_ge hbw
  by_cases hbig : ‖b‖ < t*‖v‖
  · rw [ite_eq_left ⟨rfl,hbig⟩] at hs
    let m := average w y
    let u := endpoint G m k
    let f := G u
    have ha₂ : Within (step G δ e) (.anchor w) n (.solve w b m m true 0 k) := ⟨n, le_rfl, hs⟩
    obtain ⟨i, hi, hh⟩ := ha₂.trans (solve_end G δ e w b m true)
    change i ≤ n + (k+1) at hi
    change (step G δ e)^[i] (.anchor w) = (if ‖f‖ ≤ e then .done u else
      if true = false ∧ ‖b‖ < t*‖f‖ then _ else .anchor (project δ w u f)) at hh
    rw [ite_eq_right (show ¬ (true = false ∧ ‖b‖ < t*‖f‖) from fun h => by cases h.1)] at hh
    by_cases hu : ‖f‖ ≤ e
    · rw [ite_eq_left hu] at hh
      exact Or.inl ⟨u, ⟨i, by omega, hh⟩, hu⟩
    rw [ite_eq_right hu] at hh
    have hf := he.trans (lt_of_not_ge hu)
    have hr₂ := relative_error G lip m hd
    rw [← ht2] at hr₂
    have dep := large ht ht1 ht4 hf hr hr₂ (lip u w) (lip u y) hbig
    have hdec := project_progress ht he hf (htb.trans_le dep) (hm u)
    rw [ht2] at hdec
    exact Or.inr ⟨_, ⟨i, by change i ≤ 2*k+3; omega, hh⟩, hdec.le⟩
  · rw [ite_eq_right (fun h => hbig h.2)] at hs
    have hv := he.trans (lt_of_not_ge hy)
    have dep := moderate ht ht1 hd.le hv hr (lip y w) (le_of_not_gt hbig)
    have hdec := project_progress ht he hv (htb.trans_le dep) (hm y)
    rw [ht2] at hdec
    exact Or.inr ⟨_, ⟨n, by change n ≤ 2*k+3; omega, hs⟩, hdec.le⟩

private lemma certified (G : E → E) (lip : ∀ x y, ‖G x-G y‖ ≤ ‖x-y‖)
    {z : E} {δ e : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) (he : 0 < e)
    (hm : ∀ u, -(1-δ)*‖G u‖^2 ≤ ⟪G u,u-z⟫) (w : E) (N : ℕ)
    (hN : ‖w-z‖^2 < N*(Real.sqrt δ*e^2/256)) :
    ∃ y, Within (step G δ e) (.anchor w) ((2*count δ+3)*N) (.done y) ∧ ‖G y‖ ≤ e := by
  induction N generalizing w with
  | zero => simp at hN; linarith [sq_nonneg ‖w-z‖]
  | succ n ih =>
    obtain ⟨y, ⟨i,hi,hs⟩, hy⟩ | ⟨w', hw, hdec⟩ := block G lip hd hd1 he hm w
    · exact ⟨y, ⟨i, hi.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)), hs⟩, hy⟩
    · push_cast at hN
      obtain ⟨y, hy, hacc⟩ := ih w' (by linarith)
      refine ⟨y, ?_, hacc⟩
      simpa only [Nat.mul_succ, Nat.add_comm] using hw.trans hy


open WeakMintyHybrid (margin)

lemma value_accurate {F : E → E} {z : E} {L ρ ε R : ℝ}
    (hL : 0 < L) (hρ : 0 ≤ ρ) (hρL : ρ*L < 2) (hε : 0 < ε)
    (hlip : ∀ x y, ‖F x-F y‖ ≤ L*‖x-y‖)
    (hm : ∀ x, -(ρ/2)*‖F x‖^2 ≤ ⟪F x,x-z⟫)
    (x0 : E) (hR : ‖x0-z‖ ≤ R) {B : ℕ}
    (hB : (2*count (margin L ρ)+3) *
      (1 + ⌊256*L^2*R^2/(Real.sqrt (margin L ρ)*ε^2)⌋₊) ≤ B)
    (oracle : Oracle (E ⊕ E) (E × (E →L[ℝ] E))) (J : E → E →L[ℝ] E)
    (hF : ∀ k seed x, oracle.answer k (0, Sum.inl x) seed = (F x, 0))
    (hJ : ∀ k seed x, oracle.answer k (0, Sum.inr x) seed = (0, J x))
    (seed : (values L ρ ε x0).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
    ‖F (execute oracle (values L ρ ε x0) (fun _ => B) seed ξ)‖ ≤ ε := by
  let G := fun x => L⁻¹ • F x
  let δ := margin L ρ
  have hd : 0 < δ := WeakMintyHybrid.margin_pos hρL
  have hd1 : δ ≤ 1 := WeakMintyHybrid.margin_le_one hL.le hρ
  have hn (x) : ‖G x‖ = ‖F x‖/L := by
    simp only [G, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    ring
  have lip (x y) : ‖G x-G y‖ ≤ ‖x-y‖ := by
    dsimp [G]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL),
      inv_mul_eq_div, div_le_iff₀ hL, mul_comm]
    exact hlip x y
  have minty (x) : -(1-δ)*‖G x‖^2 ≤ ⟪G x,x-z⟫ := by
    rw [hn, show G x = L⁻¹ • F x from rfl, real_inner_smul_left, inv_mul_eq_div,
      le_div_iff₀ hL]
    convert hm x using 1
    dsimp [δ, margin]
    field_simp
    ring
  let N := 1 + ⌊256*L^2*R^2/(Real.sqrt δ*ε^2)⌋₊
  have hN : 256*L^2*R^2/(Real.sqrt δ*ε^2) < (N:ℝ) := by
    dsimp only [N]
    push_cast
    linarith [Nat.lt_floor_add_one (256*L^2*R^2/(Real.sqrt δ*ε^2))]
  rw [div_lt_iff₀ (by positivity)] at hN
  have hi : ‖x0-z‖^2 < N*(Real.sqrt δ*(ε/L)^2/256) := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hR 2).trans_lt
    field_simp
    nlinarith only [hN]
  obtain ⟨y, ⟨i,hi,hs⟩,hy⟩ := certified G lip hd hd1 (div_pos hε hL) minty x0 N hi
  have hib := hi.trans hB
  have hstay := Function.iterate_fixed (f := step G δ (ε/L))
    (x := State.done y) (show step G δ (ε/L) (.done y) = .done y from rfl) (B-i)
  have hfinish : (step G δ (ε/L))^[B] (.anchor x0) = .done y := by
    rw [show B = B-i+i by omega, Function.iterate_add_apply, hs, hstay]
  have hor : ∀ k query seed, oracle.answer k (0,query) seed = WeakMintyHybrid.exactReply F J query := by
    intro k query seed
    cases query with
    | inl x => exact hF k seed x
    | inr x => exact hJ k seed x
  rw [execute_eq_of_answer_eq oracle _ hor _ B seed ξ, execute_iterate]
  change ‖F (point ((step G δ (ε/L))^[B] (.anchor x0)))‖ ≤ ε
  rw [hfinish]
  rw [hn] at hy
  exact (div_le_div_iff_of_pos_right hL).mp hy

end OracleTemplate.FullRangeWeakMintyHalpern
