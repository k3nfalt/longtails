import LongTails.Algorithms.NondualLineSearch
import LongTails.Proofs.SymmetricGeneralizedDescent
import LongTails.Proofs.Execution

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.NondualLineSearch

open LongTails.Algorithms.NondualLineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def step (f : E → ℝ) (g : E → E) (r δ : ℝ) (z y : E) (s : State E) : State E :=
  update r δ z y s (f (query z y s), g (query z y s))

omit [CompleteSpace E] in
lemma execute_line_search (O : OracleTemplate.Oracle E (Reply E))
    (f : E → ℝ) (g : E → E)
    (hO : ∀ history p seed, O.answer history (0, p) seed = (f p, g p))
    (r δ : ℝ) (z y : E) (K : ℕ) (ξ : (k : ℕ) → O.Seed k) :
    OracleTemplate.execute O (algorithm r δ z y) (fun _ => K) () ξ =
      output z y ((step f g r δ z y)^[K] .first) := by
  exact (OracleTemplate.execute_eq_of_answer_eq O (fun p => (f p, g p)) hO
    (algorithm r δ z y) K () ξ).trans
    (OracleTemplate.execute_iterate (fun p => (f p, g p)) (algorithm r δ z y) K ())

omit [CompleteSpace E] in
lemma point_sub (z y : E) (a b : ℝ) : point z y a - point z y b = (a - b) • (y - z) := by
  unfold point
  module

omit [CompleteSpace E] in
lemma point_mem (z y : E) {t : ℝ} (ht : t ∈ Icc 0 1) : point z y t ∈ segment ℝ z y := by
  rw [segment_eq_image']
  exact ⟨t, ht, rfl⟩

omit [CompleteSpace E] in
lemma point_coupling (z y w : E) (t : ℝ) :
    ⟪w, point z y t - z⟫ = t * ⟪w, y - z⟫ := by
  simp [point, real_inner_smul_right]

lemma point_objective_le {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (z y : E) {t : ℝ} (ht : t ≤ 1) (hd : 0 ≤ ⟪g (point z y t), y - z⟫) :
    f (point z y t) ≤ f y := by
  have h := OracleTemplate.Gradient.convex_support hconv hgrad (point z y t) y
  have he : y - point z y t = (1 - t) • (y - z) := by unfold point; module
  rw [he, real_inner_smul_right] at h
  have hn := mul_nonneg (sub_nonneg.mpr ht) hd
  linarith

structure BracketValid (f : E → ℝ) (g : E → E) (r δ : ℝ) (z y : E)
    (n : ℕ) (a b : ℝ) (left right : Reply E) : Prop where
  left_nonneg : 0 ≤ a
  right_le_one : b ≤ 1
  ordered : a ≤ b
  width : b - a = 1 / (2 : ℝ) ^ n
  left_reply : left = (f (point z y a), g (point z y a))
  right_reply : right = (f (point z y b), g (point z y b))
  left_sign : ⟪left.2, y - z⟫ < 0
  right_sign : 0 < ⟪right.2, y - z⟫
  right_large : δ < r * ‖right.2‖

def Finished (f : E → ℝ) (g : E → E) (r δ : ℝ) (z y p : E)
    (reply : Reply E) (small : Bool) : Prop :=
  reply = (f p, g p) ∧ p ∈ segment ℝ z y ∧
    if small then r * ‖g p‖ ≤ δ else f p ≤ f y ∧ ⟪g p, p - z⟫ ≤ 0

def Valid (f : E → ℝ) (g : E → E) (r δ : ℝ) (z y : E) (n : ℕ) : State E → Prop
  | .bracket a b left right => BracketValid f g r δ z y n a b left right
  | .done p reply small => Finished f g r δ z y p reply small
  | _ => False

lemma valid_after_two {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (r δ : ℝ) (z y : E) : Valid f g r δ z y 0 ((step f g r δ z y)^[2] .first) := by
  change Valid f g r δ z y 0
    (update r δ z y (.second (f z, g z)) (f y, g y))
  dsimp only [update]
  split_ifs with hz hy hzdir hydir
  · exact ⟨rfl, left_mem_segment ℝ z y, hz⟩
  · exact ⟨rfl, right_mem_segment ℝ z y, hy⟩
  · refine ⟨rfl, left_mem_segment ℝ z y, ?_, ?_⟩
    · have h := OracleTemplate.Gradient.convex_support hconv hgrad z y
      change 0 ≤ ⟪g z, y - z⟫ at hzdir
      linarith
    · simp
  · exact ⟨rfl, right_mem_segment ℝ z y, le_rfl, hydir⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · simp [point]
    · simp [point]
    · exact lt_of_not_ge hzdir
    · exact lt_of_not_ge hydir
    · exact lt_of_not_ge hy

lemma valid_step {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (r δ : ℝ) (z y : E) (n : ℕ) (s : State E) (hs : Valid f g r δ z y n s) :
    Valid f g r δ z y (n + 1) (step f g r δ z y s) := by
  cases s with
  | first => exact False.elim hs
  | second left => exact False.elim hs
  | done p reply small => exact hs
  | bracket a b left right =>
    obtain ⟨ha, hb, hab, hw, hl, hr, hls, hrs, hlarge⟩ := hs
    have hmid : (a + b) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith
    have hwl : b - (a + b) / 2 = 1 / (2 : ℝ) ^ (n + 1) := by
      calc
        _ = (b - a) / 2 := by ring
        _ = _ := by rw [hw, pow_succ]; ring
    have hwr : (a + b) / 2 - a = 1 / (2 : ℝ) ^ (n + 1) := by
      linarith only [hwl]
    dsimp only [step, query, update]
    by_cases hsmall : r * ‖g (point z y ((a + b) / 2))‖ ≤ δ
    · simp only [hsmall, ite_true]
      exact ⟨rfl, point_mem z y hmid, hsmall⟩
    · by_cases hzero : ⟪g (point z y ((a + b) / 2)), y - z⟫ = 0
      · simp only [hsmall, hzero, ite_false, ite_true]
        refine ⟨rfl, point_mem z y hmid, ?_, ?_⟩
        · exact point_objective_le hconv hgrad z y hmid.2 (le_of_eq hzero.symm)
        · rw [point_coupling, hzero, mul_zero]
      · by_cases hneg : ⟪g (point z y ((a + b) / 2)), y - z⟫ < 0
        · simp only [hsmall, hzero, hneg, ite_false, ite_true]
          exact ⟨hmid.1, hb, by linarith, hwl, rfl, hr, hneg, hrs, hlarge⟩
        · simp only [hsmall, hzero, hneg, ite_false]
          refine ⟨ha, hmid.2, by linarith, hwr, hl, rfl, hls, ?_, lt_of_not_ge hsmall⟩
          exact lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)

lemma valid_iterate {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (r δ : ℝ) (z y : E) (n : ℕ) :
    Valid f g r δ z y n ((step f g r δ z y)^[n + 2] .first) := by
  induction n with
  | zero => exact valid_after_two hconv hgrad r δ z y
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Function.iterate_succ_apply']
    exact valid_step hconv hgrad r δ z y n _ ih

lemma search_scalar_bounds {H G r C q L1 : ℝ}
    (hH : 0 < H) (_hG : 0 ≤ G) (hr : 0 ≤ r) (hC : 1 ≤ C)
    (hCr : L1 * r ≤ C) (hCG : r * H ≤ C * G) (hq : 128 * C ^ 2 ≤ q) :
    L1 * r / q ≤ 1 / 4 ∧ 2 * H * r ^ 2 / q ≤ G ^ 2 / (16 * H) := by
  have hCsq : C ≤ C ^ 2 := by nlinarith
  have hqp : 0 < q := by nlinarith
  constructor
  · apply (div_le_iff₀ hqp).mpr
    nlinarith
  · apply (div_le_div_iff₀ hqp (show 0 < 16 * H by positivity)).mpr
    have hs := pow_le_pow_left₀ (mul_nonneg hr hH.le) hCG 2
    have hmul := mul_le_mul_of_nonneg_left hq (sq_nonneg G)
    have hn : 0 ≤ C ^ 2 * G ^ 2 := by positivity
    nlinarith only [hs, hmul, hn]

lemma search_parameter_bounds {L0 L1 r δ G q : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hr : 0 < r) (hδ : 0 < δ)
    (hlarge : δ < r * G)
    (hq : 128 * (1 + L0 * r ^ 2 / δ + L1 * r) ^ 2 ≤ q) :
    L1 * r / q ≤ 1 / 4 ∧
      2 * (L0 + L1 * G) * r ^ 2 / q ≤ G ^ 2 / (16 * (L0 + L1 * G)) := by
  have hG : 0 < G := (mul_pos_iff_of_pos_left hr).mp (hδ.trans hlarge)
  have hC : 1 ≤ 1 + L0 * r ^ 2 / δ + L1 * r := by
    have hn : 0 ≤ L0 * r ^ 2 / δ + L1 * r := by positivity
    linarith
  have hCr : L1 * r ≤ 1 + L0 * r ^ 2 / δ + L1 * r := by
    have hn : 0 ≤ L0 * r ^ 2 / δ := by positivity
    linarith
  have hx : L0 * r ≤ L0 * r ^ 2 * G / δ := by
    apply (le_div_iff₀ hδ).mpr
    have hm := mul_le_mul_of_nonneg_left hlarge.le (show 0 ≤ L0 * r by positivity)
    nlinarith only [hm]
  have hCG : r * (L0 + L1 * G) ≤ (1 + L0 * r ^ 2 / δ + L1 * r) * G := by
    rw [div_eq_mul_inv] at hx ⊢
    nlinarith only [hx, hG.le]
  exact search_scalar_bounds (by positivity) hG.le hr.le hC hCr hCG hq

omit [CompleteSpace E] in
lemma bracket_coupling {f : E → ℝ} {g : E → E} {r δ : ℝ} {z y : E}
    {n : ℕ} {a b : ℝ} {left right : Reply E}
    (hs : BracketValid f g r δ z y n a b left right) :
    ⟪g (point z y b), point z y b - z⟫ ≤
      ‖y - z‖ * ‖g (point z y b) - g (point z y a)‖ := by
  have hl := hs.left_sign
  have hr := hs.right_sign
  rw [hs.left_reply] at hl
  rw [hs.right_reply] at hr
  change ⟪g (point z y a), y - z⟫ < 0 at hl
  change 0 < ⟪g (point z y b), y - z⟫ at hr
  rw [point_coupling]
  calc
    _ ≤ ⟪g (point z y b), y - z⟫ := mul_le_of_le_one_left hr.le hs.right_le_one
    _ ≤ ⟪g (point z y b) - g (point z y a), y - z⟫ := by
      rw [inner_sub_left]
      linarith
    _ ≤ ‖g (point z y b) - g (point z y a)‖ * ‖y - z‖ := real_inner_le_norm _ _
    _ = _ := mul_comm _ _

omit [CompleteSpace E] in
lemma bracket_distance {f : E → ℝ} {g : E → E} {r δ : ℝ} {z y : E}
    {n : ℕ} {a b : ℝ} {left right : Reply E}
    (hs : BracketValid f g r δ z y n a b left right) :
    ‖point z y b - point z y a‖ = ‖y - z‖ / (2 : ℝ) ^ n := by
  rw [point_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hs.ordered), hs.width]
  ring

omit [CompleteSpace E] in
lemma bracket_coupling_bound {f : E → ℝ} {g : E → E} (hg : Continuous g)
    {L0 L1 r δ : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hr : 0 < r) (hδ : 0 < δ)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    {z y : E} (hlen : ‖y - z‖ ≤ r) {n : ℕ} {a b : ℝ} {left right : Reply E}
    (hs : BracketValid f g r δ z y n a b left right)
    (hn : 128 * (1 + L0 * r ^ 2 / δ + L1 * r) ^ 2 ≤ (2 : ℝ) ^ n) :
    ⟪g (point z y b), point z y b - z⟫ ≤
      ‖g (point z y b)‖ ^ 2 / (16 * (L0 + L1 * ‖g (point z y b)‖)) := by
  let p := point z y b
  let q := point z y a
  let H := L0 + L1 * ‖g p‖
  have hH : 0 < H := by dsimp [H]; positivity
  have hlarge : δ < r * ‖g p‖ := by simpa only [hs.right_reply] using hs.right_large
  have hpar := search_parameter_bounds hL0 hL1 hr hδ hlarge hn
  have hdist : ‖p - q‖ ≤ r / (2 : ℝ) ^ n := by
    rw [show ‖p - q‖ = ‖y - z‖ / (2 : ℝ) ^ n from bracket_distance hs]
    exact div_le_div_of_nonneg_right hlen (by positivity)
  have hsmall : L1 * ‖p - q‖ ≤ 1 / 4 := by
    have hm := mul_le_mul_of_nonneg_left hdist hL1.le
    exact hm.trans (by simpa [mul_div_assoc] using hpar.1)
  have hexp : Real.exp (L1 * ‖p - q‖) ≤ 2 := by
    apply (Real.exp_le_exp.mpr hsmall).trans
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hgdiff := SymmetricGeneralizedSmooth.gradient_difference_bound hg hL0.le hL1 hgs q p
  rw [norm_sub_rev (g q) (g p), norm_sub_rev q p] at hgdiff
  have hgb : ‖g p - g q‖ ≤ 2 * H * r / (2 : ℝ) ^ n := by
    calc
      _ ≤ H * Real.exp (L1 * ‖p - q‖) * ‖p - q‖ := hgdiff
      _ ≤ H * 2 * (r / (2 : ℝ) ^ n) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖y - z‖ * ‖g p - g q‖ := bracket_coupling hs
    _ ≤ r * (2 * H * r / (2 : ℝ) ^ n) := by gcongr
    _ = 2 * H * r ^ 2 / (2 : ℝ) ^ n := by ring
    _ ≤ _ := hpar.2

def Guarantee (f : E → ℝ) (g : E → E) (L0 L1 r δ : ℝ) (z y : E)
    (out : E × Reply E × Bool) : Prop :=
  out.2.1 = (f out.1, g out.1) ∧ out.1 ∈ segment ℝ z y ∧
    if out.2.2 then r * ‖g out.1‖ ≤ δ else
      f out.1 ≤ f y ∧ ⟪g out.1, out.1 - z⟫ ≤ ‖g out.1‖ ^ 2 / (16 * (L0 + L1 * ‖g out.1‖))

lemma valid_output {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    {L0 L1 r δ : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hr : 0 < r) (hδ : 0 < δ)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    {z y : E} (hlen : ‖y - z‖ ≤ r) {n : ℕ} {s : State E}
    (hs : Valid f g r δ z y n s)
    (hn : 128 * (1 + L0 * r ^ 2 / δ + L1 * r) ^ 2 ≤ (2 : ℝ) ^ n) :
    Guarantee f g L0 L1 r δ z y (output z y s) := by
  cases s with
  | first => exact False.elim hs
  | second left => exact False.elim hs
  | bracket a b left right =>
    refine ⟨hs.right_reply, point_mem z y ⟨hs.left_nonneg.trans hs.ordered, hs.right_le_one⟩, ?_, ?_⟩
    · have hsgn := hs.right_sign
      rw [hs.right_reply] at hsgn
      exact point_objective_le hconv hgrad z y hs.right_le_one hsgn.le
    · exact bracket_coupling_bound hg hL0 hL1 hr hδ hgs hlen hs hn
  | done p reply small =>
    rcases hs with ⟨hrep, hseg, hrest⟩
    cases small with
    | false => exact ⟨hrep, hseg, hrest.1, hrest.2.trans (by positivity)⟩
    | true => exact ⟨hrep, hseg, hrest⟩

lemma execute_guarantee (O : OracleTemplate.Oracle E (Reply E))
    (f : E → ℝ) (g : E → E)
    (hO : ∀ history p seed, O.answer history (0, p) seed = (f p, g p))
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x) (hg : Continuous g)
    {L0 L1 r δ : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hr : 0 < r) (hδ : 0 < δ)
    (hgs : ∀ x y, ‖g x - g y‖ ≤
      (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖)
    (z y : E) (hlen : ‖y - z‖ ≤ r) (n : ℕ)
    (hn : 128 * (1 + L0 * r ^ 2 / δ + L1 * r) ^ 2 ≤ (2 : ℝ) ^ n)
    (ξ : (k : ℕ) → O.Seed k) :
    Guarantee f g L0 L1 r δ z y
      (OracleTemplate.execute O (algorithm r δ z y) (fun _ => n + 2) () ξ) := by
  have he := execute_line_search O f g hO r δ z y (n + 2) ξ
  rw [he]
  exact valid_output hconv hgrad hg hL0 hL1 hr hδ hgs hlen
    (valid_iterate hconv hgrad r δ z y n) hn

end LongTails.Proofs.NondualLineSearch
