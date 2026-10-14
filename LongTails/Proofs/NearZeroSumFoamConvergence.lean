import LongTails.Proofs.NearZeroSumModel
import LongTails.Proofs.NearZeroSumPotential
import LongTails.Proofs.NearZeroSumInner
import LongTails.Proofs.NearZeroSumExecution

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

noncomputable def centeredDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (xs z : E) : E := (1 / a) • z + xs

noncomputable def gameLyapunov {p : Public} (I : Problem p) (a b α : ℝ)
    (xs : p.E) (ys : p.F) (s : FoamState p.E p.F) : ℝ :=
  2 * a * ‖centeredDual a xs s.z‖ ^ 2 + 2 * b / α * ‖s.y - ys‖ ^ 2 +
    2 / α * gameGap I a b xs ys s.xf s.zf s.yf

lemma gap_previous_support {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    {xs : p.E} {ys : p.F} (hxs : xs ∈ p.X)
    {x xp z zp : p.E} {y yp ny : p.F}
    (hx : x ∈ p.X) (hy : y ∈ p.Y) (hvp : FastValid H G a xp zp yp)
    (hny : ConstrainedMonotone.Normal p.Y y ny) :
    gameGap I a b xs ys x z y + ⟪x + (1 / a) • z, zp - z⟫ +
      ⟪(ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny -
        (2 : ℝ) • ((G (WithLp.toLp 2 (x, y))).snd - (G (WithLp.toLp 2 (xs, y))).snd), yp - y⟫ +
      c / 2 * ‖yp - y‖ ^ 2 ≤ gameGap I a b xs ys xp zp yp := by
  obtain ⟨hxp, hyp, nxp, hnxp, hzp⟩ := hvp
  have h := game_fast_support ha hμ hν geom.convexX geom.convexY hx hxp hxs hy hyp
    geom.strongX geom.strongY geom.convexG geom.gradientH geom.gradientG geom.lipschitzG
    hnxp hny hzp (z₁ := z)
  have h₁ : 0 ≤ ‖zp - z‖ ^ 2 / (2 * a) := by positivity
  have h₂ : 0 ≤ b / 2 * ‖yp - y‖ ^ 2 := by positivity
  have h₃ : 0 ≤ a / 2 * ‖xp - x‖ ^ 2 := by positivity
  dsimp [gameGap]
  linarith

lemma gap_equilibrium_support {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) {a b c : ℝ} (ha : 0 < a)
    (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    {x z : p.E} {y ny : p.F} (hx : x ∈ p.X) (hy : y ∈ p.Y)
    (hny : ConstrainedMonotone.Normal p.Y y ny) :
    gameGap I a b xs ys x z y + ⟪x + (1 / a) • z, -a • xs - z⟫ +
      ⟪(ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny -
        (2 : ℝ) • ((G (WithLp.toLp 2 (x, y))).snd - (G (WithLp.toLp 2 (xs, y))).snd), ys - y⟫ +
      ‖-a • xs - z‖ ^ 2 / (2 * a) + (b + c) / 2 * ‖ys - y‖ ^ 2 +
      a / 2 * ‖xs - x‖ ^ 2 ≤ 0 := by
  have hnormal := product_normal hs hns
  have hz : -a • xs = (ownGradient H G (WithLp.toLp 2 (xs, ys))).fst - a • xs +
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))).fst := by
    rw [WithLp.neg_fst]
    module
  have h := game_fast_support ha hμ hν geom.convexX geom.convexY hx hs.1 hs.1 hy hs.2
    geom.strongX geom.strongY geom.convexG geom.gradientH geom.gradientG geom.lipschitzG
    hnormal.1 hny hz (z₁ := z)
  change fastValue (shiftedGame I a b) (fun y => I.g (WithLp.toLp 2 (xs, y))) a b x z y +
      ⟪x + (1 / a) • z, -a • xs - z⟫ +
      ⟪(ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny -
        (2 : ℝ) • ((G (WithLp.toLp 2 (x, y))).snd - (G (WithLp.toLp 2 (xs, y))).snd), ys - y⟫ +
      ‖-a • xs - z‖ ^ 2 / (2 * a) + (b + c) / 2 * ‖ys - y‖ ^ 2 +
      a / 2 * ‖xs - x‖ ^ 2 ≤
        fastValue (shiftedGame I a b) (fun y => I.g (WithLp.toLp 2 (xs, y))) a b xs (-a • xs) ys at h
  dsimp [gameGap]
  linarith



lemma centered_dual_identities {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : a ≠ 0) (xs x z zp : E) :
    x + (1 / a) • z = (x - xs) + centeredDual a xs z ∧
      zp - z = a • (centeredDual a xs zp - centeredDual a xs z) ∧
      -a • xs - z = (-a) • centeredDual a xs z := by
  dsimp [centeredDual]
  constructor
  · module
  constructor
  · simp only [smul_sub, smul_add, smul_smul, mul_one_div_cancel ha, one_smul]
    module
  · simp only [smul_add, smul_smul, neg_mul, mul_one_div_cancel ha, neg_one_smul]
    module

lemma normalized_gap_supports {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    {x xp z zp : p.E} {y yp ny : p.F} (hx : x ∈ p.X) (hy : y ∈ p.Y)
    (hvp : FastValid H G a xp zp yp) (hny : ConstrainedMonotone.Normal p.Y y ny) :
    let f := centeredDual a xs z
    let q := centeredDual a xs zp
    let w := (ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny
    let e := (2 : ℝ) • ((G (WithLp.toLp 2 (x, y))).snd - (G (WithLp.toLp 2 (xs, y))).snd)
    0 ≤ gameGap I a b xs ys xp zp yp ∧ ‖e‖ ≤ 2 * p.δ * ‖x - xs‖ ∧
      gameGap I a b xs ys x z y + a * ⟪(x - xs) + f, q - f⟫ +
        ⟪w - e, (yp - ys) - (y - ys)⟫ + c / 2 * ‖(yp - ys) - (y - ys)‖ ^ 2 ≤
          gameGap I a b xs ys xp zp yp ∧
      gameGap I a b xs ys x z y + a * ⟪(x - xs) + f, -f⟫ +
        ⟪w - e, -(y - ys)⟫ + a / 2 * ‖f‖ ^ 2 + (b + c) / 2 * ‖y - ys‖ ^ 2 +
        a / 2 * ‖x - xs‖ ^ 2 ≤ 0 := by
  dsimp only
  refine ⟨game_gap_nonnegative geom ha hb hc hμ hν hs hns hvp,
    cross_gradient_error (p := p) (G := G) (x := x) (xs := xs) (y := y)
      (geom.lipschitzG (WithLp.toLp 2 (x, y)) ⟨hx, hy⟩
        (WithLp.toLp 2 (xs, y)) ⟨hs.1, hy⟩), ?_, ?_⟩
  · have hp := gap_previous_support geom ha hb hμ hν hs.1 hx hy hvp hny (z := z) (ys := ys)
    have hid := centered_dual_identities ha.ne' xs x z zp
    rw [hid.1, hid.2.1, real_inner_smul_right] at hp
    have he : (yp - ys) - (y - ys) = yp - y := by module
    rw [he]
    exact hp
  · have hp := gap_equilibrium_support geom ha hμ hν hs hns hx hy hny (z := z)
    have hid := centered_dual_identities ha.ne' xs x z zp
    rw [hid.1, hid.2.2, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos ha, mul_pow, norm_sub_rev ys y, norm_sub_rev xs x] at hp
    have hnorm : a ^ 2 * ‖centeredDual a xs z‖ ^ 2 / (2 * a) =
        a / 2 * ‖centeredDual a xs z‖ ^ 2 := by field_simp
    rw [hnorm] at hp
    rw [inner_neg_right, neg_sub]
    linarith


lemma game_normalized_contraction {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) {a b c α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (htune : α ^ 2 = b / a) (hsmall : 8 * p.δ ^ 2 ≤ a * α * c)
    (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    (s : FoamState p.E p.F) (hvp : FastValid H G a s.xf s.zf s.yf)
    {x z : p.E} {y ny : p.F} (hx : x ∈ p.X) (hy : y ∈ p.Y)
    (hny : ConstrainedMonotone.Normal p.Y y ny)
    (hres :
      a ^ 2 * ‖centeredDual a xs z + (1 / 2 : ℝ) • ((x - xs) -
        (α • centeredDual a xs s.z + (1 - α) • centeredDual a xs s.zf))‖ ^ 2 +
      ‖(ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny +
        (a / 8) • ((y - ys) - (α • (s.y - ys) + (1 - α) • (s.yf - ys)))‖ ^ 2 ≤
      a ^ 2 / 64 * (‖(x - xs) +
        (α • centeredDual a xs s.z + (1 - α) • centeredDual a xs s.zf)‖ ^ 2 +
        ‖(y - ys) - (α • (s.y - ys) + (1 - α) • (s.yf - ys))‖ ^ 2)) :
    2 * a * ‖(1 / 2 : ℝ) • (centeredDual a xs s.z - (x - xs))‖ ^ 2 +
      2 * b / α * ‖(1 - α / 2) • (s.y - ys) + (α / 2) • (y - ys) -
        (α / (2 * b)) • ((ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny)‖ ^ 2 +
      2 / α * gameGap I a b xs ys x z y ≤
      (1 - α / 2) * gameLyapunov I a b α xs ys s := by
  obtain ⟨hprev, herr, hp, hsupp⟩ := normalized_gap_supports geom ha hb.le hc.le hμ hν
    hs hns hx hy hvp hny (z := z)
  exact perturbed_foam_contraction ha hb hc hα hα₁ htune hsmall
    (centeredDual a xs s.z) (x - xs) (centeredDual a xs z) (centeredDual a xs s.zf)
    (s.y - ys) (y - ys) ((ownGradient H G (WithLp.toLp 2 (x, y))).snd + ny) (s.yf - ys)
    ((2 : ℝ) • ((G (WithLp.toLp 2 (x, y))).snd - (G (WithLp.toLp 2 (xs, y))).snd))
    herr hprev hres hp hsupp

lemma inner_field_monotonicity {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {B : Joint E F → Joint E F} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (zg : E) (yg : F)
    {u v : Joint E F}
    (hmono : 2 * a * ‖u.fst - v.fst‖ ^ 2 + 2 * b * ‖u.snd - v.snd‖ ^ 2 ≤
      ⟪B u - B v, u - v⟫) :
    a / 8 * ‖u - v‖ ^ 2 ≤
      ⟪pair ((B u).fst - (a / 2) • u.fst - (1 / 2 : ℝ) • zg)
          ((B u).snd + (a / 8) • (u.snd - yg)) -
        pair ((B v).fst - (a / 2) • v.fst - (1 / 2 : ℝ) • zg)
          ((B v).snd + (a / 8) • (v.snd - yg)), u - v⟫ := by
  have he : ⟪pair ((B u).fst - (a / 2) • u.fst - (1 / 2 : ℝ) • zg)
          ((B u).snd + (a / 8) • (u.snd - yg)) -
        pair ((B v).fst - (a / 2) • v.fst - (1 / 2 : ℝ) • zg)
          ((B v).snd + (a / 8) • (v.snd - yg)), u - v⟫ =
      ⟪B u - B v, u - v⟫ - a / 2 * ‖u.fst - v.fst‖ ^ 2 + a / 8 * ‖u.snd - v.snd‖ ^ 2 := by
    simp only [pair, WithLp.prod_inner_apply,
      WithLp.fst, WithLp.snd, inner_sub_left,
      inner_add_left, real_inner_smul_left, norm_sub_sq_real, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_comm v.ofLp.1 u.ofLp.1,
      real_inner_comm v.ofLp.2 u.ofLp.2]
    ring
  rw [he, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.sub_fst, WithLp.sub_snd]
  nlinarith [sq_nonneg ‖u.fst - v.fst‖, sq_nonneg ‖u.snd - v.snd‖]

lemma inner_field_lipschitz {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {B : Joint E F → Joint E F} {a L : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) (zg : E) (yg : F)
    {u v : Joint E F} (hlip : ‖B u - B v‖ ≤ L * ‖u - v‖) :
    ‖pair ((B u).fst - (a / 2) • u.fst - (1 / 2 : ℝ) • zg)
          ((B u).snd + (a / 8) • (u.snd - yg)) -
        pair ((B v).fst - (a / 2) • v.fst - (1 / 2 : ℝ) • zg)
          ((B v).snd + (a / 8) • (v.snd - yg))‖ ≤ 2 * L * ‖u - v‖ := by
  have he : pair ((B u).fst - (a / 2) • u.fst - (1 / 2 : ℝ) • zg)
          ((B u).snd + (a / 8) • (u.snd - yg)) -
        pair ((B v).fst - (a / 2) • v.fst - (1 / 2 : ℝ) • zg)
          ((B v).snd + (a / 8) • (v.snd - yg)) =
      (B u - B v) + pair ((-a / 2) • (u.fst - v.fst)) ((a / 8) • (u.snd - v.snd)) := by
    apply WithLp.ofLp_injective 2
    ext <;> simp only [pair, WithLp.ofLp_sub, WithLp.ofLp_add,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, WithLp.fst, WithLp.snd] <;> module
  rw [he]
  have h := norm_add_le (B u - B v)
    (pair ((-a / 2) • (u.fst - v.fst)) ((a / 8) • (u.snd - v.snd)))
  have hp := pair_norm_le ((-a / 2) • (u.fst - v.fst)) ((a / 8) • (u.snd - v.snd))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonpos (show -a / 2 ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ a / 8 by positivity)] at hp
  have hx := WithLp.norm_fst_le E (u - v)
  have hy := WithLp.norm_snd_le E (u - v)
  simp only [WithLp.sub_fst, WithLp.sub_snd] at hx hy
  have hx' := mul_le_mul_of_nonneg_left hx (show 0 ≤ a / 2 by positivity)
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ a / 8 by positivity)
  have hL := mul_le_mul_of_nonneg_right haL (norm_nonneg (u - v))
  change ‖pair ((-a / 2) • (u.fst - v.fst)) ((a / 8) • (u.snd - v.snd))‖ ≤ _ at hp
  nlinarith [norm_nonneg (u - v)]



lemma centered_dual_mix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a α : ℝ) (xs z zp : E) :
    centeredDual a xs (α • z + (1 - α) • zp) =
      α • centeredDual a xs z + (1 - α) • centeredDual a xs zp := by
  dsimp [centeredDual]
  module

lemma centered_dual_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : a ≠ 0) (xs z x : E) :
    centeredDual a xs ((1 / 2 : ℝ) • z - (a / 2) • x) =
      (1 / 2 : ℝ) • (centeredDual a xs z - (x - xs)) := by
  have hcoef : 1 / a * (a / 2) = 1 / 2 := by field_simp
  simp only [centeredDual, smul_sub, smul_smul, hcoef]
  module

lemma centered_primal_update {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {b : ℝ} (hb : b ≠ 0) (α : ℝ) (ys y yf wf : F) :
    (1 - α / 2) • y - (α / (2 * b)) • wf - ys =
      (1 - α / 2) • (y - ys) + (α / 2) • (yf - ys) -
        (α / (2 * b)) • (wf + b • yf) := by
  have hcoef : α / (2 * b) * b = α / 2 := by field_simp
  simp only [smul_sub, smul_add, smul_smul, hcoef]
  module

lemma centered_residual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : a ≠ 0) (xs x z zg : E) :
    a • (centeredDual a xs z + (1 / 2 : ℝ) • ((x - xs) - centeredDual a xs zg)) =
      z + (a / 2) • x - (1 / 2 : ℝ) • zg ∧
      (x - xs) + centeredDual a xs zg = x + (1 / a) • zg := by
  constructor
  · dsimp [centeredDual]
    have hcoef : a * (1 / 2) * (1 / a) = 1 / 2 := by field_simp
    simp only [smul_add, smul_sub, smul_smul, mul_one_div_cancel ha, one_smul,
      ← mul_assoc, hcoef]
    module
  · dsimp [centeredDual]
    module


lemma normalized_residual_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (xs x z zg : E) (ys y yg w : F)
    (hres : ‖pair (z + (a / 2) • x - (1 / 2 : ℝ) • zg) (w + (a / 8) • (y - yg))‖ ≤
      a / 8 * ‖pair (x + (1 / a) • zg) (y - yg)‖) :
    a ^ 2 * ‖centeredDual a xs z + (1 / 2 : ℝ) • ((x - xs) - centeredDual a xs zg)‖ ^ 2 +
      ‖w + (a / 8) • ((y - ys) - (yg - ys))‖ ^ 2 ≤
      a ^ 2 / 64 * (‖(x - xs) + centeredDual a xs zg‖ ^ 2 + ‖(y - ys) - (yg - ys)‖ ^ 2) := by
  have h := mul_self_le_mul_self (norm_nonneg _) hres
  have he := centered_residual ha.ne' xs x z zg
  have hy : (y - ys) - (yg - ys) = y - yg := by module
  rw [hy, he.2]
  have hx : ‖z + (a / 2) • x - (1 / 2 : ℝ) • zg‖ ^ 2 =
      a ^ 2 * ‖centeredDual a xs z + (1 / 2 : ℝ) • ((x - xs) - centeredDual a xs zg)‖ ^ 2 := by
    rw [← he.1, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  simp only [← sq, mul_pow, div_pow, WithLp.prod_norm_sq_eq_of_L2, pair,
    WithLp.fst, WithLp.snd] at h
  rw [hx] at h
  norm_num at h
  simpa only [one_div] using h

set_option maxHeartbeats 100000 in
lemma evaluated_inner_certificate {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C : Set (Joint E F)} {B P : Joint E F → Joint E F}
    (hC : IsComplete C) (hne : C.Nonempty) (hP : ConstrainedMonotone.Proj C P)
    (cfg : FoamConfig) (ha : 0 < cfg.a) (hb : 0 ≤ cfg.b) (haL : cfg.a ≤ cfg.L)
    (hη : 0 < cfg.η) (hηL : cfg.η * (2 * cfg.L) ≤ 1 / 4)
    (hk : 1 ≤ cfg.innerSteps) (hK : 16 ≤ cfg.η * (cfg.a / 8) * cfg.innerSteps)
    (β : ℝ) (center : Joint E F) (zg : E) (yg : F)
    (hmono : ∀ u ∈ C, ∀ v ∈ C,
      2 * cfg.a * ‖u.fst - v.fst‖ ^ 2 + 2 * cfg.b * ‖u.snd - v.snd‖ ^ 2 ≤
        ⟪(B u + β • (u - center)) - (B v + β • (v - center)), u - v⟫)
    (hlip : ∀ u ∈ C, ∀ v ∈ C,
      ‖(B u + β • (u - center)) - (B v + β • (v - center))‖ ≤ cfg.L * ‖u - v‖) :
    let anchor := pair ((-1 / cfg.a) • zg) yg
    let st := QueryPlan.eval (Sum.elim B P)
      (repeatQueries (innerEagStep cfg β center zg yg (P anchor)) cfg.innerSteps ⟨0, P anchor, 0⟩)
    st.point ∈ C ∧ ConstrainedMonotone.Normal C st.point st.normal ∧
      ‖QueryPlan.eval (Sum.elim B P) (innerFieldQuery cfg β center zg yg st.point) + st.normal‖ ≤
        cfg.a / 8 * ‖st.point - anchor‖ := by
  let anchor := pair ((-1 / cfg.a) • zg) yg
  let A := fun u => QueryPlan.eval (Sum.elim B P) (innerFieldQuery cfg β center zg yg u)
  have hA (u : Joint E F) : A u =
      pair ((B u + β • (u - center)).fst - (cfg.a / 2) • u.fst - (1 / 2 : ℝ) • zg)
        ((B u + β • (u - center)).snd + (cfg.a / 8) • (u.snd - yg)) :=
    eval_innerFieldQuery B P cfg β center zg yg u
  have hstrong : ∀ u ∈ C, ∀ v ∈ C, cfg.a / 8 * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫ := by
    intro u hu v hv
    rw [hA, hA]
    exact inner_field_monotonicity (B := fun u => B u + β • (u - center))
      (u := u) (v := v) ha.le hb zg yg (hmono u hu v hv)
  have hLip : ∀ u ∈ C, ∀ v ∈ C, ‖A u - A v‖ ≤ (2 * cfg.L) * ‖u - v‖ := by
    intro u hu v hv
    rw [hA, hA]
    exact inner_field_lipschitz (B := fun u => B u + β • (u - center))
      (u := u) (v := v) ha.le haL zg yg (hlip u hu v hv)
  have hcert := eag_unscaled_certificate hC hne hP (show 0 < cfg.a / 8 by positivity)
    (show cfg.a / 8 ≤ 2 * cfg.L by linarith) hη hηL hstrong hLip anchor hk hK
  have he := inner_eag_execution B P cfg hη.ne' β center zg yg (P anchor) cfg.innerSteps
  dsimp only at he hcert ⊢
  rw [he.2.1, he.2.2]
  exact hcert



lemma evaluated_foam_step {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B P : Joint E F → Joint E F) (cfg : FoamConfig) (β : ℝ)
    (center : Joint E F) (s : FoamState E F) :
    let zg := cfg.α • s.z + (1 - cfg.α) • s.zf
    let yg := cfg.α • s.y + (1 - cfg.α) • s.yf
    let u0 := P (pair ((-1 / cfg.a) • zg) yg)
    let st := QueryPlan.eval (Sum.elim B P)
      (repeatQueries (innerEagStep cfg β center zg yg u0) cfg.innerSteps ⟨0, u0, 0⟩)
    let f := B st.point + β • (st.point - center)
    QueryPlan.eval (Sum.elim B P) (foamStep cfg β center s) =
      { z := (1 / 2 : ℝ) • s.z - (cfg.a / 2) • st.point.fst
        y := (1 - cfg.α / 2) • s.y -
          (cfg.α / (2 * cfg.b)) • (f.snd - cfg.b • st.point.snd + st.normal.snd)
        xf := st.point.fst, zf := f.fst - cfg.a • st.point.fst + st.normal.fst,
        yf := st.point.snd } := by
  dsimp only
  unfold foamStep
  erw [QueryPlan.eval_bind, eval_projectionQuery, QueryPlan.eval_bind, QueryPlan.eval_map,
    eval_fieldQuery]


lemma projected_output_bound {p : Public} {I : Problem p} {P : Space p → Space p}
    (hP : ConstrainedMonotone.Proj (domain p) P) {a b α : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hα₁ : α ≤ 1) (htune : α ^ 2 = b / a)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (s : FoamState p.E p.F) (hgap : 0 ≤ gameGap I a b xs ys s.xf s.zf s.yf) :
    2 * a * α * ‖P (pair ((-1 / a) • s.z) s.y) - WithLp.toLp 2 (xs, ys)‖ ^ 2 ≤
      gameLyapunov I a b α xs ys s := by
  have hp := hP.dist_le (pair ((-1 / a) • s.z) s.y) hs
  have hp₂ := mul_self_le_mul_self (norm_nonneg _) hp
  have he : ((-1 / a) • s.z - xs) = -centeredDual a xs s.z := by
    dsimp [centeredDual]
    module
  have hn : ‖pair ((-1 / a) • s.z) s.y - WithLp.toLp 2 (xs, ys)‖ ^ 2 =
      ‖centeredDual a xs s.z‖ ^ 2 + ‖s.y - ys‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(-1 / a) • s.z - xs‖ ^ 2 + ‖s.y - ys‖ ^ 2 = _
    rw [he, norm_neg]
  simp only [← sq] at hp₂
  rw [hn] at hp₂
  have hc : b / α = a * α := by
    have hh := (eq_div_iff ha.ne').mp htune
    apply (div_eq_iff hα.ne').mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hp₂ (show 0 ≤ 2 * a * α by positivity)
  have hq : 0 ≤ 2 / α * gameGap I a b xs ys s.xf s.zf s.yf := by positivity
  have hz := mul_nonneg (show 0 ≤ 2 * a * (1 - α) by positivity)
    (sq_nonneg ‖centeredDual a xs s.z‖)
  dsimp [gameLyapunov]
  have hc' : 2 * b / α = 2 * (a * α) := by rw [mul_div_assoc, hc]
  rw [hc']
  nlinarith


lemma initial_lyapunov_algebra {a b α L D δ Z2 X2 Y2 W2 V : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) (haL : a ≤ L)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hδ : 0 ≤ δ) (hδL : δ ≤ L)
    (hZ : 0 ≤ Z2) (hY : 0 ≤ Y2)
    (hx : X2 ≤ D ^ 2) (hy : Y2 ≤ D ^ 2) (hw : W2 ≤ 4 * L ^ 2 * D ^ 2)
    (hz : a ^ 2 * Z2 ≤ 2 * W2 + 2 * a ^ 2 * X2)
    (hv : V ≤ 2 * L ^ 2 * D ^ 2 / a + (2 * L + δ) * D ^ 2) :
    2 * a * Z2 + 2 * b / α * Y2 + 2 / α * V ≤ 32 * L ^ 2 * D ^ 2 / (α * a) := by
  have hL : 0 < L := ha.trans_le haL
  have hax : a ^ 2 * X2 ≤ L ^ 2 * D ^ 2 := calc
    _ ≤ a ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_left hx (sq_nonneg a)
    _ ≤ L ^ 2 * D ^ 2 := by gcongr
  have hz' : a ^ 2 * Z2 ≤ 10 * L ^ 2 * D ^ 2 := by nlinarith only [hz, hw, hax]
  have hαz := mul_le_mul_of_nonneg_right hα₁ (show 0 ≤ 2 * a ^ 2 * Z2 by positivity)
  have hdual : 2 * α * a ^ 2 * Z2 ≤ 20 * L ^ 2 * D ^ 2 := by nlinarith only [hαz, hz']
  have hby : a * b * Y2 ≤ L ^ 2 * D ^ 2 := calc
    _ ≤ L * L * D ^ 2 := by gcongr; exact hba.trans haL
    _ = _ := by ring
  have hcoef : a * (2 * L + δ) ≤ 3 * L ^ 2 := calc
    _ ≤ L * (2 * L + L) := by gcongr
    _ = _ := by ring
  have hcoefD := mul_le_mul_of_nonneg_right hcoef (sq_nonneg D)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2 * a by positivity)
  have hid : 2 * a * (2 * L ^ 2 * D ^ 2 / a + (2 * L + δ) * D ^ 2) =
      4 * L ^ 2 * D ^ 2 + 2 * a * (2 * L + δ) * D ^ 2 := by field_simp; ring
  rw [hid] at hv'
  have hpot : 2 * a * V ≤ 10 * L ^ 2 * D ^ 2 := by nlinarith only [hv', hcoefD]
  apply (le_div_iff₀ (mul_pos hα ha)).mpr
  have he : (2 * a * Z2 + 2 * b / α * Y2 + 2 / α * V) * (α * a) =
      2 * α * a ^ 2 * Z2 + 2 * a * b * Y2 + 2 * a * V := by field_simp
  rw [he]
  nlinarith only [hdual, hby, hpot]


lemma foam_state_contraction {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) (cfg : FoamConfig) {c : ℝ}
    (ha : 0 < cfg.a) (hb : 0 < cfg.b) (hc : 0 < c)
    (hα : 0 < cfg.α) (hα₁ : cfg.α ≤ 1) (htune : cfg.α ^ 2 = cfg.b / cfg.a)
    (hsmall : 8 * p.δ ^ 2 ≤ cfg.a * cfg.α * c)
    (hμ : p.μ = 2 * cfg.a) (hν : p.ν - p.δ - cfg.b = c)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    (s : FoamState p.E p.F) (hvp : FastValid H G cfg.a s.xf s.zf s.yf)
    (u n : Space p) (hu : u ∈ domain p) (hn : ConstrainedMonotone.Normal (domain p) u n)
    (hr :
      ‖pair ((ownGradient H G u).fst - (cfg.a / 2) • u.fst -
          (1 / 2 : ℝ) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        ((ownGradient H G u).snd + (cfg.a / 8) •
          (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf))) + n‖ ≤
      cfg.a / 8 * ‖u - pair ((-1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        (cfg.α • s.y + (1 - cfg.α) • s.yf)‖) :
    let sn : FoamState p.E p.F :=
      { z := (1 / 2 : ℝ) • s.z - (cfg.a / 2) • u.fst
        y := (1 - cfg.α / 2) • s.y -
          (cfg.α / (2 * cfg.b)) • ((ownGradient H G u).snd - cfg.b • u.snd + n.snd)
        xf := u.fst, zf := (ownGradient H G u).fst - cfg.a • u.fst + n.fst, yf := u.snd }
    FastValid H G cfg.a sn.xf sn.zf sn.yf ∧
      gameLyapunov I cfg.a cfg.b cfg.α xs ys sn ≤
        (1 - cfg.α / 2) * gameLyapunov I cfg.a cfg.b cfg.α xs ys s := by
  have hueta : WithLp.toLp 2 (u.fst, u.snd) = u := WithLp.toLp_ofLp 2 u
  have hnparts := product_normal hu hn
  dsimp only
  constructor
  · refine ⟨hu.1, hu.2, n.fst, hnparts.1, ?_⟩
    rw [hueta]
  have hr' : ‖pair ((ownGradient H G u).fst - cfg.a • u.fst + n.fst +
          (cfg.a / 2) • u.fst - (1 / 2 : ℝ) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        ((ownGradient H G u).snd + n.snd + (cfg.a / 8) •
          (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf)))‖ ≤
      cfg.a / 8 * ‖pair (u.fst + (1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf))‖ := by
    have heL : pair ((ownGradient H G u).fst - cfg.a • u.fst + n.fst +
          (cfg.a / 2) • u.fst - (1 / 2 : ℝ) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        ((ownGradient H G u).snd + n.snd + (cfg.a / 8) •
          (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf))) =
        pair ((ownGradient H G u).fst - (cfg.a / 2) • u.fst -
          (1 / 2 : ℝ) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
          ((ownGradient H G u).snd + (cfg.a / 8) •
            (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf))) + n := by
      apply WithLp.ofLp_injective 2
      change ((ownGradient H G u).fst - cfg.a • u.fst + n.fst +
          (cfg.a / 2) • u.fst - (1 / 2 : ℝ) • (cfg.α • s.z + (1 - cfg.α) • s.zf),
        (ownGradient H G u).snd + n.snd + (cfg.a / 8) •
          (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf))) =
        ((ownGradient H G u).fst - (cfg.a / 2) • u.fst -
          (1 / 2 : ℝ) • (cfg.α • s.z + (1 - cfg.α) • s.zf) + n.fst,
          (ownGradient H G u).snd + (cfg.a / 8) •
            (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf)) + n.snd)
      apply Prod.ext <;> dsimp only <;> module
    have heR : pair (u.fst + (1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
        (u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf)) =
        u - pair ((-1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf))
          (cfg.α • s.y + (1 - cfg.α) • s.yf) := by
      apply WithLp.ofLp_injective 2
      change (u.fst + (1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf),
          u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf)) =
        (u.fst - (-1 / cfg.a) • (cfg.α • s.z + (1 - cfg.α) • s.zf),
          u.snd - (cfg.α • s.y + (1 - cfg.α) • s.yf))
      apply Prod.ext <;> dsimp only
      module
    rw [heL, heR]
    exact hr
  have hres := normalized_residual_bound ha xs u.fst
    ((ownGradient H G u).fst - cfg.a • u.fst + n.fst)
    (cfg.α • s.z + (1 - cfg.α) • s.zf) ys u.snd
    (cfg.α • s.y + (1 - cfg.α) • s.yf) ((ownGradient H G u).snd + n.snd) hr'
  have hymix : cfg.α • s.y + (1 - cfg.α) • s.yf - ys =
      cfg.α • (s.y - ys) + (1 - cfg.α) • (s.yf - ys) := by module
  rw [centered_dual_mix, hymix] at hres
  have hcon := game_normalized_contraction geom ha hb hc hα hα₁ htune hsmall hμ hν
    hs hns s hvp hu.1 hu.2 hnparts.2 (by simpa only [hueta] using hres)
  dsimp only [gameLyapunov]
  rw [centered_dual_update ha.ne', centered_primal_update hb.ne' cfg.α ys s.y u.snd]
  have hw : (ownGradient H G u).snd - cfg.b • u.snd + n.snd + cfg.b • u.snd =
      (ownGradient H G u).snd + n.snd := by module
  rw [hw]
  simpa only [hueta, gameLyapunov] using hcon


lemma initial_state_bound {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) {a b c α L D : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hba : b ≤ a) (haL : a ≤ L)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hD : 0 ≤ D) (hδ : 0 ≤ p.δ) (hδL : p.δ ≤ L)
    (hμ : p.μ = 2 * a) (hν : p.ν - p.δ - b = c)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    (u n : Space p) (hu : u ∈ domain p) (hn : ConstrainedMonotone.Normal (domain p) u n)
    (hdiam : ‖u - WithLp.toLp 2 (xs, ys)‖ ≤ D)
    (hw : ‖ownGradient H G u + n‖ ≤ 2 * L * D) :
    let w := ownGradient H G u + n
    let z := w.fst - a • u.fst
    let s : FoamState p.E p.F := ⟨z, u.snd, u.fst, z, u.snd⟩
    FastValid H G a s.xf s.zf s.yf ∧
      gameLyapunov I a b α xs ys s ≤ 32 * L ^ 2 * D ^ 2 / (α * a) := by
  let w := ownGradient H G u + n
  let z := w.fst - a • u.fst
  have hueta : WithLp.toLp 2 (u.fst, u.snd) = u := WithLp.toLp_ofLp 2 u
  have hnparts := product_normal hu hn
  have hv : FastValid H G a u.fst z u.snd := by
    refine ⟨hu.1, hu.2, n.fst, hnparts.1, ?_⟩
    rw [hueta]
    dsimp [z, w]
    module
  dsimp only
  refine ⟨hv, ?_⟩
  have hz : centeredDual a xs z = (1 / a) • w.fst - (u.fst - xs) := by
    dsimp [centeredDual, z]
    simp only [smul_sub, smul_smul, one_div_mul_cancel ha.ne', one_smul]
    module
  obtain ⟨_, he, _, hsupp⟩ := normalized_gap_supports geom ha hb hc hμ hν hs hns
    hu.1 hu.2 hv hnparts.2 (z := z)
  rw [hz] at hsupp
  have hwy : (ownGradient H G (WithLp.toLp 2 (u.fst, u.snd))).snd + n.snd = w.snd := by
    rw [hueta]
    exact (WithLp.add_snd _ _).symm
  rw [hwy] at hsupp
  have hgap := initial_gap_from_support ha hb hc (u.fst - xs) w.fst (u.snd - ys) w.snd
    ((2 : ℝ) • ((G (WithLp.toLp 2 (u.fst, u.snd))).snd -
      (G (WithLp.toLp 2 (xs, u.snd))).snd)) hsupp
  have hxy : ‖u.fst - xs‖ ^ 2 + ‖u.snd - ys‖ ^ 2 ≤ D ^ 2 := by
    have ht := mul_self_le_mul_self (norm_nonneg _) hdiam
    simpa only [← sq, WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst, WithLp.sub_snd,
      WithLp.fst, WithLp.snd, WithLp.ofLp_sub, WithLp.ofLp_toLp, Prod.fst_sub, Prod.snd_sub] using ht
  have hwx : ‖w.fst‖ ≤ 2 * L * D := (WithLp.norm_fst_le p.E w).trans hw
  have hwy' : ‖w.snd‖ ≤ 2 * L * D := (WithLp.norm_snd_le p.E w).trans hw
  have hwx₂ : ‖w.fst‖ ^ 2 ≤ 4 * L ^ 2 * D ^ 2 := by
    have ht := mul_self_le_mul_self (norm_nonneg _) hwx
    nlinarith only [ht]
  have hgap' := initial_gap_bound ha (ha.le.trans haL) hD hδ (u.fst - xs) w.fst
    (u.snd - ys) w.snd _ hgap hxy hwx₂ hwy' he
  have hz₂ : a ^ 2 * ‖centeredDual a xs z‖ ^ 2 ≤
      2 * ‖w.fst‖ ^ 2 + 2 * a ^ 2 * ‖u.fst - xs‖ ^ 2 := by
    have htri := norm_sub_le w.fst (a • (u.fst - xs))
    have hid : a • centeredDual a xs z = w.fst - a • (u.fst - xs) := by
      rw [hz, smul_sub, smul_smul, mul_one_div_cancel ha.ne', one_smul]
    have ht := mul_self_le_mul_self (norm_nonneg _) htri
    rw [← hid, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at ht
    nlinarith [sq_nonneg (‖w.fst‖ - a * ‖u.fst - xs‖)]
  exact initial_lyapunov_algebra ha hb hba haL hα hα₁ hδ hδL
    (sq_nonneg _) (sq_nonneg _)
    (by nlinarith [sq_nonneg ‖u.snd - ys‖])
    (by nlinarith [sq_nonneg ‖u.fst - xs‖]) hwx₂ hz₂ hgap'


set_option maxHeartbeats 600000 in
lemma executed_step_contraction {p : Public} {I : Problem p} {H G B P : Space p → Space p}
    (geom : GameGeometry p I H G) (hC : IsComplete (domain p))
    (hP : ConstrainedMonotone.Proj (domain p) P)
    (cfg : FoamConfig) {c β : ℝ} (center : Space p)
    (ha : 0 < cfg.a) (hb : 0 < cfg.b) (hc : 0 < c)
    (hα : 0 < cfg.α) (hα₁ : cfg.α ≤ 1) (htune : cfg.α ^ 2 = cfg.b / cfg.a)
    (hsmall : 8 * p.δ ^ 2 ≤ cfg.a * cfg.α * c)
    (hμ : p.μ = 2 * cfg.a) (hν : p.ν - p.δ - cfg.b = c) (hνb : p.ν = 2 * cfg.b)
    (haL : cfg.a ≤ cfg.L) (hη : 0 < cfg.η) (hηL : cfg.η * (2 * cfg.L) ≤ 1 / 4)
    (hk : 1 ≤ cfg.innerSteps) (hK : 16 ≤ cfg.η * (cfg.a / 8) * cfg.innerSteps)
    (hfield : ∀ u ∈ domain p, B u + β • (u - center) = ownGradient H G u)
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p,
      ‖(B u + β • (u - center)) - (B v + β • (v - center))‖ ≤ cfg.L * ‖u - v‖)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys))))
    (s : FoamState p.E p.F) (hvp : FastValid H G cfg.a s.xf s.zf s.yf) :
    let sn := QueryPlan.eval (Sum.elim B P) (foamStep cfg β center s)
    FastValid H G cfg.a sn.xf sn.zf sn.yf ∧
      gameLyapunov I cfg.a cfg.b cfg.α xs ys sn ≤
        (1 - cfg.α / 2) * gameLyapunov I cfg.a cfg.b cfg.α xs ys s := by
  let zg := cfg.α • s.z + (1 - cfg.α) • s.zf
  let yg := cfg.α • s.y + (1 - cfg.α) • s.yf
  let u0 := P (pair ((-1 / cfg.a) • zg) yg)
  let st := QueryPlan.eval (Sum.elim B P)
    (repeatQueries (innerEagStep cfg β center zg yg u0) cfg.innerSteps ⟨0, u0, 0⟩)
  have hmono : ∀ u ∈ domain p, ∀ v ∈ domain p,
      2 * cfg.a * ‖u.fst - v.fst‖ ^ 2 + 2 * cfg.b * ‖u.snd - v.snd‖ ^ 2 ≤
        ⟪(B u + β • (u - center)) - (B v + β • (v - center)), u - v⟫ := by
    intro u hu v hv
    rw [hfield u hu, hfield v hv]
    have h := game_monotonicity geom.strongX geom.strongY geom.convexG
      geom.gradientH geom.gradientG hu hv
    simpa only [hμ, hνb] using h
  have hcert := evaluated_inner_certificate hC ⟨_, hs⟩ hP cfg ha hb.le haL hη hηL
    hk hK β center zg yg hmono hlip
  change st.point ∈ domain p ∧ ConstrainedMonotone.Normal (domain p) st.point st.normal ∧ _ at hcert
  obtain ⟨hu, hn, hr⟩ := hcert
  rw [eval_innerFieldQuery, hfield st.point hu] at hr
  have hcon := foam_state_contraction geom cfg ha hb hc hα hα₁ htune hsmall hμ hν
    hs hns s hvp st.point st.normal hu hn hr
  dsimp only
  rw [evaluated_foam_step]
  change _ ∧ _
  rw [← hfield st.point hu] at hcon
  exact hcon


lemma executed_initial_bound {p : Public} {I : Problem p} {H G B P : Space p → Space p}
    (geom : GameGeometry p I H G) (hP : ConstrainedMonotone.Proj (domain p) P)
    (cfg : FoamConfig) {c β D : ℝ} (center u0 : Space p) (hu0 : u0 ∈ domain p)
    (ha : 0 < cfg.a) (hb : 0 ≤ cfg.b) (hc : 0 ≤ c) (hba : cfg.b ≤ cfg.a)
    (haL : cfg.a ≤ cfg.L) (hα : 0 < cfg.α) (hα₁ : cfg.α ≤ 1)
    (hD : 0 ≤ D) (hδ : 0 ≤ p.δ) (hδL : p.δ ≤ cfg.L)
    (hμ : p.μ = 2 * cfg.a) (hν : p.ν - p.δ - cfg.b = c)
    (hfield : ∀ u ∈ domain p, B u + β • (u - center) = ownGradient H G u)
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p,
      ‖(B u + β • (u - center)) - (B v + β • (v - center))‖ ≤ cfg.L * ‖u - v‖)
    (hdiam : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖u - v‖ ≤ D)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys)))) :
    let s := QueryPlan.eval (Sum.elim B P) (foamInitial cfg β center u0)
    FastValid H G cfg.a s.xf s.zf s.yf ∧
      gameLyapunov I cfg.a cfg.b cfg.α xs ys s ≤ 32 * cfg.L ^ 2 * D ^ 2 / (cfg.α * cfg.a) := by
  let F := fun u => B u + β • (u - center)
  let u1 := P (u0 - (1 / cfg.L) • F u0)
  let n := cfg.L • (u0 - u1) - F u0
  have hu1 : u1 ∈ domain p := hP.mem _
  have hn : ConstrainedMonotone.Normal (domain p) u1 n :=
    forward_normal hP F (ha.trans_le haL) u0
  have hw : ‖ownGradient H G u1 + n‖ ≤ 2 * cfg.L * D := by
    rw [← hfield u1 hu1]
    exact forward_residual_bound (F := F) (u := u0) (v := u1) (ha.le.trans haL)
      (hlip u1 hu1 u0 hu0) (hdiam u1 hu1 u0 hu0)
  have hi := initial_state_bound geom ha hb hc hba haL hα hα₁ hD hδ hδL hμ hν hs hns
    u1 n hu1 hn (hdiam u1 hu1 _ hs) hw
  dsimp only
  unfold foamInitial
  erw [QueryPlan.eval_bind, eval_fieldQuery, QueryPlan.eval_bind, eval_projectionQuery,
    QueryPlan.eval_map, eval_fieldQuery]
  have hw' : F u1 + cfg.L • (u0 - u1) - F u0 = ownGradient H G u1 + n := by
    dsimp [n]
    rw [show F u1 = ownGradient H G u1 from hfield u1 hu1]
    module
  change _ ∧ _
  rw [← hw'] at hi
  exact hi


lemma state_contraction_iterates {S : Type*} (step : S → S) (valid : S → Prop)
    (V : S → ℝ) {q A : ℝ} (hq : 0 ≤ q)
    (hstep : ∀ s, valid s → valid (step s) ∧ V (step s) ≤ q * V s)
    (s0 : S) (hvalid : valid s0) (hV : V s0 ≤ A) (k : ℕ) :
    valid (step^[k] s0) ∧ V (step^[k] s0) ≤ q ^ k * A := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq, pow_zero, one_mul] using And.intro hvalid hV
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hv, hb⟩ := hstep _ ih.1
    refine ⟨hv, hb.trans ?_⟩
    calc
      q * V (step^[k] s0) ≤ q * (q ^ k * A) := mul_le_mul_of_nonneg_left ih.2 hq
      _ = q ^ (k + 1) * A := by rw [pow_succ]; ring


lemma foam_plan_bound {p : Public} {I : Problem p} {H G B P : Space p → Space p}
    (hP : ConstrainedMonotone.Proj (domain p) P) (cfg : FoamConfig) (β D : ℝ)
    (center u0 : Space p) (ha : 0 < cfg.a) (hα : 0 < cfg.α) (hα₁ : cfg.α ≤ 1)
    (htune : cfg.α ^ 2 = cfg.b / cfg.a)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hgap : ∀ s : FoamState p.E p.F, FastValid H G cfg.a s.xf s.zf s.yf →
      0 ≤ gameGap I cfg.a cfg.b xs ys s.xf s.zf s.yf)
    (hi : let s := QueryPlan.eval (Sum.elim B P) (foamInitial cfg β center u0)
      FastValid H G cfg.a s.xf s.zf s.yf ∧
        gameLyapunov I cfg.a cfg.b cfg.α xs ys s ≤ 32 * cfg.L ^ 2 * D ^ 2 / (cfg.α * cfg.a))
    (hstep : ∀ s : FoamState p.E p.F, FastValid H G cfg.a s.xf s.zf s.yf →
      let sn := QueryPlan.eval (Sum.elim B P) (foamStep cfg β center s)
      FastValid H G cfg.a sn.xf sn.zf sn.yf ∧
        gameLyapunov I cfg.a cfg.b cfg.α xs ys sn ≤
          (1 - cfg.α / 2) * gameLyapunov I cfg.a cfg.b cfg.α xs ys s) :
    let out := QueryPlan.eval (Sum.elim B P) (foamPlan cfg β center u0)
    out ∈ domain p ∧ ‖out - WithLp.toLp 2 (xs, ys)‖ ^ 2 ≤
      16 * cfg.L ^ 2 * D ^ 2 / (cfg.α ^ 2 * cfg.a ^ 2) * (1 - cfg.α / 2) ^ cfg.outerSteps := by
  let s0 := QueryPlan.eval (Sum.elim B P) (foamInitial cfg β center u0)
  let step := fun s => QueryPlan.eval (Sum.elim B P) (foamStep cfg β center s)
  have hi' := state_contraction_iterates step (fun s => FastValid H G cfg.a s.xf s.zf s.yf)
    (gameLyapunov I cfg.a cfg.b cfg.α xs ys) (show 0 ≤ 1 - cfg.α / 2 by linarith)
    hstep s0 hi.1 hi.2 cfg.outerSteps
  have hp := projected_output_bound hP ha hα hα₁ htune hs (step^[cfg.outerSteps] s0)
    (hgap _ hi'.1)
  have hout : QueryPlan.eval (Sum.elim B P) (foamPlan cfg β center u0) =
      P (pair ((-1 / cfg.a) • (step^[cfg.outerSteps] s0).z) (step^[cfg.outerSteps] s0).y) := by
    unfold foamPlan
    erw [QueryPlan.eval_bind, QueryPlan.eval_bind, eval_projectionQuery, eval_repeatQueries]
  dsimp only
  rw [hout]
  refine ⟨hP.mem _, ?_⟩
  have hb := hp.trans hi'.2
  calc
    _ ≤ ((1 - cfg.α / 2) ^ cfg.outerSteps *
      (32 * cfg.L ^ 2 * D ^ 2 / (cfg.α * cfg.a))) / (2 * cfg.a * cfg.α) := by
        apply (le_div_iff₀ (show 0 < 2 * cfg.a * cfg.α by positivity)).mpr
        nlinarith only [hb]
    _ = _ := by field_simp; ring


lemma foam_convergence {p : Public} {I : Problem p} {H G B P : Space p → Space p}
    (geom : GameGeometry p I H G) (hC : IsComplete (domain p))
    (hP : ConstrainedMonotone.Proj (domain p) P)
    (cfg : FoamConfig) {c β D : ℝ} (center u0 : Space p) (hu0 : u0 ∈ domain p)
    (ha : 0 < cfg.a) (hb : 0 < cfg.b) (hc : 0 < c) (hba : cfg.b ≤ cfg.a)
    (hα : 0 < cfg.α) (hα₁ : cfg.α ≤ 1) (htune : cfg.α ^ 2 = cfg.b / cfg.a)
    (hsmall : 8 * p.δ ^ 2 ≤ cfg.a * cfg.α * c)
    (hμ : p.μ = 2 * cfg.a) (hν : p.ν - p.δ - cfg.b = c) (hνb : p.ν = 2 * cfg.b)
    (haL : cfg.a ≤ cfg.L) (hη : 0 < cfg.η) (hηL : cfg.η * (2 * cfg.L) ≤ 1 / 4)
    (hk : 1 ≤ cfg.innerSteps) (hK : 16 ≤ cfg.η * (cfg.a / 8) * cfg.innerSteps)
    (hD : 0 ≤ D) (hδ : 0 ≤ p.δ) (hδL : p.δ ≤ cfg.L)
    (hfield : ∀ u ∈ domain p, B u + β • (u - center) = ownGradient H G u)
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p,
      ‖(B u + β • (u - center)) - (B v + β • (v - center))‖ ≤ cfg.L * ‖u - v‖)
    (hdiam : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖u - v‖ ≤ D)
    {xs : p.E} {ys : p.F} (hs : WithLp.toLp 2 (xs, ys) ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) (WithLp.toLp 2 (xs, ys))
      (-ownGradient H G (WithLp.toLp 2 (xs, ys)))) :
    let out := QueryPlan.eval (Sum.elim B P) (foamPlan cfg β center u0)
    out ∈ domain p ∧ ‖out - WithLp.toLp 2 (xs, ys)‖ ^ 2 ≤
      16 * cfg.L ^ 2 * D ^ 2 / (cfg.α ^ 2 * cfg.a ^ 2) * (1 - cfg.α / 2) ^ cfg.outerSteps := by
  apply foam_plan_bound hP cfg β D center u0 ha hα hα₁ htune hs
  · intro s hv
    exact game_gap_nonnegative geom ha hb.le hc.le hμ hν hs hns hv
  · exact executed_initial_bound geom hP cfg center u0 hu0 ha hb.le hc.le hba haL hα hα₁
      hD hδ hδL hμ hν hfield hlip hdiam hs hns
  · intro s hv
    exact executed_step_contraction geom hC hP cfg center ha hb hc hα hα₁ htune hsmall hμ hν
      hνb haL hη hηL hk hK hfield hlip hs hns s hv

end OracleTemplate.NearZeroSum
