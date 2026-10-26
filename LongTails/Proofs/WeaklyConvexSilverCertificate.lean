import LongTails.Proofs.SilverCertificate
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped RealInnerProductSpace

namespace LongTails.Proofs.WeaklyConvexSilverCertificate

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ratio_bounds : (2414213 / 1000000 : ℝ) < ratio ∧ ratio < 2414214 / 1000000 := by
  unfold ratio
  have h1 : (1414213 / 1000000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2 < 1414214 / 1000000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  constructor <;> linarith

lemma gram4_nonneg (v a w b : E) (α β γ δ : ℝ) :
    0 ≤ α * α * ⟪v, v⟫ + β * β * ⟪a, a⟫ + γ * γ * ⟪w, w⟫ + δ * δ * ⟪b, b⟫ +
      2 * α * β * ⟪v, a⟫ + 2 * α * γ * ⟪v, w⟫ + 2 * α * δ * ⟪v, b⟫ + 2 * β * γ * ⟪a, w⟫ +
      2 * β * δ * ⟪a, b⟫ + 2 * γ * δ * ⟪w, b⟫ := by
  have h := real_inner_self_nonneg (x := α • v + β • a + γ • w + δ • b)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm v a, real_inner_comm v w, real_inner_comm v b, real_inner_comm a w,
    real_inner_comm a b, real_inner_comm w b] at h
  linear_combination h

set_option maxHeartbeats 8000000 in
lemma scale_decay_two_fifths (v a w b : E) (S r2 Fy Fz η eL eRc eRy ecy ezy : ℝ)
    (hs : ratio ^ 3 ≤ S + 1)
    (hEL : ‖v‖ ^ 2 + S * (S + 1) * ‖a‖ ^ 2 + 2 * S * Fy ≤ r2 + eL)
    (hERc : ‖w‖ ^ 2 + S * (S + 1) * ‖b‖ ^ 2 + 2 * S * Fz ≤ ‖v - (1 + (ratio - 2) * (S + 1)) • a‖ ^ 2 + eRc)
    (hERy : ‖w - (v - a)‖ ^ 2 + S * (S + 1) * ‖b‖ ^ 2 + 2 * S * (Fz - Fy) + S * ‖a‖ ^ 2 ≤
      ((1 + (ratio - 2) * (S + 1)) - 1) ^ 2 * ‖a‖ ^ 2 + eRy)
    (hcy : -ecy ≤ -2 * Fy + 2 * ⟪a, v⟫ - ‖a‖ ^ 2)
    (hzy : -ezy ≤ 2 * (Fz - Fy) - 2 * ⟪a, w - v⟫ - ‖b - a‖ ^ 2)
    (hIC : -(1 / 10) * (ratio * (S + 1) - 1) * ‖b‖ ^ 2 - η ≤ Fz) :
    ‖v - (1 + (ratio - 2) * (S + 1)) • a - (w - b)‖ ^ 2 ≤ 2/5 * r2 + 2/5 * eL + 1/5 * eRc + 47/50 * eRy +
      3/25 * S * ecy + 21/50 * S * ezy + 36/25 * S * η := by
  have hb := ratio_bounds
  have h1 : (1 : ℝ) ≤ ratio ^ 3 := by exact one_le_pow₀ (by linarith [hb.1])
  have hS : 0 ≤ S := by linarith only [hs, h1]
  have n1 := gram4_nonneg v a w b (0) (0) (0) (S + 1)
  have d1 : (0:ℝ) ≤ (57/50 - 18*ratio/125) := by linarith only [hb.1, hb.2]
  have n2 := gram4_nonneg v a w b (1) (60*S*ratio/7 - 21*S + 60*ratio/7 - 21) (3/7) (0)
  have d2 : (0:ℝ) ≤ (7/50) := by linarith only [hb.1, hb.2]
  have n3 := gram4_nonneg v a w b (0) (-53*S*ratio/4 + 161*S/5 - 53*ratio/4 + 161/5) (1) (0)
  have d3 : (0:ℝ) ≤ (4/35) := by linarith only [hb.1, hb.2]
  have n4 := gram4_nonneg v a w b (0) (S + 1) (0) (0)
  have d4 : (0:ℝ) ≤ (183*ratio/2 - 110443/500) := by linarith only [hb.1, hb.2]
  have n5 := gram4_nonneg v a w b (-57875*ratio/3595298 - 192875/3595298) (1373615*S*ratio/3595298 - 1642280*S/1797649 + 1373615*ratio/3595298 - 1642280/1797649) (57875*ratio/3595298 + 192875/3595298) (S + 1)
  have d5 : (0:ℝ) ≤ (13271*ratio/125 - 31943/125) := by linarith only [hb.1, hb.2]
  have n6 := gram4_nonneg v a w b (1) (-7079480*S*ratio/53369839 + 68717138*S/160109517 - 7079480*ratio/53369839 + 68717138/160109517) (70718750*ratio/160109517 - 90841457/160109517) (0)
  have d6 : (0:ℝ) ≤ (31605834/44941225 - 848625*ratio/3595298) := by linarith only [hb.1, hb.2]
  have n7 := gram4_nonneg v a w b (0) (539870147*S*ratio/105309346 - 3353523911*S/263273365 + 539870147*ratio/105309346 - 3353523911/263273365) (1) (0)
  have d7 : (0:ℝ) ≤ (250950974/800547585 - 14143750*ratio/160109517) := by linarith only [hb.1, hb.2]
  have n8 := gram4_nonneg v a w b (0) (S + 1) (0) (0)
  have d8 : (0:ℝ) ≤ (347632863501*ratio/5265467300 - 4195893738341/26327336500) := by linarith only [hb.1, hb.2]
  have n9 := gram4_nonneg v a w b (0) (-355*S/391 - 355/391) (0) (S + 1)
  have d9 : (0:ℝ) ≤ (391/250) := by linarith only [hb.1, hb.2]
  have n10 := gram4_nonneg v a w b (0) (S + 1) (0) (0)
  have d10 : (0:ℝ) ≤ (4406/9775) := by linarith only [hb.1, hb.2]
  have hq0 : 0 ≤ (107*⟪a, a⟫*S^2*ratio/25 - 103*⟪a, a⟫*S^2/10 + 214*⟪a, a⟫*S*ratio/25 - 103*⟪a, a⟫*S/5 + 107*⟪a, a⟫*ratio/25 - 103*⟪a, a⟫/10 - 2*⟪a, w⟫*S*ratio + 121*⟪a, w⟫*S/25 - 2*⟪a, w⟫*ratio + 121*⟪a, w⟫/25 - 18*⟪b, b⟫*S^2*ratio/125 + 57*⟪b, b⟫*S^2/50 - 36*⟪b, b⟫*S*ratio/125 + 57*⟪b, b⟫*S/25 - 18*⟪b, b⟫*ratio/125 + 57*⟪b, b⟫/50 + 12*⟪v, a⟫*S*ratio/5 - 147*⟪v, a⟫*S/25 + 12*⟪v, a⟫*ratio/5 - 147*⟪v, a⟫/25 + 7*⟪v, v⟫/50 + 3*⟪v, w⟫/25 + 7*⟪w, w⟫/50) := by
    linear_combination mul_nonneg d1 n1 + mul_nonneg d2 n2 + mul_nonneg d3 n3 + mul_nonneg d4 n4 + (607*⟪a, a⟫*S^2/20 + 607*⟪a, a⟫*S/10 + 607*⟪a, a⟫/20) * ratio_square
  have hqu : 0 ≤ (-111*⟪a, a⟫*S^2*ratio^2/2 + 6782*⟪a, a⟫*S^2*ratio/25 - 16571*⟪a, a⟫*S^2/50 - 111*⟪a, a⟫*S*ratio^2 + 13564*⟪a, a⟫*S*ratio/25 - 16571*⟪a, a⟫*S/25 - 111*⟪a, a⟫*ratio^2/2 + 6782*⟪a, a⟫*ratio/25 - 16571*⟪a, a⟫/50 + 81*⟪a, b⟫*S^2*ratio^2 - 389*⟪a, b⟫*S^2*ratio + 11676*⟪a, b⟫*S^2/25 + 162*⟪a, b⟫*S*ratio^2 - 778*⟪a, b⟫*S*ratio + 23352*⟪a, b⟫*S/25 + 81*⟪a, b⟫*ratio^2 - 389*⟪a, b⟫*ratio + 11676*⟪a, b⟫/25 - 34*⟪a, w⟫*S*ratio/5 + 409*⟪a, w⟫*S/25 - 34*⟪a, w⟫*ratio/5 + 409*⟪a, w⟫/25 - 1919*⟪b, b⟫*S^2*ratio^2/50 + 22866*⟪b, b⟫*S^2*ratio/125 - 54291*⟪b, b⟫*S^2/250 - 1919*⟪b, b⟫*S*ratio^2/25 + 45732*⟪b, b⟫*S*ratio/125 - 54291*⟪b, b⟫*S/125 - 1919*⟪b, b⟫*ratio^2/50 + 22866*⟪b, b⟫*ratio/125 - 54291*⟪b, b⟫/250 + 52*⟪v, a⟫*S*ratio/5 - 627*⟪v, a⟫*S/25 + 52*⟪v, a⟫*ratio/5 - 627*⟪v, a⟫/25 - 10*⟪v, b⟫*S*ratio + 24*⟪v, b⟫*S - 10*⟪v, b⟫*ratio + 24*⟪v, b⟫ + 7*⟪v, v⟫/50 + 3*⟪v, w⟫/25 + 10*⟪w, b⟫*S*ratio - 24*⟪w, b⟫*S + 10*⟪w, b⟫*ratio - 24*⟪w, b⟫ + 7*⟪w, w⟫/50) := by
    linear_combination mul_nonneg d5 n5 + mul_nonneg d6 n6 + mul_nonneg d7 n7 + mul_nonneg d8 n8 + (20167872075800650321793776718838345613580382043*⟪a, a⟫*S^2*ratio/1531181491291250266871046052619761486544484540 - 14939906384216646113019952714130602387646495083*⟪a, a⟫*S^2/1531181491291250266871046052619761486544484540 + 20167872075800650321793776718838345613580382043*⟪a, a⟫*S*ratio/765590745645625133435523026309880743272242270 - 14939906384216646113019952714130602387646495083*⟪a, a⟫*S/765590745645625133435523026309880743272242270 + 20167872075800650321793776718838345613580382043*⟪a, a⟫*ratio/1531181491291250266871046052619761486544484540 - 14939906384216646113019952714130602387646495083*⟪a, a⟫/1531181491291250266871046052619761486544484540 + 5609708*⟪a, b⟫*S^2/44941225 + 11219416*⟪a, b⟫*S/44941225 + 5609708*⟪a, b⟫/44941225 + 24549559792143059625372358295*⟪a, w⟫*S*ratio/18409058423131192032403674242 - 174428049781215221488696374535891995*⟪a, w⟫*S/484661475753934276283210435605516433 + 24549559792143059625372358295*⟪a, w⟫*ratio/18409058423131192032403674242 - 174428049781215221488696374535891995*⟪a, w⟫/484661475753934276283210435605516433 + 1919*⟪b, b⟫*S^2/50 + 1919*⟪b, b⟫*S/25 + 1919*⟪b, b⟫/50 - 8440140279895*⟪v, a⟫*S*ratio/6463083854402 - 109572673477456920165*⟪v, a⟫*S/172466872376467090639 - 8440140279895*⟪v, a⟫*ratio/6463083854402 - 109572673477456920165*⟪v, a⟫/172466872376467090639 - 6144473*⟪v, b⟫*S/1797649 - 6144473*⟪v, b⟫/1797649 + 355611374875*⟪v, v⟫*ratio/12926167708804 + 2225504588625*⟪v, v⟫/12926167708804 - 355611374875*⟪v, w⟫*ratio/6463083854402 - 190697199179935293875*⟪v, w⟫/344933744752934181278 + 6144473*⟪w, b⟫*S/1797649 + 6144473*⟪w, b⟫/1797649 - 2047554633916819815962470375*⟪w, w⟫*ratio/110454350538787152194422045452 + 37065970025246246143712120875*⟪w, w⟫/110454350538787152194422045452) * ratio_square
  have hq2 : 0 ≤ (87*⟪a, a⟫*S^2/50 + 87*⟪a, a⟫*S/25 + 87*⟪a, a⟫/50 - 71*⟪a, b⟫*S^2/25 - 142*⟪a, b⟫*S/25 - 71*⟪a, b⟫/25 + 391*⟪b, b⟫*S^2/250 + 391*⟪b, b⟫*S/125 + 391*⟪b, b⟫/250) := by
    linear_combination mul_nonneg d9 n9 + mul_nonneg d10 n10 + (0) * ratio_square
  have hsu : 0 ≤ (S + 1) * ratio ^ 3 := mul_nonneg (by linarith) (by linarith)
  have hss : 0 ≤ (S + 1) * (S + 1 - ratio ^ 3) := mul_nonneg (by linarith) (by linarith)
  have hus : 0 ≤ (5*ratio - 12) * (S + 1 - ratio ^ 3) := mul_nonneg (by linarith [hb.1]) (by linarith)
  have hpsi : 0 ≤ (107*⟪a, a⟫*S^4*ratio/25 - 103*⟪a, a⟫*S^4/10 + 368*⟪a, a⟫*S^3*ratio/25 - 883*⟪a, a⟫*S^3/25 + 462*⟪a, a⟫*S^2*ratio/25 - 459*⟪a, a⟫*S^2/10 + 248*⟪a, a⟫*S*ratio/25 - 676*⟪a, a⟫*S/25 + 47*⟪a, a⟫*ratio/25 - 154*⟪a, a⟫/25 + 2*⟪a, b⟫*S^3*ratio - 121*⟪a, b⟫*S^3/25 + 6*⟪a, b⟫*S^2*ratio - 292*⟪a, b⟫*S^2/25 + 6*⟪a, b⟫*S*ratio - 221*⟪a, b⟫*S/25 + 2*⟪a, b⟫*ratio - 2*⟪a, b⟫ - 2*⟪a, w⟫*S^3*ratio + 121*⟪a, w⟫*S^3/25 - 6*⟪a, w⟫*S^2*ratio + 339*⟪a, w⟫*S^2/25 - 6*⟪a, w⟫*S*ratio + 63*⟪a, w⟫*S/5 - 2*⟪a, w⟫*ratio + 97*⟪a, w⟫/25 - 18*⟪b, b⟫*S^4*ratio/125 + 57*⟪b, b⟫*S^4/50 - 54*⟪b, b⟫*S^3*ratio/125 + 498*⟪b, b⟫*S^3/125 - 54*⟪b, b⟫*S^2*ratio/125 + 887*⟪b, b⟫*S^2/250 - 18*⟪b, b⟫*S*ratio/125 - 37*⟪b, b⟫*S/125 - ⟪b, b⟫ + 12*⟪v, a⟫*S^3*ratio/5 - 147*⟪v, a⟫*S^3/25 + 36*⟪v, a⟫*S^2*ratio/5 - 401*⟪v, a⟫*S^2/25 + 36*⟪v, a⟫*S*ratio/5 - 361*⟪v, a⟫*S/25 + 12*⟪v, a⟫*ratio/5 - 107*⟪v, a⟫/25 - 2*⟪v, b⟫*S^2 - 4*⟪v, b⟫*S - 2*⟪v, b⟫ + 7*⟪v, v⟫*S^2/50 + 7*⟪v, v⟫*S/25 + 7*⟪v, v⟫/50 + 3*⟪v, w⟫*S^2/25 + 6*⟪v, w⟫*S/25 + 3*⟪v, w⟫/25 + 2*⟪w, b⟫*S^2 + 4*⟪w, b⟫*S + 2*⟪w, b⟫ + 7*⟪w, w⟫*S^2/50 + 7*⟪w, w⟫*S/25 + 7*⟪w, w⟫/50) := by
    linear_combination mul_nonneg hsu hqu + mul_nonneg hq0 hss + mul_nonneg hq2 hus + (-111*⟪a, a⟫*S^3*ratio^3/2 + 156*⟪a, a⟫*S^3*ratio^2 - 3231*⟪a, a⟫*S^3*ratio/50 + 669*⟪a, a⟫*S^3/25 - 333*⟪a, a⟫*S^2*ratio^3/2 + 4593*⟪a, a⟫*S^2*ratio^2/10 - 9519*⟪a, a⟫*S^2*ratio/50 + 3927*⟪a, a⟫*S^2/50 - 333*⟪a, a⟫*S*ratio^3/2 + 2253*⟪a, a⟫*S*ratio^2/5 - 1869*⟪a, a⟫*S*ratio/10 + 384*⟪a, a⟫*S/5 - 111*⟪a, a⟫*ratio^3/2 + 1473*⟪a, a⟫*ratio^2/10 - 3057*⟪a, a⟫*ratio/50 + 1251*⟪a, a⟫/50 + 81*⟪a, b⟫*S^3*ratio^3 - 227*⟪a, b⟫*S^3*ratio^2 + 2351*⟪a, b⟫*S^3*ratio/25 - 973*⟪a, b⟫*S^3/25 + 243*⟪a, b⟫*S^2*ratio^3 - 3334*⟪a, b⟫*S^2*ratio^2/5 + 6911*⟪a, b⟫*S^2*ratio/25 - 2848*⟪a, b⟫*S^2/25 + 243*⟪a, b⟫*S*ratio^3 - 3263*⟪a, b⟫*S*ratio^2/5 + 6769*⟪a, b⟫*S*ratio/25 - 2777*⟪a, b⟫*S/25 + 81*⟪a, b⟫*ratio^3 - 1064*⟪a, b⟫*ratio^2/5 + 2209*⟪a, b⟫*ratio/25 - 902*⟪a, b⟫/25 - 24*⟪a, w⟫*S^2*ratio^2/5 + 48*⟪a, w⟫*S^2*ratio/25 - 24*⟪a, w⟫*S^2/25 - 48*⟪a, w⟫*S*ratio^2/5 + 96*⟪a, w⟫*S*ratio/25 - 48*⟪a, w⟫*S/25 - 24*⟪a, w⟫*ratio^2/5 + 48*⟪a, w⟫*ratio/25 - 24*⟪a, w⟫/25 - 1919*⟪b, b⟫*S^3*ratio^3/50 + 13289*⟪b, b⟫*S^3*ratio^2/125 - 2203*⟪b, b⟫*S^3*ratio/50 + 2274*⟪b, b⟫*S^3/125 - 5757*⟪b, b⟫*S^2*ratio^3/50 + 77779*⟪b, b⟫*S^2*ratio^2/250 - 32263*⟪b, b⟫*S^2*ratio/250 + 13253*⟪b, b⟫*S^2/250 - 5757*⟪b, b⟫*S*ratio^3/50 + 37912*⟪b, b⟫*S*ratio^2/125 - 31481*⟪b, b⟫*S*ratio/250 + 6431*⟪b, b⟫*S/125 - 1919*⟪b, b⟫*ratio^3/50 + 24623*⟪b, b⟫*ratio^2/250 - 10233*⟪b, b⟫*ratio/250 + 4157*⟪b, b⟫/250 + 8*⟪v, a⟫*S^2*ratio^2 - 16*⟪v, a⟫*S^2*ratio/5 + 8*⟪v, a⟫*S^2/5 + 16*⟪v, a⟫*S*ratio^2 - 32*⟪v, a⟫*S*ratio/5 + 16*⟪v, a⟫*S/5 + 8*⟪v, a⟫*ratio^2 - 16*⟪v, a⟫*ratio/5 + 8*⟪v, a⟫/5 - 10*⟪v, b⟫*S^2*ratio^2 + 4*⟪v, b⟫*S^2*ratio - 2*⟪v, b⟫*S^2 - 20*⟪v, b⟫*S*ratio^2 + 8*⟪v, b⟫*S*ratio - 4*⟪v, b⟫*S - 10*⟪v, b⟫*ratio^2 + 4*⟪v, b⟫*ratio - 2*⟪v, b⟫ + 10*⟪w, b⟫*S^2*ratio^2 - 4*⟪w, b⟫*S^2*ratio + 2*⟪w, b⟫*S^2 + 20*⟪w, b⟫*S*ratio^2 - 8*⟪w, b⟫*S*ratio + 4*⟪w, b⟫*S + 10*⟪w, b⟫*ratio^2 - 4*⟪w, b⟫*ratio + 2*⟪w, b⟫) * ratio_square
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm v a, real_inner_comm v w, real_inner_comm v b, real_inner_comm a w, real_inner_comm a b, real_inner_comm w b] at hEL hERc hERy hcy hzy hIC ⊢
  have mEL : 0 ≤ (2/5) * (S + 1) ^ 2 := by positivity
  have mERc : 0 ≤ (1/5) * (S + 1) ^ 2 := by positivity
  have mERy : 0 ≤ (47/50) * (S + 1) ^ 2 := by positivity
  have mDcy : 0 ≤ (3/25) * S * (S + 1) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hS) (sq_nonneg _)
  have mDzy : 0 ≤ (21/50) * S * (S + 1) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hS) (sq_nonneg _)
  have mIC : 0 ≤ (36/25) * S * (S + 1) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hS) (sq_nonneg _)
  have hmain : 0 ≤ ((3*S*ecy/25 + 36*S*η/25 + 21*S*ezy/50 + 2*eL/5 + eRc/5 + 47*eRy/50 + 2*r2/5) - (⟪a, a⟫*S^2*ratio^2 - 4*⟪a, a⟫*S^2*ratio + 4*⟪a, a⟫*S^2 + 2*⟪a, a⟫*S*ratio^2 - 6*⟪a, a⟫*S*ratio + 4*⟪a, a⟫*S + ⟪a, a⟫*ratio^2 - 2*⟪a, a⟫*ratio + ⟪a, a⟫ - 2*⟪a, b⟫*S*ratio + 4*⟪a, b⟫*S - 2*⟪a, b⟫*ratio + 2*⟪a, b⟫ + 2*⟪a, w⟫*S*ratio - 4*⟪a, w⟫*S + 2*⟪a, w⟫*ratio - 2*⟪a, w⟫ + ⟪b, b⟫ - 2*⟪v, a⟫*S*ratio + 4*⟪v, a⟫*S - 2*⟪v, a⟫*ratio + 2*⟪v, a⟫ + 2*⟪v, b⟫ + ⟪v, v⟫ - 2*⟪v, w⟫ - 2*⟪w, b⟫ + ⟪w, w⟫)) * (S + 1) ^ 2 := by
    linear_combination mul_le_mul_of_nonneg_left hEL mEL + mul_le_mul_of_nonneg_left hERc mERc + mul_le_mul_of_nonneg_left hERy mERy + mul_le_mul_of_nonneg_left hcy mDcy + mul_le_mul_of_nonneg_left hzy mDzy + mul_le_mul_of_nonneg_left hIC mIC + hpsi + (107*⟪a, a⟫*S^4/50 + 214*⟪a, a⟫*S^3/25 + 321*⟪a, a⟫*S^2/25 + 214*⟪a, a⟫*S/25 + 107*⟪a, a⟫/50) * ratio_square
  have hpos : 0 < (S + 1) ^ 2 := by positivity
  have hX : 0 ≤ (3*S*ecy/25 + 36*S*η/25 + 21*S*ezy/50 + 2*eL/5 + eRc/5 + 47*eRy/50 + 2*r2/5) - (⟪a, a⟫*S^2*ratio^2 - 4*⟪a, a⟫*S^2*ratio + 4*⟪a, a⟫*S^2 + 2*⟪a, a⟫*S*ratio^2 - 6*⟪a, a⟫*S*ratio + 4*⟪a, a⟫*S + ⟪a, a⟫*ratio^2 - 2*⟪a, a⟫*ratio + ⟪a, a⟫ - 2*⟪a, b⟫*S*ratio + 4*⟪a, b⟫*S - 2*⟪a, b⟫*ratio + 2*⟪a, b⟫ + 2*⟪a, w⟫*S*ratio - 4*⟪a, w⟫*S + 2*⟪a, w⟫*ratio - 2*⟪a, w⟫ + ⟪b, b⟫ - 2*⟪v, a⟫*S*ratio + 4*⟪v, a⟫*S - 2*⟪v, a⟫*ratio + 2*⟪v, a⟫ + 2*⟪v, b⟫ + ⟪v, v⟫ - 2*⟪v, w⟫ - 2*⟪w, b⟫ + ⟪w, w⟫) := (mul_nonneg_iff_of_pos_right hpos).mp hmain
  linear_combination hX

set_option maxHeartbeats 8000000 in
lemma scale_decay_three_fifths (v a w b : E) (S r2 Fy Fz η eL eRc eRy ecy ezy : ℝ)
    (hs : ratio ≤ S + 1)
    (hEL : ‖v‖ ^ 2 + S * (S + 1) * ‖a‖ ^ 2 + 2 * S * Fy ≤ r2 + eL)
    (hERc : ‖w‖ ^ 2 + S * (S + 1) * ‖b‖ ^ 2 + 2 * S * Fz ≤ ‖v - (1 + (ratio - 2) * (S + 1)) • a‖ ^ 2 + eRc)
    (hERy : ‖w - (v - a)‖ ^ 2 + S * (S + 1) * ‖b‖ ^ 2 + 2 * S * (Fz - Fy) + S * ‖a‖ ^ 2 ≤
      ((1 + (ratio - 2) * (S + 1)) - 1) ^ 2 * ‖a‖ ^ 2 + eRy)
    (hcy : -ecy ≤ -2 * Fy + 2 * ⟪a, v⟫ - ‖a‖ ^ 2)
    (hzy : -ezy ≤ 2 * (Fz - Fy) - 2 * ⟪a, w - v⟫ - ‖b - a‖ ^ 2)
    (hIC : -(1 / 10) * (ratio * (S + 1) - 1) * ‖b‖ ^ 2 - η ≤ Fz) :
    ‖v - (1 + (ratio - 2) * (S + 1)) • a - (w - b)‖ ^ 2 ≤ 3/5 * r2 + 3/5 * eL + 2/25 * eRc + 34/25 * eRy +
      7/50 * S * ecy + 31/50 * S * ezy + 41/25 * S * η := by
  have hb := ratio_bounds
  have h1 : (1 : ℝ) ≤ ratio := by linarith [hb.1]
  have hS : 0 ≤ S := by linarith only [hs, h1]
  have n1 := gram4_nonneg v a w b (0) (0) (0) (S + 1)
  have d1 : (0:ℝ) ≤ (36/25 - 41*ratio/250) := by linarith only [hb.1, hb.2]
  have n2 := gram4_nonneg v a w b (1) (27*S*ratio/22 - 73*S/22 + 27*ratio/22 - 73/22) (-9/22) (0)
  have d2 : (0:ℝ) ≤ (22/25) := by linarith only [hb.1, hb.2]
  have n3 := gram4_nonneg v a w b (0) (-307*S*ratio/161 + 112*S/23 - 307*ratio/161 + 112/23) (1) (0)
  have d3 : (0:ℝ) ≤ (161/550) := by linarith only [hb.1, hb.2]
  have n4 := gram4_nonneg v a w b (0) (S + 1) (0) (0)
  have d4 : (0:ℝ) ≤ (51133*ratio/4025 - 246493/8050) := by linarith only [hb.1, hb.2]
  have n5 := gram4_nonneg v a w b (-15875*ratio/140671 - 54125/140671) (131965*S*ratio/140671 - 275580*S/140671 + 131965*ratio/140671 - 275580/140671) (15875*ratio/140671 + 54125/140671) (S + 1)
  have d5 : (0:ℝ) ≤ (687*ratio/250 - 1501/250) := by linarith only [hb.1, hb.2]
  have n6 := gram4_nonneg v a w b (1) (-20888907*S*ratio/90628514 + 52342461*S/90628514 - 20888907*ratio/90628514 + 52342461/90628514) (17590625*ratio/90628514 - 55555983/90628514) (0)
  have d6 : (0:ℝ) ≤ (5404137/3516775 - 54125*ratio/140671) := by linarith only [hb.1, hb.2]
  have n7 := gram4_nonneg v a w b (0) (3535809398*S*ratio/3870489241 - 9202687776*S/3870489241 + 3535809398*ratio/3870489241 - 9202687776/3870489241) (1) (0)
  have d7 : (0:ℝ) ≤ (903484807/2265712850 - 9147125*ratio/90628514) := by linarith only [hb.1, hb.2]
  have n8 := gram4_nonneg v a w b (0) (S + 1) (0) (0)
  have d8 : (0:ℝ) ≤ (185322511776*ratio/96762231025 - 441516942271/96762231025) := by linarith only [hb.1, hb.2]
  have n9 := gram4_nonneg v a w b (0) (-405*S/446 - 405/446) (0) (S + 1)
  have d9 : (0:ℝ) ≤ (223/125) := by linarith only [hb.1, hb.2]
  have n10 := gram4_nonneg v a w b (0) (S + 1) (0) (0)
  have d10 : (0:ℝ) ≤ (8227/22300) := by linarith only [hb.1, hb.2]
  have hq0 : 0 ≤ (122*⟪a, a⟫*S^2*ratio/25 - 58*⟪a, a⟫*S^2/5 + 244*⟪a, a⟫*S*ratio/25 - 116*⟪a, a⟫*S/5 + 122*⟪a, a⟫*ratio/25 - 58*⟪a, a⟫/5 - 2*⟪a, w⟫*S*ratio + 131*⟪a, w⟫*S/25 - 2*⟪a, w⟫*ratio + 131*⟪a, w⟫/25 - 41*⟪b, b⟫*S^2*ratio/250 + 36*⟪b, b⟫*S^2/25 - 41*⟪b, b⟫*S*ratio/125 + 72*⟪b, b⟫*S/25 - 41*⟪b, b⟫*ratio/250 + 36*⟪b, b⟫/25 + 54*⟪v, a⟫*S*ratio/25 - 146*⟪v, a⟫*S/25 + 54*⟪v, a⟫*ratio/25 - 146*⟪v, a⟫/25 + 22*⟪v, v⟫/25 - 18*⟪v, w⟫/25 + 11*⟪w, w⟫/25) := by
    linear_combination mul_nonneg d1 n1 + mul_nonneg d2 n2 + mul_nonneg d3 n3 + mul_nonneg d4 n4 + (9619*⟪a, a⟫*S^2/4025 + 19238*⟪a, a⟫*S/4025 + 9619*⟪a, a⟫/4025) * ratio_square
  have hqu : 0 ≤ (-4*⟪a, a⟫*S^2*ratio^2 + 112*⟪a, a⟫*S^2*ratio/5 - 766*⟪a, a⟫*S^2/25 - 8*⟪a, a⟫*S*ratio^2 + 224*⟪a, a⟫*S*ratio/5 - 1532*⟪a, a⟫*S/25 - 4*⟪a, a⟫*ratio^2 + 112*⟪a, a⟫*ratio/5 - 766*⟪a, a⟫/25 + 131*⟪a, b⟫*S^2*ratio^2/25 - 111*⟪a, b⟫*S^2*ratio/5 + 586*⟪a, b⟫*S^2/25 + 262*⟪a, b⟫*S*ratio^2/25 - 222*⟪a, b⟫*S*ratio/5 + 1172*⟪a, b⟫*S/25 + 131*⟪a, b⟫*ratio^2/25 - 111*⟪a, b⟫*ratio/5 + 586*⟪a, b⟫/25 - 63*⟪a, w⟫*S*ratio/25 + 157*⟪a, w⟫*S/25 - 63*⟪a, w⟫*ratio/25 + 157*⟪a, w⟫/25 - 81*⟪b, b⟫*S^2*ratio^2/50 + 1497*⟪b, b⟫*S^2*ratio/250 - 548*⟪b, b⟫*S^2/125 - 81*⟪b, b⟫*S*ratio^2/25 + 1497*⟪b, b⟫*S*ratio/125 - 1096*⟪b, b⟫*S/125 - 81*⟪b, b⟫*ratio^2/50 + 1497*⟪b, b⟫*ratio/250 - 548*⟪b, b⟫/125 + 78*⟪v, a⟫*S*ratio/25 - 194*⟪v, a⟫*S/25 + 78*⟪v, a⟫*ratio/25 - 194*⟪v, a⟫/25 - 2*⟪v, b⟫*S*ratio + 4*⟪v, b⟫*S - 2*⟪v, b⟫*ratio + 4*⟪v, b⟫ + 22*⟪v, v⟫/25 - 18*⟪v, w⟫/25 + 2*⟪w, b⟫*S*ratio - 4*⟪w, b⟫*S + 2*⟪w, b⟫*ratio - 4*⟪w, b⟫ + 11*⟪w, w⟫/25) := by
    linear_combination mul_nonneg d5 n5 + mul_nonneg d6 n6 + mul_nonneg d7 n7 + mul_nonneg d8 n8 + (28167611687622283964911925571646886193354285919*⟪a, a⟫*S^2*ratio/12174204739151434514558152665586597987040650580 - 70630162326954639360720945585734379962199867423*⟪a, a⟫*S^2/12174204739151434514558152665586597987040650580 + 28167611687622283964911925571646886193354285919*⟪a, a⟫*S*ratio/6087102369575717257279076332793298993520325290 - 70630162326954639360720945585734379962199867423*⟪a, a⟫*S/6087102369575717257279076332793298993520325290 + 28167611687622283964911925571646886193354285919*⟪a, a⟫*ratio/12174204739151434514558152665586597987040650580 - 70630162326954639360720945585734379962199867423*⟪a, a⟫/12174204739151434514558152665586597987040650580 - 59182*⟪a, b⟫*S^2/703355 - 118364*⟪a, b⟫*S/703355 - 59182*⟪a, b⟫/703355 + 50082204645917289549780555*⟪a, w⟫*S*ratio/81265997799973845933047618 + 67035147593538122091988438662728855*⟪a, w⟫*S/314539170143928440765252411809677938 + 50082204645917289549780555*⟪a, w⟫*ratio/81265997799973845933047618 + 67035147593538122091988438662728855*⟪a, w⟫/314539170143928440765252411809677938 + 81*⟪b, b⟫*S^2/50 + 81*⟪b, b⟫*S/25 + 81*⟪b, b⟫/50 - 11513814285*⟪v, a⟫*S*ratio/19788330241 - 433811951660653145*⟪v, a⟫*S/896693482141545937 - 11513814285*⟪v, a⟫*ratio/19788330241 - 433811951660653145*⟪v, a⟫/896693482141545937 - 87249*⟪v, b⟫*S/140671 - 87249*⟪v, b⟫/140671 + 1385077875*⟪v, v⟫*ratio/39576660482 + 9188656375*⟪v, v⟫/39576660482 - 1385077875*⟪v, w⟫*ratio/19788330241 - 550308951518860250*⟪v, w⟫/896693482141545937 + 87249*⟪w, b⟫*S/140671 + 87249*⟪w, b⟫/140671 + 3332243308254386274209875*⟪w, w⟫*ratio/162531995599947691866095236 + 57314396157541621142496625*⟪w, w⟫/162531995599947691866095236) * ratio_square
  have hq2 : 0 ≤ (46*⟪a, a⟫*S^2/25 + 92*⟪a, a⟫*S/25 + 46*⟪a, a⟫/25 - 81*⟪a, b⟫*S^2/25 - 162*⟪a, b⟫*S/25 - 81*⟪a, b⟫/25 + 223*⟪b, b⟫*S^2/125 + 446*⟪b, b⟫*S/125 + 223*⟪b, b⟫/125) := by
    linear_combination mul_nonneg d9 n9 + mul_nonneg d10 n10 + (0) * ratio_square
  have hsu : 0 ≤ (S + 1) * ratio := mul_nonneg (by linarith) (by linarith)
  have hss : 0 ≤ (S + 1) * (S + 1 - ratio) := mul_nonneg (by linarith) (by linarith)
  have hus : 0 ≤ (ratio - 2) * (S + 1 - ratio) := mul_nonneg (by linarith [hb.1]) (by linarith)
  have hpsi : 0 ≤ (122*⟪a, a⟫*S^4*ratio/25 - 58*⟪a, a⟫*S^4/5 + 434*⟪a, a⟫*S^3*ratio/25 - 1014*⟪a, a⟫*S^3/25 + 114*⟪a, a⟫*S^2*ratio/5 - 1348*⟪a, a⟫*S^2/25 + 326*⟪a, a⟫*S*ratio/25 - 814*⟪a, a⟫*S/25 + 68*⟪a, a⟫*ratio/25 - 38*⟪a, a⟫/5 + 2*⟪a, b⟫*S^3*ratio - 131*⟪a, b⟫*S^3/25 + 6*⟪a, b⟫*S^2*ratio - 312*⟪a, b⟫*S^2/25 + 6*⟪a, b⟫*S*ratio - 231*⟪a, b⟫*S/25 + 2*⟪a, b⟫*ratio - 2*⟪a, b⟫ - 2*⟪a, w⟫*S^3*ratio + 131*⟪a, w⟫*S^3/25 - 6*⟪a, w⟫*S^2*ratio + 76*⟪a, w⟫*S^2/5 - 6*⟪a, w⟫*S*ratio + 367*⟪a, w⟫*S/25 - 2*⟪a, w⟫*ratio + 118*⟪a, w⟫/25 - 41*⟪b, b⟫*S^4*ratio/250 + 36*⟪b, b⟫*S^4/25 - 123*⟪b, b⟫*S^3*ratio/250 + 638*⟪b, b⟫*S^3/125 - 123*⟪b, b⟫*S^2*ratio/250 + 611*⟪b, b⟫*S^2/125 - 41*⟪b, b⟫*S*ratio/250 + 28*⟪b, b⟫*S/125 - ⟪b, b⟫ + 54*⟪v, a⟫*S^3*ratio/25 - 146*⟪v, a⟫*S^3/25 + 162*⟪v, a⟫*S^2*ratio/25 - 414*⟪v, a⟫*S^2/25 + 162*⟪v, a⟫*S*ratio/25 - 78*⟪v, a⟫*S/5 + 54*⟪v, a⟫*ratio/25 - 122*⟪v, a⟫/25 - 2*⟪v, b⟫*S^2 - 4*⟪v, b⟫*S - 2*⟪v, b⟫ + 22*⟪v, v⟫*S^2/25 + 44*⟪v, v⟫*S/25 + 22*⟪v, v⟫/25 - 18*⟪v, w⟫*S^2/25 - 36*⟪v, w⟫*S/25 - 18*⟪v, w⟫/25 + 2*⟪w, b⟫*S^2 + 4*⟪w, b⟫*S + 2*⟪w, b⟫ + 11*⟪w, w⟫*S^2/25 + 22*⟪w, w⟫*S/25 + 11*⟪w, w⟫/25) := by
    linear_combination mul_nonneg hsu hqu + mul_nonneg hq0 hss + mul_nonneg hq2 hus + (-4*⟪a, a⟫*S^3*ratio + 238*⟪a, a⟫*S^3/25 - 12*⟪a, a⟫*S^2*ratio + 668*⟪a, a⟫*S^2/25 - 12*⟪a, a⟫*S*ratio + 622*⟪a, a⟫*S/25 - 4*⟪a, a⟫*ratio + 192*⟪a, a⟫/25 + 131*⟪a, b⟫*S^3*ratio/25 - 293*⟪a, b⟫*S^3/25 + 393*⟪a, b⟫*S^2*ratio/25 - 798*⟪a, b⟫*S^2/25 + 393*⟪a, b⟫*S*ratio/25 - 717*⟪a, b⟫*S/25 + 131*⟪a, b⟫*ratio/25 - 212*⟪a, b⟫/25 - 13*⟪a, w⟫*S^2/25 - 26*⟪a, w⟫*S/25 - 13*⟪a, w⟫/25 - 81*⟪b, b⟫*S^3*ratio/50 + 364*⟪b, b⟫*S^3/125 - 243*⟪b, b⟫*S^2*ratio/50 + 869*⟪b, b⟫*S^2/125 - 243*⟪b, b⟫*S*ratio/50 + 646*⟪b, b⟫*S/125 - 81*⟪b, b⟫*ratio/50 + 141*⟪b, b⟫/125 + 24*⟪v, a⟫*S^2/25 + 48*⟪v, a⟫*S/25 + 24*⟪v, a⟫/25 - 2*⟪v, b⟫*S^2 - 4*⟪v, b⟫*S - 2*⟪v, b⟫ + 2*⟪w, b⟫*S^2 + 4*⟪w, b⟫*S + 2*⟪w, b⟫) * ratio_square
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm v a, real_inner_comm v w, real_inner_comm v b, real_inner_comm a w, real_inner_comm a b, real_inner_comm w b] at hEL hERc hERy hcy hzy hIC ⊢
  have mEL : 0 ≤ (3/5) * (S + 1) ^ 2 := by positivity
  have mERc : 0 ≤ (2/25) * (S + 1) ^ 2 := by positivity
  have mERy : 0 ≤ (34/25) * (S + 1) ^ 2 := by positivity
  have mDcy : 0 ≤ (7/50) * S * (S + 1) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hS) (sq_nonneg _)
  have mDzy : 0 ≤ (31/50) * S * (S + 1) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hS) (sq_nonneg _)
  have mIC : 0 ≤ (41/25) * S * (S + 1) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hS) (sq_nonneg _)
  have hmain : 0 ≤ ((7*S*ecy/50 + 41*S*η/25 + 31*S*ezy/50 + 3*eL/5 + 2*eRc/25 + 34*eRy/25 + 3*r2/5) - (⟪a, a⟫*S^2*ratio^2 - 4*⟪a, a⟫*S^2*ratio + 4*⟪a, a⟫*S^2 + 2*⟪a, a⟫*S*ratio^2 - 6*⟪a, a⟫*S*ratio + 4*⟪a, a⟫*S + ⟪a, a⟫*ratio^2 - 2*⟪a, a⟫*ratio + ⟪a, a⟫ - 2*⟪a, b⟫*S*ratio + 4*⟪a, b⟫*S - 2*⟪a, b⟫*ratio + 2*⟪a, b⟫ + 2*⟪a, w⟫*S*ratio - 4*⟪a, w⟫*S + 2*⟪a, w⟫*ratio - 2*⟪a, w⟫ + ⟪b, b⟫ - 2*⟪v, a⟫*S*ratio + 4*⟪v, a⟫*S - 2*⟪v, a⟫*ratio + 2*⟪v, a⟫ + 2*⟪v, b⟫ + ⟪v, v⟫ - 2*⟪v, w⟫ - 2*⟪w, b⟫ + ⟪w, w⟫)) * (S + 1) ^ 2 := by
    linear_combination mul_le_mul_of_nonneg_left hEL mEL + mul_le_mul_of_nonneg_left hERc mERc + mul_le_mul_of_nonneg_left hERy mERy + mul_le_mul_of_nonneg_left hcy mDcy + mul_le_mul_of_nonneg_left hzy mDzy + mul_le_mul_of_nonneg_left hIC mIC + hpsi + (61*⟪a, a⟫*S^4/25 + 244*⟪a, a⟫*S^3/25 + 366*⟪a, a⟫*S^2/25 + 244*⟪a, a⟫*S/25 + 61*⟪a, a⟫/25) * ratio_square
  have hpos : 0 < (S + 1) ^ 2 := by positivity
  have hX : 0 ≤ (7*S*ecy/50 + 41*S*η/25 + 31*S*ezy/50 + 3*eL/5 + 2*eRc/25 + 34*eRy/25 + 3*r2/5) - (⟪a, a⟫*S^2*ratio^2 - 4*⟪a, a⟫*S^2*ratio + 4*⟪a, a⟫*S^2 + 2*⟪a, a⟫*S*ratio^2 - 6*⟪a, a⟫*S*ratio + 4*⟪a, a⟫*S + ⟪a, a⟫*ratio^2 - 2*⟪a, a⟫*ratio + ⟪a, a⟫ - 2*⟪a, b⟫*S*ratio + 4*⟪a, b⟫*S - 2*⟪a, b⟫*ratio + 2*⟪a, b⟫ + 2*⟪a, w⟫*S*ratio - 4*⟪a, w⟫*S + 2*⟪a, w⟫*ratio - 2*⟪a, w⟫ + ⟪b, b⟫ - 2*⟪v, a⟫*S*ratio + 4*⟪v, a⟫*S - 2*⟪v, a⟫*ratio + 2*⟪v, a⟫ + 2*⟪v, b⟫ + ⟪v, v⟫ - 2*⟪v, w⟫ - 2*⟪w, b⟫ + ⟪w, w⟫) := (mul_nonneg_iff_of_pos_right hpos).mp hmain
  linear_combination hX

end LongTails.Proofs.WeaklyConvexSilverCertificate
