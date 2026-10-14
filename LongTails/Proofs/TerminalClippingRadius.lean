import LongTails.Proofs.TerminalClippingPath
import LongTails.Proofs.TerminalClippingStopping
import LongTails.Proofs.TerminalClippingConcentration

open MeasureTheory
open scoped RealInnerProductSpace
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma local_moment_bound {B G D : ℝ} (hD : 0 ≤ D) (hG : G ^ 2 ≤ B ^ 2 * D)
    {x : E} (hx : ‖x‖ ≤ 5 * Real.sqrt D) :
    B ^ 2 * ‖x‖ ^ 2 + G ^ 2 ≤ 26 * B ^ 2 * D := by
  have hs := pow_le_pow_left₀ (norm_nonneg x) hx 2
  rw [mul_pow, Real.sq_sqrt hD] at hs
  have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg B)
  nlinarith

omit [InnerProductSpace ℝ E] in
lemma local_mean_scale {B G D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hG : G ^ 2 ≤ B ^ 2 * D) {x : E} (hx : ‖x‖ ≤ 5 * Real.sqrt D) :
    Real.sqrt (B ^ 2 * ‖x‖ ^ 2 + G ^ 2) ≤ 6 * B * Real.sqrt D := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow, Real.sq_sqrt hD]
  have h := local_moment_bound hD hG hx
  nlinarith [mul_nonneg (sq_nonneg B) hD]

lemma auxiliary_influence_norm {a D : ℝ} (ha : 0 ≤ a) {x p : E}
    (hx : ‖x‖ ≤ 5 * Real.sqrt D) (hp : ‖p‖ ≤ 5 * Real.sqrt D) :
    ‖a • (x - p)‖ ≤ 10 * a * Real.sqrt D := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hs : ‖x - p‖ ≤ 10 * Real.sqrt D := by linarith [norm_sub_le x p]
  exact (mul_le_mul_of_nonneg_left hs ha).trans_eq (by ring)

lemma radius_bias_drift {η e a B D T : ℝ} (he : η ≤ e)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hT : 0 < T) (hea : η * a ≤ 4 * e / T) :
    2 * η * (4 * Real.sqrt D) *
      (6 * B * Real.sqrt D / Real.sqrt T + B * Real.sqrt T * (10 * a * Real.sqrt D)) ≤
      48 * e * B * D / Real.sqrt T + 320 * e * B * Real.sqrt T * D / T := by
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h1 := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 48 * B * D / Real.sqrt T by positivity)
  have h2 := mul_le_mul_of_nonneg_right hea
    (show 0 ≤ 80 * B * Real.sqrt T * D by positivity)
  have hs := Real.sq_sqrt hD
  have heq : 2 * η * (4 * Real.sqrt D) *
      (6 * B * Real.sqrt D / Real.sqrt T + B * Real.sqrt T * (10 * a * Real.sqrt D)) =
      η * (48 * B * D / Real.sqrt T) + (η * a) * (80 * B * Real.sqrt T * D) := by
    field_simp
    ring_nf
    simp only [Real.sq_sqrt hD]; ring
  rw [heq]
  convert add_le_add h1 h2 using 1; ring

lemma radius_energy_mean_bound {η e a b B D T : ℝ}
    (hη : 0 ≤ η) (he : η ≤ e) (hB : 0 ≤ B) (hD : 0 ≤ D) (hT : 0 < T)
    (hea : η * a ≤ 4 * e / T)
    (hb : b ≤ (4 * Real.sqrt D) *
      (6 * B * Real.sqrt D / Real.sqrt T + B * Real.sqrt T * (10 * a * Real.sqrt D))) :
    2 * η * b + η ^ 2 * (26 * B ^ 2 * D) ≤
      400 * e * B * D / Real.sqrt T + 26 * e ^ 2 * B ^ 2 * D := by
  have he0 : 0 ≤ e := hη.trans he
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h1 := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * η by positivity)
  have h2 := radius_bias_drift he hB hD hT hea
  have heq : 320 * e * B * Real.sqrt T * D / T = 320 * e * B * D / Real.sqrt T := by
    apply (div_eq_div_iff (ne_of_gt hT) (ne_of_gt hs)).mpr
    calc
      _ = 320 * e * B * D * (Real.sqrt T) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hT.le]
  rw [heq] at h2
  have h3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hη he 2)
    (show 0 ≤ 26 * B ^ 2 * D by positivity)
  have hn : 0 ≤ e * B * D / Real.sqrt T := by positivity
  have h12 : 2 * η * b ≤ 368 * e * B * D / Real.sqrt T := by
    have hh := h1.trans (by convert h2 using 1; ring)
    convert hh using 1; ring
  have hsum := add_le_add h12 h3
  have hextra : 368 * e * B * D / Real.sqrt T ≤ 400 * e * B * D / Real.sqrt T := by
    have hh := mul_le_mul_of_nonneg_right (show (368 : ℝ) ≤ 400 by norm_num) hn
    convert hh using 1 <;> ring
  exact hsum.trans (by nlinarith)

lemma radius_energy_second_bound {η e C B D T d : ℝ}
    (hη : 0 ≤ η) (he : η ≤ e) (hD : 0 ≤ D)
    (hd : d ^ 2 ≤ 16 * D) (hC : C ^ 2 ≤ 26 * B ^ 2 * D * T) :
    (8 * η ^ 2 * d ^ 2 + 2 * η ^ 4 * C ^ 2) * (26 * B ^ 2 * D) ≤
      3328 * e ^ 2 * B ^ 2 * D ^ 2 + 1352 * e ^ 4 * B ^ 4 * D ^ 2 * T := by
  have he0 : 0 ≤ e := hη.trans he
  have he2 := pow_le_pow_left₀ hη he 2
  have he4 := pow_le_pow_left₀ hη he 4
  have h1 := mul_le_mul he2 hd (sq_nonneg d) (sq_nonneg e)
  have h2 := mul_le_mul he4 hC (sq_nonneg C) (by positivity : 0 ≤ e ^ 4)
  have hh : 8 * η ^ 2 * d ^ 2 + 2 * η ^ 4 * C ^ 2 ≤
      128 * e ^ 2 * D + 52 * e ^ 4 * B ^ 2 * D * T := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ 26 * B ^ 2 * D by positivity)
  convert hh' using 1; ring

lemma radius_energy_jump_bound {η e C B D T d : ℝ}
    (hη : 0 ≤ η) (he : η ≤ e) (hC0 : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
     (hd0 : 0 ≤ d) (hd : d ≤ 4 * Real.sqrt D)
    (hC : C ≤ 6 * B * Real.sqrt D * Real.sqrt T)
    (hC2 : C ^ 2 ≤ 26 * B ^ 2 * D * T) :
    2 * η * C * d + η ^ 2 * C ^ 2 ≤
      48 * e * B * D * Real.sqrt T + 26 * e ^ 2 * B ^ 2 * D * T := by
  have he0 : 0 ≤ e := hη.trans he
  have hp := mul_le_mul hC hd hd0 (by positivity : 0 ≤ 6 * B * Real.sqrt D * Real.sqrt T)
  have hp' : C * d ≤ 24 * B * D * Real.sqrt T := by
    convert hp using 1; ring_nf; rw [Real.sq_sqrt hD]; ring
  have h1 := mul_le_mul he hp' (mul_nonneg hC0 hd0) he0
  have h2 := mul_le_mul (pow_le_pow_left₀ hη he 2) hC2 (sq_nonneg C) (sq_nonneg e)
  nlinarith

lemma radius_normalized_jump {B D T q : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hT : 1 ≤ T) (hq : 1 ≤ q) :
    let e := 1 / (4096 * B * Real.sqrt T * q)
    let τ := 4096 * q / (100 * D)
    τ * (48 * e * B * D * Real.sqrt T + 26 * e ^ 2 * B ^ 2 * D * T) ≤ 1 := by
  dsimp only
  have ht : 0 < T := by linarith
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hqp : 0 < q := by linarith
  have he : 4096 * q / (100 * D) *
      (48 * (1 / (4096 * B * Real.sqrt T * q)) * B * D * Real.sqrt T +
        26 * (1 / (4096 * B * Real.sqrt T * q)) ^ 2 * B ^ 2 * D * T) =
        48 / 100 + 26 / (409600 * q) := by
    have hs4 : (Real.sqrt T) ^ 4 = T ^ 2 := by
      calc
        _ = ((Real.sqrt T) ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt ht.le]
    field_simp
    ring_nf
    simp only [Real.sq_sqrt ht.le]

  rw [he]
  have hh : 26 / (409600 * q) ≤ (26 : ℝ) / 409600 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  linarith

lemma radius_normalized_compensator {B D T q : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hT : 1 ≤ T) (hq : 1 ≤ q) :
    let e := 1 / (4096 * B * Real.sqrt T * q)
    let τ := 4096 * q / (100 * D)
    τ * (400 * e * B * D / Real.sqrt T + 26 * e ^ 2 * B ^ 2 * D) +
      τ ^ 2 * (3328 * e ^ 2 * B ^ 2 * D ^ 2 + 1352 * e ^ 4 * B ^ 4 * D ^ 2 * T) ≤
      8 * q / T := by
  dsimp only
  have ht : 0 < T := by linarith
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hqp : 0 < q := by linarith
  have he : 4096 * q / (100 * D) *
      (400 * (1 / (4096 * B * Real.sqrt T * q)) * B * D / Real.sqrt T +
        26 * (1 / (4096 * B * Real.sqrt T * q)) ^ 2 * B ^ 2 * D) +
      (4096 * q / (100 * D)) ^ 2 *
        (3328 * (1 / (4096 * B * Real.sqrt T * q)) ^ 2 * B ^ 2 * D ^ 2 +
          1352 * (1 / (4096 * B * Real.sqrt T * q)) ^ 4 * B ^ 4 * D ^ 2 * T) =
      (4 + 26 / (409600 * q) + 3328 / 10000 + 1352 / (167772160000 * q ^ 2)) / T := by
    have hs4 : (Real.sqrt T) ^ 4 = T ^ 2 := by
      calc
        _ = ((Real.sqrt T) ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt ht.le]
    field_simp
    ring_nf
    simp only [Real.sq_sqrt ht.le, hs4]; ring
  rw [he]
  apply div_le_div_of_nonneg_right _ ht.le
  have h1 : 26 / (409600 * q) ≤ (26 : ℝ) / 409600 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have h2 : 1352 / (167772160000 * q ^ 2) ≤ (1352 : ℝ) / 167772160000 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  linarith

lemma biased_subgradient_inward {f : E → ℝ} {x u h m : E} {b : ℝ}
    (hmin : f u ≤ f x) (hsub : f x - f u ≤ ⟪h, x - u⟫)
    (hb : ‖h - m‖ ≤ b) : -⟪x - u, m⟫ ≤ ‖x - u‖ * b := by
  have hh : 0 ≤ ⟪x - u, h⟫ := by rw [real_inner_comm]; linarith
  have hi := (real_inner_le_norm (x - u) (h - m)).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  rw [inner_sub_right] at hi
  linarith

lemma threshold_projected_mgf {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (hgi : Integrable g P)
    (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    {projection : E → E} (hp : Measurable projection) {f : E → ℝ}
    (x u x0 U : E) (hmin : f u ≤ f x)
    (hsub : f x - f u ≤ ⟪∫ ω, g ω ∂P, x - u⟫)
    (hproj : ∀ y, ‖projection y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2)
    {B G η τ : ℝ} {T : ℕ} (hB : 0 < B) (hG : 0 < G) (hT : 0 < T)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ B ^ 2 * ‖x - x0‖ ^ 2 + G ^ 2)
    (hsmall : τ * (2 * η * threshold B G T (x - x0) U * ‖x - u‖ +
      η ^ 2 * (threshold B G T (x - x0) U) ^ 2) ≤ 1) :
    let C := threshold B G T (x - x0) U
    let M := B ^ 2 * ‖x - x0‖ ^ 2 + G ^ 2
    let b := ‖x - u‖ * (Real.sqrt M / Real.sqrt T + B * Real.sqrt T * ‖U‖)
    Integrable (fun ω => Real.exp (τ * ‖projection (x - η • clip C (g ω)) - u‖ ^ 2)) P ∧
    (∫ ω, Real.exp (τ * ‖projection (x - η • clip C (g ω)) - u‖ ^ 2) ∂P) ≤
      Real.exp (τ * ‖x - u‖ ^ 2 + τ * (2 * η * b + η ^ 2 * M) +
        τ ^ 2 * (8 * η ^ 2 * ‖x - u‖ ^ 2 + 2 * η ^ 4 * C ^ 2) * M) := by
  dsimp only
  have hC := threshold_pos hB hG hT (x - x0) U
  have hi := integrable_clip (P := P) hg hC.le
  have hs := full_moment_clip_second hg hmi hC.le
  apply projected_energy_mgf ((measurable_clip _).comp hg) hi hs.1 hp x u hproj hη hτ
  · exact fun ω => norm_clip_le hC.le (g ω)
  · exact biased_subgradient_inward hmin hsub (threshold_oracle_bias hg hgi hmi hB hG hT (x - x0) U hm)
  · exact hs.2.trans hm
  · exact hsmall

lemma radius_local_mgf {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → E}
    (hg : Measurable g) (hgi : Integrable g P)
    (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    {projection : E → E} (hp : Measurable projection) {f : E → ℝ}
    (x u x0 U : E) (hmin : f u ≤ f x)
    (hsub : f x - f u ≤ ⟪∫ ω, g ω ∂P, x - u⟫)
    (hproj : ∀ y, ‖projection y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2)
    {B G η a D q : ℝ} {T : ℕ} (hB : 0 < B) (hG : 0 < G) (hT : 0 < T)
    (hD : 0 < D) (hq : 1 ≤ q) (hη : 0 ≤ η)
    (he : η ≤ 1 / (4096 * B * Real.sqrt T * q))
    (hea : η * a ≤ 4 * (1 / (4096 * B * Real.sqrt T * q)) / T)
    (hGD : G ^ 2 ≤ B ^ 2 * D)
    (hx : ‖x - x0‖ ≤ 5 * Real.sqrt D) (hd : ‖x - u‖ ^ 2 ≤ 16 * D)
    (hU : ‖U‖ ≤ 10 * a * Real.sqrt D)
    (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ B ^ 2 * ‖x - x0‖ ^ 2 + G ^ 2) :
    let τ := 4096 * q / (100 * D)
    let C := threshold B G T (x - x0) U
    Integrable (fun ω => Real.exp (τ * ‖projection (x - η • clip C (g ω)) - u‖ ^ 2)) P ∧
    (∫ ω, Real.exp (τ * ‖projection (x - η • clip C (g ω)) - u‖ ^ 2) ∂P) ≤
      Real.exp (τ * ‖x - u‖ ^ 2 + 8 * q / T) := by
  let e := 1 / (4096 * B * Real.sqrt T * q)
  let τ := 4096 * q / (100 * D)
  let C := threshold B G T (x - x0) U
  let M := B ^ 2 * ‖x - x0‖ ^ 2 + G ^ 2
  let b := ‖x - u‖ * (Real.sqrt M / Real.sqrt T + B * Real.sqrt T * ‖U‖)
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have ht1 : 1 ≤ (T : ℝ) := by exact_mod_cast hT
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hC : 0 ≤ C := (threshold_pos hB hG hT _ _).le
  have hM : M ≤ 26 * B ^ 2 * D := local_moment_bound hD.le hGD hx
  have hs : Real.sqrt M ≤ 6 * B * Real.sqrt D := local_mean_scale hB.le hD.le hGD hx
  have hc1 : C ≤ 6 * B * Real.sqrt D * Real.sqrt T :=
    (threshold_size (x - x0) U).trans (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))
  have hc2 : C ^ 2 ≤ 26 * B ^ 2 * D * T :=
    (threshold_square hB hG hT (x - x0) U).trans
      (mul_le_mul_of_nonneg_right hM ht.le)
  have hd1 : ‖x - u‖ ≤ 4 * Real.sqrt D := by
    nlinarith [Real.sq_sqrt hD.le, Real.sqrt_nonneg D, norm_nonneg (x - u)]
  have hb : b ≤ (4 * Real.sqrt D) *
      (6 * B * Real.sqrt D / Real.sqrt T + B * Real.sqrt T * (10 * a * Real.sqrt D)) := by
    dsimp [b]
    apply mul_le_mul hd1
    · exact add_le_add (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left hU (by positivity))
    · positivity
    · positivity
  have hj := radius_energy_jump_bound hη he hC hB.le hD.le (norm_nonneg _) hd1 hc1 hc2
  have hsmall : τ * (2 * η * C * ‖x - u‖ + η ^ 2 * C ^ 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hj hτ).trans (radius_normalized_jump hB hD ht1 hq)
  have hh := threshold_projected_mgf hg hgi hmi hp x u x0 U hmin hsub hproj
    hB hG hT hη hτ hm hsmall
  refine ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr ?_)⟩
  have hmean := radius_energy_mean_bound hη he hB.le hD.le ht hea hb
  have hmean' : 2 * η * b + η ^ 2 * M ≤
      400 * e * B * D / Real.sqrt T + 26 * e ^ 2 * B ^ 2 * D :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hM (sq_nonneg η))).trans hmean
  have hsecond := radius_energy_second_bound hη he hD.le hd hc2
  have hsecond' : (8 * η ^ 2 * ‖x - u‖ ^ 2 + 2 * η ^ 4 * C ^ 2) * M ≤
      3328 * e ^ 2 * B ^ 2 * D ^ 2 + 1352 * e ^ 4 * B ^ 4 * D ^ 2 * T :=
    (mul_le_mul_of_nonneg_left hM (by positivity)).trans hsecond
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hmean' hτ)
    (mul_le_mul_of_nonneg_left hsecond' (sq_nonneg τ))
  have htotal := hsum.trans (radius_normalized_compensator hB hD ht1 hq)
  change τ * ‖x - u‖ ^ 2 + τ * (2 * η * b + η ^ 2 * M) +
    τ ^ 2 * (8 * η ^ 2 * ‖x - u‖ ^ 2 + 2 * η ^ 4 * C ^ 2) * M ≤ _
  linarith

def radiusInvariant (q : Public) (X : Set (Vector q.d)) (D : ℝ)
    (s : ℕ × (Vector q.d × Vector q.d)) : Prop :=
  s.2.1 ∈ X ∧ ‖s.2.2‖ ≤ 5 * Real.sqrt D

def radiusGood (q : Public) (X : Set (Vector q.d)) (u : Vector q.d) (D : ℝ)
    (s : ℕ × (Vector q.d × Vector q.d)) : Prop :=
  radiusInvariant q X D s ∧ ‖s.2.1 - u‖ ^ 2 ≤ 16 * D

lemma radiusGood_measurable (q : Public) {X : Set (Vector q.d)} (hX : MeasurableSet X)
    (u : Vector q.d) (D : ℝ) : MeasurableSet {s | radiusGood q X u D s} := by
  apply MeasurableSet.inter
  · exact (hX.preimage measurable_snd.fst).inter
      (measurableSet_le (measurable_snd.snd.norm) measurable_const)
  · exact measurableSet_le ((measurable_snd.fst.sub_const u).norm.pow_const 2) measurable_const

lemma radiusInvariant_initial (q : Public) {X : Set (Vector q.d)} (hx : q.x0 ∈ X)
    (D : ℝ) : radiusInvariant q X D (0, q.x0, 0) := by
  exact ⟨hx, by simp only [norm_zero]; positivity⟩

lemma radiusInvariant_transition {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    {X : Set (Vector q.d)} (hp : ∀ x, projection x ∈ X)
    {u : Vector q.d} {D : ℝ} (hD : 0 ≤ D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D)
    (s : ℕ × (Vector q.d × Vector q.d)) (hs : radiusGood q X u D s) (ω : Ω) :
    radiusInvariant q X D (transition q g projection s ω) := by
  have hr : ‖q.x0 - u‖ ≤ Real.sqrt D := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg D)).mp
    rwa [Real.sq_sqrt hD]
  have hx := radius_geometry hD (Real.sqrt_nonneg D) (Real.sq_sqrt hD).le hr hs.2
  refine ⟨hp _, ?_⟩
  change ‖nextAuxiliary q.B q.δ q.T s.1 (s.2.1 - q.x0) s.2.2‖ ≤ 5 * Real.sqrt D
  by_cases ht : s.1 < q.T
  · exact nextAuxiliary_norm hB hδ hδ1 ht hx hs.1.2
  · rw [nextAuxiliary_after q.B q.δ (by omega : q.T ≤ s.1)]
    exact hx

lemma radius_transition_mgf {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure Ω) (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hB : 0 < q.B) (hG : 0 < q.G) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} {f : Vector q.d → ℝ} {u : Vector q.d}
    (hmin : ∀ x ∈ X, f u ≤ f x)
    (hsub : ∀ x ∈ X, f x - f u ≤ ⟪∫ ω, g x ω ∂(P : Measure Ω), x - u⟫)
    (hgi : ∀ x ∈ X, Integrable (g x) (P : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (P : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(P : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    (hproj : ∀ y, ‖projection y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2)
    {D : ℝ} (hD : 0 < D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D)
    (s : ℕ × (Vector q.d × Vector q.d)) (hs : radiusGood q X u D s) :
    let τ := 4096 * Real.log (8 / q.δ) / (100 * D)
    Integrable (fun ω => Real.exp (τ * ‖(transition q g projection s ω).2.1 - u‖ ^ 2)) (P : Measure Ω) ∧
    (∫ ω, Real.exp (τ * ‖(transition q g projection s ω).2.1 - u‖ ^ 2) ∂(P : Measure Ω)) ≤
      Real.exp (τ * ‖s.2.1 - u‖ ^ 2 + 8 * Real.log (8 / q.δ) / q.T) := by
  have hpoint (ω : Ω) : (transition q g projection s ω).2.1 =
      projection (s.2.1 - stepSize q.B q.δ q.T s.1 •
        clip (threshold q.B q.G q.T (s.2.1 - q.x0)
          (influenceScale q.B q.δ q.T s.1 • ((s.2.1 - q.x0) - s.2.2))) (g s.2.1 ω)) := by
    dsimp [transition, nextPoint]
    congr 1
    module
  simp_rw [hpoint]
  by_cases ht : s.1 < q.T
  · have hr : ‖q.x0 - u‖ ≤ Real.sqrt D := by
      nlinarith [Real.sq_sqrt hD.le, Real.sqrt_nonneg D, norm_nonneg (q.x0 - u)]
    have hx := radius_geometry hD.le (Real.sqrt_nonneg D) (Real.sq_sqrt hD.le).le hr hs.2
    apply radius_local_mgf (hg.comp (measurable_const.prodMk measurable_id))
      (hgi _ hs.1.1) (hmi _ hs.1.1) hp _ _ _ _ (hmin _ hs.1.1) (hsub _ hs.1.1)
      hproj hB hG hT hD (confidence_ge_one hδ hδ1)
      (stepSize_pos hB hδ hδ1 ht).le (stepSize_le_base hB hδ hδ1 hT)
    · convert step_influenceScale_bound hB hδ hδ1 ht using 1; ring
    · exact hGD
    · exact hx
    · exact hs.2
    · exact auxiliary_influence_norm (influenceScale_nonneg hB hδ hδ1 ht) hx hs.1.2
    · exact hm _ hs.1.1
  · rw [stepSize_after q.B q.δ (by omega : q.T ≤ s.1)]
    simp only [zero_smul, sub_zero]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    apply Real.exp_le_exp.mpr
    have hc : 0 ≤ 8 * Real.log (8 / q.δ) / q.T := by
      have hh := confidence_pos hδ hδ1
      positivity
    have hh := mul_le_mul_of_nonneg_left (hproj s.2.1)
      (show 0 ≤ 4096 * Real.log (8 / q.δ) / (100 * D) by
        have hh := confidence_pos hδ hδ1
        positivity)
    linarith

lemma stopped_radius_invariant {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    {X : Set (Vector q.d)} (hx0 : q.x0 ∈ X) (hp : ∀ x, projection x ∈ X)
    {u : Vector q.d} {D : ℝ} (hD : 0 ≤ D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D)
    (n : ℕ) (ξ : Fin n → Ω) :
    radiusInvariant q X D (iterateSamples
      (stopUnless (radiusGood q X u D) (transition q g projection)) n (0, q.x0, 0) ξ) := by
  apply stopped_invariant (radiusGood q X u D) (radiusInvariant q X D) (transition q g projection)
  · intro s _ hs ω
    exact radiusInvariant_transition q g projection hB hδ hδ1 hp hD hstart s hs ω
  · exact radiusInvariant_initial q hx0 D

lemma stopped_radius_coupling {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    {X : Set (Vector q.d)} (hx0 : q.x0 ∈ X) (hp : ∀ x, projection x ∈ X)
    {u : Vector q.d} {D : ℝ} (hD : 0 ≤ D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D)
    (n : ℕ) (ξ : Fin n → Ω)
    (hfinal : ‖(iterateSamples
      (stopUnless (radiusGood q X u D) (transition q g projection)) n (0, q.x0, 0) ξ).2.1 - u‖ ^ 2 ≤ 16 * D) :
    ∀ k (hk : k ≤ n), ‖(iterateSamples (transition q g projection) k (0, q.x0, 0)
      (fun i => ξ (Fin.castLE hk i))).2.1 - u‖ ^ 2 ≤ 16 * D := by
  have hi := stopped_radius_invariant q g projection hB hδ hδ1 hx0 hp hD hstart n ξ
  have hg : radiusGood q X u D (iterateSamples
      (stopUnless (radiusGood q X u D) (transition q g projection)) n (0, q.x0, 0) ξ) := ⟨hi, hfinal⟩
  intro k hk
  have hpre := stopped_prefix_good (radiusGood q X u D) (transition q g projection) n
    (0, q.x0, 0) ξ hg k hk
  have he := (stopped_compare (radiusGood q X u D) (transition q g projection) k
    (0, q.x0, 0) (fun i => ξ (Fin.castLE hk i))).resolve_right (fun hn => hn hpre)
  rw [he]
  exact hpre.2

lemma stopped_radius_tail {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure Ω) (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} (hX : MeasurableSet X) (u : Vector q.d)
    {D : ℝ} (hD : 0 < D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D)
    (hstep : ∀ s, radiusGood q X u D s →
      Integrable (fun ω => Real.exp (4096 * Real.log (8 / q.δ) / (100 * D) *
        ‖(transition q g projection s ω).2.1 - u‖ ^ 2)) (P : Measure Ω) ∧
      (∫ ω, Real.exp (4096 * Real.log (8 / q.δ) / (100 * D) *
        ‖(transition q g projection s ω).2.1 - u‖ ^ 2) ∂(P : Measure Ω)) ≤
      Real.exp (4096 * Real.log (8 / q.δ) / (100 * D) * ‖s.2.1 - u‖ ^ 2 +
        8 * Real.log (8 / q.δ) / q.T)) :
    (Measure.pi fun _ : Fin q.T => (P : Measure Ω)) {ξ | 16 * D <
      ‖(iterateSamples (stopUnless (radiusGood q X u D) (transition q g projection))
        q.T (0, q.x0, 0) ξ).2.1 - u‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-Real.log (8 / q.δ))) := by
  let τ := 4096 * Real.log (8 / q.δ) / (100 * D)
  let V := fun s : ℕ × (Vector q.d × Vector q.d) => τ * ‖s.2.1 - u‖ ^ 2
  have hq := confidence_pos hδ hδ1
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have ht : (q.T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hT)
  have hv : Measurable V := by dsimp [V]; fun_prop
  have hh := stopped_exponential_tail (radiusGood_measurable q hX u D)
    (transition_measurable q hg hp) hv P
    (show 0 ≤ 8 * Real.log (8 / q.δ) / q.T by positivity)
    hstep q.T (0, q.x0, 0) (τ * (16 * D))
  have hevent : {ξ : Fin q.T → Ω | 16 * D <
      ‖(iterateSamples (stopUnless (radiusGood q X u D) (transition q g projection))
        q.T (0, q.x0, 0) ξ).2.1 - u‖ ^ 2} =
      {ξ | τ * (16 * D) < V (iterateSamples
        (stopUnless (radiusGood q X u D) (transition q g projection)) q.T (0, q.x0, 0) ξ)} := by
    ext ξ
    exact (mul_lt_mul_iff_of_pos_left hτ).symm
  rw [hevent]
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hinit := mul_le_mul_of_nonneg_left hstart hτ.le
  change τ * ‖q.x0 - u‖ ^ 2 + q.T * (8 * Real.log (8 / q.δ) / q.T) - τ * (16 * D) ≤ _
  have hc : (q.T : ℝ) * (8 * Real.log (8 / q.δ) / q.T) = 8 * Real.log (8 / q.δ) := by field_simp
  rw [hc]
  have he : τ * D = 4096 * Real.log (8 / q.δ) / 100 := by dsimp [τ]; field_simp
  nlinarith

lemma radius_prefix_tail {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure Ω) (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} (hX : MeasurableSet X) (hx0 : q.x0 ∈ X)
    (hpX : ∀ x, projection x ∈ X) (u : Vector q.d)
    {D : ℝ} (hD : 0 < D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D)
    (hstep : ∀ s, radiusGood q X u D s →
      Integrable (fun ω => Real.exp (4096 * Real.log (8 / q.δ) / (100 * D) *
        ‖(transition q g projection s ω).2.1 - u‖ ^ 2)) (P : Measure Ω) ∧
      (∫ ω, Real.exp (4096 * Real.log (8 / q.δ) / (100 * D) *
        ‖(transition q g projection s ω).2.1 - u‖ ^ 2) ∂(P : Measure Ω)) ≤
      Real.exp (4096 * Real.log (8 / q.δ) / (100 * D) * ‖s.2.1 - u‖ ^ 2 +
        8 * Real.log (8 / q.δ) / q.T)) :
    (Measure.pi fun _ : Fin q.T => (P : Measure Ω))
      {ξ | ∃ (k : ℕ) (hk : k ≤ q.T), 16 * D <
        ‖(iterateSamples (transition q g projection) k (0, q.x0, 0)
          (fun i => ξ (Fin.castLE hk i))).2.1 - u‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-Real.log (8 / q.δ))) := by
  apply (measure_mono ?_).trans (stopped_radius_tail q g projection P hg hp hδ hδ1 hT hX u hD hstart hstep)
  intro ξ hξ
  rcases hξ with ⟨k, hk, hbad⟩
  change 16 * D < ‖(iterateSamples (stopUnless (radiusGood q X u D)
    (transition q g projection)) q.T (0, q.x0, 0) ξ).2.1 - u‖ ^ 2
  by_contra hh
  have hfinal := le_of_not_gt hh
  exact (not_lt_of_ge (stopped_radius_coupling q g projection hB hδ hδ1 hx0 hpX
    hD.le hstart q.T ξ hfinal k hk)) hbad

end OracleTemplate.TerminalClipping
