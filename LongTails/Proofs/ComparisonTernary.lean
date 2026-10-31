import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.ComparisonOrth

noncomputable def trisectLeft (l u : ℝ) : ℝ := l + (u - l) / 3

noncomputable def trisectRight (l u : ℝ) : ℝ := u - (u - l) / 3

noncomputable def ternaryStep (keepLeft : Bool) (l u : ℝ) : ℝ × ℝ :=
  if keepLeft then (l, trisectRight l u) else (trisectLeft l u, u)

lemma ternaryStep_width (b : Bool) (l u : ℝ) :
    (ternaryStep b l u).2 - (ternaryStep b l u).1 = 2 / 3 * (u - l) := by
  cases b <;> simp [ternaryStep, trisectLeft, trisectRight] <;> ring

lemma ternaryStep_sub (b : Bool) {l u : ℝ} (h : l ≤ u) :
    l ≤ (ternaryStep b l u).1 ∧ (ternaryStep b l u).1 ≤ (ternaryStep b l u).2 ∧
      (ternaryStep b l u).2 ≤ u := by
  cases b <;> simp only [ternaryStep, trisectLeft, trisectRight, Bool.false_eq_true,
    ↓reduceIte] <;> exact ⟨by linarith, by linarith, by linarith⟩

lemma ternaryStep_keep {φ ψ : ℝ → ℝ} {s : Set ℝ} (hφ : ConvexOn ℝ s φ)
    {e l u y : ℝ} (he : 0 ≤ e) (hlu : l ≤ u) (hls : Set.Icc l u ⊆ s)
    (hψ : ∀ t ∈ Set.Icc l u, φ t ≤ ψ t ∧ ψ t ≤ φ t + e)
    (hy : y ∈ Set.Icc l u) :
    ∃ y' ∈ Set.Icc (ternaryStep (decide (ψ (trisectLeft l u) ≤ ψ (trisectRight l u))) l u).1
        (ternaryStep (decide (ψ (trisectLeft l u) ≤ ψ (trisectRight l u))) l u).2,
      φ y' ≤ φ y + e := by
  set m1 := trisectLeft l u with hm1
  set m2 := trisectRight l u with hm2
  have hm1m2 : m1 ≤ m2 := by simp only [hm1, hm2, trisectLeft, trisectRight]; linarith
  have hlm1 : l ≤ m1 := by simp only [hm1, trisectLeft]; linarith
  have hm2u : m2 ≤ u := by simp only [hm2, trisectRight]; linarith
  have hgap1 : m1 - l = m2 - m1 := by simp only [hm1, hm2, trisectLeft, trisectRight]; ring
  have hgap2 : u - m2 = m2 - m1 := by simp only [hm1, hm2, trisectLeft, trisectRight]; ring
  have hm1I : m1 ∈ Set.Icc l u := ⟨hlm1, hm1m2.trans hm2u⟩
  have hm2I : m2 ∈ Set.Icc l u := ⟨hlm1.trans hm1m2, hm2u⟩
  by_cases hcmp : ψ m1 ≤ ψ m2
  · simp only [hcmp, decide_true, ternaryStep]
    by_cases hym : y ≤ m2
    · exact ⟨y, ⟨hy.1, hym⟩, by linarith⟩
    · push Not at hym
      refine ⟨m2, ⟨hlm1.trans hm1m2, le_rfl⟩, ?_⟩
      rcases eq_or_lt_of_le hm1m2 with heq | hlt
      · have : u - l = 0 := by linarith
        linarith [hy.2]
      have hslope := hφ.slope_mono_adjacent (hls hm1I) (hls hy) hlt hym
      have h1 := hψ m1 hm1I
      have h2 := hψ m2 hm2I
      have hdiff : -e ≤ φ m2 - φ m1 := by linarith
      have hpos1 : 0 < m2 - m1 := by linarith
      have hpos2 : 0 < y - m2 := by linarith
      have hyle : y - m2 ≤ m2 - m1 := by linarith [hy.2]
      rw [div_le_div_iff₀ hpos1 hpos2] at hslope
      by_contra hcon
      push Not at hcon
      have : (φ y - φ m2) * (m2 - m1) < -e * (m2 - m1) := by
        apply mul_lt_mul_of_pos_right _ hpos1; linarith
      nlinarith
  · simp only [hcmp, decide_false, ternaryStep]
    push Not at hcmp
    by_cases hym : m1 ≤ y
    · exact ⟨y, ⟨hym, hy.2⟩, by linarith⟩
    · push Not at hym
      refine ⟨m1, ⟨le_rfl, hm1m2.trans hm2u⟩, ?_⟩
      rcases eq_or_lt_of_le hm1m2 with heq | hlt
      · have : u - l = 0 := by linarith
        linarith [hy.1]
      have hslope := hφ.slope_mono_adjacent (hls hy) (hls hm2I) hym hlt
      have h1 := hψ m1 hm1I
      have h2 := hψ m2 hm2I
      have hdiff : φ m2 - φ m1 ≤ e := by linarith
      have hpos1 : 0 < m2 - m1 := by linarith
      have hpos2 : 0 < m1 - y := by linarith
      have hyle : m1 - y ≤ m2 - m1 := by linarith [hy.1]
      rw [div_le_div_iff₀ hpos2 hpos1] at hslope
      by_contra hcon
      push Not at hcon
      have : e * (m1 - y) < (φ m1 - φ y) * (m2 - m1) := by
        calc e * (m1 - y) ≤ e * (m2 - m1) := mul_le_mul_of_nonneg_left hyle he
          _ < (φ m1 - φ y) * (m2 - m1) := mul_lt_mul_of_pos_right (by linarith) hpos1
      nlinarith

end OracleTemplate.ComparisonOrth

namespace OracleTemplate.ComparisonOrth

noncomputable def ternaryRound (ψ : ℝ → ℝ) (I : ℝ × ℝ) : ℝ × ℝ :=
  ternaryStep (decide (ψ (trisectLeft I.1 I.2) ≤ ψ (trisectRight I.1 I.2))) I.1 I.2

lemma ternaryRound_iterate_props (ψ : ℝ → ℝ) (m : ℕ) {l u : ℝ} (h : l ≤ u) :
    l ≤ ((ternaryRound ψ)^[m] (l, u)).1 ∧
      ((ternaryRound ψ)^[m] (l, u)).1 ≤ ((ternaryRound ψ)^[m] (l, u)).2 ∧
      ((ternaryRound ψ)^[m] (l, u)).2 ≤ u ∧
      ((ternaryRound ψ)^[m] (l, u)).2 - ((ternaryRound ψ)^[m] (l, u)).1 =
        (2 / 3) ^ m * (u - l) := by
  induction m with
  | zero => simp [h]
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2, h3, h4⟩ := ih
      set I := (ternaryRound ψ)^[m] (l, u)
      have hs := ternaryStep_sub
        (decide (ψ (trisectLeft I.1 I.2) ≤ ψ (trisectRight I.1 I.2))) h2
      have hw := ternaryStep_width
        (decide (ψ (trisectLeft I.1 I.2) ≤ ψ (trisectRight I.1 I.2))) I.1 I.2
      simp only [ternaryRound]
      refine ⟨h1.trans hs.1, hs.2.1, hs.2.2.trans h3, ?_⟩
      rw [hw, h4, pow_succ]
      ring

lemma ternaryRound_iterate_keep {φ ψ : ℝ → ℝ} {l0 u0 e : ℝ} (hφ : ConvexOn ℝ (Set.Icc l0 u0) φ)
    (he : 0 ≤ e) (hlu : l0 ≤ u0)
    (hψ : ∀ t ∈ Set.Icc l0 u0, φ t ≤ ψ t ∧ ψ t ≤ φ t + e) (m : ℕ)
    {y : ℝ} (hy : y ∈ Set.Icc l0 u0) :
    ∃ y' ∈ Set.Icc ((ternaryRound ψ)^[m] (l0, u0)).1 ((ternaryRound ψ)^[m] (l0, u0)).2,
      φ y' ≤ φ y + m * e := by
  induction m with
  | zero => exact ⟨y, by simpa using hy, by simp⟩
  | succ m ih =>
      obtain ⟨y', hy', hφy'⟩ := ih
      obtain ⟨h1, h2, h3, -⟩ := ternaryRound_iterate_props ψ m hlu
      set I := (ternaryRound ψ)^[m] (l0, u0) with hI
      have hsub : Set.Icc I.1 I.2 ⊆ Set.Icc l0 u0 :=
        Set.Icc_subset_Icc h1 h3
      obtain ⟨y'', hy'', hφy''⟩ := ternaryStep_keep hφ he h2 hsub
        (fun t ht => hψ t (hsub ht)) hy'
      refine ⟨y'', ?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact hy''
      · push_cast
        linarith

lemma ternaryRound_final {φ ψ : ℝ → ℝ} {l0 u0 e M : ℝ}
    (hφ : ConvexOn ℝ (Set.Icc l0 u0) φ)
    (hlip : ∀ s ∈ Set.Icc l0 u0, ∀ t ∈ Set.Icc l0 u0, φ s ≤ φ t + M * |s - t|)
    (hM : 0 ≤ M) (he : 0 ≤ e) (hlu : l0 ≤ u0)
    (hψ : ∀ t ∈ Set.Icc l0 u0, φ t ≤ ψ t ∧ ψ t ≤ φ t + e) (m : ℕ)
    {y : ℝ} (hy : y ∈ Set.Icc l0 u0) :
    ((ternaryRound ψ)^[m] (l0, u0)).1 ∈ Set.Icc l0 u0 ∧
      ψ ((ternaryRound ψ)^[m] (l0, u0)).1 ≤
        φ y + (m + 1) * e + M * ((2 / 3) ^ m * (u0 - l0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := ternaryRound_iterate_props ψ m hlu
  obtain ⟨y', hy', hφy'⟩ := ternaryRound_iterate_keep hφ he hlu hψ m hy
  set I := (ternaryRound ψ)^[m] (l0, u0)
  have hlI : I.1 ∈ Set.Icc l0 u0 := ⟨h1, h2.trans h3⟩
  have hy'0 : y' ∈ Set.Icc l0 u0 := ⟨h1.trans hy'.1, hy'.2.trans h3⟩
  refine ⟨hlI, ?_⟩
  have habs : |I.1 - y'| ≤ (2 / 3) ^ m * (u0 - l0) := by
    rw [abs_le]; constructor <;> linarith [hy'.1, hy'.2]
  have := hlip I.1 hlI y' hy'0
  have := (hψ I.1 hlI).2
  nlinarith [mul_le_mul_of_nonneg_left habs hM]

end OracleTemplate.ComparisonOrth

namespace OracleTemplate.ComparisonOrth

variable {V : Type*}

noncomputable def partialInf (G : ℝ → V → ℝ) (S : Set V) (a : ℝ) : ℝ :=
  ⨅ v : S, G a v

lemma partialInf_le {G : ℝ → V → ℝ} {S : Set V} {B : ℝ} (hB : ∀ a v, B ≤ G a v)
    (a : ℝ) {v : V} (hv : v ∈ S) : partialInf G S a ≤ G a v :=
  ciInf_le ⟨B, by rintro _ ⟨w, rfl⟩; exact hB a w⟩ (⟨v, hv⟩ : S)

lemma le_partialInf {G : ℝ → V → ℝ} {S : Set V} (hS : S.Nonempty) {a c : ℝ}
    (h : ∀ v ∈ S, c ≤ G a v) : c ≤ partialInf G S a := by
  have : Nonempty S := hS.to_subtype
  exact le_ciInf fun v => h v v.2

lemma partialInf_lipschitz {G : ℝ → V → ℝ} {S : Set V} {I : Set ℝ} {B M : ℝ}
    (hS : S.Nonempty) (hB : ∀ a v, B ≤ G a v)
    (hG : ∀ v ∈ S, ∀ a ∈ I, ∀ b ∈ I, G a v ≤ G b v + M * |a - b|) :
    ∀ a ∈ I, ∀ b ∈ I, partialInf G S a ≤ partialInf G S b + M * |a - b| := by
  intro a ha b hb
  have : partialInf G S a - M * |a - b| ≤ partialInf G S b := by
    apply le_partialInf hS
    intro v hv
    have := partialInf_le hB a hv
    have := hG v hv a ha b hb
    linarith
  linarith

lemma partialInf_convex [AddCommGroup V] [Module ℝ V] {G : ℝ → V → ℝ} {S : Set V} {I : Set ℝ} {B : ℝ}
    (hS : S.Nonempty) (hB : ∀ a v, B ≤ G a v) (hI : Convex ℝ I)
    (hG : ConvexOn ℝ (I ×ˢ S) (fun p => G p.1 p.2)) :
    ConvexOn ℝ I (partialInf G S) := by
  refine ⟨hI, ?_⟩
  intro a ha b hb s t hs ht hst
  have : Nonempty S := hS.to_subtype
  have hbdd : ∀ c, BddBelow (Set.range fun v : S => G c v) :=
    fun c => ⟨B, by rintro _ ⟨w, rfl⟩; exact hB c w⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨v, hv⟩ := exists_lt_of_ciInf_lt (show partialInf G S a < partialInf G S a + δ by
    linarith)
  obtain ⟨w, hw⟩ := exists_lt_of_ciInf_lt (show partialInf G S b < partialInf G S b + δ by
    linarith)
  have hmem' := hG.1 (show (a, v.1) ∈ I ×ˢ S from ⟨ha, v.2⟩)
    (show (b, w.1) ∈ I ×ˢ S from ⟨hb, w.2⟩) hs ht hst
  have hmem : s • v.1 + t • w.1 ∈ S := by simpa using hmem'.2
  have hconv := hG.2 (show (a, v.1) ∈ I ×ˢ S from ⟨ha, v.2⟩)
    (show (b, w.1) ∈ I ×ˢ S from ⟨hb, w.2⟩) hs ht hst
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hconv
  have hle := partialInf_le hB (s * a + t * b) hmem
  have h1 : s * G a v ≤ s * (partialInf G S a + δ) := mul_le_mul_of_nonneg_left hv.le hs
  have h2 : t * G b w ≤ t * (partialInf G S b + δ) := mul_le_mul_of_nonneg_left hw.le ht
  simp only [smul_eq_mul]
  have hst' : s * δ + t * δ = δ := by rw [← add_mul, hst, one_mul]
  nlinarith

end OracleTemplate.ComparisonOrth
