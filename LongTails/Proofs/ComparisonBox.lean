import LongTails.Proofs.ComparisonDirection

open scoped RealInnerProductSpace

namespace OracleTemplate.ComparisonOrth

open QueryPlan

lemma eval_ternaryRoundPlan {n c : ℕ} (f : Pt n → ℝ) (inner : ℝ → CPlan n (Pt n) c)
    (I : ℝ × ℝ) :
    eval (cmp f) (ternaryRoundPlan inner I) =
      ternaryRound (fun t => f (eval (cmp f) (inner t))) I := by
  simp only [ternaryRoundPlan, eval_bind]
  rfl

lemma eval_searchPlan {n c : ℕ} (f : Pt n → ℝ) (m : ℕ) (inner : ℝ → CPlan n (Pt n) c)
    (w : ℝ) :
    eval (cmp f) (searchPlan m inner w) =
      eval (cmp f) (inner ((ternaryRound (fun t => f (eval (cmp f) (inner t))))^[m] (-w, w)).1) := by
  simp only [searchPlan, eval_bind, eval_iteratePlan, eval_ternaryRoundPlan]

lemma search_level {n c : ℕ} (f : Pt n → ℝ) (m : ℕ) (inner : ℝ → CPlan n (Pt n) c)
    (φ : ℝ → ℝ) {w e M : ℝ} (hw : 0 ≤ w) (hφ : ConvexOn ℝ (Set.Icc (-w) w) φ)
    (hlip : ∀ s ∈ Set.Icc (-w) w, ∀ t ∈ Set.Icc (-w) w, φ s ≤ φ t + M * |s - t|)
    (hM : 0 ≤ M) (he : 0 ≤ e)
    (hψ : ∀ t ∈ Set.Icc (-w) w, φ t ≤ f (eval (cmp f) (inner t)) ∧
      f (eval (cmp f) (inner t)) ≤ φ t + e) :
    ∃ t ∈ Set.Icc (-w) w, eval (cmp f) (searchPlan m inner w) = eval (cmp f) (inner t) ∧
      ∀ y ∈ Set.Icc (-w) w, f (eval (cmp f) (searchPlan m inner w)) ≤
        φ y + (m + 1) * e + M * ((2 / 3) ^ m * (w - -w)) := by
  have hlu : -w ≤ w := by linarith
  refine ⟨((ternaryRound (fun t => f (eval (cmp f) (inner t))))^[m] (-w, w)).1, ?_,
    eval_searchPlan f m inner w, ?_⟩
  · exact (ternaryRound_final hφ hlip hM he hlu hψ m (y := w) ⟨hlu, le_rfl⟩).1
  · intro y hy
    rw [eval_searchPlan]
    exact (ternaryRound_final hφ hlip hM he hlu hψ m hy).2

noncomputable def affine3 {n : ℕ} (x0 u1 u2 u3 : Pt n) (a b c : ℝ) : Pt n :=
  x0 + a • u1 + b • u2 + c • u3

lemma mix_self (a s t : ℝ) (hst : s + t = 1) : s * a + t * a = a := by
  rw [← add_mul, hst, one_mul]

section Box

variable {n : ℕ} {f : Pt n → ℝ} (hc : ConvexOn ℝ Set.univ f)
  (hg : ∀ x, HasGradientAt f (gradient f x) x)
include hc hg

omit hc hg in
lemma affine3_mix (x0 u1 u2 u3 : Pt n) (a b c a' b' c' s t : ℝ) (hst : s + t = 1) :
    affine3 x0 u1 u2 u3 (s * a + t * a') (s * b + t * b') (s * c + t * c') =
      s • affine3 x0 u1 u2 u3 a b c + t • affine3 x0 u1 u2 u3 a' b' c' := by
  have : t = 1 - s := by linarith
  subst this
  simp only [affine3]
  module

lemma lip_of_grad {M : ℝ} {p q : Pt n}
    (hp : ‖gradient f p‖ ≤ M) : f p ≤ f q + M * ‖p - q‖ := by
  have h1 := Gradient.convex_support hc hg p q
  have h2 : ⟪gradient f p, p - q⟫ ≤ M * ‖p - q‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
  rw [show q - p = -(p - q) by abel, inner_neg_right] at h1
  linarith

omit hg in
lemma affine3_convex (x0 u1 u2 u3 : Pt n) (a b c a' b' c' s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) :
    f (affine3 x0 u1 u2 u3 (s * a + t * a') (s * b + t * b') (s * c + t * c')) ≤
      s * f (affine3 x0 u1 u2 u3 a b c) + t * f (affine3 x0 u1 u2 u3 a' b' c') := by
  rw [affine3_mix x0 u1 u2 u3 a b c a' b' c' s t hst]
  have := hc.2 (Set.mem_univ (affine3 x0 u1 u2 u3 a b c))
    (Set.mem_univ (affine3 x0 u1 u2 u3 a' b' c')) hs ht hst
  simpa [smul_eq_mul] using this

omit hc hg in
theorem box_guarantee_abs (Φ : ℝ → ℝ → ℝ → Pt n) {B M w1 w2 w3 : ℝ}
    (hB : ∀ a b c, B ≤ f (Φ a b c)) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3)
    (hM : 0 ≤ M)
    (hconv : ∀ a b c a' b' c' s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
      f (Φ (s * a + t * a') (s * b + t * b') (s * c + t * c')) ≤
        s * f (Φ a b c) + t * f (Φ a' b' c'))
    (hla : ∀ a ∈ Set.Icc (-w1) w1, ∀ a' ∈ Set.Icc (-w1) w1, ∀ b ∈ Set.Icc (-w2) w2,
      ∀ c ∈ Set.Icc (-w3) w3, f (Φ a b c) ≤ f (Φ a' b c) + M * |a - a'|)
    (hlb : ∀ a ∈ Set.Icc (-w1) w1, ∀ b ∈ Set.Icc (-w2) w2, ∀ b' ∈ Set.Icc (-w2) w2,
      ∀ c ∈ Set.Icc (-w3) w3, f (Φ a b c) ≤ f (Φ a b' c) + M * |b - b'|)
    (hlc : ∀ a ∈ Set.Icc (-w1) w1, ∀ b ∈ Set.Icc (-w2) w2, ∀ c ∈ Set.Icc (-w3) w3,
      ∀ c' ∈ Set.Icc (-w3) w3, f (Φ a b c) ≤ f (Φ a b c') + M * |c - c'|) (m : ℕ) :
    ∃ a ∈ Set.Icc (-w1) w1, ∃ b ∈ Set.Icc (-w2) w2, ∃ c ∈ Set.Icc (-w3) w3,
      eval (cmp f) (boxPlan m Φ w1 w2 w3) = Φ a b c ∧
      ∀ a' ∈ Set.Icc (-w1) w1, ∀ b' ∈ Set.Icc (-w2) w2, ∀ c' ∈ Set.Icc (-w3) w3,
        f (eval (cmp f) (boxPlan m Φ w1 w2 w3)) ≤ f (Φ a' b' c') +
          ((m + 1) * ((m + 1) * (M * ((2 / 3) ^ m * (w3 - -w3))) +
            M * ((2 / 3) ^ m * (w2 - -w2))) + M * ((2 / 3) ^ m * (w1 - -w1))) := by
  have hq0 : (0 : ℝ) ≤ (2 / 3) ^ m := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = M * ((2 / 3) ^ m * (w3 - -w3)) := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : ℝ, E2 = (m + 1) * E1 + M * ((2 / 3) ^ m * (w2 - -w2)) :=
    ⟨_, rfl⟩
  have hE1n : 0 ≤ E1 := by rw [hE1]; exact mul_nonneg hM (mul_nonneg hq0 (by linarith))
  have hE2n : 0 ≤ E2 := by
    rw [hE2]; exact add_nonneg (mul_nonneg hm0 hE1n) (mul_nonneg hM (mul_nonneg hq0 (by linarith)))
  have hI2 : (Set.Icc (-w2) w2).Nonempty := ⟨0, by constructor <;> linarith⟩
  have hI3 : (Set.Icc (-w3) w3).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ → ℝ → Pt n, ∀ a b,
      eval (cmp f) (searchPlan m (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) = P1 a b :=
    ⟨_, fun _ _ => rfl⟩
  have lev1 : ∀ a ∈ Set.Icc (-w1) w1, ∀ b ∈ Set.Icc (-w2) w2, ∃ c ∈ Set.Icc (-w3) w3,
      P1 a b = Φ a b c ∧ ∀ y ∈ Set.Icc (-w3) w3, f (P1 a b) ≤ f (Φ a b y) + E1 := by
    intro a ha b hb
    have hcv : ConvexOn ℝ (Set.Icc (-w3) w3) (fun c => f (Φ a b c)) := by
      refine ⟨convex_Icc _ _, ?_⟩
      intro c _ c' _ s t hs ht hst
      have := hconv a b c a b c' s t hs ht hst
      rw [mix_self a s t hst, mix_self b s t hst] at this
      simpa only [smul_eq_mul] using this
    obtain ⟨c, hcI, heq, hle⟩ := search_level f m (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0))
      (fun c => f (Φ a b c)) hw3 hcv (fun s hs t ht => hlc a ha b hb s hs t ht) hM le_rfl
      (fun t _ => ⟨le_rfl, by rw [add_zero]; exact le_rfl⟩)
    rw [hP1] at heq hle
    refine ⟨c, hcI, heq, fun y hy => ?_⟩
    have := hle y hy
    rw [mul_zero, add_zero, ← hE1] at this
    exact this
  obtain ⟨φ2, hφ2⟩ : ∃ φ2 : ℝ → ℝ → ℝ, ∀ a,
      φ2 a = partialInf (fun b c => f (Φ a b c)) (Set.Icc (-w3) w3) := ⟨_, fun _ => rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2 : ℝ → Pt n, ∀ a,
      eval (cmp f) (searchPlan m (fun b => searchPlan m
        (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) w2) = P2 a := ⟨_, fun _ => rfl⟩
  have lev2 : ∀ a ∈ Set.Icc (-w1) w1, ∃ b ∈ Set.Icc (-w2) w2, ∃ c ∈ Set.Icc (-w3) w3,
      P2 a = Φ a b c ∧ ∀ y ∈ Set.Icc (-w2) w2, f (P2 a) ≤ φ2 a y + E2 := by
    intro a ha
    have hcv : ConvexOn ℝ (Set.Icc (-w2) w2) (φ2 a) := by
      rw [hφ2]
      apply partialInf_convex hI3 (fun b c => hB a b c) (convex_Icc _ _)
      refine ⟨(convex_Icc _ _).prod (convex_Icc _ _), ?_⟩
      intro p _ q _ s t hs ht hst
      have := hconv a p.1 p.2 a q.1 q.2 s t hs ht hst
      rw [mix_self a s t hst] at this
      simpa only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
        using this
    have hlp : ∀ s ∈ Set.Icc (-w2) w2, ∀ t ∈ Set.Icc (-w2) w2, φ2 a s ≤ φ2 a t + M * |s - t| := by
      rw [hφ2]
      exact partialInf_lipschitz hI3 (fun b c => hB a b c)
        (fun c hcc b hb b' hb' => hlb a ha b hb b' hb' c hcc)
    have hψ : ∀ t ∈ Set.Icc (-w2) w2, φ2 a t ≤ f (eval (cmp f) ((fun b => searchPlan m
        (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) t)) ∧
        f (eval (cmp f) ((fun b => searchPlan m
          (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) t)) ≤ φ2 a t + E1 := by
      intro t ht
      simp only [hP1]
      obtain ⟨c, hcI, heq, hle⟩ := lev1 a ha t ht
      refine ⟨?_, ?_⟩
      · rw [heq, hφ2]; exact partialInf_le (fun b c => hB a b c) t hcI
      · have : f (P1 a t) - E1 ≤ φ2 a t := by
          rw [hφ2]; exact le_partialInf hI3 (fun y hy => by have := hle y hy; linarith)
        linarith
    obtain ⟨b, hbI, heq, hle⟩ := search_level f m _ (φ2 a) hw2 hcv hlp hM hE1n hψ
    simp only [hP1, hP2] at heq hle
    obtain ⟨c, hcI, heq1, -⟩ := lev1 a ha b hbI
    refine ⟨b, hbI, c, hcI, heq.trans heq1, fun y hy => ?_⟩
    have := hle y hy
    rw [hE2]; linarith
  obtain ⟨φ3, hφ3⟩ : ∃ φ3 : ℝ → ℝ,
      φ3 = partialInf (fun a (v : ℝ × ℝ) => f (Φ a v.1 v.2))
        (Set.Icc (-w2) w2 ×ˢ Set.Icc (-w3) w3) := ⟨_, rfl⟩
  have hS : (Set.Icc (-w2) w2 ×ˢ Set.Icc (-w3) w3).Nonempty := hI2.prod hI3
  have hcv3 : ConvexOn ℝ (Set.Icc (-w1) w1) φ3 := by
    rw [hφ3]
    apply partialInf_convex hS (fun a v => hB a v.1 v.2) (convex_Icc _ _)
    refine ⟨(convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _)), ?_⟩
    intro p _ q _ s t hs ht hst
    have := hconv p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 s t hs ht hst
    simpa only [smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
      using this
  have hlp3 : ∀ s ∈ Set.Icc (-w1) w1, ∀ t ∈ Set.Icc (-w1) w1, φ3 s ≤ φ3 t + M * |s - t| := by
    rw [hφ3]
    exact partialInf_lipschitz hS (fun a v => hB a v.1 v.2)
      (fun v hv a ha a' ha' => hla a ha a' ha' v.1 hv.1 v.2 hv.2)
  have hψ3 : ∀ t ∈ Set.Icc (-w1) w1, φ3 t ≤ f (eval (cmp f) ((fun a => searchPlan m
        (fun b => searchPlan m (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) w2) t)) ∧
      f (eval (cmp f) ((fun a => searchPlan m
        (fun b => searchPlan m (fun c => (.done (Φ a b c) : CPlan n (Pt n) 0)) w3) w2) t)) ≤
        φ3 t + E2 := by
    intro t ht
    simp only [hP2]
    obtain ⟨b, hbI, c, hcI, heq, hle⟩ := lev2 t ht
    refine ⟨?_, ?_⟩
    · rw [heq, hφ3]
      exact partialInf_le (fun a v => hB a v.1 v.2) t
        (show (b, c) ∈ Set.Icc (-w2) w2 ×ˢ Set.Icc (-w3) w3 from ⟨hbI, hcI⟩)
    · have : f (P2 t) - E2 ≤ φ3 t := by
        rw [hφ3]
        apply le_partialInf hS
        intro v hv
        have h1 := hle v.1 hv.1
        have h2 : φ2 t v.1 ≤ f (Φ t v.1 v.2) := by
          rw [hφ2]; exact partialInf_le (fun b c => hB t b c) v.1 hv.2
        linarith
      linarith
  obtain ⟨a, haI, heq, hle⟩ := search_level f m _ φ3 hw1 hcv3 hlp3 hM hE2n hψ3
  simp only [hP2] at heq
  obtain ⟨b, hbI, c, hcI, heq2, -⟩ := lev2 a haI
  refine ⟨a, haI, b, hbI, c, hcI, heq.trans heq2, ?_⟩
  intro a' ha' b' hb' c' hc'
  have h1 := hle a' ha'
  have h2 : φ3 a' ≤ f (Φ a' b' c') := by
    rw [hφ3]
    exact partialInf_le (fun a v => hB a v.1 v.2) a'
      (show (b', c') ∈ Set.Icc (-w2) w2 ×ˢ Set.Icc (-w3) w3 from ⟨hb', hc'⟩)
  rw [hE2] at h1
  rw [← hE1]
  exact le_trans h1 (by linarith)

theorem box_guarantee {xs : Pt n} (hmin : ∀ y, f xs ≤ f y) (x0 u1 u2 u3 : Pt n)
    (hu1 : ‖u1‖ ≤ 1) (hu2 : ‖u2‖ ≤ 1) (hu3 : ‖u3‖ ≤ 1) {w1 w2 w3 M : ℝ}
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) (hM : 0 ≤ M)
    (hgrad : ∀ a b c, a ∈ Set.Icc (-w1) w1 → b ∈ Set.Icc (-w2) w2 → c ∈ Set.Icc (-w3) w3 →
      ‖gradient f (affine3 x0 u1 u2 u3 a b c)‖ ≤ M) (m : ℕ) :
    ∃ a ∈ Set.Icc (-w1) w1, ∃ b ∈ Set.Icc (-w2) w2, ∃ c ∈ Set.Icc (-w3) w3,
      eval (cmp f) (boxPlan m (affine3 x0 u1 u2 u3) w1 w2 w3) = affine3 x0 u1 u2 u3 a b c ∧
      ∀ a' ∈ Set.Icc (-w1) w1, ∀ b' ∈ Set.Icc (-w2) w2, ∀ c' ∈ Set.Icc (-w3) w3,
        f (eval (cmp f) (boxPlan m (affine3 x0 u1 u2 u3) w1 w2 w3)) ≤
          f (affine3 x0 u1 u2 u3 a' b' c') +
            ((m + 1) * ((m + 1) * (M * ((2 / 3) ^ m * (w3 - -w3))) +
              M * ((2 / 3) ^ m * (w2 - -w2))) + M * ((2 / 3) ^ m * (w1 - -w1))) := by
  apply box_guarantee_abs (affine3 x0 u1 u2 u3) (B := f xs) (fun a b c => hmin _) hw1 hw2 hw3 hM
    (fun a b c a' b' c' s t hs ht hst => affine3_convex hc x0 u1 u2 u3 a b c a' b' c' s t hs ht hst)
  · intro a ha a' _ b hb c hcc
    have := lip_of_grad hc hg (q := affine3 x0 u1 u2 u3 a' b c) (hgrad a b c ha hb hcc)
    have hn : ‖affine3 x0 u1 u2 u3 a b c - affine3 x0 u1 u2 u3 a' b c‖ ≤ |a - a'| := by
      rw [show affine3 x0 u1 u2 u3 a b c - affine3 x0 u1 u2 u3 a' b c = (a - a') • u1 by
        simp only [affine3]; module, norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (a - a')]
    nlinarith
  · intro a ha b hb b' _ c hcc
    have := lip_of_grad hc hg (q := affine3 x0 u1 u2 u3 a b' c) (hgrad a b c ha hb hcc)
    have hn : ‖affine3 x0 u1 u2 u3 a b c - affine3 x0 u1 u2 u3 a b' c‖ ≤ |b - b'| := by
      rw [show affine3 x0 u1 u2 u3 a b c - affine3 x0 u1 u2 u3 a b' c = (b - b') • u2 by
        simp only [affine3]; module, norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (b - b')]
    nlinarith
  · intro a ha b hb c hcc c' _
    have := lip_of_grad hc hg (q := affine3 x0 u1 u2 u3 a b c') (hgrad a b c ha hb hcc)
    have hn : ‖affine3 x0 u1 u2 u3 a b c - affine3 x0 u1 u2 u3 a b c'‖ ≤ |c - c'| := by
      rw [show affine3 x0 u1 u2 u3 a b c - affine3 x0 u1 u2 u3 a b c' = (c - c') • u3 by
        simp only [affine3]; module, norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (c - c')]
    nlinarith

end Box

end OracleTemplate.ComparisonOrth
