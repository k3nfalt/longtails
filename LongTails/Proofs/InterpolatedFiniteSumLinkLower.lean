import LongTails.Proofs.InterpolatedFiniteSumLinkParameters
import LongTails.Proofs.InterpolatedFiniteSumLinkFamily
import LongTails.Proofs.InterpolatedFiniteSumExponentialParameters

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open OracleTemplate MeasureTheory Classical

namespace LongTails.Proofs.InterpolatedFiniteSumLinkLower

open LongTails.Setups.ExpectedInterpolatedGeneralizedFiniteSum
open InterpolatedFiniteSumLinkGeometry InterpolatedFiniteSumLinkReplies
open InterpolatedFiniteSumExponentialFamily InterpolatedFiniteSumDistinctSearch
open InterpolatedFiniteSumPairs (ownerQuery)
open InterpolatedFiniteSumHiddenComponent
open InterpolatedFiniteSumBlockOracle (safeEmbedding safeEmbedding_good safeEmbedding_avoids)

set_option maxHeartbeats 2400000 in
lemma failure_of_scales (p : Params) (hp : spec.valid p) {g k : ℕ} (hg : 0 < g) (hgn : 2 * g ≤ p.n)
    (hT : 2 * (k + 1) ≤ g) (fallback : Fin (k + 1) ↪ Fin p.d) (carrier : Fin p.d)
    (hf : ∀ i, fallback i ≠ carrier) (v : Point p) (hv : ‖v‖ = 2 * p.L1 / 7)
    (hvs : ∀ x : Point p, x carrier = 0 → ⟪v, x⟫ = 0)
    (C η a B α : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η) (ha : 0 < a) (hL : 0 < p.L1)
    (hq : 21 / 2 ≤ p.L1 * p.R) (hBpos : 0 ≤ B) (hα : 0 < α) (hαL : p.L1 * α ≤ 1 / 4)
    (hgeom : (k + 1 : ℕ) * a ^ 2 ≤ p.R ^ 2)
    (hfirstgrad : 2 * η / a ≤ p.L1 / 14)
    (hfirstcurv : 6 * η / a ^ 2 ≤ (4 * p.L1 ^ 2 / 49) / 3)
    (hadd : 2 * C * p.L1 ^ 2 / 7 ≤ p.L0)
    (hgap : (2 * C / p.n) * (Real.exp η - 1) ≤ p.Δ)
    (hB : 4 * p.R + (η + 4) / (p.L1 / 14) ≤ B)
    (hterminal : Real.exp η - 1 ≤ (k + 1 : ℕ) * (256 * ((2 * η * Real.exp η / a) / p.L1) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / p.L1))))))
    (hAA : 0 ≤ (2 * C / p.n) * (Real.exp η - 1 - (2 * η * Real.exp η / a) * α))
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hdim : 8 * (((k + 1 : ℕ) : ℝ) ^ 2 + (k + 1 : ℕ) +
      (b + 1 : ℕ) * (k + 1 : ℕ) * (B ^ 2 / α ^ 2)) ≤ p.d)
    (hloss : p.ε < 7 * ((2 * C / p.n) * (Real.exp η - 1 - (2 * η * Real.exp η / a) * α)) / 8 -
      ((2 * C / p.n) * (256 * ((2 * η * Real.exp η / a) / p.L1) *
        (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / p.L1)))))) * (4 * b / g)) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let : Nonempty (Fin p.d) := ⟨carrier⟩
  let : Nonempty (OwnerWords g (k + 1)) := ownerWords_nonempty g (k + 1) (by omega)
  let I := OwnerWords g (k + 1) × (Fin (k + 1) → Fin p.d)
  have hd : (0 : ℝ) < p.d := by exact_mod_cast (show 0 < p.d from Nat.zero_lt_of_lt carrier.isLt)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hR := hp.2.2.1
  let G := p.L1 / 14
  have hG : 0 < G := by dsimp [G]; positivity
  let emb := fun π : Fin (k + 1) → Fin p.d => safeEmbedding fallback carrier π
  let m := fun u : I => family (owner u.1) (emb u.2) η a p.L1 p.R G 4
  let dm := fun u : I => familyField (owner u.1) (emb u.2) η a p.L1 p.R G 4
  let f := fun u : I => components hgn (m u) v C
  let df := fun u : I => fields hgn (m u) (dm u) v C
  let z := fun u : I => minimizer (emb u.2) a
  let s0 := 2 * η * Real.exp η / a
  let K := 256 * (s0 / p.L1) * (1 + max 0 (Real.log (256 * (s0 / p.L1))))
  let AA := (2 * C / p.n) * (Real.exp η - 1 - s0 * α)
  let CC := (2 * C / p.n) * K
  have hzR (u : I) : ‖z u‖ ≤ p.R := by
    have hh := (minimizer_norm_sq (emb u.2) a).trans hgeom
    dsimp [z]
    nlinarith [norm_nonneg (minimizer (emb u.2) a), hR]
  have hvz (u : I) : ⟪v, z u⟫ = 0 :=
    hvs _ (minimizer_outside (emb u.2) a carrier (safeEmbedding_avoids fallback carrier hf u.2))
  have hgrad (π : Fin (k + 1) → Fin p.d) (j : Fin (k + 1)) : coefficient η j * ‖vector π a p.L1 j‖ ≤ G :=
    gradient_bound π η a p.L1 ha hL.le hfirstgrad j
  have hcurv (π : Fin (k + 1) → Fin p.d) (j : Fin (k + 1)) :
      3 * coefficient η j * ‖vector π a p.L1 j‖ ^ 2 ≤ (4 * p.L1 ^ 2 / 49) / 3 :=
    curvature_bound π η a p.L1 ha hL.le hfirstcurv j
  have hnon (u : I) (i : Fin g) (x : Point p) : 0 ≤ m u i x :=
    InterpolatedFiniteSumLinkFamily.family_nonnegative (owner u.1) (emb u.2) η a p.L1 p.R G 4 hη (by norm_num) i x
  have hmz (u : I) (i : Fin g) : m u i (z u) = 0 :=
    InterpolatedFiniteSumLinkFamily.family_minimizer_value (owner u.1) (emb u.2) η a p.L1 p.R G 4 hη ha hR
      hG.le (by norm_num) (hzR u) i
  have hAd (u : I) : spec.admissible p (f u) (exactOracle p (f u) (df u)) := by
    apply InterpolatedFiniteSumLinkFamily.admissible p hp hgn (owner u.1) (emb u.2) v C η a p.R G 4
      hC hη ha hR hG.le (by norm_num)
    · dsimp [G]
      nlinarith
    · exact InterpolatedFiniteSumExponentialParameters.radial_tuned p.L1 p.R hR hL.le hq
    · exact hgrad (emb u.2)
    · exact hcurv (emb u.2)
    · dsimp [G]; linarith
    · exact hv
    · exact hadd
    · exact hzR u
    · exact hzR u
    · exact hvz u
    · exact hgap
  apply finite_prior_failure p f df z hAd
    (fun u => components_nonnegative hgn (m u) v C hC (hnon u))
    (fun u => components_minimizer_value hgn (m u) v C (z u) (hmz u) (hvz u)) A b
    (7 * AA / 8 - CC * (4 * b / g)) hloss
  intro seed ξ
  let pick := fun q : Fin p.n × Point p => ownerQuery g q.1
  let rep := reply (T := k + 1) hgn v C η a p.L1 p.R G 4 B
  let ina := inactive hgn v C p.R G 4 B
  let bad := fun u : I => InterpolatedFiniteSumLinkOracle.Bad A pick rep ina
    Prod.snd id (A.initial seed) u.1.val b B α carrier u.2
  let cost := fun u : I => ((InterpolatedFiniteSumLinkOracle.process A pick rep ina
    (A.initial seed) u.1.val u.2 b).1.1.2.length : ℝ)
  let loss := fun u : I => objective (f u) (execute (exactOracle p (f u) (df u)) A (fun _ => b) seed ξ)
  have hnonneg (u : I) : 0 ≤ loss u := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => components_nonnegative hgn (m u) v C hC (hnon u) i _)
  have hgood (u : I) (hu : ¬bad u) : AA - CC * cost u ≤ loss u := by
    have hinj : Function.Injective u.2 := by
      by_contra hh
      exact hu (Or.inl hh)
    have havoid : ∀ j, u.2 j ≠ carrier := by intro j hh; exact hu (Or.inr (Or.inl ⟨j, hh⟩))
    have he : (emb u.2 : Fin (k + 1) → Fin p.d) = u.2 := safeEmbedding_good fallback carrier u.2 hinj havoid
    have hgood' : ¬InterpolatedFiniteSumLinkOracle.Bad A pick rep ina Prod.snd id (A.initial seed)
        u.1.val b B α carrier (emb u.2) := by rwa [he]
    have hex := coupled_execution hgn u.1 (emb u.2) v C η a p.L1 p.R G 4 B α hη hL.le hG (by norm_num)
      (hgrad (emb u.2)) hB hαL A b seed ξ carrier hgood'
    rw [he] at hex
    let st := (InterpolatedFiniteSumLinkOracle.process A pick rep ina (A.initial seed) u.1.val u.2 b).1
    have hlen : st.1.2.length ≤ k + 1 := by
      have hh := congrArg List.length (InterpolatedFiniteSumLinkOracle.process_prefix A pick rep ina
        (A.initial seed) u.1.val u.2 b)
      rw [List.length_append, ownerWord_length] at hh
      change st.1.2.length + _ = k + 1 at hh
      omega
    have hout := InterpolatedFiniteSumLinkFamily.output_lower hgn (owner u.1) (emb u.2) v C η a p.L1 p.R G 4 B α
      hC hη ha hL hR.le hG (by norm_num) hα.le hB st.1.2.length hlen hterminal (A.output st.1.1) (by
        intro hnear j hj
        have hh := InterpolatedFiniteSumLinkOracle.good_coordinate A pick rep ina Prod.snd id (A.initial seed)
          u.1.val b B α carrier u.2 hu (Fin.last b) j hj (by
            simpa only [InterpolatedFiniteSumLinkOracle.observation, Fin.val_last, ite_true, id_eq] using hnear)
        rw [he]
        simpa only [InterpolatedFiniteSumLinkOracle.observation, Fin.val_last, ite_true, id_eq] using hh)
    have hlo : loss u = (p.n : ℝ)⁻¹ * ∑ i, f u i (A.output st.1.1) := by
      change (p.n : ℝ)⁻¹ * (∑ i, f u i
        (execute (fullOracle hgn (owner u.1) (emb u.2) v C η a p.L1 p.R G 4) A (fun _ => b) seed ξ)) = _
      rw [he, hex]
    rw [hlo]
    exact hout
  have hbadword (w : OwnerWords g (k + 1)) :
      (∑ π : Fin (k + 1) → Fin p.d, if bad (w, π) then (1 : ℝ) else 0) ≤
        Fintype.card (Fin (k + 1) → Fin p.d) / 8 := by
    have hh := InterpolatedFiniteSumLinkOracle.bad_bound A pick rep ina
      (reply_local hgn v C η a p.L1 p.R G 4 B) Prod.snd id (A.initial seed) w.val b B α hBpos hα carrier
    have hm := mul_le_mul_of_nonneg_right hdim
      (Nat.cast_nonneg (Fintype.card (Fin (k + 1) → Fin p.d)) : (0 : ℝ) ≤ _)
    change (p.d : ℝ) * (∑ π, if bad (w, π) then (1 : ℝ) else 0) ≤ _ at hh
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith only [hh, hm]
  have hbad : (∑ u : I, if bad u then (1 : ℝ) else 0) ≤ Fintype.card I / 8 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hbadword w)
    simpa only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_prod, Nat.cast_mul, mul_div_assoc, I] using hh
  have hcostcoord (π : Fin (k + 1) → Fin p.d) :
      (g : ℝ) * (∑ w : OwnerWords g (k + 1), cost (w, π)) ≤ 4 * b * Fintype.card (OwnerWords g (k + 1)) := by
    dsimp only [cost]
    simp_rw [InterpolatedFiniteSumLinkOracle.process_discoveries]
    exact owner_discovery_half g (k + 1) b hT _
  have hcost : (∑ u : I, cost u) ≤ (4 * b / g) * Fintype.card I := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun π _ => hcostcoord π)
    rw [← Finset.mul_sum, Finset.sum_comm] at hh
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    have he : (∑ u : I, cost u) = ∑ w : OwnerWords g (k + 1), ∑ π : Fin (k + 1) → Fin p.d, cost (w, π) :=
      Fintype.sum_prod_type _
    rw [he]
    apply (mul_le_mul_iff_right₀ hgR).mp
    simp only [I, Fintype.card_prod, Nat.cast_mul]
    have hid : (4 * b / (g : ℝ) * (Fintype.card (OwnerWords g (k + 1)) *
        (Fintype.card (Fin (k + 1) → Fin p.d) : ℝ))) * g =
        Fintype.card (Fin (k + 1) → Fin p.d) * (4 * b * (Fintype.card (OwnerWords g (k + 1)) : ℝ)) := by
      field_simp
    nlinarith only [hh, hid]
  exact InterpolatedFiniteSumHiding.finite_average_loss_sum bad loss cost AA CC (4 * b / g) hAA
    (by dsimp [CC, K, s0]; positivity) (fun u => Nat.cast_nonneg _) hnonneg hgood hbad hcost

set_option maxHeartbeats 2400000 in
lemma tuned_failure (p : Params) (hp : spec.valid p) (hL : 0 < p.L1) (δ η : ℝ)
    (hδ : 0 < δ) (hδdef : δ = p.L0 / (4 * p.L1 ^ 2)) (hη : 0 ≤ η)
    (hexp : δ * Real.exp η = δ + 2 * (p.n / 2 : ℕ) * p.ε) {k : ℕ}
    (hT : 2 * (k + 1) ≤ p.n / 2) (hq : 64 ≤ p.L1 * p.R)
    (hderiv : 128 * η * Real.sqrt (k + 1 : ℕ) ≤ p.L1 * p.R)
    (hwidth : 2 * (1 + η) * Real.sqrt (k + 1 : ℕ) ≤ p.L1 * p.R)
    (hshape : p.L1 * p.R ≤ 64 * (k + 1 : ℕ) * Real.sqrt (k + 1 : ℕ))
    (hTq : ((k + 1 : ℕ) : ℝ) ≤ p.L1 * p.R)
    (A : Algorithm (Fin p.n × Point p) (ℝ × Point p) (Point p)) (b : ℕ)
    (hb : b ≤ (p.n / 2) * (k + 1))
    (hcost : (δ / (p.n / 2 : ℕ)) *
      (256 * ((2 * η * Real.exp η / (p.R / Real.sqrt (k + 1 : ℕ))) / p.L1) *
        (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / (p.R / Real.sqrt (k + 1 : ℕ))) / p.L1))))) *
      (4 * b / (p.n / 2 : ℕ)) ≤ 7 * p.ε / 16) :
    ∃ (f : Fin p.n → Point p → ℝ) (O : Oracle (Fin p.n × Point p) (ℝ × Point p)),
      spec.admissible p f O ∧ ¬ spec.successful p f
        (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => b) w.1 w.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let g := p.n / 2
  let T := k + 1
  have hn2 := hp.2.2.2.2.1
  have hn : 0 < p.n := by omega
  have hg : 0 < g := by dsimp [g]; omega
  have hgn : 2 * g ≤ p.n := by dsimp [g]; omega
  have hng : p.n ≤ 3 * g := by dsimp [g]; omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hnR : (0 : ℝ) < p.n := by exact_mod_cast hn
  have hTpos : 0 < T := Nat.succ_pos k
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  let C := p.n * δ / (2 * g)
  let a := p.R / Real.sqrt T
  let B := 5 * p.R
  let α := 1 / (16 * p.L1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hαL : p.L1 * α ≤ 1 / 4 := by
    have he : p.L1 * α = 1 / 16 := by dsimp [α]; field_simp
    rw [he]
    norm_num
  have hgeom : (T : ℝ) * a ^ 2 ≤ p.R ^ 2 :=
    (InterpolatedFiniteSumLinkParameters.radius_tuned T hTpos p.R).le
  have hfirstgrad : 2 * η / a ≤ p.L1 / 14 :=
    InterpolatedFiniteSumLinkParameters.first_gradient T hTpos η p.L1 p.R hη hR hderiv
  have hfirstcurv : 6 * η / a ^ 2 ≤ (4 * p.L1 ^ 2 / 49) / 3 :=
    InterpolatedFiniteSumLinkParameters.first_curvature T hTpos η p.L1 p.R hη hL hR hderiv hwidth
  have hcoef : 2 * C / p.n = δ / g := by dsimp [C]; field_simp
  have hadd : 2 * C * p.L1 ^ 2 / 7 ≤ p.L0 := by
    have hngR : (p.n : ℝ) ≤ 3 * g := by exact_mod_cast hng
    have hmul := mul_le_mul_of_nonneg_right hngR hδ.le
    have hδL : 4 * δ * p.L1 ^ 2 = p.L0 := by rw [hδdef]; field_simp
    dsimp [C]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 7)).mpr
    have he : 2 * (p.n * δ / (2 * g)) * p.L1 ^ 2 = p.n * δ * p.L1 ^ 2 / g := by ring
    rw [he]
    apply (div_le_iff₀ hgR).mpr
    have hh := mul_le_mul_of_nonneg_right hmul (sq_nonneg p.L1)
    nlinarith only [hh, hδL, mul_nonneg hgR.le hp.1.le]
  have hinit : (2 * C / p.n) * (Real.exp η - 1) = 2 * p.ε := by
    rw [hcoef]
    change δ * Real.exp η = δ + 2 * (g : ℝ) * p.ε at hexp
    rw [show δ / (g : ℝ) * (Real.exp η - 1) = δ * (Real.exp η - 1) / g by ring]
    apply (div_eq_iff (ne_of_gt hgR)).mpr
    nlinarith only [hexp]
  have hgap : (2 * C / p.n) * (Real.exp η - 1) ≤ p.Δ := by rw [hinit]; exact hp.2.2.2.2.2.1
  have hB : 4 * p.R + (η + 4) / (p.L1 / 14) ≤ B :=
    InterpolatedFiniteSumLinkParameters.threshold T hTpos η p.L1 p.R hη hL hderiv hq
  have hterminal := InterpolatedFiniteSumLinkParameters.terminal T hTpos η p.L1 p.R hη hL hR hshape
  have hpen : (2 * C / p.n) * (2 * η * Real.exp η / a) * α ≤ p.ε / 8 := by
    rw [hcoef]
    exact InterpolatedFiniteSumLinkParameters.initial_penalty g T hg hTpos δ η p.ε p.L1 p.R hδ hε hL hR hexp hwidth
  have hAA : 7 * p.ε / 4 ≤ (2 * C / p.n) * (Real.exp η - 1 - (2 * η * Real.exp η / a) * α) := by
    nlinarith only [hinit, hpen, hε]
  have hAA0 : 0 ≤ (2 * C / p.n) * (Real.exp η - 1 - (2 * η * Real.exp η / a) * α) := by
    linarith only [hAA, hε]
  have hcost' : ((2 * C / p.n) * (256 * ((2 * η * Real.exp η / a) / p.L1) *
      (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / p.L1)))))) * (4 * b / g) ≤ 7 * p.ε / 16 := by
    rw [hcoef]
    exact hcost
  have hloss : p.ε < 7 * ((2 * C / p.n) * (Real.exp η - 1 - (2 * η * Real.exp η / a) * α)) / 8 -
      ((2 * C / p.n) * (256 * ((2 * η * Real.exp η / a) / p.L1) *
        (1 + max 0 (Real.log (256 * ((2 * η * Real.exp η / a) / p.L1)))))) * (4 * b / g) := by
    nlinarith only [hAA, hcost', hε]
  have hb' : b ≤ p.n * T := hb.trans (Nat.mul_le_mul_right T (by omega))
  have hdimb := InterpolatedFiniteSumLinkParameters.setup_dimension p hp T b hTpos hTq hb'
  have hratio : B ^ 2 / α ^ 2 = 6400 * (p.L1 * p.R) ^ 2 :=
    InterpolatedFiniteSumLinkParameters.hiding_ratio p.L1 p.R hL
  have hdim : 8 * ((T : ℝ) ^ 2 + T + (b + 1 : ℕ) * T * (B ^ 2 / α ^ 2)) ≤ p.d := by
    rw [hratio]
    exact hdimb
  have hTd : T < p.d := by
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
    have hrest : 0 ≤ ((b + 1 : ℕ) : ℝ) * T * (B ^ 2 / α ^ 2) := by positivity
    have hh : (T : ℝ) < p.d := by nlinarith [sq_nonneg (T : ℝ)]
    exact_mod_cast hh
  have hd : 0 < p.d := hTpos.trans hTd
  let carrier : Fin p.d := ⟨0, hd⟩
  let fallback : Fin (k + 1) ↪ Fin p.d :=
    { toFun := fun j => ⟨j.val + 1, by have := j.isLt; change j.val + 1 < p.d; dsimp [T] at hTd; omega⟩
      inj' := by intro i j hij; apply Fin.ext; have hh := congrArg Fin.val hij; simpa using hh }
  have hf : ∀ i, fallback i ≠ carrier := by
    intro i hi
    have hh := congrArg Fin.val hi
    change i.val + 1 = 0 at hh
    omega
  let v : Point p := (2 * p.L1 / 7) • PiLp.single 2 carrier (1 : ℝ)
  have hv : ‖v‖ = 2 * p.L1 / 7 := by
    simp only [v, norm_smul, PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one]
    exact abs_of_pos (by positivity)
  have hvs : ∀ x : Point p, x carrier = 0 → ⟪v, x⟫ = 0 := by
    intro x hx
    simp only [v, real_inner_smul_left, EuclideanSpace.inner_single_left, hx, mul_zero]
  exact failure_of_scales p hp hg hgn hT fallback carrier hf v hv hvs C η a B α hC hη ha hL
    (by linarith only [hq]) (by dsimp [B]; positivity) hα hαL hgeom hfirstgrad hfirstcurv hadd
    hgap hB hterminal hAA0 A b hdim hloss

end LongTails.Proofs.InterpolatedFiniteSumLinkLower
