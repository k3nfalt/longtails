import LongTails.Proofs.FrontierChainProfiles

namespace LongTails.Proofs.FrontierChain

open FrontierChainProfiles

noncomputable def edge (u v : ℝ) : ℝ :=
  gate (-u) * potential (-v) - gate u * potential v

noncomputable def edgeLeft (u v : ℝ) : ℝ :=
  -(gateSlope (-u) * potential (-v)) - gateSlope u * potential v

noncomputable def edgeRight (u v : ℝ) : ℝ :=
  -(gate (-u) * potentialSlope (-v)) - gate u * potentialSlope v

lemma edge_bounds (u v : ℝ) : -4 ≤ edge u v ∧ edge u v ≤ 4 := by
  have h1 := mul_nonneg (gate_bounds (-u)).1 (potential_bounds (-v)).1
  have h2 := mul_nonneg (gate_bounds u).1 (potential_bounds v).1
  have h3 := mul_le_mul (gate_bounds (-u)).2 (potential_bounds (-v)).2
    (potential_bounds (-v)).1 (by norm_num : (0 : ℝ) ≤ 1)
  have h4 := mul_le_mul (gate_bounds u).2 (potential_bounds v).2
    (potential_bounds v).1 (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [edge]
  constructor <;> nlinarith

lemma edgeLeft_bounds (u v : ℝ) : -16 ≤ edgeLeft u v ∧ edgeLeft u v ≤ 0 := by
  have h1 := mul_nonneg (gateSlope_bounds (-u)).1 (potential_bounds (-v)).1
  have h2 := mul_nonneg (gateSlope_bounds u).1 (potential_bounds v).1
  have h3 := mul_le_mul (gateSlope_bounds (-u)).2 (potential_bounds (-v)).2
    (potential_bounds (-v)).1 (by norm_num : (0 : ℝ) ≤ 4)
  have h4 := mul_le_mul (gateSlope_bounds u).2 (potential_bounds v).2
    (potential_bounds v).1 (by norm_num : (0 : ℝ) ≤ 4)
  rcases gateSlope_disjoint u with h | h
  · simp only [edgeLeft, h, zero_mul, sub_zero]
    constructor <;> nlinarith
  · simp only [edgeLeft, h, zero_mul, neg_zero, zero_sub]
    constructor <;> nlinarith

lemma edgeRight_bounds (u v : ℝ) : -1 ≤ edgeRight u v ∧ edgeRight u v ≤ 0 := by
  have h1 := mul_nonneg (gate_bounds (-u)).1 (potentialSlope_bounds (-v)).1
  have h2 := mul_nonneg (gate_bounds u).1 (potentialSlope_bounds v).1
  have h3 := mul_le_mul (gate_bounds (-u)).2 (potentialSlope_bounds (-v)).2
    (potentialSlope_bounds (-v)).1 (by norm_num : (0 : ℝ) ≤ 1)
  have h4 := mul_le_mul (gate_bounds u).2 (potentialSlope_bounds v).2
    (potentialSlope_bounds v).1 (by norm_num : (0 : ℝ) ≤ 1)
  rcases gate_disjoint u with h | h
  · simp only [edgeRight, h, zero_mul, sub_zero]
    constructor <;> nlinarith
  · simp only [edgeRight, h, zero_mul, neg_zero, zero_sub]
    constructor <;> nlinarith

lemma edgeRight_large {u v : ℝ} (hu : 1 ≤ |u|) (hv : |v| ≤ 1) :
    edgeRight u v = -1 := by
  have hp := potentialSlope_one hv
  have hn := potentialSlope_one (by simpa using hv : |-v| ≤ 1)
  rcases le_abs.mp hu with hu | hu
  · rw [edgeRight, (gate_one hu).1, (gate_flat (by linarith : -u ≤ 1 / 2)).1, hp]
    ring
  · rw [edgeRight, (gate_one (by linarith : 1 ≤ -u)).1,
      (gate_flat (by linarith : u ≤ 1 / 2)).1, hn]
    ring

lemma edge_flat {u v : ℝ} (hu : |u| ≤ 1 / 2) :
    edge u v = 0 ∧ edgeLeft u v = 0 ∧ edgeRight u v = 0 := by
  have hp := gate_flat (abs_le.mp hu).2
  have hn := gate_flat (show -u ≤ 1 / 2 by linarith [(abs_le.mp hu).1])
  simp [edge, edgeLeft, edgeRight, hp.1, hp.2, hn.1, hn.2]

lemma edge_left_deriv (u v : ℝ) : HasDerivAt (fun t => edge t v) (edgeLeft u v) u := by
  have hn := (gate_deriv (-u)).comp u (hasDerivAt_id u).neg
  have h := (hn.mul_const (potential (-v))).sub ((gate_deriv u).mul_const (potential v))
  convert h using 1
  · ext t
    simp [edge]
  · simp [edgeLeft]

lemma edge_right_deriv (u v : ℝ) : HasDerivAt (edge u) (edgeRight u v) v := by
  have hn := (potential_deriv (-v)).comp v (hasDerivAt_id v).neg
  have h := (hn.const_mul (gate (-u))).sub ((potential_deriv v).const_mul (gate u))
  convert h using 1
  · ext t
    simp [edge]
  · simp [edgeRight]

variable {d : ℕ}

lemma coordinate_deriv {f : ℝ → ℝ} {c : ℝ} (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (h : HasDerivAt f c (x i)) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => f (y i))
      (c • (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x :=
  h.comp_hasFDerivAt x
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt

lemma coordinate_gradient {f : ℝ → ℝ} {c : ℝ} (i : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (h : HasDerivAt f c (x i)) :
    HasGradientAt (fun y : EuclideanSpace ℝ (Fin d) => f (y i))
      (c • EuclideanSpace.single i (1 : ℝ)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert coordinate_deriv i x h using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_single_left]

noncomputable def edgeField (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  edgeLeft (x i) (x j) • EuclideanSpace.single i (1 : ℝ) +
    edgeRight (x i) (x j) • EuclideanSpace.single j (1 : ℝ)

lemma edge_gradient (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (fun y : EuclideanSpace ℝ (Fin d) => edge (y i) (y j))
      (edgeField i j x) x := by
  have hg := coordinate_deriv i x (gate_deriv (x i))
  have hp := coordinate_deriv j x (potential_deriv (x j))
  have hgn := coordinate_deriv i x ((gate_deriv (-x i)).comp (x i) (hasDerivAt_id (x i)).neg)
  have hpn := coordinate_deriv j x
    ((potential_deriv (-x j)).comp (x j) (hasDerivAt_id (x j)).neg)
  have h := (hgn.mul hpn).sub (hg.mul hp)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · ext y
    simp [edge]
  · ext v
    simp [edgeField, edgeLeft, edgeRight, InnerProductSpace.toDual_apply_apply,
      EuclideanSpace.inner_single_left]
    ring

noncomputable def objective {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -potential (x (π 0)) + ∑ i : Fin k, edge (x (π i.castSucc)) (x (π i.succ))

noncomputable def field {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  -(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)) +
    ∑ i : Fin k, edgeField (π i.castSucc) (π i.succ) x

lemma objective_gradient {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (objective π) (field π x) x := by
  have hs := HasFDerivAt.sum (u := Finset.univ)
    (fun (i : Fin k) _ => (edge_gradient (π i.castSucc) (π i.succ) x).hasFDerivAt)
  have hp := (coordinate_gradient (π 0) x (potential_deriv (x (π 0)))).hasFDerivAt.neg
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hp.add hs using 1
  · ext y
    simp [objective]
  · simp [field]

lemma objective_gap {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) : objective π x - objective π y ≤ 8 * (k + 1) := by
  have hsum : ∑ i : Fin k, (edge (x (π i.castSucc)) (x (π i.succ)) -
      edge (y (π i.castSucc)) (y (π i.succ))) ≤ 8 * k := by
    calc _ ≤ ∑ _i : Fin k, (8 : ℝ) := Finset.sum_le_sum fun i _ => by
          have h1 := (edge_bounds (x (π i.castSucc)) (x (π i.succ))).2
          have h2 := (edge_bounds (y (π i.castSucc)) (y (π i.succ))).1
          linarith
      _ = _ := by simp; ring
  dsimp [objective]
  rw [Finset.sum_sub_distrib] at hsum
  have h1 := (potential_bounds (x (π 0))).1
  have h2 := (potential_bounds (y (π 0))).2
  nlinarith

lemma edgeField_nonpos (i j l : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    edgeField i j x l ≤ 0 := by
  classical
  have h1 := (edgeLeft_bounds (x i) (x j)).2
  have h2 := (edgeRight_bounds (x i) (x j)).2
  simp only [edgeField, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs <;> simp_all
  all_goals linarith

lemma edgeField_right {i j : Fin d} (h : i ≠ j) (x : EuclideanSpace ℝ (Fin d)) :
    edgeField i j x j = edgeRight (x i) (x j) := by
  simp [edgeField, h]

lemma field_nonpos {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (l : Fin d) : field π x l ≤ 0 := by
  classical
  have hs : ∑ i : Fin k, edgeField (π i.castSucc) (π i.succ) x l ≤ 0 :=
    Finset.sum_nonpos fun i _ => edgeField_nonpos _ _ _ _
  have hp := (potentialSlope_bounds (x (π 0))).1
  simp only [field, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_neg,
    Pi.neg_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, PiLp.single_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  split_ifs <;> simp_all
  all_goals linarith

lemma field_first_deficient {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (h : |x (π 0)| ≤ 1) : field π x (π 0) ≤ -1 := by
  have hs : ∑ i : Fin k, edgeField (π i.castSucc) (π i.succ) x (π 0) ≤ 0 :=
    Finset.sum_nonpos fun i _ => edgeField_nonpos _ _ _ _
  simpa [field, potentialSlope_one h, WithLp.ofLp_sum, Finset.sum_apply] using hs

lemma field_successor_deficient {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin k)
    (hu : 1 ≤ |x (π i.castSucc)|) (hv : |x (π i.succ)| ≤ 1) :
    field π x (π i.succ) ≤ -1 := by
  classical
  have hij : π i.castSucc ≠ π i.succ := by
    apply π.injective.ne
    intro h
    have := congrArg Fin.val h
    simp at this
  have he : edgeField (π i.castSucc) (π i.succ) x (π i.succ) = -1 := by
    rw [edgeField_right hij, edgeRight_large hu hv]
  have hs : ∑ j : Fin k, edgeField (π j.castSucc) (π j.succ) x (π i.succ) ≤ -1 := by
    calc _ ≤ ∑ j : Fin k, if j = i then (-1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs with hj
          · subst j
            exact he.le
          · exact edgeField_nonpos _ _ _ _
      _ = _ := by simp
  have hi0 : π 0 ≠ π i.succ := π.injective.ne (Fin.succ_ne_zero i).symm
  simpa [field, hi0, WithLp.ofLp_sum, Finset.sum_apply] using hs

lemma exists_deficient {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (h : |x (π (Fin.last k))| < 1) :
    ∃ j : Fin (k + 1), |x (π j)| < 1 ∧ field π x (π j) ≤ -1 := by
  classical
  have hex : ∃ n : ℕ, ∃ hn : n < k + 1, |x (π ⟨n, hn⟩)| < 1 :=
    ⟨k, by omega, h⟩
  obtain ⟨hn, hs⟩ := Nat.find_spec hex
  let j : Fin (k + 1) := ⟨Nat.find hex, hn⟩
  change |x (π j)| < 1 at hs
  have hmin (i : Fin (k + 1)) (hi : i.val < j.val) : 1 ≤ |x (π i)| := by
    by_contra hb
    have hi' : ∃ hn : i.val < k + 1, |x (π ⟨i.val, hn⟩)| < 1 :=
      ⟨i.isLt, lt_of_not_ge hb⟩
    exact Nat.find_min hex hi hi'
  refine ⟨j, hs, ?_⟩
  by_cases hj : j = 0
  · rw [hj]
    exact field_first_deficient π x (by simpa only [hj] using hs.le)
  · let i := j.pred hj
    have he : i.succ = j := Fin.succ_pred j hj
    have hi : i.castSucc.val < j.val := by
      rw [← he]
      simp
    have hp := field_successor_deficient π x i (hmin i.castSucc hi)
      (by simpa [he] using hs.le)
    simpa [he] using hp

lemma field_norm_lower {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (h : |x (π (Fin.last k))| < 1) :
    1 ≤ ‖field π x‖ := by
  obtain ⟨j, _, hj⟩ := exists_deficient π x h
  have hc := PiLp.norm_apply_le (field π x) (π j)
  rw [Real.norm_eq_abs, abs_of_nonpos (by linarith : field π x (π j) ≤ 0)] at hc
  linarith

end LongTails.Proofs.FrontierChain
