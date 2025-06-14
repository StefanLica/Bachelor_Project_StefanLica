import Bachelor_Project_StefanLica.abc_Z_imp_general_Brocard
open Polynomial



/-!
# Multypling by a constant

This file treats a generalization of the main result, namely what happens when the equation is changed to
P(x) = c * n!, where c is an integer constant. It is proven in this file that this equation can be reduced
to the main problem by a rescaling argument in the polynomial, followed by a case distinction of wether or not c divides x.
`Qc_degree` and `Qc_id` are helping lemmas for the rescaled polynomial.

## Main statements


* `abc_Z_imp_poly_eq_const_dvd_fac_finite_sol`: Treating the case when c divides x.
* `abc_Z_imp_poly_eq_const_fac_finite_sol`: The general case, where c does not have to divide x. This case is reduced to the previous one.

-/



lemma Qc_degree (P Qc : ℤ[X]) (d : ℕ) (c : ℤ) (hcne0 : c ≠ 0) (hdeg : P.degree ≥ 2) (hd : d = P.natDegree) (hqc : Qc = (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * (C (P.coeff i)) * X ^ i) + C (P.coeff 0 / c)) : Qc.degree ≥ 2 := by

  rw [hqc]
  set k := (P.coeff 0 / c)

  set p := (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * C (P.coeff i) * X ^ i + C k) with hp
  have hsumdeg : (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * C (P.coeff i) * X ^ i).degree ≥ ↑d := by
    refine Polynomial.le_degree_of_ne_zero ?_
    simp only [Polynomial.finset_sum_coeff, ←Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    simp
    constructor
    rw [(Polynomial.degree_eq_iff_natDegree_eq (ne_zero_of_coe_le_degree hdeg)).2 (by exact id (Eq.symm hd))] at hdeg
    simp at hdeg
    exact Nat.ne_zero_of_lt hdeg
    constructor
    intro hc
    absurd hcne0
    exact hc
    refine coeff_ne_zero_of_eq_degree ((degree_eq_iff_natDegree_eq (ne_zero_of_coe_le_degree hdeg)).mpr (id (Eq.symm hd)))
  have hsumdeg' : (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * C (P.coeff i) * X ^ i).natDegree ≥ d := by exact le_natDegree_of_coe_le_degree hsumdeg
  have hp0 : p ≠ 0 := by
    by_contra hpc
    have hpd : p.degree = ⊥ := by exact degree_eq_bot.mpr hpc
    unfold p at hpd
    rw [Polynomial.degree_add_C] at hpd
    rw [hpd] at hsumdeg
    simp at hsumdeg
    refine lt_of_le_of_lt' hsumdeg ?_
    simp
    rw [hd]
    refine natDegree_pos_iff_degree_pos.mpr (lt_of_le_of_lt' hdeg (by simp))
  have hcontrapose := (Polynomial.natDegree_lt_iff_degree_lt (p := p) (n := 2) hp0).2
  have hcon : p.natDegree ≥ 2 → p.degree ≥ ↑2 := by exact fun a ↦ le_imp_le_of_lt_imp_lt hcontrapose a
  refine hcon ?_
  unfold p
  rw [Polynomial.natDegree_add_C]
  refine ge_trans hsumdeg' ?_
  rw [hd]
  exact le_natDegree_of_coe_le_degree hdeg

lemma Qc_id {P Q Qc : ℤ[X]} {d n : ℕ} {x c z : ℤ} (hcne0 : c ≠ 0) (hz : x = c * z) (h : eval x P = c * ↑n.factorial) (hd : d = P.natDegree) (hq : Q = P.comp (C c * X)) (hqc : Qc = (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * (C (P.coeff i)) * X ^ i) + C (P.coeff 0 / c)) : (Q.eval z = c * (Qc.eval z)) := by

  have hp : P.eval (c * z) = ∑ i ∈ Finset.range (d + 1), c ^ i * P.coeff i * z ^ i := by
    rw [eval_eq_sum_range]
    rw [← hd]
    refine Finset.sum_congr rfl ?_
    intro i hir
    conv_rhs => rw [mul_assoc, mul_comm, mul_assoc]
    simp
    constructor
    ring
  have hdvd : c ∣ P.coeff 0 := by
    have hpr : ∑ i ∈ Finset.range (d + 1), c ^ i * P.coeff i * z ^ i = (∑ i ∈ Finset.range (d + 1) \ {0}, c ^ i  * P.coeff i * z ^ i) + P.coeff 0  := by simp
    rw [hz, hp, hpr] at h
    set s := ∑ i ∈ Finset.range (d + 1) \ {0}, c ^ i * P.coeff i * z ^ i
    apply Eq.symm (a := s + P.coeff 0) at h
    apply Int.sub_eq_iff_eq_add'.2 at h
    have hs : c ∣ s := by
      unfold s
      refine Finset.dvd_sum ?_
      intro i hi
      simp at hi
      refine Int.dvd_mul.mpr ?_
      use c, 1
      constructor
      refine Int.dvd_mul.mpr ?_
      use c, 1
      constructor
      refine dvd_pow_self c hi.2
      constructor
      simp
      simp
      constructor
      simp
      simp
    rw [←h]
    refine Int.dvd_sub (Int.dvd_mul_right c ↑n.factorial) hs
  obtain ⟨k, hdvd⟩ := hdvd
  have hk : k = P.coeff 0 / c := by exact Int.eq_ediv_of_mul_eq_right hcne0 (id (Eq.symm hdvd))
  rw [hqc, ←hk]
  rw [Polynomial.eval_add, mul_add, Polynomial.eval_finset_sum]
  simp only [←Polynomial.C_mul, Polynomial.eval_mul_X_pow, Polynomial.eval_C]
  rw [Finset.mul_sum]
  have h11 : ∑ i ∈ Finset.range (d + 1) \ {0}, c * (c ^ (i - 1) * P.coeff i * z ^ i) = ∑ i ∈ Finset.range (d + 1) \ {0}, (c ^ i * P.coeff i * z ^ i) := by
    refine Finset.sum_congr rfl ?_
    intro i hir
    simp at hir
    ring_nf
    simp
    constructor
    constructor
    refine mul_pow_sub_one hir.2 c
  rw [h11]
  rw [hq]
  rw [Polynomial.eval_comp, Polynomial.eval_mul_X, Polynomial.eval_C]
  rw [hp]
  have hfin : Finset.range (d + 1) = (Finset.range (d + 1) \ {0}) ∪ {0} := by simp
  conv_lhs =>
    rw [hfin, Finset.sum_union (Finset.sdiff_disjoint), Finset.sum_singleton]
    simp only [pow_zero, one_mul, mul_one, sub_add_cancel]
  rw [hdvd]




lemma abc_Z_imp_poly_eq_const_dvd_fac_finite_sol (P : ℤ[X]) (hdeg : P.degree ≥ 2) (c : ℤ) (hcne0 : c ≠ 0) :
  abc_Z → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , (c ∣ x) → (P.eval x = c * n.factorial) → (n < N) ∧ (|x| < N)) := by

  set d := P.natDegree with hd
  intro abcz
  let Q : ℤ[X] := P.comp (C c * X)
  let Qc : ℤ[X] := (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * (C (P.coeff i)) * X ^ i) + C (P.coeff 0 / c)
  have hqcdeg : Qc.degree ≥ 2 := by exact Qc_degree P Qc d c hcne0 hdeg hd rfl
  obtain ⟨M, hng⟩ := abc_Z_imp_poly_eq_fac_finite_sol Qc hqcdeg abcz
  use c.natAbs * M
  intro n x hdvd hcc
  obtain ⟨z, h0⟩ := hdvd
  have hqc : Q.eval z = c * (Qc.eval z) := by exact Qc_id hcne0 h0 hcc hd rfl rfl
  have hcc' : P.eval x = Q.eval z := by
    rw [h0]
    unfold Q
    simp
  rw [hqc] at hcc'
  rw [hcc'] at hcc
  rw [Int.mul_eq_mul_left_iff hcne0] at hcc
  specialize hng n z hcc
  constructor
  refine lt_of_lt_of_le hng.1 ?_
  refine Nat.le_mul_of_pos_left M (Int.natAbs_pos.mpr hcne0)
  rw [h0]
  zify
  rw [abs_mul]
  refine Int.mul_lt_mul_of_pos_left hng.2 (abs_pos.mpr hcne0)




/-- Variation of the main result, namely what happens when the equation is changed to
P(x) = c * n!, where c is an integer constant. Using `abc_Z_imp_poly_eq_const_dvd_fac_finite_sol`,
this variation can be reduced to an equation of the form P(x) = n!, and it is thus
solved by the main theorem, `abc_Z_imp_poly_eq_fac_finite_sol`.-/
theorem abc_Z_imp_poly_eq_const_fac_finite_sol (P : ℤ[X]) (hdeg : P.degree ≥ 2) (c : ℤ) (hcne0 : c ≠ 0) :
  abc_Z → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , (P.eval x = c * n.factorial) → (n < N) ∧ (|x| < N)) := by

  set d := P.natDegree with hd
  intro abcz
  let f (i : ℕ) : ℤ := c * (i.factorial : ℤ)
  refine assume P hdeg f ?_
  unfold f
  set cn := c.natAbs
  haveI : NeZero cn := by exact neZero_iff.mpr (by exact Int.natAbs_ne_zero.mpr hcne0)
  let Q (i : Fin cn) : ℤ[X] := P.comp (X + C (i.val : ℤ))
  have hqd : ∀ i : Fin cn, (Q i).degree ≥ 2 := by
    intro i
    have hqi : (Q i).natDegree = (Q i).degree := by
      refine Eq.symm (degree_eq_natDegree ?_)
      unfold Q
      refine comp_X_add_C_ne_zero_iff.mpr (ne_zero_of_coe_le_degree hdeg)
    rw [←hqi]
    simp
    unfold Q
    rw [Polynomial.natDegree_comp]
    rw [natDegree_X_add_C ((i:ℕ):ℤ)]
    simp
    exact le_natDegree_of_coe_le_degree hdeg

  let N (i : Fin cn) : ℕ := by exact (abc_Z_imp_poly_eq_const_dvd_fac_finite_sol (Q i) (hqd i) c hcne0 abcz).choose
  have hn : ∀ (i : Fin cn) (n : ℕ) (x : ℤ), c ∣ x → eval x (Q i) = c * ↑n.factorial → n < N i ∧ |x| < N i := fun i ↦ (abc_Z_imp_poly_eq_const_dvd_fac_finite_sol (Q i) (hqd i) c hcne0 abcz).choose_spec
  obtain ⟨j, hj⟩ := Finite.exists_max N
  use N j
  intro n x hcc

  have hmod : x % c + (x / c) * c = x := by exact Int.emod_add_ediv' x c
  set r := x % c
  have hrdvd : c ∣ x - r := by
    rw [←hmod]
    simp
  set q := x / c
  have hr0 : 0 ≤ r := by exact Int.emod_nonneg x hcne0
  have hr_lt : r < cn := by exact Int.emod_lt x hcne0
  set r' := r.toNat
  have hf5 : r' = r := by
    unfold r'
    simp
    exact Int.emod_nonneg x hcne0
  have hr'cn : r' < cn := by
    zify
    rw [hf5]
    exact hr_lt
  set rf := Fin.mk r' hr'cn
  refine lt_of_lt_of_le ?_ (hj rf)
  specialize hn rf n (x - r) hrdvd
  choose he hee using hn
  refine he ?_
  convert hcc using 1
  simp [Q]
  congr
  refine Eq.symm ((fun {b a c} ↦ Int.sub_eq_iff_eq_add.mp) ?_)
  congr









--#print axioms abc_Z_imp_poly_eq_const_fac_finite_sol










#eval Nat.primeFactors 0
--#eval Finset.prod {∅} id
#check Finset.prod {2,4} id

--#print axioms radical


lemma Archimedes : ∀ ε : ℝ, ε > 0 → ∃ n : ℕ, 1 / n < ε := by
  intro e he
  use Nat.ceil (1 / e) + 1
  refine (one_div_lt he ?_).mp ?_
  · simp only [one_div, Nat.cast_add, Nat.cast_one]
    linarith
  · simp only [one_div, Nat.cast_add, Nat.cast_one]
    have h1 : e⁻¹ ≤ ⌈e⁻¹⌉₊ := by exact Nat.le_ceil e⁻¹
    have h2 : ⌈e⁻¹⌉₊ < ⌈e⁻¹⌉₊ + 1 := by linarith
    rify at h2
    exact lt_of_le_of_lt h1 h2


lemma sum_example (a b c : ℤ) (ha : a ≥ 0) (hb : b ≤ 0) (hc : c ≤ 0) (hsum : a + b = c) : a.toNat + c.natAbs = b.natAbs := by
  zify
  have h1 : a.toNat = a := by simp only [Int.ofNat_toNat, sup_eq_left.2 ha]
  have h2 : |b| = -b := by simp only [abs_eq_neg_self.2 hb]
  have h3 : |c| = -c := by simp only [abs_eq_neg_self.2 hc]
  rw [h1, h2, h3]
  omega


--defaultTargets = ["Bachelor_Project_StefanLica"]
