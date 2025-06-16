import Bachelor_Project_StefanLica.abc_variants
open Polynomial
open Real


/-!
# The abc-conjecture implies finite solutions to the equation P(x) = n!

This file consists of the main result, a proof of the generalized Brocard-Ramanujan
problem, conditional on the abc-conjecture: For any polynomial P with integer coefficients
and of degree at least 2, the quation `P(x) = n!` has finitely many pairs of integer solutions, (x,n).
It also consists of several lemmas, which are intermediate steps of the main proof, separated
from it in order to shorten it.
Moreover, it includes another proof of the original Brocard-Ramanujan problem by specializing
the main statement to P(x) = x² - 1.

-/



section notations_and_general_results_about_P
variable (P : ℤ[X])


-- Number definitions
def d' : ℕ := P.natDegree
local notation "d" => d' P
def ad' : ℤ := P.coeff d
local notation "ad" => ad' P
def c' : ℤ := d ^ d * ad ^ (d - 1)
local notation "c" => c' P
def b' (i : ℕ) : ℤ := P.coeff i * d ^ (d - i) * ad ^ (d - i - 1)
local notation "b" => b' P


-- Polynomial definitions
noncomputable def Qq' : ℤ[X] := X ^ d + ∑ i in Finset.range d, C (b i) * X ^ i
local notation "Qq" => Qq' P

noncomputable def Q' : ℤ[X] := (Qq).comp (X - C (P.coeff (d - 1)))
local notation "Q" => Q' P


lemma hPne0 (hdeg : P.degree ≥ 2) : P.degree ≠ ⊥ := by
  refine degree_ne_bot.mpr ?_
  exact ne_zero_of_coe_le_degree hdeg

lemma hpdeg (hdeg : P.degree ≥ 2) : P.degree = P.natDegree := by exact Polynomial.degree_eq_natDegree (degree_ne_bot.1 (hPne0 P hdeg))

lemma hd2 (hdeg : P.degree ≥ 2) : d ≥ 2 := by
  unfold d'
  refine le_natDegree_of_coe_le_degree ?_
  exact hdeg

lemma hadne0 (hdeg : P.degree ≥ 2) : ad ≠ 0 := by
  unfold ad' d'
  rw [Polynomial.coeff_natDegree]
  have hhelp : ¬ (P.degree = ⊥) → ¬ (P.leadingCoeff = 0) := by
    contrapose
    push_neg
    exact Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot.1
  push_neg at hhelp
  exact hhelp (hPne0 P hdeg)

lemma hcne0 (hdeg : P.degree ≥ 2) : c ≠ 0 := by
  unfold c'
  refine Int.mul_ne_zero_iff.mpr ?_
  constructor
  simp
  exact pow_ne_zero (d - 1) (hadne0 P hdeg)

lemma hcabsne1 (hdeg : P.degree ≥ 2) : |c| ≠ 1 := by
  have hd2l := hd2 P hdeg
  by_contra hc
  rw [←abs_one] at hc
  rw [abs_eq_abs] at hc
  cases hc with
  | inl h =>
    unfold c' at h
    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at h
    cases h with
    | inl hm1 =>
      choose hdd hadd using hm1
      rw [pow_eq_one_iff_of_ne_zero (very_simple d (hd2 P hdeg))] at hdd
      cases hdd with
      | inl hdd1 =>
        simp at hdd1
        rw [hdd1] at hd2l
        simp at hd2l
      | inr hdd2 =>
        choose hdm1 hdeven using hdd2
        simp at hdm1
    | inr hm2 =>
      choose hdm1 hdeven using hm2
      --have hdgt0 : 0 < d := by exact Nat.zero_lt_of_lt hd2l
      have hdgt0p : 0 < (d : ℤ) ^ d := by exact Lean.Omega.Int.pos_pow_of_pos (↑d) d (Int.natCast_pos.mpr (Nat.zero_lt_of_lt hd2l))
      rw [hdm1] at hdgt0p
      contradiction
  | inr h =>
    unfold c' at h
    rw [Int.mul_eq_neg_one_iff_eq_one_or_neg_one] at h
    cases h with
    | inl h =>
      let h1 := h.1
      rw [pow_eq_one_iff_of_ne_zero (very_simple d (hd2 P hdeg))] at h1
      cases h1 with
      | inl h1 =>
        simp at h1
        rw [h1] at h
        let hc9 := h.2
        simp at hc9
      | inr h1 =>
        have hdgt0 : 0 < (d : ℤ) := by
          simp
          exact Nat.pos_of_ne_zero (very_simple d (hd2 P hdeg))
        have hdlt0 : 0 > -1 := by linarith
        rw [←h1.1] at hdlt0
        contradiction
    | inr h =>
      let hc := h.1
      have hdgt0 : 0 < (d : ℤ) := by
        simp
        exact Nat.pos_of_ne_zero (very_simple d (hd2 P hdeg))
      have hdgt0p : 0 < (d : ℤ) ^ d := by exact Lean.Omega.Int.pos_pow_of_pos (↑d) d hdgt0
      rw [hc] at hdgt0p
      contradiction

lemma deg_if_then : ∀ i, (C (b i) * X ^ i).natDegree = if b i ≠ 0 then i else 0 := by
  intro i
  split_ifs with hbne0
  · exact natDegree_C_mul_X_pow i (b i) hbne0
  · push_neg at hbne0
    simp
    rw [hbne0]
    simp

lemma QqPdeg (hdeg : P.degree ≥ 2) : P.natDegree = (Qq).natDegree := by
  unfold Qq'
  have hdn0 : 0 < d := lt_of_le_of_lt (by simp) (hd2 P hdeg)
  have hso : ∀ i, C (b i) = ((b i) : ℤ[X]) := by exact fun i ↦ rfl
  rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
  exact Eq.symm (natDegree_X_pow d)
  refine Polynomial.degree_lt_degree ?_
  rw [natDegree_X_pow d]
  set U := ∑ i ∈ Finset.range d, C (b i) * X ^ i with HU
  have hineq : (∑ x ∈ Finset.range d, C (b x) * X ^ x).natDegree ≤ Finset.fold max 0 (natDegree ∘ fun i ↦ C (b i) * X ^ i ) (Finset.range d) := by exact Polynomial.natDegree_sum_le (Finset.range d) (fun i ↦ C (b i) * X ^ i )
  simp at hineq
  simp only [← hso] at hineq
  simp only [deg_if_then] at hineq
  rw [Finset.le_fold_max] at hineq
  cases hineq with
  | inl h =>
    simp at h
    simp only [← hso] at h
    rw [← HU] at h
    rw [h]
    exact hdn0
  | inr h =>
    obtain ⟨r, hr⟩ := h
    let h := hr.2
    have hq : (if b r ≠ 0 then r else 0) ≤ d - 1 := by
      split_ifs with hq0
      let ho := hr.1
      simp at ho
      exact (Nat.le_sub_one_iff_lt hdn0).mpr ho
      push_neg at hq0
      exact (Nat.le_sub_one_iff_lt hdn0).mpr hdn0
    have hq' : (if b r ≠ 0 then r else 0) < d := by exact Nat.lt_of_le_pred hdn0 hq
    rw [← HU] at h
    exact Nat.lt_of_le_of_lt h hq'

lemma PcompQq (hdeg : P.degree ≥ 2) : c • P = (Qq).comp ((ad * d) • X) := by
    simp
    unfold Qq'
    simp only [eq_intCast, add_comp, pow_comp, X_comp, sum_comp, mul_comp, intCast_comp]
    unfold b'
    simp
    refine Eq.symm (ext ?_)
    intro i
    simp
    by_cases hii : i > d
  -- case i > d :
    have hpci : P.coeff i = 0 := by
      unfold d' at hii
      exact coeff_eq_zero_of_natDegree_lt hii
    rw [hpci]
    simp
    have h1 : (((ad : ℤ[X]) * (d : ℤ[X]) * X) ^ d).coeff i = 0 := by
      have h11 : (ad : ℤ[X]) * (d : ℤ[X]) = C (ad * d) := by simp
      rw [h11]
      have h12 : (C (ad * ↑d) * X) ^ d = (C (ad * ↑d)) ^ d * X ^ d := by ring
      rw [h12]
      have h13 : (C (ad * ↑d)) ^ d = C ((ad * ↑d) ^ d) := by exact Eq.symm C_pow
      rw [h13]
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs with hi
      have hneg : ¬ (i = d) := by exact Nat.ne_of_lt' hii
      absurd hi
      exact hneg
      simp
    rw [h1]
    simp
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp at hj
    have h11 : (ad : ℤ[X]) * (d : ℤ[X]) = C (ad * d) := by simp
    rw [h11]
    have h12 : (C (ad * ↑d) * X) ^ j = (C (ad * ↑d)) ^ j * X ^ j := by ring
    have h13 : (C (ad * ↑d)) ^ j = C ((ad * ↑d) ^ j) := by exact Eq.symm C_pow
    rw [h12, h13]
    set cj := (P.coeff j : ℤ[X])
    have hcj : cj = C (P.coeff j) := by exact rfl
    set q := C ((ad * ↑d) ^ j)
    set a := (ad : ℤ[X]) ^ (d - j - 1)
    set e := (d : ℤ[X]) ^ (d - j)
    set f := cj * e * a
    have h14 : (f * (q * X ^ j)) = (f * q * X ^ j) := by ring
    rw [h14]
    set g := f * q
    rw [Polynomial.coeff_mul_X_pow']
    simp
    intro hji
    have hijn : i ≠ j := by
      by_contra hc
      rw [hc] at hii
      have hiii : j ≥ d := by exact Nat.le_of_succ_le hii
      have hic : ¬ (j < d) := by exact Nat.not_lt.mpr hiii
      absurd hic
      exact hj
    have hij0 : i - j ≠ 0 := by
      refine Nat.sub_ne_zero_iff_lt.mpr ?_
      exact Nat.lt_of_le_of_ne hji (id (Ne.symm hijn))
    have ha : C (ad) ^ (d - j - 1) = C (ad ^ (d - j - 1)) := by exact Eq.symm C_pow
    have ha1 : a = C (ad ^ (d - j - 1)) := by exact ha
    have he : C (d : ℤ) ^ (d - j) = C ((d : ℤ) ^ (d - j)) := by exact Eq.symm C_pow
    have he1 : e = C ((d : ℤ) ^ (d - j)) := by exact he
    have hg : g = (C (P.coeff j) * C ((d : ℤ) ^ (d - j)) * C (ad ^ (d - j - 1))) * C ((ad * ↑d) ^ j) := by rw [←hcj, ←he1, ← ha1]
    have hgg : g = C ((P.coeff j) * ((d : ℤ) ^ (d - j)) * (ad ^ (d - j - 1))* ((ad * ↑d) ^ j)) := by
      simp
      simp at hg
      exact hg
    set l := (P.coeff j) * ((d : ℤ) ^ (d - j)) * (ad ^ (d - j - 1))* ((ad * ↑d) ^ j)
    rw [hgg]
    set dif := i - j
    exact Polynomial.coeff_C_ne_zero hij0

  -- case i ≤ d :
    push_neg at hii
    have h123 : ((ad : ℤ[X]) * (d : ℤ[X]) * X) ^ d = C (ad * d) ^ d * X ^ d := by
      simp
      ring
    have h1234 : C (ad * d) ^ d = C ((ad * d) ^ d) := by exact Eq.symm C_pow
    rw [h1234] at h123
    by_cases hiii : i = d
  -- case i = d :
    rw [hiii]
    rw [h123]
    have hw : (C ((ad * d) ^ d) * X ^ d).coeff d = (ad * d) ^ d := by
      rw [Polynomial.coeff_C_mul_X_pow]
      simp
    rw [hw]
    have hcoef0 : ∑ j ∈ Finset.range d, ((P.coeff j : ℤ[X]) * (d:ℤ[X]) ^ (d - j) * (ad:ℤ[X]) ^ (d - j - 1) * ((ad:ℤ[X]) * (d:ℤ[X]) * X) ^ j).coeff d = 0 := by
      ring_nf
      simp only [←Polynomial.C_eq_intCast, ←Polynomial.C_eq_natCast, ←Polynomial.C_pow]
      repeat simp only [←Polynomial.C_mul]
      simp only [Int.cast_id]
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp
    rw [hcoef0]
    simp
    unfold c'
    ring_nf
    have hd11 : 1 ≤ d := by
      unfold d'
      refine le_natDegree_of_coe_le_degree ?_
      simp
      exact le_trans (by simp) hdeg
    have hadp :  ad * ad ^ (d - 1) = ad ^ d := by
      have had1 : ad * ad ^ (d - 1) = ad ^ 1 * ad ^ (d - 1) := by simp
      rw [had1]
      exact pow_mul_pow_sub ad (hd11)
    have haad : ad = P.coeff d := by
      unfold ad'
      simp
    rw [← haad]
    ring_nf
    rw [hadp]
  -- case i ≠ d :
    push_neg at hiii
    have hidlt : i < d := by exact Nat.lt_of_le_of_ne hii hiii
    ring_nf
    have hrrr : ∑ x ∈ Finset.range d, ((ad:ℤ[X]) ^ (d - x - 1) * (ad:ℤ[X]) ^ x * (d:ℤ[X]) ^ (d - x) * (d:ℤ[X]) ^ x * X ^ x * (P.coeff x : ℤ[X])).coeff i = ∑ x ∈ Finset.range d, ((ad:ℤ[X]) ^ (d - x - 1) * (ad:ℤ[X]) ^ x * (d:ℤ[X]) ^ (d - x) * (d:ℤ[X]) ^ x * (P.coeff x : ℤ[X]) * X ^ x).coeff i  := by ring_nf
    rw [hrrr]
    simp only [←Polynomial.C_eq_intCast, ←Polynomial.C_eq_natCast, ←Polynomial.C_pow]
    repeat simp only [←Polynomial.C_mul]
    rw [Polynomial.coeff_C_mul_X_pow]
    have h11 : (if i = d then ad ^ d * ↑d ^ d else 0) = 0 := by
      simp
      intro hfa
      absurd hiii
      exact hfa
    simp only [Int.cast_id]
    rw [h11]
    simp only [zero_add]
    simp only [Polynomial.coeff_C_mul_X_pow]
    simp
    have h12 : (if i < d then ad ^ (d - i - 1) * ad ^ i * ↑d ^ (d - i) * ↑d ^ i * P.coeff i else 0) = ad ^ (d - i - 1) * ad ^ i * ↑d ^ (d - i) * ↑d ^ i * P.coeff i := by
      split_ifs
      simp
    rw [h12]
    unfold c'
    ring_nf
    refine Lean.Omega.Int.mul_congr ?_ rfl
    have hdrpo : (d:ℤ) ^ (d - i) * ↑d ^ i = d ^ d := by
      rw [mul_comm]
      exact pow_mul_pow_sub (d:ℤ) hii
    rw [mul_comm] at hdrpo
    conv_lhs => rw [mul_assoc, mul_assoc, hdrpo, ←mul_assoc]
    refine Lean.Omega.Int.mul_congr ?_ rfl
    have hfinal : ad ^ i * ad ^ (d - i - 1) = ad ^ (d - 1) := by
      have hrr : d - i - 1 = d - 1 - i := by exact Nat.sub_right_comm d i 1
      simp only [hrr]
      set d1 := d - 1
      refine pow_mul_pow_sub (m := i) (n := d1) ad ?_
      unfold d1
      exact Nat.le_sub_one_of_lt hidlt
    rw [mul_comm]
    exact hfinal

lemma hQdegree (hdeg : P.degree ≥ 2) : (Q).natDegree = P.natDegree := by
  unfold Q'
  rw [Polynomial.natDegree_comp]
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  simp
  exact Eq.symm (QqPdeg P hdeg)
  simp

lemma hQmonic : (Q).Monic := by
  unfold Q'
  refine Polynomial.Monic.comp ?_ ?_ ?_
  refine Monic.add_of_left (monic_X_pow d) ?_
  rw [degree_X_pow]
  simp
  rw [← Fin.sum_univ_eq_sum_range]
  apply Polynomial.degree_sum_fin_lt (fun i : Fin d => b i)
  change (X - C (P.coeff (d - 1))).Monic
  apply Polynomial.monic_X_sub_C
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
  simp

lemma hQprw (hdeg : P.degree ≥ 2) : ∀ x : ℤ, P.eval x = (((Qq).comp ((ad * d) • X)).eval x) / c := by
  intro x
  have hPrw := fun x ↦ congrArg (eval x) (PcompQq P hdeg)
  specialize hPrw x
  simp at hPrw
  refine Int.eq_ediv_of_mul_eq_right (hcne0 P hdeg) ?_
  rw [hPrw]
  simp

lemma Q_change_var_cancel_term (hdeg : P.degree ≥ 2) : (Q).coeff (P.natDegree - 1) = 0 := by
  have hq : Q = (Qq).comp (X - C (P.coeff (d - 1))) := rfl
  have hqq : Qq = X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i := rfl
  have hd : P.natDegree = d := rfl
  have hdd12 : (d - (d - 1)) = 1 := by
    set r := d - 1
    have hr : d = r + 1 := by
      unfold r
      refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
      have hPne0 : P.degree ≠ ⊥ := by
        refine degree_ne_bot.mpr ?_
        exact ne_zero_of_coe_le_degree hdeg
      have hpdeg : P.degree = P.natDegree := by exact Polynomial.degree_eq_natDegree (degree_ne_bot.1 hPne0)
      unfold d'
      refine le_natDegree_of_coe_le_degree ?_
      have hbot : 1 ≤ (2 : WithBot ℕ) := by exact one_le_two
      exact Preorder.le_trans (↑1) 2 P.degree hbot hdeg
    rw [hr]
    simp
  rw [hq, hqq]
  simp
  have hrw : X - (P.coeff (d - 1) : ℤ[X]) = X + ( - (P.coeff (d - 1) : ℤ[X])) := by ring
  rw [hrw]
  set co := - (P.coeff (d - 1))
  have hco : - ((P.coeff (d - 1)) : ℤ[X]) = (co : ℤ[X]) := by
    unfold co
    exact Eq.symm (Int.cast_neg (P.coeff (d - 1)))
  rw [hco]
  have hc : (co : ℤ[X]) = C (co) := by exact rfl
  rw [hc]
  rw [Polynomial.coeff_X_add_C_pow]
  have hchoose : (d).choose (d - 1) = d := by
    have hdd1 : d - 1 ≤ d := by exact Nat.sub_le d 1
    have hhelp : (d).choose (d - 1) * (d - 1).factorial * (d - (d - 1)).factorial = (d).factorial := by exact Nat.choose_mul_factorial_mul_factorial hdd1
    rw [hdd12] at hhelp
    simp at hhelp
    have h1 : (d).choose (d - 1) = (d).factorial / (d - 1).factorial := by
      rw [mul_comm] at hhelp
      refine Nat.eq_div_of_mul_eq_right (by exact Nat.factorial_ne_zero (d - 1)) hhelp
    have h2 : (d).factorial / (d - 1).factorial = d := by
      have hee : d = (d - 1) + 1 := by exact (Nat.sub_eq_iff_eq_add' hdd1).mp hdd12
      have he : (d).factorial = ((d - 1) + 1).factorial := by exact congrArg Nat.factorial hee
      rw [he]
      rw [Nat.factorial_succ]
      rw [← hee]
      refine Eq.symm (Nat.eq_div_of_mul_eq_left ?_ rfl)
      exact Nat.factorial_ne_zero (d - 1)
    rw [h2] at h1
    exact h1
  rw [hd, hchoose, hdd12]
  simp only [pow_one]
  simp only [Polynomial.coeff_X_add_C_pow]
  have hichoose : ∀ i ∈ Finset.range (d - 1), i.choose (d - 1) = 0 := by
    intro i hi
    simp at hi
    exact Nat.choose_eq_zero_of_lt hi
  have hfs : Finset.range d = (Finset.range (d - 1)) ∪ {d - 1} := by
    have hdr : d = (d - 1) + 1 := by omega
    conv_lhs =>
      rw [hdr]
    rw [Finset.range_add_one]
    rw [Finset.insert_eq]
    exact Finset.union_comm {d - 1} (Finset.range (d - 1))
  rw [hfs]
  rw [Finset.sum_union]
  swap
  simp
  simp
  have hsum : ∑ x ∈ Finset.range (d - 1), b x * (co ^ (x - (d - 1)) * (x.choose (d - 1))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    refine Int.mul_eq_zero.mpr ?_
    rw [Or.comm]
    constructor
    exact mul_eq_zero_of_right (co ^ (i - (d - 1))) (congrArg Nat.cast (hichoose i hi))
  rw [hsum]
  simp
  have hbu : b (d - 1) = P.coeff (d - 1) * d := by
    unfold b'
    rw [mul_assoc]
    simp
    constructor
    rw [hdd12]
    simp
  rw [hbu]
  unfold co
  simp

lemma Qq_eval_fac (hdeg : P.degree ≥ 2) (n : ℕ) (x : ℤ) (hi : P.eval x = n.factorial) : (Qq).eval (ad * d * x) = c * n.factorial := by
  have hd1 : d ≥ 1 := by exact Nat.one_le_of_lt (hd2 P hdeg)
  rw [hQprw] at hi
  simp at hi
  conv_rhs =>
    rw [mul_comm]
  refine (Int.ediv_eq_iff_eq_mul_left (hcne0 P hdeg) ?_).mp hi
  have hQq : Qq = X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i := rfl
  have hbu : b = fun i ↦ P.coeff i * ↑d ^ (d - i) * ad ^ (d - i - 1) := rfl
  have hc : c = ↑d ^ d * ad ^ (d - 1) := rfl
  have hc1diveval : c ∣ eval (ad * ↑d * x) Qq := by
    have h1 : (Qq).eval (ad * ↑d * x) = (ad * ↑d * x) ^ d + ∑ i ∈ Finset.range d, (b i) * (ad * (d:ℤ) * x) ^ i := by
      have h11 : (Qq).eval (ad * ↑d * x) = (X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i).eval (ad * (d:ℤ) * x) := by exact congrArg (eval (ad * ↑d * x)) hQq
      simp at h11
      have h12 : (∑ i ∈ Finset.range d, C (b i) * X ^ i).eval (ad * (d:ℤ) * x) = ∑ i ∈ Finset.range d, (C (b i) * X ^ i).eval (ad * (d:ℤ) * x) := by exact eval_finset_sum (Finset.range d) (fun i ↦ C (b i) * X ^ i) (ad * ↑d * x)
      simp at h12
      rw [h12] at h11
      exact h11
    have h2 : ∀ i ∈ Finset.range d, b i * (ad * ↑d * x) ^ i = P.coeff i * (d ^ d * ad ^ (d - 1) * x ^ i) := by
      intro i hfi
      simp_rw [hbu]
      rw [mul_assoc, mul_assoc]
      refine Eq.symm (Lean.Omega.Int.mul_congr rfl ?_)
      have hrw : (ad * ↑d * x) ^ i = ad ^ i * d ^ i * x ^ i := by ring
      rw [hrw]
      ring_nf
      have hrwd : (d:ℤ) ^ i * ↑d ^ (d - i) = d ^ d := by exact pow_mul_pow_sub (d:ℤ) (Finset.mem_range_le hfi)
      have hrwad :  ad ^ i * ad ^ (d - i - 1) = ad ^ (d - 1) := by
        have hrr : d - i - 1 = d - 1 - i := by exact Nat.sub_right_comm d i 1
        simp only [hrr]
        set d1 := d - 1
        refine pow_mul_pow_sub (m := i) (n := d1) ad ?_
        unfold d1
        simp at hfi
        exact Nat.le_sub_one_of_lt hfi
      rw [hrwd]
      conv_rhs => rw [mul_comm, mul_assoc, hrwad, mul_comm]
    rw [Finset.sum_congr rfl h2] at h1
    have h3 : ∑ i ∈ Finset.range d, P.coeff i * (↑d ^ d * ad ^ (d - 1) * x ^ i) = ↑d ^ d * ad ^ (d - 1) * ∑ i ∈ Finset.range d, P.coeff i * x ^ i := by
      have h31 : ∀ i ∈ Finset.range d, P.coeff i * (↑d ^ d * ad ^ (d - 1) * x ^ i) = (↑d ^ d * ad ^ (d - 1)) * (P.coeff i * x ^ i) := by
        intro i hif
        ring
      conv_lhs => rw [Finset.sum_congr rfl h31]
      exact Eq.symm (Finset.mul_sum (Finset.range d) (fun i ↦ P.coeff i * x ^ i) (↑d ^ d * ad ^ (d - 1)))
    rw [h3] at h1
    set s := ∑ i ∈ Finset.range d, P.coeff i * x ^ i
    have h4 : (ad * ↑d * x) ^ d + ↑d ^ d * ad ^ (d - 1) * s = d ^ d * ad ^ (d - 1) * (ad * x ^ d + s) := by
      have hrw : (ad * ↑d * x) ^ d = ad ^ d * d ^ d * x ^ d := by ring
      rw [hrw]
      have hrwad : ad ^ d = ad * ad ^ (d - 1) := by
        apply Eq.symm ?_
        have had1 : ad * ad ^ (d - 1) = ad ^ 1 * ad ^ (d - 1) := by simp
        rw [had1]
        refine pow_mul_pow_sub ad hd1
      rw [hrwad]
      have hrw1 : ad * ad ^ (d - 1) * ↑d ^ d * x ^ d = (ad ^ (d - 1) * ↑d ^ d) * (ad * x ^ d) := by ring
      rw [hrw1]
      ring
    rw [h4] at h1
    rw [h1]
    rw [hc]
    exact Int.dvd_mul_right (↑d ^ d * ad ^ (d - 1)) (ad * x ^ d + s)
  exact hc1diveval
  exact hdeg

lemma QqQ (x : ℤ) : (Q).eval (ad * d * x + P.coeff (d - 1)) = (Qq).eval (ad * d * x) := by
  unfold Q'
  simp



noncomputable def R' : ℤ[X] := ∑ i ∈ Finset.range (d - 1), C ((Q).coeff i) * X ^ i
local notation "R" => R' P

noncomputable def SR' := (R).support
local notation "SR" => SR' P




lemma hqrh (hdeg : P.degree ≥ 2) : ∀ i ∈ Finset.range (d - 1), (Q).coeff i = (R).coeff i := by
  intro i hd1
  simp at hd1
  have hQ : (Q) = X ^ (Q).natDegree + ∑ i ∈ Finset.range (Q).natDegree, C ((Q).coeff i) * X ^ i := by exact Monic.as_sum (hQmonic P)
  rw [hQ]
  simp only [eq_intCast, coeff_add]
  have hqdd : (Q).natDegree = d := by
    unfold d'
    exact hQdegree P hdeg
  rw [hqdd]
  have hxc : ((X : ℤ[X]) ^ d).coeff i = 0 := by
    rw [Polynomial.coeff_X_pow]
    split_ifs with hci
    have hid : i ≥ d := by exact Nat.le_of_eq (id (Eq.symm hci))
    have hidc2 : i < d := by exact Nat.lt_of_lt_pred hd1
    have hidc : ¬ (i ≥ d) := by exact Nat.not_le_of_lt hidc2
    absurd hidc
    exact hid
    simp
  rw [hxc]
  simp
  split_ifs with hid
  unfold R'
  simp
  intro hc
  absurd hc
  push_neg
  exact Nat.add_lt_of_lt_sub hd1
  absurd hid
  exact Nat.lt_of_lt_pred hd1


lemma hsrn (hr : R ≠ 0) : (SR).Nonempty := by
  unfold SR'
  simp
  exact hr


lemma hSRmin (hr : R ≠ 0) : (SR).min' (hsrn P hr) ∈ SR := by exact Finset.min'_mem SR (hsrn P hr)



noncomputable def j' (hr : R ≠ 0) := (SR).min' (hsrn P hr)
local notation "j" => j' P



lemma hjd  (hr : R ≠ 0) : (j hr) ≤ d - 1 := by
  have hsrmin := hSRmin P hr
  have hjdef : (j hr) = (SR).min' (hsrn P hr) := by
    unfold j'
    simp
  rw [←hjdef] at hsrmin
  unfold SR' R' at hsrmin
  simp at hsrmin
  let h1111 := hsrmin.1
  exact le_of_lt h1111

lemma hjd2 (hdeg : P.degree ≥ 2) (hr : R ≠ 0) : (j hr) ≤ d - 2 := by
  have hsrmin := hSRmin P hr
  have hjdef : (j hr) = (SR).min' (hsrn P hr) := by
    unfold j'
    simp
  rw [←hjdef] at hsrmin
  -- set nj := (j hr)
  unfold SR' R' at hsrmin
  simp at hsrmin
  choose h1 h2 using hsrmin
  have hdge2 := hd2 P hdeg
  omega


lemma hrj (hdeg : P.degree ≥ 2) (hr : R ≠ 0) : R = ∑ i ∈ (Finset.range (d - 1) \ Finset.range (j hr)), C ((Q).coeff i) * X ^ i := by
  have hrange : Finset.range (d - 1) = (Finset.range (d - 1) \ Finset.range (j hr)) ∪ Finset.range (j hr) := by
    simp
    exact hjd P hr
  set nj := j hr
  have hR : R = ∑ i ∈ Finset.range (d - 1), C ((Q).coeff i) * X ^ i := by
    unfold R'
    simp
  rw [hrange, Finset.sum_union] at hR
  swap
  have hdisj : Disjoint (Finset.range (d - 1) \ Finset.range nj) (Finset.range nj) := by
    rw [disjoint_comm]
    exact Finset.disjoint_sdiff
  exact hdisj
  have hjtail : ∑ x ∈ Finset.range nj, C ((Q).coeff x) * X ^ x = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hji
    simp at hji
    simp
    have hirange : i ∈ Finset.range (d - 1) := by
      simp
      exact Nat.lt_of_lt_of_le hji (hjd P hr)
    --specialize hqrh i hirange
    rw [hqrh P hdeg]
    unfold nj j' at hji
    simp at hji
    have hisr : i ∉ SR := by
      contrapose hji
      push_neg at hji ⊢
      use i
    unfold SR' at hisr
    exact Polynomial.notMem_support_iff.1 hisr
    exact hirange
  rw [hjtail] at hR
  simp at hR ⊢
  exact hR

lemma hrjc (hdeg : P.degree ≥ 2) (hr : R ≠ 0) : R = X ^ (j hr) * ∑ i ∈ (Finset.range (d - 1) \ Finset.range (j hr)), C ((Q).coeff i) * X ^ (i - (j hr)) := by
  rw [Finset.mul_sum]
  rw [hrj P hdeg hr]
  refine Finset.sum_congr ?_ ?_
  simp
  intro i hira
  conv_rhs =>
    rw [mul_comm]
    rw [mul_assoc]
    rw [←pow_add]
  have hhelp : i - (j hr) + (j hr) = i := by
    apply Nat.sub_add_cancel ?_
    simp at hira
    exact hira.2
  rw [hhelp]


lemma QR (hdeg : P.degree ≥ 2) : Q = X ^ d + R := by
  unfold R'
  have hQ : Q = X ^ (Q).natDegree + ∑ i ∈ Finset.range (Q).natDegree, C ((Q).coeff i) * X ^ i := by exact Monic.as_sum (hQmonic P)
  have hQ' : ∑ i ∈ Finset.range d, C ((Q).coeff i) * X ^ i = ∑ i ∈ Finset.range (d - 1), C ((Q).coeff i) * X ^ i := by
    have hfs : Finset.range d = (Finset.range (d - 1)) ∪ {d - 1} := by
      have homega : d ≥ 2 := hd2 P hdeg
      have hdr : d = (d - 1) + 1 := by omega
      conv_lhs =>
        rw [hdr]
      rw [Finset.range_add_one]
      rw [Finset.insert_eq]
      exact Finset.union_comm {d - 1} (Finset.range (d - 1))
    rw [hfs]
    rw [Finset.sum_union (by simp)]
    have hdm1 : ∑ x ∈ {d - 1}, C ((Q).coeff x) * X ^ x = 0 := by
      simp
      exact Q_change_var_cancel_term P hdeg
    rw [hdm1]
    simp
  have hdqd : (Q).natDegree = d := by
    unfold d'
    exact hQdegree P hdeg
  rw [hdqd] at hQ
  conv_lhs => rw [hQ]
  rw [hQ']





noncomputable def R1' (hr : R ≠ 0) : ℤ[X] := ∑ i ∈ Finset.range (d - 1) \ Finset.range (j hr), C ((Q).coeff i) * X ^ (i - (j hr))
local notation "R1" => R1' P

lemma QR1 (hdeg : P.degree ≥ 2) (hr : R ≠ 0) : Q = X ^ d + X ^ (j hr) * (R1 hr) := by
  have hq := QR P hdeg
  have h1 : R = X ^ (j hr) * (R1 hr) := by
    unfold R1'
    rw [hrjc P hdeg hr]
  rw [h1] at hq
  exact hq



lemma R1nebot (hdeg : P.degree ≥ 2) (hr : R ≠ 0) : (R1 hr).degree ≠ ⊥ := by
  simp
  have hr1def : (R1 hr) = ∑ i ∈ Finset.range (d - 1) \ Finset.range (j hr), C ((Q).coeff i) * X ^ (i - (j hr)) := rfl
  have hhrjc := hrjc P hdeg hr
  rw [←hr1def] at hhrjc
  by_contra hc
  rw [hc] at hhrjc
  simp at hhrjc
  absurd hr
  exact hhrjc


--/-- Intermediate result applying the polynomial asymptotic lemmas to the main proof-/
lemma h15_asymp (hdeg : P.degree ≥ 2) (hr : R ≠ 0) : ∃ C4 C3 : ℕ, ∀ z : ℤ, C4 > 1 ∧ C3 > 1 ∧ ((|z| > C4) → |(R1 hr).eval z| < (C3:ℝ) * (|z| ^ (d - (j hr) - 2))) := by
  set NR := R1 hr with HNR
  set dr := NR.natDegree with hdr
  have hnrdef :  NR = ∑ i ∈ Finset.range (d - 1) \ Finset.range (j hr), C ((Q).coeff i) * X ^ (i - (j hr)) := by
    unfold NR
    rfl
  have hnrd : NR.degree ≠ ⊥ := by
    unfold NR
    exact R1nebot P hdeg hr
  have hdrb : ↑dr = NR.degree := by
    unfold dr
    apply Eq.symm (degree_eq_natDegree (Polynomial.degree_ne_bot.1 hnrd))
  have hlc : NR.leadingCoeff ≠ 0 := by
    unfold Polynomial.leadingCoeff
    rw [←hdr]
    exact Polynomial.coeff_ne_zero_of_eq_degree (id (Eq.symm hdrb))
  have hr1de : NR.natDegree ≤ d - (j hr) - 2 := by
    have hlee : ∀ i ∈ Finset.range (d - 1) \ Finset.range (j hr), (C ((Q).coeff i) * X ^ (i - (j hr))).natDegree ≤ d - (j hr) - 2 := by
      intro i hidj
      simp at hidj
      have hcxde : (C ((Q).coeff i) * X ^ (i - (j hr))).degree ≤ ↑(i - (j hr)) := by exact degree_C_mul_X_pow_le (i - (j hr)) ((Q).coeff i)
      rw [←Polynomial.natDegree_le_iff_degree_le] at hcxde
      have hf : i - (j hr) ≤ d - (j hr) - 2 := by omega
      exact Nat.le_trans hcxde hf
    rw [hnrdef]
    exact Polynomial.natDegree_sum_le_of_forall_le (Finset.range (d - 1) \ Finset.range (j hr)) (fun i ↦ C ((Q).coeff i) * X ^ (i - (j hr))) hlee
  let RR : ℝ[X] := NR.map (Int.castRingHom ℝ)
  have hrr : RR.leadingCoeff ≠ 0 := by
    simp [RR, leadingCoeff_map]
    push_neg
    refine (Polynomial.map_ne_zero_iff (by exact RingHom.injective_int (Int.castRingHom ℝ))).mpr ?_
    exact leadingCoeff_ne_zero.mp hlc
  have hdrr1 : NR.natDegree = RR.natDegree := by
    unfold RR
    apply Eq.symm ?_
    exact natDegree_map_eq_of_injective (by exact RingHom.injective_int (Int.castRingHom ℝ)) NR
  have hrde : RR.natDegree ≤ d - (j hr) - 2 := by
    rw [←hdrr1]
    exact hr1de
  obtain ⟨nr, lemma1⟩ := poly_asymp_general RR hrr
  let C4 := nr + 1
  use C4, (2 * (NR.leadingCoeff).natAbs + 1)
  intro x
  specialize lemma1 x
  choose nrgt hl using lemma1
  constructor
  unfold C4
  simp
  exact nrgt
  constructor
  zify
  simp
  exact leadingCoeff_ne_zero.mp hlc
  intro hzc4
  have hxgtnr : |(x:ℝ)| > nr := by
    unfold C4 at hzc4
    rify at hzc4
    exact gt_trans hzc4 (lt_add_one (nr:ℝ))
  specialize hl hxgtnr
  choose hl1 hl2 using hl
  have hl2r1 : |NR.eval x| < 2 * |NR.leadingCoeff| * |x| ^ NR.natDegree := by
    have hu1 : |NR.eval x| = |RR.eval (x:ℝ)| := by
      simp
      refine abs_eq_abs.mpr ?_
      constructor
      unfold RR
      simp
    have hu2 : 2 * |NR.leadingCoeff| * |x| ^ NR.natDegree = 2 * |RR.leadingCoeff| * |(x:ℝ)| ^ RR.natDegree := by
      rw [mul_assoc, mul_assoc]
      simp
      have h1 : |(NR.leadingCoeff : ℝ)| = |RR.leadingCoeff| := by
        refine abs_eq_abs.mpr ?_
        constructor
        unfold RR
        rw [Polynomial.leadingCoeff_map' (RingHom.injective_int (Int.castRingHom ℝ)) NR]
        simp
      have h2 : |(x:ℝ)| ^ NR.natDegree = |↑x| ^ RR.natDegree := by exact congrArg (HPow.hPow |(x:ℝ)|) hdrr1
      exact Mathlib.Tactic.LinearCombination'.mul_pf h1 h2
    rify
    simp at hu1 hu2
    rw [hu1, hu2]
    exact hl2
  have hrif : (NR.leadingCoeff.natAbs : ℝ) = |NR.leadingCoeff| := by exact Nat.cast_natAbs NR.leadingCoeff
  simp
  rw [hrif]
  have hf :  2 * |NR.leadingCoeff| * |x| ^ NR.natDegree ≤ (2 * |NR.leadingCoeff| + 1) * |x| ^ (d - (j hr) - 2) := by
    refine Int.mul_le_mul (by simp) ?_ (pow_nonneg (by simp) NR.natDegree) (Int.add_nonneg (by simp) (by simp))
    refine (pow_le_pow_iff_right₀ ?_).mpr hr1de
    unfold C4 at hzc4
    simp at hzc4
    exact Int.lt_trans (Int.lt_add_of_pos_left 1 (Int.natCast_pos.mpr nrgt)) hzc4
  rify at hl2r1 hf
  simp
  exact lt_of_lt_of_le hl2r1 hf



noncomputable def D' (hr : R ≠ 0) (x : ℤ) : ℕ := Int.gcd (x ^ (d - (j hr))) ((R1 hr).eval x)
local notation "D" => D' P

lemma D1 (x : ℤ) (hr : R ≠ 0) : ((D hr x) : ℤ) ∣ x ^ (d - (j hr)) := by
  unfold D'
  exact Int.gcd_dvd_left _ _

lemma D2 (x : ℤ) (hr : R ≠ 0) : ((D hr x) : ℤ) ∣ |(R1 hr).eval x| := by
  have h11 : ((D hr x) : ℤ) ∣ (R1 hr).eval x := by
    unfold D'
    exact Int.gcd_dvd_right _ _
  have h12 : (R1 hr).eval x ∣ |(R1 hr).eval x| := by exact self_dvd_abs (eval x (R1 hr))
  exact Int.dvd_trans h11 h12

lemma D3 (x : ℤ) (hr : R ≠ 0) : (x ≠ 0 → (D hr x) > 0) := by
  intro hx0
  refine Nat.pos_of_ne_zero ?_
  unfold D'
  refine Nat.gcd_ne_zero_left ?_
  simp only [ne_eq, Int.natAbs_eq_zero, pow_eq_zero_iff']
  push_neg
  intro hxc
  absurd hx0
  exact hxc




/-- `Rzero_imp_false` proves that the case when the polynomial R, defined in the proof, is
identically zero leads to contradiction-/
lemma Rzero_imp_false (hdeg : P.degree ≥ 2) (n : ℕ) (x : ℤ) (hii : x ^ d = c * n.factorial) (hb : n > 2 * |c|) : False := by
  have hc1gt0 : c > 0 := by
    by_cases hdpar : Odd d
  -- case Odd d :
    have hadpow : ad ^ (d - 1) > 0 := by
      have hd1e : Even (d - 1) := by exact Nat.Odd.sub_odd hdpar (by exact Nat.odd_iff.mpr rfl)
      exact Even.pow_pos hd1e (hadne0 P hdeg)
    have hddpow : d ^ d > 0 := by exact Nat.pow_self_pos
    unfold c'
    zify at hddpow
    exact Int.mul_pos hddpow hadpow
  -- case Even d :
    rw [Nat.not_odd_iff_even] at hdpar
    have hxvne0 : x ^ d ≠ 0 := by
      rw [hii]
      simp
      constructor
      exact (hcne0 P hdeg)
      exact Nat.factorial_ne_zero n
    have hxv : x ≠ 0 := by exact ne_zero_pow (very_simple d (hd2 P hdeg)) hxvne0
    have hxvgt0 : x ^ d > 0 := by exact Even.pow_pos hdpar hxv
    rw [hii] at hxvgt0
    have hfac0 : n.factorial > 0 := by exact Nat.factorial_pos n
    zify at hfac0
    exact (pos_iff_pos_of_mul_pos hxvgt0).2 hfac0
  have hcom : n > 2 * c := by
    have hinter : 2 * |c| ≥ 2 * c := by
      simp
      exact le_abs_self c
    exact lt_of_le_of_lt hinter hb
  have hassume2 : n ≥ 2 := by
    have hc12 : 2 * c ≥ 2 := by exact (le_mul_iff_one_le_right (by simp)).mpr hc1gt0
    zify
    have hf := lt_of_le_of_lt hc12 hcom
    exact Int.le_of_lt hf


  have hprime : ∃ p : ℕ, Nat.Prime p ∧ n/2 < p ∧ p ≤ n := by
    have hnb : n / 2 ≠ 0 := by
      simp
      exact hassume2
    have hph : ∃ p : ℕ, Nat.Prime p ∧ n/2 < p ∧ p ≤ 2 * (n/2) := by exact Nat.bertrand (n/2) hnb
    obtain ⟨p, hi⟩ := hph
    let hchange := hi.2.2
    have hch : 2 * (n/2) ≤ n := by exact Nat.mul_div_le n 2
    have htrans : p ≤ n := by exact Nat.le_trans hchange hch
    let hi1 := hi.1
    let hi2 := hi.2.1
    use p
  obtain ⟨p, hp⟩ := hprime
  let hp1 := hp.1
  let hp2 := hp.2.1
  have h2' : n < 2 * p := by omega
  have hpdiv : p ∣ n.factorial := by
    refine Nat.dvd_factorial ?_ ?_
    exact Nat.zero_lt_of_lt hp2
    exact hp.2.2
  have h3' : ¬ (2 * p ∣ n) := by
    by_contra h
    have hc : 2 * p ≤ n := by exact Nat.le_of_dvd (by exact Nat.zero_lt_of_ne_zero (by exact Nat.ne_zero_of_lt hassume2)) h
    rw [← Nat.not_lt] at hc
    contradiction
  have h5' : (n.factorial).factorization p = 1 := by exact fac_fact_helper_h5'' n p hassume2 hp h2'
  zify at hp2
  have hps : c < p := by
    refine (mul_lt_mul_left (a := 2) (by linarith)).1 ?_
    zify at h2'
    exact Int.lt_trans hcom h2'
  have h8 : ¬ ((p:ℤ) ∣ c) := by
    by_contra hi
    have hc1' : p ≤ c := by exact Int.le_of_dvd hc1gt0 hi
    have hcontradi : ¬ (p > c) := by exact Int.not_lt.mpr hc1'
    contradiction
  have h9' : ∀ k : ℕ, k ≥ 2 → ¬ (p ^ k ∣ n.factorial):= by
    by_contra hhc
    push_neg at hhc
    obtain ⟨k, hk, hkdiv⟩ := hhc
    have hcontra : k ≤ (n.factorial).factorization p := by exact (Nat.Prime.pow_dvd_iff_le_factorization hp1 (by exact Nat.factorial_ne_zero n)).1 hkdiv
    rw [h5'] at hcontra
    have hk'' : k > 1 := by exact hk
    have hnk : ¬ (k ≤ 1) := by exact Nat.not_le_of_lt hk
    absurd hnk
    exact hcontra
  specialize h9' d (hd2 P hdeg)
  have hpdiv2 : (p:ℤ) ∣ c * n.factorial := by
    zify at hpdiv
    exact dvd_mul_of_dvd_right hpdiv c
  have h3 : (p:ℤ) ∣ x ^ d := by
    rw [hii]
    exact hpdiv2
  have h4 : (p:ℤ) ∣ x := by exact Int.Prime.dvd_pow' hp1 h3
  have h5 : ∃ k : ℤ, x = k * (p:ℤ) := by exact exists_eq_mul_left_of_dvd h4
  obtain ⟨k, h5⟩ := h5
  have h6 : x ^ d = k ^ d * p ^ d := by
    rw [h5]
    ring
  have h7 : (p:ℤ) ^ d ∣ c * n.factorial := by
    rw [h6] at hii
    rw [←hii]
    exact Int.dvd_mul_left (k ^ d) (↑p ^ d)
  have h9 : ¬ ((p : ℤ) ^ d ∣ c * n.factorial) := by
    by_contra hcc
    have hpint : Prime (p : ℤ) := by exact Nat.prime_iff_prime_int.mp hp1
    have h_c : (p : ℤ) ^ d ∣ n.factorial := by exact Prime.pow_dvd_of_dvd_mul_left hpint d h8 hcc
    zify at h9'
    absurd h_c
    exact h9'

  absurd h9
  exact h7


lemma rad_lt22 (hdeg : P.degree ≥ 2) (hr : R ≠ 0) (C3 C4 : ℕ) (C3gt1 : C3 > 1) (h15 : ∀ z : ℤ , |z| > C4 → |(R1 hr).eval z| < (C3:ℝ) * (|z| ^ (d - (j hr) - 2)))
: ∀ (n : ℕ) (z : ℤ), z ≠ 0 → |z| > C4 → n > 2 * |c| → eval z Q = c * ↑n.factorial → rad (Int.natAbs ((z ^ (d - (j hr)) / (D hr z)) * ((R1 hr).eval z / (D hr z)) * ((c * n.factorial) / (z ^ (j hr) * (D hr z))))) < |z| * (((C3:ℝ) * |z| ^ (d - (j hr) - 2)) / (D hr z)) * 4 ^ n := by

  intro n z hz0 hz4 hnc12abs hqeval
  have hn2c1 : n > 2 * c := by
    have hc1abs : 2 * |c| ≥ 2 * c := by
      simp
      exact le_abs_self c
    exact Int.lt_of_le_of_lt hc1abs hnc12abs

----GENERALS:
  --generals for polynomials:

  have hQeval_at : (Q).eval z = z ^ d + (R).eval z := by
    have hiii : (Q).eval z = (X ^ d + R).eval z := by exact congrArg (eval z) (QR P hdeg)
    simp at hiii
    exact hiii
  have hR1eval : (R).eval z = z ^ (j hr) * (R1 hr).eval z := by
    have h111 : (R).eval z = (X ^ (j hr) * (R1 hr)).eval z := by exact congrArg (eval z) (hrjc P hdeg hr)
    simp at h111
    exact h111
  have hR1Qeval : (Q).eval z = z ^ d + z ^ (j hr) * (R1 hr).eval z := by rw [hQeval_at, ←hR1eval]

  have hc3 : C3 > 0 := by exact Nat.zero_lt_of_lt C3gt1
  have hzpjne0 : z ^ (j hr) ≠ 0 := by exact pow_ne_zero (j hr) hz0
  have hdzne0 : (D hr z) ≠ 0 := by exact Nat.ne_zero_of_lt (D3 P z hr hz0)
  have hDgt0 : (D hr z) > 0 := by exact Nat.zero_lt_of_ne_zero hdzne0
  have hqdvd : ↑(D hr z) ∣ eval z (R1 hr) := by
    unfold D'
    exact Int.gcd_dvd_right (z ^ (d - (j hr))) (eval z (R1 hr))

  have hdzdvdzp : ↑(D hr z) ∣ z ^ (d - (j hr)) := by exact (D1 P z hr)
  have hzpowne0 : z ^ (d - (j hr)) ≠ 0 := by exact pow_ne_zero (d - (j hr)) hz0

  have h19 : rad (Int.natAbs (z ^ (d - (j hr)) / (D hr z))) ≤ |z| := by
    set u := z ^ (d - (j hr)) / (D hr z) with hu
    have hune0 : u ≠ 0 := by
      unfold u
      by_contra hco
      have hcon : z ^ (d - (j hr)) = 0 := by exact Int.eq_zero_of_ediv_eq_zero hdzdvdzp hco
      absurd hzpowne0
      exact hcon
    have huu : u * (D hr z) = z ^ (d - (j hr)) := by
      unfold u
      rw [mul_comm]
      exact Int.mul_ediv_cancel' (D1 P z hr)
    have huabs := congr_arg Int.natAbs huu
    rw [Int.natAbs_mul] at huabs
    rw [Int.natAbs_natCast] at huabs
    have hrad1 : rad (u.natAbs) ≤ rad (u.natAbs * (D hr z)) := by
      refine rad_dvd_le (u.natAbs * (D hr z)) u.natAbs ?_ (by simp)
      simp
      exact And.intro hune0 hdzne0
    have hrad2 : rad (u.natAbs * (D hr z)) ≤ |z| := by
      have hh : (z ^ (d - (j hr))).natAbs = (z.natAbs) ^ (d - (j hr)) := by
        zify
        simp
      rw [huabs, hh]
      have h1 : (rad (z.natAbs ^ (d - (j hr)))) ≤ z.natAbs := by exact rad_pow_le z.natAbs (d - (j hr)) (Int.natAbs_ne_zero.mpr hz0)
      zify at h1
      exact h1
    zify at hrad1
    exact Int.le_trans hrad1 hrad2


  have h20 : rad ((R1 hr).eval z / (D hr z)).natAbs < ((C3:ℝ) * |z| ^ (d - (j hr) - 2)) / (D hr z) := by
    have heval : (R1 hr).eval z ≠ 0 := by
      by_contra hco
      rw [hco] at hR1Qeval
      simp at hR1Qeval
      rw [hqeval] at hR1Qeval
      exact Rzero_imp_false P hdeg n z (Eq.symm hR1Qeval) hnc12abs
    have h1 : rad ((R1 hr).eval z / (D hr z)).natAbs ≤ |(R1 hr).eval z| / (D hr z) := by
      have hi1 : rad ((R1 hr).eval z / (D hr z)).natAbs ≤ ((R1 hr).eval z / (D hr z)).natAbs := by
        refine radx_le_x ((R1 hr).eval z / (D hr z)).natAbs ?_
        simp
        contrapose heval
        push_neg at heval ⊢
        refine Int.eq_zero_of_ediv_eq_zero ?_ heval
        unfold D'
        exact Int.gcd_dvd_right _ _
      have hexact : |(R1 hr).eval z| / (D hr z) = ((R1 hr).eval z / (D hr z)).natAbs := by
        simp
        refine abs_div_eq_div ((R1 hr).eval z) (D hr z) (Int.natCast_pos.mpr hDgt0) hqdvd
      rw [hexact]
      simp
      zify at hi1
      exact hi1
    specialize h15 z hz4
    have hineq : |eval z (R1 hr)| / ((D hr z) : ℝ) < ↑C3 * |z| ^ (d - (j hr) - 2) / ((D hr z) : ℝ) := by exact div_lt_div_of_pos_right h15 (Nat.cast_pos'.mpr hDgt0)
    have hdivcast : ↑(|eval z (R1 hr)| / ((D hr z) : ℤ)) = (|eval z (R1 hr)| / (D hr z) : ℝ) := by
      refine Int.cast_div (D2 P z hr) ?_
      simp
      exact hdzne0
    rw [←hdivcast] at hineq
    rify at h1
    exact lt_of_le_of_lt h1 hineq

  have h21 : rad (Int.natAbs ((c * n.factorial) / (z ^ (j hr) * (D hr z)))) ≤ 4 ^ n := by
    let hcopy := hqeval
    rw [hQeval_at] at hqeval
    rw [hR1eval] at hqeval
    have hdj : d = (j hr) + (d - (j hr)) := by
      have ho1 := hjd P hr
      omega
    rw [hdj] at hqeval
    have hzdj : z ^ ((j hr) + (d - (j hr))) = z ^ (j hr) * z ^ (d - (j hr)) := by ring
    rw [hzdj] at hqeval
    have hfactor : z ^ (j hr) * z ^ (d - (j hr)) + z ^ (j hr) * eval z (R1 hr) = z ^ (j hr) * (z ^ (d - (j hr)) + eval z (R1 hr)) := by ring
    rw [hfactor, ←hcopy] at hqeval
    have hqzdvd : z ^ (j hr) ∣ (Q).eval z := by exact Dvd.intro (z ^ (d - (j hr)) + eval z (R1 hr)) hqeval
    let hqevals := hqeval.symm
    apply (Int.ediv_eq_of_eq_mul_right hzpjne0) at hqevals
    have h1 : (eval z (Q) / z ^ (j hr)) / (D hr z) = (z ^ (d - (j hr)) + eval z (R1 hr)) / (D hr z) := by exact congrFun (congrArg HDiv.hDiv hqevals) ((D hr z) : ℤ)
    rw [Int.add_ediv_of_dvd_right hqdvd] at h1

    have hdivdiv : (Q).eval z / z ^ (j hr) / ((D hr z): ℤ) = (Q).eval z / (z ^ (j hr) * ((D hr z) : ℤ)) := by  --exact Int.ediv_ediv_eq_ediv_mul
      have hdzqdvdd : ((D hr z) : ℤ) ∣ (Q).eval z / z ^ (j hr) := by
        set fr := z ^ (d - (j hr)) / ↑(D hr z) + eval z (R1 hr) / ↑(D hr z)
        rw [hqevals]
        exact (Int.dvd_add_right hdzdvdzp).mpr hqdvd
      exact Int.ediv_ediv_eq_ediv_mul_dvd ((Q).eval z) hdzqdvdd
    rw [hdivdiv] at h1
    have hudvd : (z ^ (j hr) * ↑(D hr z)) ∣ c * ↑n.factorial := by
      rw [← hcopy]
      refine Int.mul_dvd_of_dvd_div hqzdvd ?_
      rw [hqevals]
      unfold D'
      exact (Int.dvd_add_right (Int.gcd_dvd_left _ _)).mpr (Int.gcd_dvd_right _ _)


    set u := c * ↑n.factorial / (z ^ (j hr) * ↑(D hr z))
    have hune0 : u ≠ 0 := by
      unfold u
      have hfacne0 : n.factorial ≠ 0 := by exact Nat.factorial_ne_zero n
      zify at hfacne0
      exact int_div_ne_zero (hcne0 P hdeg) hfacne0 hudvd

    have hu : u * (z ^ (j hr) * ↑(D hr z)) = c * n.factorial := by
      unfold u
      rw [mul_comm]
      refine Int.mul_ediv_cancel' ?_
      have hqddvd : z ^ (j hr) * ↑(D hr z) ∣ c * ↑n.factorial := by
        rw [← hcopy]
        refine Int.mul_dvd_of_dvd_div hqzdvd ?_
        rw [hqevals]
        unfold D'
        refine (Int.dvd_add_right ?_).mpr ?_
        exact Int.gcd_dvd_left _ _
        exact Int.gcd_dvd_right _ _
      exact hqddvd
    have huabs := congr_arg Int.natAbs hu
    rw [Int.natAbs_mul] at huabs
    have hrad1 : rad (u.natAbs) ≤ rad (u.natAbs * (z ^ (j hr) * ↑(D hr z)).natAbs) := by
      refine rad_dvd_le (u.natAbs * (z ^ (j hr) * ↑(D hr z)).natAbs) u.natAbs ?_ (Nat.dvd_mul_right u.natAbs (z ^ (j hr) * ↑(D hr z)).natAbs)
      simp
      constructor
      exact hune0
      constructor
      intro hzc
      absurd hz0
      exact hzc
      exact hdzne0
    have hrad2 : rad (u.natAbs * (z ^ (j hr) * ↑(D hr z)).natAbs) = rad ((c * ↑n.factorial).natAbs) := by exact congrArg rad huabs
    rw [hrad2] at hrad1
    have hrad3 : rad (c * ↑n.factorial).natAbs ≤ 4 ^ n := by
      rw [Int.natAbs_mul]
      have hs : ((n.factorial) : ℤ).natAbs = n.factorial := by exact rfl
      rw [hs]
      have hc1abs : (c).natAbs ≤ n := by
        zify
        have hn11 : n > |c| := by exact gt_trans hnc12abs (lt_two_mul_self (abs_pos.mpr (hcne0 P hdeg)))
        exact Int.le_of_lt hn11
      rw [rad_le n (c).natAbs (by exact Int.natAbs_ne_zero.mpr (hcne0 P hdeg)) hc1abs]
      rw [rad_eq_primorial]
      exact primorial_le_4_pow n
    exact Nat.le_trans hrad1 hrad3
  have hhelpge0 : 0 ≤ |z| * ((C3:ℝ) * |z| ^ (d - (j hr) - 2) / ↑(D hr z)) := by
    simp
    refine mul_nonneg (by exact abs_nonneg (z:ℝ)) ?_
    refine div_nonneg (mul_nonneg (Nat.cast_nonneg' C3) (pow_nonneg (by exact abs_nonneg (z:ℝ)) (d - (j hr) - 2))) (Nat.cast_nonneg' (D hr z))

  have hrw : (rad (z ^ (d - (j hr)) / ↑(D hr z) * (eval z (R1 hr) / ↑(D hr z)) * (c * ↑n.factorial / (z ^ (j hr) * ↑(D hr z)))).natAbs) ≤ rad ((z ^ (d - (j hr)) / (D hr z)).natAbs) * rad (((R1 hr).eval z / (D hr z)).natAbs) * rad (((c * n.factorial) / (z ^ (j hr) * (D hr z))).natAbs) := by
    rw [Int.natAbs_mul]
    rw [Int.natAbs_mul]
    set a := (z ^ (d - (j hr)) / ↑(D hr z)).natAbs * (eval z (R1 hr) / ↑(D hr z)).natAbs
    set s := (c * ↑n.factorial / (z ^ (j hr) * ↑(D hr z))).natAbs
    have h1 : rad (a * s) ≤ rad a * rad s := by exact rad_mul_le a s
    set c1 := (z ^ (d - (j hr)) / ↑(D hr z)).natAbs
    set w := (eval z (R1 hr) / ↑(D hr z)).natAbs
    have ha : a = c1 * w := by
      unfold c1 w
      exact rfl
    have hrad2 : rad (c1 * w) ≤ rad c1 * rad w := by exact rad_mul_le c1 w
    rw [ha] at h1
    have h2 : rad (c1 * w) * rad s ≤ rad c1 * rad w * rad s := by exact Nat.mul_le_mul_right (rad s) hrad2
    have h3 : rad (c1 * w * s) ≤ rad c1 * rad w * rad s := by exact Nat.le_trans h1 h2
    rw [ha]
    exact h3
  set w := z ^ (d - (j hr)) / ↑(D hr z)
  set r := (eval z (R1 hr) / ↑(D hr z))
  set t := (c * ↑n.factorial / (z ^ (j hr) * ↑(D hr z)))
  have h1 : rad w.natAbs * rad r.natAbs < |z| * (((C3:ℝ) * |z| ^ (d - (j hr) - 2)) / ↑(D hr z)) := by
    rify at h19
    set a1 := (rad w.natAbs : ℝ)
    set b1 := (rad r.natAbs : ℝ)
    simp at h20 ⊢
    set d1 := ((C3:ℝ) * |(z:ℝ)| ^ (d - (j hr) - 2)) / ↑(D hr z)
    set c1' := (|z|:ℝ)
    refine mul_lt_mul_of_nonneg_of_pos' h19 h20 ?_ ?_
    unfold b1
    simp
    unfold c1'
    simp
    exact hz0
  have h2 : (rad w.natAbs : ℝ) * rad r.natAbs * rad t.natAbs < |z| * ((C3:ℝ) * |z| ^ (d - (j hr) - 2) / ↑(D hr z)) * 4 ^ n := by
    set a1 := (rad w.natAbs : ℝ) * rad r.natAbs
    set c1' := |z| * ((C3:ℝ) * |z| ^ (d - (j hr) - 2) / ↑(D hr z))
    set b1 := (rad t.natAbs : ℝ)
    set d1 := (4 ^ n : ℝ)
    refine mul_lt_mul_of_pos_of_nonneg' h1 ?_ ?_ hhelpge0
    unfold b1 d1
    rify at h21
    exact h21
    unfold b1
    simp
    exact rad_gt_0 (t.natAbs)
  rify at hrw

  exact lt_of_le_of_lt hrw h2




lemma eq1015 (C1 C2 C9 C10 : ℝ) (hc1 : C1 > 0) (hc10 : C10 > 0) : ∃ C11 : ℝ, ∀ (n : ℕ) (z : ℤ), C11 > 0 ∧ (|z| > C2 → (eval z Q = c * ↑n.factorial → |↑d * log |↑z| - log ↑n.factorial| < C1 → d * log |z| < C9 * n + C10 → log (n.factorial) < C9 * n + C11)) := by
  let c11 := C1 + C10
  use c11
  intro n z
  have hc11gt0 : c11 > 0 := by
    unfold c11
    exact Right.add_pos' hc1 hc10
  constructor
  exact hc11gt0
  intro hzc2 heval h1 h2
  rw [abs_lt] at h1
  let huse := h1.1
  rw [lt_sub_iff_add_lt'] at huse
  simp only [add_neg_lt_iff_lt_add] at huse
  have htrabs : ↑d * log |↑z| < ↑d * log |↑z| + C1 := by exact lt_add_of_pos_right (↑d * log |↑z|) hc1
  have ht : ↑d * log |↑z| + C1 < (C9 * ↑n + C10) + C1 := by exact (add_lt_add_iff_right C1).mpr h2
  have htt : log n.factorial < (C9 * ↑n + C10) + C1 := by exact gt_trans ht huse
  unfold c11
  rw [add_comm C1 C10]
  rw [←add_assoc]
  exact htt



lemma ygtM (hdeg : P.degree ≥ 2) (x adm : ℤ) (M : ℝ) (h : |x| > (M + (|adm| : ℝ)) / (|ad * d| : ℝ)) : |ad * d * x + adm| > M := by
  have hww : ↑|x| = |(x : ℝ)| := by exact Int.cast_abs
  have hw : ↑|adm| = |(adm : ℝ)| := by exact Int.cast_abs
  have hmabs : 0 < |ad * d| := by
    simp
    exact And.intro (hadne0 P hdeg) (very_simple d (hd2 P hdeg))
  set w := (M + (|adm| : ℝ)) / (|ad * d| : ℝ)
  simp at h
  have ht1 : |ad * ↑d * x + adm| ≥ |ad * d| * |x| - |adm| := by
    set g := ad * ↑d * x
    have hyy : |g + adm| = |g - (-adm)| := by ring_nf
    set madm := - adm
    rw [hyy]
    have hadabs : |madm| = |adm| := by
      unfold madm
      simp
    have h12 : |g - madm| ≥ |g| - |madm| := by exact abs_sub_abs_le_abs_sub g madm
    have htt : |g| = |ad * ↑d| * |x| := by
      unfold g
      exact abs_mul (ad * ↑d) x
    rw [←htt, ←hadabs]
    exact h12
  have ht2 : |ad * d| * |x| - |adm| > |ad * d| * w - |adm| := by
    simp
    rify at hmabs
    exact (mul_lt_mul_left hmabs).2 h
  rify at ht1
  rw [←ge_iff_le] at ht1
  rw [← hww] at ht1
  simp only [Int.cast_abs, Int.cast_mul, Int.cast_natCast] at ht2
  rw [←Int.cast_abs] at ht1
  have ht3 : |ad * ↑d * x + adm| > ↑|ad * ↑d| * w - ↑|adm| := by
    simp only [Int.cast_abs, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [←hww] at ht2
    conv_lhs at ht2 => rw [←hw]
    exact lt_of_le_of_lt' ht1 ht2
  have hf : M = ↑|ad * ↑d| * w - ↑|adm| := by
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_natCast]
    apply Eq.symm
    rw [sub_eq_iff_eq_add]
    set g := |(ad : ℝ) * ↑d|
    set i :=  M + |↑adm|
    apply Eq.symm
    rw [mul_comm]
    rw [←mul_inv_eq_iff_eq_mul₀]
    swap
    unfold g
    rify at hmabs
    exact Ne.symm (ne_of_lt hmabs)
    rw [mul_comm, inv_mul_eq_div]
  rw [← hf] at ht3
  exact ht3



lemma Qasymp_ineq (hdeg : P.degree ≥ 2) (C2 : ℕ) (hz : ∀ (z : ℤ), |z| > C2 → (|z| ^ d / 2 : ℝ) < |eval z Q| ∧ |eval z Q| < 2 * |z| ^ d)
: ∃ (C1 : ℝ), ∀ (z : ℤ) (n : ℕ), C1 > 0 ∧ (|z| > C2 → (Q).eval z = c * n.factorial → |d * log |z| - log (n.factorial)| < C1) := by

  -- have hasymp := poly_asymp_Z (Q) (hQmonic P)
  -- obtain ⟨C2, hasymp⟩ := hasymp
  -- choose hc2 hz using hasymp
  have hd := hQdegree P hdeg
  have hdd : P.natDegree = d := rfl
  rw [hdd] at hd

  use (log |c| + log 2)
  intro x n
  have hcabsi : |c| > 1 := by
    refine Int.lt_iff_le_and_ne.mpr ?_
    constructor
    swap
    apply Ne.symm
    exact (hcabsne1 P hdeg)
    refine Int.one_le_abs (hcne0 P hdeg)
  constructor
  rify at hcabsi
  have hlogc1 : log |c| > 0 := by exact log_pos hcabsi
  have hlog2 : log 2 > 0 := by exact log_pos (by exact one_lt_two)
  exact Right.add_pos' hlogc1 hlog2

  intro hxg hxn

  have hexact : |↑d * log |↑x| - log ↑n.factorial| < log |↑c| + log 2 := by
    have hx0 : x ≠ 0 := by
      --let hxg := hxn.1
      by_contra hx0
      rw [hx0] at hxg
      simp at hxg
      have hcont : C2 ≥ 0 := by exact Nat.zero_le C2
      zify at hcont
      have hco : ¬ ((C2 : ℤ) < 0) := by exact Int.not_ofNat_neg C2
      contradiction
    have hexact : 0 < |x| ^ d := by
        apply pow_pos
        simp
        push_neg
        exact hx0
    rify at hexact
    specialize hz x hxg
    --specialize hc2 x
    have hxq : |(Q).eval x| = |c| * n.factorial := by
      rw [hxn]
      rw [abs_mul]
      simp
    rw [hxq] at hz
    let hz1 := hz.1
    let hz2 := hz.2
    have hz1l : log (|x| ^ (Q).natDegree / 2) < log (|c| * ↑n.factorial) := by
      --rify at hz1
      apply (Real.log_lt_log_iff ?_ ?_).2
      simp
      simp at hz1
      rw [hd]
      exact hz1
      simp
      rw [hd]
      exact hexact
      refine mul_pos ?_ ?_
      simp
      push_neg
      exact (hcne0 P hdeg)
      have he : 0 < n.factorial := by exact Nat.factorial_pos n
      rify at he
      exact he
    have hz2l : log (|c| * n.factorial) < log (2 * |x| ^ (Q).natDegree) := by
      apply (Real.log_lt_log_iff ?_ ?_).2
      rify at hz2
      simp
      rw [hd]
      exact hz2
      refine mul_pos ?_ ?_
      simp
      push_neg
      exact hcne0 P hdeg
      have he : 0 < n.factorial := by exact Nat.factorial_pos n
      rify at he
      exact he
      simp
      rw [hd]
      exact hexact
    apply abs_lt.2
    constructor
    · rw [neg_add]
      rw [← sub_eq_add_neg]
      have hrw :  - log |c| - log 2 < log |c| - log 2 := by
        simp only [sub_lt_sub_iff_right, neg_lt_self_iff]
        refine log_pos ?_
        rify at hcabsi
        exact hcabsi
      refine lt_trans hrw ?_
      rw [Real.log_mul] at hz2l
      swap
      simp
      push_neg
      exact hcne0 P hdeg
      swap
      simp
      push_neg
      exact Nat.factorial_ne_zero n
      rw [Real.log_mul] at hz2l
      swap
      simp
      swap
      rw [hd]
      simp only [Int.cast_abs]
      refine pow_ne_zero d ?_
      simp
      push_neg
      exact hx0
      rw [hd] at hz2l
      rw [Real.log_pow] at hz2l
      rw [Int.cast_abs] at hz2l
      rw [Int.cast_abs] at hz2l
      rw [sub_lt_iff_lt_add]
      rw [add_comm, ←add_sub_assoc]
      rw [lt_sub_iff_add_lt]
      exact hz2l
    · rw [hd] at hz1l
      rw [Real.log_div] at hz1l
      swap
      rw [Int.cast_abs]
      refine pow_ne_zero d ?_
      simp
      push_neg
      exact hx0
      swap
      simp
      rw [Real.log_mul] at hz1l
      swap
      simp
      push_neg
      exact hcne0 P hdeg
      swap
      simp
      push_neg
      exact Nat.factorial_ne_zero n
      rw [Int.cast_abs] at hz1l
      rw [Int.cast_abs] at hz1l
      rw [Real.log_pow] at hz1l
      rw [sub_lt_iff_lt_add]
      --rw [add_comm, ←add_assoc]
      rw [sub_lt_iff_lt_add] at hz1l
      rw [add_assoc]
      rw [add_comm (log 2)]
      rw [←add_assoc]
      exact hz1l
  exact hexact



/-- `forabc` is the lemma used for extracting the bounds on the set of solutions by
applying `abc_Z` to the desired abc-triple.-/
lemma forabc (hdeg : P.degree ≥ 2) (hr : R ≠ 0)
: abc_Z → (∃ (C5 : ℝ → ℝ), ∀ (ε : ℝ), ε > 0 → C5 ε > 0 ∧ (ε ≠ 1 → (∀ (n : ℕ) (z : ℤ), n > 2 * |c| → z ≠ 0 → (Q).eval z = c * n.factorial → |z ^ (d - (j hr)) / (D hr z)| < (C5 ε) * rad (Int.natAbs ((z ^ (d - (j hr)) / (D hr z)) * ((R1 hr).eval z / (D hr z)) * ((c * n.factorial) / (z ^ (j hr) * (D hr z))))) ^ (1 + ε)))) := by

  have hR1Qeval : ∀ (z : ℤ), eval z Q = z ^ d + z ^ (j hr) * eval z (R1 hr) := by
    intro z
    have huse := QR1 P hdeg hr
    have hu2 : eval z Q = (X ^ d + X ^ (j hr) * (R1 hr)).eval z := congrArg (eval z) huse
    simp at hu2
    exact hu2
  unfold abc_Z
  intro abcz
  obtain ⟨C5, habc⟩ := abcz
  use C5
  intro e he
  constructor

  specialize habc e he 1 1 2 (by simp) (by simp) rfl (Int.isCoprime_iff_gcd_eq_one.mpr rfl)
  simp at habc
  rw [rad2_eq2] at habc
  have htrans : 0 < C5 e * ↑2 ^ (1 + e) := lt_trans (by linarith) habc
  exact (mul_pos_iff_of_pos_right (Real.rpow_pos_of_pos (by linarith) (1 + e))).1 htrans

  intro hene1 n z hngt hz0 heval
  specialize habc e he

  set r := z ^ (d - (j hr)) / ↑(D hr z) with hr'
  set t := (eval z (R1 hr) / ↑(D hr z)) with ht
  set s := (c * ↑n.factorial / (z ^ (j hr) * ↑(D hr z))) with hs

  --- generals:
  have hzpowne0 : z ^ (d - (j hr)) ≠ 0 := by exact pow_ne_zero (d - (j hr)) hz0
  have hDne0 : (D hr z) ≠ 0 := by exact Nat.pos_iff_ne_zero.mp (D3 P z hr hz0)
  have hddvdzpow : ((D hr z) : ℤ)∣ z ^ (d - (j hr)) := by exact (D1 P z hr)
  have hddvdr1eval : ((D hr z) : ℤ) ∣ (R1 hr).eval z := by exact Int.dvd_trans (D2 P z hr) (abs_dvd_self ((R1 hr).eval z))
  have hqevalne0 : (R1 hr).eval z ≠ 0 := by
    by_contra hc
    have heev : (Q).eval z = z ^ d + z ^ (j hr) * (R1 hr).eval z := by exact hR1Qeval z
    rw [hc] at heev
    simp at heev
    rw [heval] at heev
    exact Rzero_imp_false P hdeg n z (Eq.symm heev) hngt

  specialize habc r t s

  have h1 : r ≠ 0 := by
    unfold r
    rify at hDne0
    by_contra hc
    have hcup : z ^ (d - (j hr)) = 0 := by exact Int.eq_zero_of_ediv_eq_zero hddvdzpow hc
    absurd hcup
    exact hzpowne0
  have h2 : t ≠ 0 := by
    unfold t
    rify at hDne0
    by_contra hc
    have hcup : (R1 hr).eval z = 0 := by exact Int.eq_zero_of_ediv_eq_zero hddvdr1eval hc
    absurd hcup
    exact hqevalne0

  have h3 : r + t = s := by
    have hqeval : (Q).eval z = z ^ d + (R).eval z := by
      have hh : (Q).eval z = (X ^ d + R).eval z := by exact congrArg (eval z) (QR P hdeg)
      simp at hh
      exact hh
    have hreval : (R).eval z = z ^ (j hr) * (R1 hr).eval z := by
      have hh : (R).eval z = (X ^ (j hr) * (R1 hr)).eval z := by exact congrArg (eval z) (hrjc P hdeg hr)
      simp at hh
      exact hh
    rw [hreval] at hqeval
    have hdj : d = (j hr) + (d - (j hr)) := by
      have ho := hjd2 P hdeg hr
      omega
    rw [hdj] at hqeval
    have hzdj : z ^ ((j hr) + (d - (j hr))) = z ^ (j hr) * z ^ (d - (j hr)) := by ring
    rw [hzdj] at hqeval
    have hfactor : z ^ (j hr) * z ^ (d - (j hr)) + z ^ (j hr) * eval z (R1 hr) = z ^ (j hr) * (z ^ (d - (j hr)) + eval z (R1 hr)) := by ring
    rw [hfactor] at hqeval
    have hqdvd : z ^ (j hr) ∣ (Q).eval z := by exact Dvd.intro (z ^ (d - (j hr)) + eval z (R1 hr)) (Eq.symm (hqeval))
    apply (Int.ediv_eq_of_eq_mul_right (pow_ne_zero (j hr) hz0)) at hqeval
    have h1' : (eval z Q / z ^ (j hr)) / (D hr z) = (z ^ (d - (j hr)) + eval z (R1 hr)) / (D hr z) := by exact congrFun (congrArg HDiv.hDiv hqeval) ((D hr z) : ℤ)
    rw [Int.add_ediv_of_dvd_right ?_] at h1'
    swap
    exact hddvdr1eval

    have hdivdiv : (Q).eval z / z ^ (j hr) / ((D hr z) : ℤ) = (Q).eval z / (z ^ (j hr) * ((D hr z) : ℤ)) := by
      have hdzqdvdd : ((D hr z) : ℤ) ∣ (Q).eval z / z ^ (j hr) := by
        set fr := z ^ (d - (j hr)) / ↑(D hr z) + eval z (R1 hr) / ↑(D hr z)
        rw [hqeval]
        exact (Int.dvd_add_right hddvdzpow).mpr hddvdr1eval
      exact Int.ediv_ediv_eq_ediv_mul_dvd ((Q).eval z) hdzqdvdd
    rw [hdivdiv] at h1'
    rw [heval] at h1'
    rw [←hr', ←ht, ←hs] at h1'
    exact id (Eq.symm h1')

  have h4 : IsCoprime r t := by
    have hdz : (D hr z) = (z ^ (d - (j hr))).gcd (eval z (R1 hr)) := by exact congrFun rfl z
    rw [hdz] at ht
    set r1 := z ^ (d - (j hr)) with hr1
    set t1 := eval z (R1 hr) with ht1
    refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
    rw [hr', ht]
    rw [hdz]
    exact Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_left hzpowne0
  specialize habc h1 h2 h3 h4
  refine lt_of_le_of_lt (by simp) habc



lemma forabc22 (hdeg : P.degree ≥ 2) (hr : R ≠ 0) (C3 C4 : ℕ) (C5 : ℝ → ℝ) (C3gt1 : C3 > 1) (hC5gt0 : ∀ e, e > 0 → C5 e > 0)
 : ∀ ε : ℝ, ∃ (C6 : ℝ), ε > 0 → C6 > 0 ∧ (ε ≠ 1 → ∀ (n : ℕ) (z : ℤ), (n > 2 * |c| → z ≠ 0 → eval z Q = c * ↑n.factorial → (|z| > ↑C4 → |z ^ (d - (j hr)) / (D hr z)| < (C5 ε) * rad (Int.natAbs ((z ^ (d - (j hr)) / (D hr z)) * ((R1 hr).eval z / (D hr z)) * ((c * n.factorial) / (z ^ (j hr) * (D hr z))))) ^ (1 + ε) → rad (Int.natAbs ((z ^ (d - (j hr)) / (D hr z)) * ((R1 hr).eval z / (D hr z)) * ((c * n.factorial) / (z ^ (j hr) * (D hr z))))) < |z| * (((C3:ℝ) * |z| ^ (d - (j hr) - 2)) / (D hr z)) * 4 ^ n → ((|z| : ℤ) ^ (d - (j hr)) / ((D hr z) : ℤ) : ℤ) < C6 * (|z| ^ (d - (j hr) - 1) / (D hr z) * 4 ^ n) ^ (1 + ε)))) := by

  intro e
  set c6 := (C5 e) * C3 ^ (1 + e)
  use c6
  intro he
  specialize hC5gt0 e he

  have hc3c5 : (C5 e) * C3 ^ (1 + e) > 0 := by
    refine mul_pos ?_ ?_
    exact hC5gt0
    refine rpow_pos_of_pos ?_ (1 + e)
    simp
    exact (by exact Nat.zero_lt_of_lt C3gt1)
  constructor
  unfold c6
  exact hc3c5

  intro hene1 n z hngt hz0 heval hzgt habc' h22'

  --generals:
  have hddjdvd : ↑(D hr z) ∣ |z| ^ (d - (j hr)) := by
    have hinter : ↑(D hr z) ∣ z ^ (d - (j hr)) := by exact (D1 P z hr)
    have hinter2 : z ^ (d - (j hr)) ∣ |z| ^ (d - (j hr)) := by exact pow_dvd_pow_of_dvd (self_dvd_abs z) (d - (j hr))
    exact Int.dvd_trans hinter hinter2
  have hDgt0 : (D hr z) > 0 := by exact (D3 P z hr hz0)
  have hDne0 : (D hr z) ≠ 0 := by exact Nat.ne_zero_of_lt hDgt0


  set v := ↑(rad (z ^ (d - (j hr)) / ((D hr z) : ℤ) * (eval z (R1 hr) / ((D hr z) : ℤ)) * (c * n.factorial / (z ^ (j hr) * ((D hr z) : ℤ)))).natAbs)
  have hv0 : v > 0 := by
    unfold v
    set vin := ((z ^ (d - (j hr)) / ((D hr z) : ℤ) * (eval z (R1 hr) / ((D hr z) : ℤ)) * (c * ↑n.factorial / (z ^ (j hr) * ((D hr z) : ℤ)))).natAbs)
    exact rad_gt_0 vin
  have hee : 1 + e > 0 := by exact lt_trans he (lt_one_add e)

  have habs :  |z ^ (d - (j hr)) / ((D hr z) : ℤ)| = |z| ^ (d - (j hr)) / ((D hr z) : ℤ) := by
    have habspow : |z| ^ (d - (j hr)) = |z ^ (d - (j hr))| := by exact pow_abs z (d - (j hr))
    rw [habspow]
    exact (abs_div_eq_div (z ^ (d - (j hr))) ((D hr z) : ℤ) (Int.natCast_pos.mpr hDgt0) ((D1 P z hr))).symm
  rw [habs] at habc'
  rw [Int.cast_div hddjdvd] at habc' ⊢
  swap
  simp
  exact hDne0
  swap
  simp
  exact hDne0
  simp at h22' habc' ⊢
  ring_nf at h22' habc' ⊢
  rw [mul_inv_lt_iff₀ (Nat.cast_pos'.mpr hDgt0)] at habc' ⊢
  --have hrw1 : (((D z : ℝ))⁻¹ * 4 ^ n) ^ (1 + e) * (D z) =
  have hrew : |(z:ℝ)| ^ (1:ℕ) * |(z:ℝ)| ^ (d - (j hr) - 2) = |(z:ℝ)| ^  (d - (j hr) - 1) := by
    rw [←pow_add]
    have hf : 1 + (d - (j hr) - 2) = d - (j hr) - 1 := by
      have ho := hjd P hr
      have ho2 := hjd2 P hdeg hr
      have ho3 := hd2 P hdeg
      omega
    rw [hf]
  simp at hrew
  rw [hrew] at h22'
  apply Real.rpow_lt_rpow (z := 1 + e) (Nat.cast_nonneg' v) at h22'
  specialize h22' hee
  apply mul_lt_mul_of_pos_left (a := (C5 e)) at h22'
  specialize h22' hC5gt0
  apply mul_lt_mul_of_pos_right (a := ((D hr z) : ℝ)) at h22'
  specialize h22' (Nat.cast_pos'.mpr hDgt0)
  have hf : C5 e * (|↑z| ^ (d - (j hr) - 1) * ↑C3 * (↑(D hr z))⁻¹ * 4 ^ n) ^ (1 + e) * ↑(D hr z) = C5 e * ↑C3 ^ (1 + e) * (|↑z| ^ (d - (j hr) - 1) * (↑(D hr z))⁻¹ * 4 ^ n) ^ (1 + e) * ↑(D hr z) := by
    ring_nf
    rw [mul_assoc]
    conv_rhs => rw [mul_assoc, mul_assoc]
    refine mul_eq_mul_left_iff.mpr ?_
    constructor
    refine mul_eq_mul_left_iff.mpr ?_
    constructor
    rw [← Real.mul_rpow (Nat.cast_nonneg' C3)]
    swap
    refine mul_nonneg (mul_nonneg (by simp) (by simp)) (by simp)
    refine (rpow_left_inj ?_ ?_ (Ne.symm (ne_of_lt hee))).mpr ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (by simp) (Nat.cast_nonneg' C3)) (by simp)) (by simp)
    exact mul_nonneg (Nat.cast_nonneg' C3) (mul_nonneg (mul_nonneg (by simp) (by simp)) (by simp))
    ring_nf
  rw [← hf]
  exact gt_trans h22' habc'



lemma eq25 (hdeg : P.degree ≥ 2) (hr : R ≠ 0) (C6 : ℝ → ℝ) (hc6gt0 : ∀ ε > 0, C6 ε > 0)
: ∃ (ε C9 C10 : ℝ), ∀ (n : ℕ) (z : ℤ), (ε > 0 ∧ C10 > 0 ∧ ε ≠ 1) ∧ (n > 2 * |c| → z ≠ 0 → eval z Q = c * ↑n.factorial → |z| > 1 → |z| ^ (1 + ε - ε * (d - (j hr))) < (C6 ε) * 4 ^ (n * (1 + ε)) → d * log |z| < C9 * n + C10) := by

  set e := (1 : ℝ) / (2 * d) with he
  have he0 : e > 0 := by
    unfold e
    simp
    exact Nat.zero_lt_of_ne_zero (very_simple d (hd2 P hdeg))
  have hene1 : e ≠ 1 := by
    unfold e
    refine div_ne_one_of_ne ?_
    refine Ne.symm ?_
    by_contra hc0
    have h12 : (d : ℝ) = 1 / 2 := by linarith
    have hfloor : d = Nat.floor ((1:ℝ) / 2) := by
      refine Eq.symm (Nat.le_antisymm ?_ ?_)
      refine Nat.floor_le_of_le (by exact le_of_eq (id (Eq.symm h12)))
      refine Nat.le_floor (by exact le_of_eq h12)
    have hfloor12 : Nat.floor ((1:ℝ) / 2) = 0 := by norm_num
    rw [hfloor12] at hfloor
    absurd (very_simple d (hd2 P hdeg))
    exact hfloor

  set c9 := (2 * d + 1) * log 4
  set c10 := 2 * d * |log (C6 e)| + 1
  use e, c9, c10
  intro n z
  constructor
  constructor
  exact he0
  constructor
  unfold c10
  refine add_pos_of_nonneg_of_pos ?_ ?_
  refine Left.mul_nonneg ?_ ?_
  simp
  exact abs_nonneg (log (C6 e))
  simp
  exact hene1

  intro hn2c1 hz heval hzabs1 h

  have hzabs0 : 0 < |z| := by exact abs_pos.mpr hz
  rify at hzabs1
  have hdgt0 : 0 < d := by exact Nat.zero_lt_of_ne_zero (very_simple d (hd2 P hdeg))
  rify at hdgt0
  have hhelp1 : 0 < (|z| : ℝ) ^ ((1 : ℝ) / 2) := by
    refine rpow_pos_of_pos ?_ (1 / 2)
    simp
    exact hz
  have hhelp2 : 0 < (C6 e) * 4 ^ (↑n * (1 + e)) := by
    refine mul_pos (hc6gt0 e he0) ?_
    refine rpow_pos_of_pos (by linarith) ((n:ℝ) * (1 + e))
  have hhelp3 : (4 : ℝ) ^ (↑n * (1 + e)) ≠ 0 := by
    refine (rpow_ne_zero (by linarith) ?_).mpr (by simp)
    simp
    constructor
    have hc1t : 2 * |c| ≥ 0 := by simp
    have hngt0 : n > 0 := by
      zify
      exact lt_of_le_of_lt hc1t hn2c1
    exact Nat.ne_zero_of_lt hngt0
    push_neg
    refine Ne.symm (ne_of_lt ?_)
    exact lt_trans he0 (lt_one_add e)
  have hdinv : (d : ℝ) * (d : ℝ)⁻¹ = 1 := by exact CommGroupWithZero.mul_inv_cancel (d : ℝ) (by exact Nat.cast_ne_zero.mpr (very_simple d (hd2 P hdeg)))
  have h1 : (|z| : ℝ) ^ ((1 : ℝ) / 2) < |z| ^ (1 + e - e * (d - (j hr))) := by
    simp
    refine Real.rpow_lt_rpow_of_exponent_lt hzabs1 ?_
    unfold e
    ring_nf
    rw [hdinv]
    simp
    have h12inv : 1 + (-1)/2 = (1 : ℝ)/2 := by ring
    rw [h12inv]
    simp
    rw [add_assoc]
    simp only [lt_add_iff_pos_right]
    have hh1 : (d:ℝ)⁻¹ * 2⁻¹ + (↑d)⁻¹ * ↑(j hr) * 2⁻¹ = (↑d)⁻¹ * 2⁻¹ * (1 + (j hr)) := by ring
    rw [hh1]
    refine mul_pos ?_ ?_
    simp at hdgt0 ⊢
    exact hdgt0
    have hj00 : 0 ≤ (j hr) := by exact Nat.zero_le (j hr)
    rify at hj00
    have hj01 : ((j hr) : ℝ) > -1 := by exact lt_of_le_of_lt' hj00 (by linarith)
    exact neg_lt_iff_pos_add'.mp hj01
  rify at hzabs0
  have h2 : (|z| : ℝ) ^ ((1 : ℝ) / 2) < (C6 e) * 4 ^ (↑n * (1 + e)) := by exact gt_trans h h1
  rw [←Real.log_lt_log_iff hhelp1 hhelp2] at h2
  rw [Real.log_mul (by exact Ne.symm (ne_of_lt (hc6gt0 e he0))) hhelp3] at h2
  conv_rhs at h2 => rw [Real.log_rpow (by linarith)]
  conv_lhs at h2 => rw [Real.log_rpow (x := (|z| : ℝ)) hzabs0 ((1 : ℝ)/2)]
  simp only [Int.cast_abs] at h1
  unfold c9 c10
  set c6 := C6 e
  unfold e at h2
  ring_nf at h2
  rw [←mul_lt_mul_right (a := (2 : ℝ)) (by linarith)] at h2
  simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel_right] at h2
  ring_nf at h2
  rw [←mul_lt_mul_right (a := (d : ℝ)) hdgt0] at h2
  ring_nf at h2
  have hrw : (d:ℝ) * n * (d:ℝ)⁻¹ = n := by
    rw [mul_comm] at hdinv
    rw [mul_comm, ←mul_assoc, hdinv]
    simp
  rw [hrw] at h2
  have hr2 : (n:ℝ) * log 4 + (d:ℝ) * n * log 4 * 2 = (2 * ↑d + 1) * log 4 * n := by ring_nf
  rw [add_assoc, hr2] at h2
  conv_lhs at h2 => rw [mul_comm]
  have hr3 : ↑d * log c6 * 2 = 2 * ↑d * log c6 := by ring_nf
  rw [hr3] at h2
  rw [add_comm] at h2
  have h3 : (2 * ↑d + 1) * log 4 * ↑n + 2 * ↑d * log c6 ≤ (2 * ↑d + 1) * log 4 * ↑n + (2 * ↑d * |log c6| + 1) := by
    simp
    have hh1 : 2 * ↑d * log c6 ≤ 2 * ↑d * |log c6| := by
      refine (mul_le_mul_left ?_).mpr ?_
      simp
      exact Nat.zero_lt_of_ne_zero (very_simple d (hd2 P hdeg))
      exact le_abs_self (log c6)
    have hh2 : 2 * ↑d * log c6 = 2 * ↑d * log c6 + 0 := by simp
    rw [hh2]
    refine add_le_add hh1 (by linarith)
  have h4 : ↑d * log |↑z| < (2 * ↑d + 1) * log 4 * ↑n + (2 * ↑d * |log c6| + 1) := by exact lt_of_le_of_lt' h3 h2
  exact h4




lemma abcrw (hdeg : P.degree ≥ 2) (hr : R ≠ 0) (C4 : ℕ) (C6 : ℝ) (hc6gt0 : C6 > 0)
: ∀ (n : ℕ) (z : ℤ) (ε : ℝ), ε > 0 → ε ≠ 1 → (eval z Q = c * ↑n.factorial) → z ≠ 0 → |z| > C4 → n > 2 * |c| → ((|z| : ℤ) ^ (d - (j hr)) / ((D hr z) : ℤ) : ℤ) < (C6) * (|z| ^ (d - (j hr) - 1) / (D hr z) * 4 ^ n) ^ (1 + ε) → |z| ^ (1 + ε - ε * (d - (j hr))) < (C6) * 4 ^ (n * (1 + ε)) := by

  intro n z e he hene1 heval hz0 hzc4 hn2c1 h
  -- generals:
  have hddjdvd : ↑(D hr z) ∣ |z| ^ (d - (j hr)) := by
    have hinter : ↑(D hr z) ∣ z ^ (d - (j hr)) := by exact (D1 P z hr)
    have hinter2 : z ^ (d - (j hr)) ∣ |z| ^ (d - (j hr)) := by exact pow_dvd_pow_of_dvd (self_dvd_abs z) (d - (j hr))
    exact Int.dvd_trans hinter hinter2
  have hDgt0 : (D hr z) > 0 := by exact (D3 P z hr hz0)
  have hDne0 : (D hr z) ≠ 0 := by exact Nat.ne_zero_of_lt hDgt0
  have homega1 := hjd P hr
  have homega2 := hjd2 P hdeg hr
  have homega3 := hd2 P hdeg

  rw [Int.cast_div hddjdvd] at h
  swap
  simp
  exact hDne0
  simp at h ⊢
  have h1 : |z| ^ (d - (j hr)) < (C6) * |z| ^ ((d - (j hr) - 1) * (1 + e)) * 4 ^ (n * (1 + e)) := by
    simp at h ⊢
    rw [← inv_mul_eq_div] at h
    set a1 := ((D hr z) : ℝ) with ha1
    set b1 := (|z| : ℝ) ^ (d - (j hr))
    set c1' :=  (C6) * (|↑z| ^ (d - (j hr) - 1) / a1 * 4 ^ n) ^ (1 + e)
    rw[inv_mul_lt_iff₀ ?_] at h
    swap
    unfold a1
    simp
    exact hDgt0
    have h2 : a1 * c1' = (C6) * ((((|z| : ℝ) ^ ((d - (j hr) - 1) * (1 + e))) * 4 ^ (n * (1 + e))) / ((D hr z) ^ e)) := by
      rw [mul_comm]
      unfold c1'
      rw [mul_assoc]
      refine mul_eq_mul_left_iff.2 ?_
      constructor
      have hcalc1 : ((|z| : ℝ) ^ (d - (j hr) - 1) / a1 * 4 ^ n) ^ (1 + e) * a1 = ((|z| : ℝ) ^ (d - (j hr) - 1) / a1) ^ (1 + e) * (4 ^ n) ^ (1 + e) * a1 := by
        refine mul_eq_mul_right_iff.2 ?_
        constructor
        have hr1 : 0 ≤ |↑z| ^ (d - (j hr) - 1) / a1 := by
          refine div_nonneg ?_ ?_
          exact pow_nonneg (by exact abs_nonneg (z:ℝ)) (d - (j hr) - 1)
          unfold a1
          simp
        refine Real.mul_rpow hr1 (by simp)
      rw [hcalc1]
      have hr2 : (0 : ℝ) ≤ |↑z| ^ (d - (j hr) - 1) := by exact pow_nonneg (by exact abs_nonneg (z:ℝ)) (d - (j hr) - 1)
      rw [Real.div_rpow (x := |↑z| ^ (d - (j hr) - 1)) (y := a1) hr2 ?_ (1 + e)]
      swap
      unfold a1
      simp
      have hr3 : (|↑z| ^ (d - (j hr) - 1)) ^ (1 + e) = (|z| : ℝ) ^ ((d - (j hr) - 1) * (1 + e)) := by
        rw [←Real.rpow_natCast_mul]
        swap
        exact abs_nonneg (z : ℝ)
        refine congrArg (HPow.hPow (|z| : ℝ)) ?_
        simp
        constructor
        rw [Nat.cast_sub (by omega)]
        rw [Nat.cast_sub (by omega)]
        simp
      rw [hr3]
      set zp := (|z| : ℝ) ^ ((↑d - ↑(j hr) - 1) * (1 + e))
      rw [mul_assoc, mul_comm, mul_assoc]
      have ha1ge0 : a1 ≥ 0 := by
        unfold a1
        simp
      have hr4 : a1 * (zp / a1 ^ (1 + e)) = zp / a1 ^ e := by
          have ha1 : a1 ≠ 0 := by
            unfold a1
            simp
            exact hDne0
          have ha1ge : a1 ≥ 0 := by
            unfold a1
            simp
          ring_nf
          rw [mul_comm (a := a1), mul_assoc]
          refine mul_eq_mul_left_iff.mpr ?_
          constructor
          refine (mul_inv_eq_iff_eq_mul₀ ?_).mpr ?_
          have he10 : 1 + e ≠ 0 := by
            refine Ne.symm (ne_of_lt ?_)
            have hee1 : e < 1 + e := by exact lt_one_add e
            exact gt_trans hee1 he
          refine (rpow_ne_zero ha1ge he10).mpr ha1
          rw [← Real.rpow_neg_one]
          rw [← Real.rpow_mul]
          swap
          exact ha1ge
          simp
          rw [← Real.rpow_add]
          swap
          exact lt_of_le_of_ne ha1ge (id (Ne.symm ha1))
          simp
      rw [hr4]
      rw [←Real.rpow_natCast_mul (by linarith)]
      set n4 := (4 : ℝ) ^ (↑n * (1 + e))
      rw [← ha1]
      set a1e := a1 ^ e
      conv_rhs => rw [mul_comm]
      exact Eq.symm (mul_div_assoc n4 zp a1e)
      --have hnum : (|↑z| ^ (d - j - 1) / a1 * 4 ^ n) ^ (1 + e) = |↑z| ^ ((↑d - ↑j - 1) * (1 + e)) * 4 ^ (↑n * (1 + e)) := by
    set up := (((|z| : ℝ) ^ ((d - (j hr) - 1) * (1 + e))) * 4 ^ (n * (1 + e)))
    set down := (((D hr z) : ℝ) ^ e)
    have h3 : (C6) * (up / down) ≤ (C6) * up := by
      refine mul_le_mul_of_nonneg_left ?_ (by exact le_of_lt hc6gt0)
      refine div_le_self ?_ ?_
      unfold up
      have hex : (0 : ℝ) ≤ |↑z| ^ ((↑d - ↑(j hr) - 1) * (1 + e)) * 4 ^ (n * (1 + e)) := by
        have hq1 : 0 ≤ (|z| : ℝ) ^ ((↑d - ↑(j hr) - 1) * (1 + e)) := by
          set p := ((↑d - ↑(j hr) - 1) * (1 + e))
          refine Real.rpow_nonneg ?_ p
          simp
        have hq2 : 0 ≤ (4 : ℝ) ^ (↑n * (1 + e)) := by
          set p := (↑n * (1 + e))
          refine Real.rpow_nonneg ?_ p
          linarith
        exact mul_nonneg hq1 hq2
      exact hex
      unfold down
      have hdge1 : 1 ≤ (D hr z) := by exact hDgt0
      rify at hdge1
      have hrew : 1 = ((D hr z) : ℝ) ^ (0 : ℝ) := by exact Eq.symm (rpow_zero ((D hr z) : ℝ))
      rw [hrew]
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      exact hdge1
      exact le_of_lt he
    have h4 : b1 < (C6) * up := by
      rw [h2] at h
      exact lt_of_le_of_lt' h3 h
    unfold up at h4
    rw [←mul_assoc] at h4
    exact h4

  rw [mul_comm, ←mul_assoc] at h1
  set a1 := 4 ^ (↑n * (1 + e)) * (C6) with ha1
  simp at h1
  set b1 := (|z| : ℝ) ^ ((↑d - ↑(j hr) - 1) * (1 + e))
  set c1' := (|z| : ℝ) ^ (d - (j hr))
  rw [mul_comm] at h1
  have hb1gt0 : b1 > 0 := by
    unfold b1
    refine rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hz0)) (((d:ℝ) - ((j hr):ℝ) - 1) * (1 + e))
  apply (inv_mul_lt_iff₀ hb1gt0).2 at h1
  have hf : b1⁻¹ * c1' = (|z| : ℝ) ^ (1 + e - e * (↑d - ↑(j hr))) := by
    rw [←Real.rpow_neg_one]
    have hr1 : b1 ^ (- (1 : ℝ)) = (|z| : ℝ) ^ (- ((↑d - ↑(j hr) - 1) * (1 + e))) := by
      unfold b1
      rw [←Real.rpow_mul (by exact abs_nonneg (z : ℝ))]
      simp
    rw [hr1]
    unfold c1'
    have hcru : ↑(d - (j hr)) = ((d - (j hr)) : ℝ) := by exact Nat.cast_sub (by omega)
    have hzpoww : |(z:ℝ)| ^ (d - (j hr)) = |(z:ℝ)| ^ ((d - (j hr)) : ℝ) := by
      rw [← Real.rpow_natCast]
      refine congrArg (HPow.hPow (|z| : ℝ)) hcru
    rw [hzpoww]
    rify at hz0
    rw [←Real.rpow_add (abs_pos.2 hz0)]
    rw [←hcru]
    refine congrArg (HPow.hPow (|z| : ℝ)) (casting_help d (j hr) (hjd2 P hdeg hr) (hd2 P hdeg) e)
  simp
  conv_rhs => rw [mul_comm]
  rw [←hf, ←ha1]
  exact h1


noncomputable def cj (hr : R ≠ 0) := (R).coeff (j hr)

end notations_and_general_results_about_P






/-!
* Lemmas used in the first part of the proof, proving general identities between related
polynomials, transformed by compositions.
* `Rzero_imp_false` is used for doing a case distinction on wheter or not the polynomial R,
defined in the main proof, is identically zero. It shows that R being zero leads to a contradiction.
-/










/-!
* The final intermediate results needed to conclude the main proof. They involve algebraic manipulations
to the terms of the abc-triple to which the integer abc-conjecture, `abc_Z` will be applied.
* `forabc` is the only lemma in this category which depends on the abc-conjecture. It is used
to extract the bounds on set the of solutions using `abc_Z`.
-/







/-!
* The main theorem: the abc-conjecture implies that there are finitely many integer solutions
of the equation P(x) = n!, for any polynomial P with integer coefficients and of degree at least 2.
* `main_imp_Brocard` proposes another proof of the original Brocard-Ramanujan problem,
by specializing in the general result the polynomial P(x) = x² - 1.
-/



/-- Main Theorem: If P is a polynomial with integer coefficients and of degree at least 2, then the
equation P(x) = n! has finitely many pairs of integer solutions, assuming the abc-conjecture.-/
theorem abc_Z_imp_poly_eq_fac_finite_sol (P : ℤ[X]) (hdeg : P.degree ≥ 2) :
  abc_Z → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , (P.eval x = n.factorial) → (n < N) ∧ (|x| < N)) := by

  unfold abc_Z
  intro abcz
  let f (i : ℕ) : ℤ := i.factorial
  refine assume P hdeg f ?_
  unfold f

  set d := d' P with hd
  set ad := ad' P with had
  set c := c' P with hc
  let b (i : ℕ) : ℤ := b' P i
  set Qq : ℤ[X] := Qq' P with hqq
  set Q : ℤ[X] := Q' P with hq
  set R : ℤ[X] := R' P with hr

  have hqr := QR P hdeg
  rw [←hd, ←hr, ← hq] at hqr

  by_cases hR : R = 0
-- case R = 0:
  rw [hR] at hqr
  simp at hqr
  use (2 * c).natAbs + 1
  intro n x h
  by_cases hb : n ≤ 2 * |c|
-- case n ≤ 2 * |c1|:
  zify
  rw [abs_mul]
  simp
  exact Int.le_iff_lt_add_one.mp hb
-- case n > 2 * |c1|:
  push_neg at hb
  have hi := Qq_eval_fac P hdeg n x h
  rw [←hd, ←had, ←hc, ←hqq] at hi
  have forfalse := QqQ P x
  set xv := ad * d * x + P.coeff (d - 1)
  have hff : (Q).eval xv = xv ^ d := by
    have hf1 : (Q).eval xv = (X ^ d).eval xv := by exact congrArg (eval xv) hqr
    simp at hf1
    exact hf1
  rw [←hq, ←had, ←hd, ←hqq] at forfalse
  rw [← forfalse, hff] at hi
  exact False.elim (Rzero_imp_false P hdeg n xv hi hb)
  push_neg at hR

-- case R ≠ 0:

  set SR := SR' R with HSR
  set j := j' P hR with hjdef
  set R1 := R1' P hR with hr1

  obtain ⟨C2, hasy1⟩ := poly_asymp_Z Q (hQmonic P)
  choose hC2gt0 hz using hasy1
  specialize hC2gt0 1
  have hqde := hQdegree P hdeg
  unfold d' at hd
  rw[←hq, ←hd] at hqde
  rw [hqde] at hz

  obtain ⟨C1, hasy2⟩ := Qasymp_ineq P hdeg C2 hz
  choose hC1gt0 h1 using hasy2
  specialize hC1gt0 1 1

  obtain ⟨C4, C3, h15⟩ := h15_asymp P hdeg hR
  choose hC4gt1 hC3gt1 h15 using h15
  specialize hC3gt1 1
  specialize hC4gt1 1

  obtain ⟨C5, hfabc⟩ := forabc P hdeg hR abcz
  choose hC5gt0 hfabc using hfabc

  choose C6 hC6gt0 hfabc22 using forabc22 P hdeg hR C3 C4 C5 hC3gt1 hC5gt0

  obtain ⟨e, C9, C10, h25⟩ := eq25 P hdeg hR C6 hC6gt0
  choose h25' h25 using h25
  specialize h25' 1 1
  choose he hC10gt0 hene1 using h25'

  obtain ⟨C11, h1025⟩ := eq1015 P C1 C2 C9 C10 hC1gt0 hC10gt0
  choose hC11gt0 h1025 using h1025
  specialize hC11gt0 1 1

  obtain ⟨C12, hfinal⟩ := logn_le_bounded C9 C11 hC11gt0


  let M := (max C2 C4 : ℝ)
  let w := (M + |P.coeff (d - 1)|) / |ad * d|
  refine assume_x_gt P (Nat.ceil w) ?_
  let Nuse := max (max (Nat.ceil C12) 4) ((2 * c).natAbs + 1)
  use Nuse
  intro n x hx h

  set y := ad * d * x + P.coeff (d - 1)
  have hqeval : Q.eval y = c * n.factorial := by
    unfold y
    unfold Q Q'
    simp
    unfold d'
    rw [← hd]
    ring_nf
    rw [← hqq]
    exact Qq_eval_fac P hdeg n x h
  have hgeuse : |y| > M := by
    unfold y
    have hxr : (|x| : ℝ) > w := by
      rify at hx
      have htr : w ≤ Nat.ceil w := by exact Nat.le_ceil w
      exact lt_of_le_of_lt htr hx
    unfold w at hxr
    set adm := P.coeff (d - 1)
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_natCast] at hxr
    conv_lhs at hxr => simp only [←Int.cast_abs]
    exact ygtM P hdeg x adm M hxr
  have hyc2 : |y| > C2 := by
    rify
    unfold M at hgeuse
    simp at hgeuse
    exact hgeuse.1
  have hyc4 : |y| > C4 := by
    rify
    unfold M at hgeuse
    simp at hgeuse
    exact hgeuse.2
  have hyne0 : y ≠ 0 := by
    by_contra hc
    rw [hc] at hyc2
    simp at hyc2
    absurd hC2gt0
    rify
    push_neg
    rify at hyc2
    exact le_of_lt hyc2
  have hy1 : |y| > 1 := by
    zify at hC4gt1
    exact lt_trans hC4gt1 hyc4

  by_cases hn4 : n < 4
-- case n < 4:
  unfold Nuse
  simp
  right; left;
  exact hn4
-- case n ≥ 4:
  push_neg at hn4
  have hn2 : n ≥ 2 := by exact Nat.le_trans (by linarith) hn4

  by_cases hn2c1a : n ≤ 2 * |c|
--case n ≤ 2 * |c|:
  unfold Nuse
  simp
  right; right;
  zify
  rw [abs_mul]
  simp
  exact Int.le_iff_lt_add_one.mp hn2c1a
  push_neg at hn2c1a

  specialize hfabc e he hene1 n y hn2c1a hyne0 hqeval
  specialize hfabc22 e he hene1 n y hn2c1a hyne0 hqeval hyc4

  have hradlt := rad_lt22 P hdeg hR C3 C4 hC3gt1 h15 n y hyne0 hyc4 hn2c1a hqeval
  have habcrw := abcrw P hdeg hR C4 (C6 e) (hC6gt0 e he) n y e he hene1 hqeval hyne0 hyc4 hn2c1a (hfabc22 hfabc hradlt)

  specialize h25 n y hn2c1a hyne0 hqeval hy1 habcrw

  have hyc2r := hyc2
  rify at hyc2r
  simp only [Int.cast_abs] at h1025

  specialize h1025 n y hyc2r hqeval (h1 y n hyc2 hqeval) h25
  specialize hfinal n hn4 h1025

  unfold Nuse
  simp
  left;
  convert Nat.lt_ceil.2 hfinal



--#print axioms abc_Z_imp_poly_eq_fac_finite_sol


/-- The original Brocard-Ramanujan problem, this time proven using the main result, `abc_Z_imp_poly_eq_fac_finite_sol`-/
theorem main_imp_Brocard : abc_Z → (∃ (N : ℕ) , ∀ (x y : ℕ) , (x.factorial + 1 = y^2) → (x < N) ∧ (y < N)) := by

  unfold abc_Z
  intro abcz

  set P : ℤ[X] := X ^ 2 - 1
  have hdeg : P.degree ≥ 2 := by
    unfold P
    refine le_of_eq ?_
    have hr : X ^ 2 - 1 = C 1 * X ^ 2 + C 0 * X + C (- 1) := by aesop
    rw [hr]
    apply Eq.symm
    exact Polynomial.degree_quadratic (by simp)
  obtain ⟨M, hpol⟩ := abc_Z_imp_poly_eq_fac_finite_sol P hdeg abcz
  use M + 1
  intro n x hi
  have heq : eval (↑x) P = ↑n.factorial := by
    unfold P
    simp
    rw [Int.sub_eq_iff_eq_add']
    rw [add_comm]
    apply Eq.symm
    zify at hi
    exact hi
  specialize hpol n x heq
  simp at hpol
  choose b1 b2 using hpol
  constructor
  exact Nat.lt_add_right 1 b1
  exact Nat.lt_add_right 1 b2



--#print axioms main_imp_Brocard
