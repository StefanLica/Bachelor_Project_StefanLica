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




--/-- Intermediate result applying the polynomial asymptotic lemmas to the main proof-/
lemma h15_asymp (Q R1 : ℤ[X]) (d j : ℕ) (hd2 : d ≥ 2) (hdeg : R1.degree ≠ ⊥) (hr1 : R1 = ∑ i ∈ Finset.range (d - 1) \ Finset.range j, C (Q.coeff i) * X ^ (i - j))
  : ∃ C4 C3 : ℕ, ∀ z : ℤ, C4 > 1 ∧ C3 > 1 ∧ ((|z| > C4) → |R1.eval z| < (C3:ℝ) * (|z| ^ (d - j - 2))) := by

  set dr := R1.natDegree with hdr
  have hdrb : ↑dr = R1.degree := by exact Eq.symm (degree_eq_natDegree (degree_ne_bot.mp hdeg))
  have hlc : R1.leadingCoeff ≠ 0 := by
    unfold Polynomial.leadingCoeff
    rw [←hdr]
    exact Polynomial.coeff_ne_zero_of_eq_degree (id (Eq.symm hdrb))
  have hr1de : R1.natDegree ≤ d - j - 2 := by
    have hlee : ∀ i ∈ Finset.range (d - 1) \ Finset.range j, (C (Q.coeff i) * X ^ (i - j)).natDegree ≤ d - j - 2 := by
      intro i hidj
      simp at hidj
      have hcxde : (C (Q.coeff i) * X ^ (i - j)).degree ≤ ↑(i - j) := by exact degree_C_mul_X_pow_le (i - j) (Q.coeff i)
      rw [←Polynomial.natDegree_le_iff_degree_le] at hcxde
      have hf : i - j ≤ d - j - 2 := by omega
      exact Nat.le_trans hcxde hf
    rw [hr1]
    exact Polynomial.natDegree_sum_le_of_forall_le (Finset.range (d - 1) \ Finset.range j) (fun i ↦ C (Q.coeff i) * X ^ (i - j)) hlee
  let R : ℝ[X] := R1.map (Int.castRingHom ℝ)
  have hrr : R.leadingCoeff ≠ 0 := by
    simp [R, leadingCoeff_map]
    push_neg
    refine (Polynomial.map_ne_zero_iff (by exact RingHom.injective_int (Int.castRingHom ℝ))).mpr ?_
    exact leadingCoeff_ne_zero.mp hlc
  have hdrr1 : R1.natDegree = R.natDegree := by
    unfold R
    apply Eq.symm ?_
    exact natDegree_map_eq_of_injective (by exact RingHom.injective_int (Int.castRingHom ℝ)) R1
  have hrde : R.natDegree ≤ d - j - 2 := by
    rw [←hdrr1]
    exact hr1de
  obtain ⟨nr, lemma1⟩ := poly_asymp_general R hrr
  let C4 := nr + 1
  use C4, (2 * (R1.leadingCoeff).natAbs + 1)
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
  have hl2r1 : |R1.eval x| < 2 * |R1.leadingCoeff| * |x| ^ R1.natDegree := by
    have hu1 : |R1.eval x| = |R.eval (x:ℝ)| := by
      simp
      refine abs_eq_abs.mpr ?_
      constructor
      unfold R
      simp
    have hu2 : 2 * |R1.leadingCoeff| * |x| ^ R1.natDegree = 2 * |R.leadingCoeff| * |(x:ℝ)| ^ R.natDegree := by
      rw [mul_assoc, mul_assoc]
      simp
      have h1 : |(R1.leadingCoeff : ℝ)| = |R.leadingCoeff| := by
        refine abs_eq_abs.mpr ?_
        constructor
        unfold R
        rw [Polynomial.leadingCoeff_map' (RingHom.injective_int (Int.castRingHom ℝ)) R1]
        simp
      have h2 : |(x:ℝ)| ^ R1.natDegree = |↑x| ^ R.natDegree := by exact congrArg (HPow.hPow |(x:ℝ)|) hdrr1
      exact Mathlib.Tactic.LinearCombination'.mul_pf h1 h2
    rify
    simp at hu1 hu2
    rw [hu1, hu2]
    exact hl2
  have hrif : (R1.leadingCoeff.natAbs : ℝ) = |R1.leadingCoeff| := by exact Nat.cast_natAbs R1.leadingCoeff
  simp
  rw [hrif]
  have hf :  2 * |R1.leadingCoeff| * |x| ^ R1.natDegree ≤ (2 * |R1.leadingCoeff| + 1) * |x| ^ (d - j - 2) := by
    refine Int.mul_le_mul (by simp) ?_ (pow_nonneg (by simp) R1.natDegree) (Int.add_nonneg (by simp) (by simp))
    refine (pow_le_pow_iff_right₀ ?_).mpr hr1de
    unfold C4 at hzc4
    simp at hzc4
    exact Int.lt_trans (Int.lt_add_of_pos_left 1 (Int.ofNat_pos.mpr nrgt)) hzc4
  rify at hl2r1 hf
  simp
  exact lt_of_lt_of_le hl2r1 hf




/-!
* Lemmas allowing for certain simplifications of the main proof, for example, `assume`, which
shows it is sufficient to prove that the set of solutions for n is bounded, since this implies
that the set of solutions for x is also bounded.
-/


lemma assume_help (S : Set ℤ) (hs : Set.Finite S) : ∃ (M : ℕ), ∀ (x : ℤ), (x ∈ S) → |x| < M := by

  have habove : BddAbove S := by exact Set.Finite.bddAbove hs
  have hbelow : BddBelow S := by exact Set.Finite.bddBelow hs

  unfold BddAbove at habove
  unfold BddBelow at hbelow

  unfold upperBounds at habove
  unfold lowerBounds at hbelow

  unfold Set.Nonempty at habove hbelow

  obtain ⟨a, ha⟩ := habove
  obtain ⟨b, hb⟩ := hbelow
  simp at ha hb
  let m := |a| + |b| + 2

  let M := m.toNat
  use M
  intro x hx
  specialize hb hx
  specialize ha hx
  rw [abs_lt]
  constructor
  · unfold M
    rw [Int.toNat_of_nonneg]
    swap
    unfold m
    refine Int.add_nonneg (a := |a| + |b|) ?_ ?_
    refine Int.add_nonneg ?_ ?_
    exact abs_nonneg a
    exact abs_nonneg b
    linarith
    unfold m
    by_cases hb0 : b ≥ 0
    · have hbabs : |b| = b := by exact abs_of_nonneg hb0
      rw [hbabs]
      simp
      change -b < 1 + 1 + x + |a|
      have h2 : -b < 1 + 1 + x + |a| ↔ -b - 1 < 1 + x + |a| := by
        constructor
        intro h11
        linarith
        intro h11
        linarith
      rw [h2]
      refine Int.add_lt_add_of_le_of_lt (a := -b) ?_ ?_
      have h3 : -b ≤ b := by exact neg_le_self hb0
      have hb' : b ≤ 1 + x := by
        rw [add_comm]
        exact Int.le_add_one hb
      exact Int.le_trans h3 hb'
      have h4 : 0 ≤ |a| := by exact abs_nonneg a
      exact h4
    · push_neg at hb0
      have hbabs : |b| = -b := by exact abs_of_neg hb0
      rw [hbabs]
      simp
      change b < 1 + 1 + x + |a|
      have h2 : b < 1 + 1 + x + |a| ↔ b - 1 < 1 + x + |a| := by
        constructor
        intro h11
        linarith
        intro h11
        linarith
      rw [h2]
      refine Int.add_lt_add_of_le_of_lt (a := b) ?_ ?_
      have h3 : x ≤ 1 + x := by linarith
      exact Int.le_trans hb h3
      have h4 : 0 ≤ |a| := by exact abs_nonneg a
      exact h4
  · unfold M
    rw [Int.toNat_of_nonneg]
    swap
    unfold m
    refine Int.add_nonneg (a := |a| + |b|) ?_ ?_
    refine Int.add_nonneg ?_ ?_
    exact abs_nonneg a
    exact abs_nonneg b
    linarith
    unfold m
    have h1 : a ≤ |a| := by exact le_abs_self a
    have h2 : x ≤ |a| := by exact Int.le_trans ha h1
    have h3 : |a| < |a| + |b| + 2 := by
      refine Int.lt_add_of_le_of_pos ?_ ?_
      simp
      linarith
    exact Int.lt_of_le_of_lt h2 h3


lemma assume_help_finite (N : ℕ) (P : Polynomial ℤ) (hdeg : P.degree ≥ 2) (f : ℕ → ℤ) (S : ℕ → Set ℤ) (hs : S = fun N ↦ {x : ℤ | ∃ n : ℕ, n < N ∧ P.eval x = f n}) : Set.Finite (S N) := by
  have hdef : S N = ⋃ n ∈ Finset.range N, {x : ℤ | P.eval x = f n} := by
    ext x
    constructor
    intro hx
    simp
    rw [hs] at hx
    simp at hx
    exact hx
    intro hx
    simp at hx
    rw [hs]
    simp
    exact hx
  rw [hdef]
  refine Set.Finite.biUnion ?_ ?_
  apply Finset.finite_toSet
  intro i hi
  simp at hi
  let T := P - f i
  have htn0 : T ≠ 0 := by
    by_contra hc
    unfold T at hc
    rw [sub_eq_zero] at hc
    have hid : (f i : ℤ[X]).natDegree = 0 := by exact natDegree_intCast (f i)
    have hc' : P.natDegree = (f i : ℤ[X]).natDegree := by exact congrArg natDegree hc
    rw [hid] at hc'
    have hco : P.natDegree ≠ 0 := by
      have hh : P.degree ≤ P.natDegree := by exact Polynomial.degree_le_natDegree
      have hh1 : P.natDegree ≥ 2 := by exact le_natDegree_of_coe_le_degree hdeg
      linarith
    contradiction
  have hh1 : {x | P.eval x = f i} = {x | P.eval x - f i = 0} := by
    ext x
    simp [sub_eq_zero]
  rw [hh1]
  have hS1 : {x | P.eval x - f i = 0} = {x | T.eval x = 0} := by
    ext x
    simp [T]
  rw [hS1]
  clear hh1 hS1
  have hroot : {x | eval x T = 0} = T.roots.toFinset := by
    refine Eq.symm (Set.ext ?_)
    intro r
    constructor
    intro h1
    simp at h1
    simp
    exact h1.2
    intro h1
    simp at h1 ⊢
    constructor
    swap
    exact h1
    push_neg
    exact htn0
  rw [hroot]
  simp


lemma assume (P : ℤ[X]) (hdeg : P.degree ≥ 2) (f : ℕ → ℤ) : (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , (P.eval x = f n) → (n < N)) → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , (P.eval x = f n) → (n < N) ∧ (|x| < N)) := by
  rintro ⟨N, h⟩
  set S := {x : ℤ | ∃ n : ℕ, n < N ∧ P.eval x = f n} with hS
  set H : ℕ → Set ℤ := fun N ↦ {x : ℤ | ∃ n : ℕ, n < N ∧ P.eval x = f n} with hh
  have hsh : H N = S := by exact hS
  have hfin' : Set.Finite (H N) := by exact assume_help_finite N P hdeg f H hh
  have hfin : Set.Finite S := by exact hfin'
  clear H hh hsh hfin'

  have hhh : ∃ (M : ℕ), ∀ (x : ℤ), Set.Finite S ∧ x ∈ S → |x| < M := by
    obtain ⟨M, hm⟩ := assume_help S hfin
    use M
    intro y hy
    specialize hm y hy.2
    exact hm

  obtain ⟨u, hu⟩ := hhh
  let M := max u N
  use M
  intro n x h'
  specialize hu x
  specialize h n x h'

  have hneed2 : x ∈ S := by
    unfold S
    simp
    use n
  specialize hu (And.intro hfin hneed2)
  constructor
  · unfold M
    simp
    exact Or.inr h
  · unfold M
    simp
    constructor
    exact hu


lemma polynomial_bounded (P : ℤ[X]) (m : ℕ) : ∃ M, ∀ x : ℤ, |x| ≤ m → P.eval x < M := by
  set M := ∑ n ∈ P.support, (fun e a ↦ |a| * (m:ℤ) ^ e) n (P.coeff n)
  use M + 1
  intro x hx
  simp only [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  refine Int.lt_add_one_iff.2 ?_
  unfold M
  refine Finset.sum_le_sum ?_
  intro i hi
  simp
  have hinter : P.coeff i * x ^ i ≤ |P.coeff i * x ^ i| := by exact le_abs_self (P.coeff i * x ^ i)
  rw [abs_mul, abs_pow] at hinter
  have hinter2 : |P.coeff i| * |x| ^ i ≤ |P.coeff i| * m ^ i := by
    refine Int.mul_le_mul_of_nonneg_left ?_ (abs_nonneg (P.coeff i))
    refine pow_le_pow_left₀ (abs_nonneg x) hx i
  exact Int.le_trans hinter hinter2


lemma assume_x_gt (P : ℤ[X]) (m : ℕ) : (∃ N : ℕ, ∀ (n : ℕ) (x : ℤ), (|x| > m → ((P.eval x = n.factorial) → n < N))) → (∃ N : ℕ, ∀ (n : ℕ) (x : ℤ), (P.eval x = n.factorial) → n < N) := by

  rintro ⟨N1, h1⟩
  set H : ℕ → Set ℕ := fun N ↦ {n : ℕ | ∃ x : ℤ, |x| ≤ N ∧ P.eval x = n.factorial} with hh

  have h2 : ∃ N, ∀ (n : ℕ) (x : ℤ), |x| ≤ m → eval x P = n.factorial → n < N := by
    obtain ⟨M, pol_bound⟩ := polynomial_bounded P m
    use M.natAbs
    intro n x hxm hprop
    specialize pol_bound x hxm
    rw [hprop] at pol_bound
    have hfacb : n.factorial < M.natAbs := by
      zify
      rw [lt_abs]
      exact Or.symm (Or.inr pol_bound)
    refine lt_of_le_of_lt (Nat.self_le_factorial n) hfacb

  obtain ⟨N2, h2⟩ := h2

  use max N1 N2
  intro n x h
  by_cases hm : |x| > m
  --
  specialize h1 n x hm h
  exact lt_sup_of_lt_left h1
  --
  push_neg at hm
  specialize h2 n x hm h
  exact lt_sup_of_lt_right h2


/-!
* Lemmas used in the first part of the proof, proving general identities between related
polynomials, transformed by compositions.
* `Rzero_imp_false` is used for doing a case distinction on wheter or not the polynomial R,
defined in the main proof, is identically zero. It shows that R being zero leads to a contradiction.
-/

lemma Qq_eval_fac (n : ℕ) (x : ℤ) (P Qq : ℤ[X]) (hdeg : P.degree ≥ 2) (b : ℕ → ℤ) (d : ℕ) (ad c1 : ℤ) (hc1ne0 : c1 ≠ 0) (hd : d = P.natDegree) (hc1 : c1 = d ^ d * ad ^ (d - 1)) (hbu : b = fun i ↦ P.coeff i * d ^ (d - i) * ad ^ (d - i - 1))
  (hQq : Qq = X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i) (hi : P.eval x = n.factorial) (hQprw : ∀ x : ℤ, P.eval x = ((Qq.comp ((ad * d) • X)).eval x) / c1) : Qq.eval (ad * d * x) = c1 * n.factorial := by

  have hd1 : d ≥ 1 := by
    have hd2 : d ≥ 2 := by
      rw [hd]
      exact le_natDegree_of_coe_le_degree hdeg
    exact Nat.one_le_of_lt hd2
  rw [hQprw] at hi
  simp at hi
  conv_rhs =>
    rw [mul_comm]
  refine (Int.ediv_eq_iff_eq_mul_left hc1ne0 ?_).mp hi
  have hc1diveval : c1 ∣ eval (ad * ↑d * x) Qq := by
    have h1 : Qq.eval (ad * ↑d * x) = (ad * ↑d * x) ^ d + ∑ i ∈ Finset.range d, (b i) * (ad * (d:ℤ) * x) ^ i := by
      have h11 : Qq.eval (ad * ↑d * x) = (X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i).eval (ad * (d:ℤ) * x) := by exact congrArg (eval (ad * ↑d * x)) hQq
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
    rw [hc1]
    exact Int.dvd_mul_right (↑d ^ d * ad ^ (d - 1)) (ad * x ^ d + s)
  exact hc1diveval


lemma D_gcd_poly (P : ℤ[X]) (d j D : ℕ) (x : ℤ) (hd : D = Int.gcd (x ^ (d - j)) (P.eval x)) : ((D : ℤ) ∣ x ^ (d - j)) ∧ ((D : ℤ) ∣ |P.eval x|) ∧ (x ≠ 0 → D > 0) := by

  have h1 : (D : ℤ) ∣ x ^ (d - j) := by
    rw [hd]
    exact Int.gcd_dvd_left _ _
  have h2 : (D : ℤ) ∣ |P.eval x| := by
    have h11 : (D : ℤ) ∣ P.eval x := by
      rw [hd]
      exact Int.gcd_dvd_right _ _
    have h12 : P.eval x ∣ |P.eval x| := by exact self_dvd_abs (eval x P)
    exact Int.dvd_trans h11 h12
  have h3 : x ≠ 0 → D > 0 := by
    intro hx0
    refine Nat.pos_of_ne_zero ?_
    rw [hd]
    refine Nat.gcd_ne_zero_left ?_
    simp only [ne_eq, Int.natAbs_eq_zero, pow_eq_zero_iff']
    push_neg
    intro hxc
    absurd hx0
    exact hxc

  exact And.intro h1 (And.intro h2 h3)


lemma fac_fact_helper_h5' (n p : ℕ) (hassume2 : 2 ≤ n) (hp : Nat.Prime p ∧ n / 2 < p ∧ p ≤ n) (h2' : n < 2 * p) : (n.factorial).factorization p = 1 := by

  let hp1 := hp.1
  let hp2 := hp.2.1
  have hfd : n.factorial = ∏ i ∈ {i ∈ Finset.range (n + 1) | i ≠ 0}, i := by exact fac_as_prod n hassume2
  rw [hfd]
  rw [Nat.factorization_prod]
  have hlema : ∀ i ∈ {i ∈ Finset.range (n + 1) | i ≠ 0 ∧ i ≠ p}, i.factorization p = 0 := by
    intro i h
    simp at h
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    by_contra hc
    apply exists_eq_mul_left_of_dvd at hc
    obtain ⟨k, hk⟩ := hc
    have hk1 : k ≥ 2 := by
      by_contra hc
      push_neg at hc
      apply Nat.le_of_lt_succ at hc
      apply Nat.le_one_iff_eq_zero_or_eq_one.mp at hc
      cases hc with
      | inl hc1 =>
        rw [hc1] at hk
        simp at hk
        let hcontrad := h.2.1
        contradiction
      | inr hc2 =>
        rw [hc2] at hk
        simp at hk
        let hcontrad := h.2.2
        contradiction
    have hineq : i ≥ 2 * p := by
      change 2 ≤ k at hk1
      apply (mul_le_mul_right (a := p) (by exact Nat.zero_lt_of_lt hp2)).2 at hk1
      rw [←hk] at hk1
      exact hk1
    have hc1 : 2 * p < n + 1 := by exact Nat.lt_of_le_of_lt hineq h.1
    apply Nat.le_of_lt_succ at hc1
    have hcc : ¬ (n < 2 * p) := by exact Nat.not_lt.mpr hc1
    contradiction
  have hlema2 : {i ∈ Finset.range (n + 1) | i ≠ 0} = {i ∈ Finset.range (n + 1) | i ≠ 0 ∧ i ≠ p} ∪ {p} := by
    refine Finset.ext_iff.mpr ?_
    intro a
    constructor
    intro ha
    simp at ha ⊢
    refine and_or_right.mpr ?_
    constructor
    constructor
    exact ha.1
    refine and_or_right.mpr ?_
    constructor
    constructor
    exact ha.2
    exact ne_or_eq a p
    simp
    intro ha
    cases ha with
    | inl h =>
      rw [←and_assoc] at h
      exact h.1
    | inr h =>
      rw [h]
      constructor
      exact Order.lt_add_one_iff.2 (hp.2.2)
      push_neg
      exact Nat.ne_zero_of_lt hp2
  rw [hlema2]
  simp
  rw [Finset.sum_union]
  simp
  have hobv : p.factorization p = 1 := by exact Nat.Prime.factorization_self hp1
  rw [hobv]
  simp
  intro i hisu hine hipne
  have hspec : i ∈ {i ∈ Finset.range (n + 1) | i ≠ 0 ∧ i ≠ p} := by
    simp
    exact And.intro hisu (And.intro hine hipne)
  specialize hlema i hspec
  exact hlema
  simp
  intro i hi
  simp at hi
  let hoi := hi.2
  push_neg at hoi
  exact hoi


lemma hrj_hrjc (R Q : ℤ[X]) (d j : ℕ) (SR : Finset ℕ) (HSR : SR = R.support) (hsrn : SR.Nonempty) (hjdef : j = SR.min' hsrn)
  (hr : R = ∑ i ∈ Finset.range (d - 1), C (Q.coeff i) * X ^ i) (hqrh : ∀ i ∈ Finset.range (d - 1), Q.coeff i = R.coeff i)
  :
  j ≤ d - 1 ∧ j ≤ d - 2 ∧ R = ∑ i ∈ (Finset.range (d - 1) \ Finset.range j), C (Q.coeff i) * X ^ i ∧ R = X ^ j * ∑ i ∈ (Finset.range (d - 1) \ Finset.range j), C (Q.coeff i) * X ^ (i - j) := by


  have hsrmin : SR.min' hsrn ∈ SR := by exact Finset.min'_mem SR hsrn
  have hdj2 : j ≤ d - 2 := by
    rw [←hjdef] at hsrmin
    simp only [HSR] at hsrmin
    simp only [hr] at hsrmin
    simp at hsrmin
    let h1111 := hsrmin.1
    cases d with
    | zero =>
      simp
      have h01 : 0 - 1 = 0 := by exact rfl
      rw [h01] at h1111
      have hco : j ≠ 0 := by cases h1111
      contradiction
    | succ n =>
      simp at h1111 ⊢
      exact Nat.le_sub_one_of_lt h1111
  have hjd : j ≤ d - 1 := by
    rw [←hjdef] at hsrmin
    simp only [HSR] at hsrmin
    simp only [hr] at hsrmin
    simp at hsrmin
    let h1111 := hsrmin.1
    exact le_of_lt h1111
  constructor
  exact hjd
  have hrj : R = ∑ i ∈ (Finset.range (d - 1) \ Finset.range j), C (Q.coeff i) * X ^ i := by
    have hrange : Finset.range (d - 1) = (Finset.range (d - 1) \ Finset.range j) ∪ Finset.range j := by
      simp
      exact hjd
    rw [hrange] at hr
    rw [Finset.sum_union] at hr
    swap
    have hdisj : Disjoint (Finset.range (d - 1) \ Finset.range j) (Finset.range j) := by
      rw [disjoint_comm]
      exact Finset.disjoint_sdiff
    exact hdisj
    have hjtail : ∑ x ∈ Finset.range j, C (Q.coeff x) * X ^ x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hji
      simp at hji
      simp
      have hirange : i ∈ Finset.range (d - 1) := by
        simp
        exact Nat.lt_of_lt_of_le hji hjd
      specialize hqrh i hirange
      rw [hqrh]
      simp only [hjdef] at hji
      have hisr : i ∉ SR := by
        contrapose hji
        push_neg at hji ⊢
        exact Finset.min'_le SR i hji
      simp only [HSR] at hisr
      exact Polynomial.not_mem_support_iff.1 hisr
    rw [hjtail] at hr
    simp at hr
    simp
    exact hr
  have hrjc : R = X ^ j * ∑ i ∈ (Finset.range (d - 1) \ Finset.range j), C (Q.coeff i) * X ^ (i - j) := by
    rw [Finset.mul_sum]
    rw [hrj]
    refine Finset.sum_congr ?_ ?_
    simp
    intro i hira
    conv_rhs =>
      rw [mul_comm]
      rw [mul_assoc]
      rw [←pow_add]
    have hhelp : i - j + j = i := by
      apply Nat.sub_add_cancel ?_
      simp at hira
      exact hira.2
    rw [hhelp]
  constructor
  exact hdj2
  exact And.intro hrj hrjc


lemma Q_change_var_cancel_term (P : ℤ[X]) (hdeg : P.degree ≥ 2) (b : ℕ → ℤ) (hb : b = fun i ↦ P.coeff i * (P.natDegree) ^ (P.natDegree - i) * (P.leadingCoeff) ^ (P.natDegree - i - 1))
  (Qq : ℤ[X]) (hqq : Qq = X ^ P.natDegree + ∑ i ∈ Finset.range (P.natDegree), C (b i) * X ^ i) (Q : ℤ[X]) (hq : Q = Qq.comp (X - (P.coeff (P.natDegree - 1) : ℤ[X]))) : Q.coeff (P.natDegree - 1) = 0 := by

    set d := P.natDegree
    set ad := P.leadingCoeff
    have hdd12 : (d - (d - 1)) = 1 := by
      set r := d - 1
      have hr : d = r + 1 := by
        unfold r
        refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
        have hPne0 : P.degree ≠ ⊥ := by
          refine degree_ne_bot.mpr ?_
          exact ne_zero_of_coe_le_degree hdeg
        have hpdeg : P.degree = P.natDegree := by exact Polynomial.degree_eq_natDegree (degree_ne_bot.1 hPne0)
        unfold d
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
    have hchoose : d.choose (d - 1) = d := by
      have hdd1 : d - 1 ≤ d := by exact Nat.sub_le d 1
      have hhelp : d.choose (d - 1) * (d - 1).factorial * (d - (d - 1)).factorial = d.factorial := by exact Nat.choose_mul_factorial_mul_factorial hdd1
      rw [hdd12] at hhelp
      simp at hhelp
      have h1 : d.choose (d - 1) = d.factorial / (d - 1).factorial := by
        rw [mul_comm] at hhelp
        refine Nat.eq_div_of_mul_eq_right (by exact Nat.factorial_ne_zero (d - 1)) hhelp
      have h2 : d.factorial / (d - 1).factorial = d := by
        have hee : d = (d - 1) + 1 := by exact (Nat.sub_eq_iff_eq_add' hdd1).mp hdd12
        have he : d.factorial = ((d - 1) + 1).factorial := by exact congrArg Nat.factorial hee
        rw [he]
        rw [Nat.factorial_succ]
        rw [← hee]
        refine Eq.symm (Nat.eq_div_of_mul_eq_left ?_ rfl)
        exact Nat.factorial_ne_zero (d - 1)
      rw [h2] at h1
      exact h1
    rw [hchoose]
    rw [hdd12]
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
      rw [hb]
      simp
      rw [mul_assoc]
      simp
      constructor
      rw [hdd12]
      simp
    rw [hbu]
    unfold co
    simp


lemma asymp_imp_ineq1 (Q : ℤ[X]) (C2 d : ℕ) (c1 : ℤ) (hc1ne0 : c1 ≠ 0) (hc1absne1 : |c1| ≠ 1) (hd : Q.natDegree = d) (hz : ∀ (z : ℤ), |z| > C2 → (|z| ^ d / 2 : ℝ) < |eval z Q| ∧ |eval z Q| < 2 * |z| ^ d) : ∃ C1, ∀ (z : ℤ) (n : ℕ), C1 > 0 ∧ (|z| > C2 → Q.eval z = c1 * n.factorial → |d * log |z| - log (n.factorial)| < C1) := by


  use (log |c1| + log 2)
  intro x n
  have hcabsi : |c1| > 1 := by
    by_contra hcabs
    push_neg at hcabs
    by_cases habs1 : |c1| = 1
    contradiction
    push_neg at habs1
    have habs0 : |c1| = 0 := by
      have hlt1 : |c1| < 1 := by exact lt_of_le_of_ne hcabs habs1
      have hle0 : |c1| ≥ 0 := by exact abs_nonneg c1
      interval_cases |c1|
      simp
    rw [abs_eq_zero] at habs0
    contradiction

  constructor

  rify at hcabsi
  have hlogc1 : log |c1| > 0 := by exact log_pos hcabsi
  have hlog2 : log 2 > 0 := by exact log_pos (by exact one_lt_two)
  exact Right.add_pos' hlogc1 hlog2

  intro hxg hxn
  have hexact : |↑d * log |↑x| - log ↑n.factorial| < log |↑c1| + log 2 := by
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
    have hxq : |Q.eval x| = |c1| * n.factorial := by
      rw [hxn]
      rw [abs_mul]
      simp
    rw [hxq] at hz
    let hz1 := hz.1
    let hz2 := hz.2
    have hz1l : log (|x| ^ Q.natDegree / 2) < log (|c1| * ↑n.factorial) := by
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
      exact hc1ne0
      have he : 0 < n.factorial := by exact Nat.factorial_pos n
      rify at he
      exact he
    have hz2l : log (|c1| * n.factorial) < log (2 * |x| ^ Q.natDegree) := by
      apply (Real.log_lt_log_iff ?_ ?_).2
      rify at hz2
      simp
      rw [hd]
      exact hz2
      refine mul_pos ?_ ?_
      simp
      push_neg
      exact hc1ne0
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
      have hrw :  - log |c1| - log 2 < log |c1| - log 2 := by
        simp only [sub_lt_sub_iff_right, neg_lt_self_iff]
        refine log_pos ?_
        rify at hcabsi
        exact hcabsi
      refine lt_trans hrw ?_
      rw [Real.log_mul] at hz2l
      swap
      simp
      push_neg
      exact hc1ne0
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
      exact hc1ne0
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


lemma smalls (P : ℤ[X]) (hdeg : P.degree ≥ 2) (d : ℕ) (ad c1 : ℤ) (hd : d = P.natDegree) (had : ad = P.coeff d) (hc1 : c1 = d ^ d * ad ^ (d - 1)) : P.degree ≠ ⊥ ∧ P.degree = P.natDegree ∧ ad ≠ 0 ∧ d ≥ 2 ∧ c1 ≠ 0 ∧ |c1| ≠ 1 := by

  have hPne0 : P.degree ≠ ⊥ := by
    refine degree_ne_bot.mpr ?_
    exact ne_zero_of_coe_le_degree hdeg
  have hpdeg : P.degree = P.natDegree := by exact Polynomial.degree_eq_natDegree (degree_ne_bot.1 hPne0)
  have hd2 : d ≥ 2 := by
    rw [hd]
    refine le_natDegree_of_coe_le_degree ?_
    exact hdeg
  have hadne0 : ad ≠ 0 := by
    rw [hd] at had
    rw [Polynomial.coeff_natDegree] at had
    rw [had]
    have hhelp : ¬ (P.degree = ⊥) → ¬ (P.leadingCoeff = 0) := by
      contrapose
      push_neg
      exact Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot.1
    push_neg at hhelp
    exact hhelp hPne0
  have hdne0 : d ≠ 0 := by
    rw [hpdeg] at hdeg
    simp at hdeg
    by_contra hcd
    rw [hcd] at hd2
    contradiction
  have hc1ne0 : c1 ≠ 0 := by
    rw [hc1]
    refine Int.mul_ne_zero_iff.mpr ?_
    constructor
    simp
    exact pow_ne_zero (d - 1) hadne0
  have hc1absne1 : |c1| ≠ 1 := by
    by_contra hc
    rw [←abs_one] at hc
    rw [abs_eq_abs] at hc
    cases hc with
    | inl h =>
      rw [h] at hc1
      have hm : d ^ d * ad ^ (d - 1) = 1 := by exact id (Eq.symm hc1)
      clear hc1
      rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at hm
      cases hm with
      | inl hm1 =>
        let hdd := hm1.1
        rw [pow_eq_one_iff_of_ne_zero hdne0] at hdd
        cases hdd with
        | inl hdd1 =>
          let hddd := hm1.2
          simp at hdd1
          rw [hdd1] at hd2
          simp at hd2
        | inr hdd2 =>
          have hdgt0 : 0 < (d : ℤ) := by
            simp
            exact Nat.pos_of_ne_zero hdne0
          have hdlt0 : 0 > -1 := by linarith
          rw [←hdd2.1] at hdlt0
          contradiction
      | inr hm2 =>
        let hc := hm2.1
        have hdgt0 : 0 < (d : ℤ) := by
          simp
          exact Nat.pos_of_ne_zero hdne0
        have hdgt0p : 0 < (d : ℤ) ^ d := by exact Lean.Omega.Int.pos_pow_of_pos (↑d) d hdgt0
        rw [hc] at hdgt0p
        contradiction
    | inr h =>
      rw [hc1] at h
      rw [Int.mul_eq_neg_one_iff_eq_one_or_neg_one] at h
      cases h with
      | inl h =>
        let h1 := h.1
        rw [pow_eq_one_iff_of_ne_zero hdne0] at h1
        cases h1 with
        | inl h1 =>
          simp at h1
          rw [h1] at h
          let hc9 := h.2
          simp at hc9
        | inr h1 =>
          have hdgt0 : 0 < (d : ℤ) := by
            simp
            exact Nat.pos_of_ne_zero hdne0
          have hdlt0 : 0 > -1 := by linarith
          rw [←h1.1] at hdlt0
          contradiction
      | inr h =>
        let hc := h.1
        have hdgt0 : 0 < (d : ℤ) := by
          simp
          exact Nat.pos_of_ne_zero hdne0
        have hdgt0p : 0 < (d : ℤ) ^ d := by exact Lean.Omega.Int.pos_pow_of_pos (↑d) d hdgt0
        rw [hc] at hdgt0p
        contradiction
  constructor
  exact hPne0
  constructor
  exact hpdeg
  constructor
  exact hadne0
  constructor
  exact hd2
  constructor
  exact hc1ne0
  exact hc1absne1


lemma polys_changes (P Qq : ℤ[X]) (hdeg : P.degree ≥ 2) (d : ℕ) (ad c1 : ℤ) (hd : d = P.natDegree) (hdne0 : d ≠ 0) (had : ad = P.coeff d) (hc1 : c1 = d ^ d * ad ^ (d - 1))
  (b : ℕ → ℤ) (hbu : b = fun i ↦ P.coeff i * d ^ (d - i) * ad ^ (d - i - 1)) (hQq : Qq = X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i) : (∀ i, (C (b i) * X ^ i).natDegree = if b i ≠ 0 then i else 0) ∧ (P.natDegree = Qq.natDegree) ∧ (c1 • P = Qq.comp ((ad * d) • X)) := by

  have hd11 : 1 ≤ d := by
    have h12 : 2 ≤ d := by
      rw [hd]
      exact le_natDegree_of_coe_le_degree hdeg
    exact Nat.one_le_of_lt h12

  have hcd : ∀ i, (C (b i) * X ^ i).natDegree = if b i ≠ 0 then i else 0 := by
    intro i
    split_ifs with hbne0
    · exact natDegree_C_mul_X_pow i (b i) hbne0
    · push_neg at hbne0
      simp
      rw [hbne0]
      simp

  have hqqdeg : P.natDegree = Qq.natDegree := by
    rw [←hd]
    rw [hQq]
    have hdn0 : 0 < d := by exact Nat.pos_of_ne_zero hdne0
    have hso : ∀ i, C (b i) = ((b i) : ℤ[X]) := by exact fun i ↦ rfl
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
    exact Eq.symm (natDegree_X_pow d)
    refine Polynomial.degree_lt_degree ?_
    rw [natDegree_X_pow d]
    set U := ∑ i ∈ Finset.range d, C (b i) * X ^ i with HU
    have hineq : (∑ x ∈ Finset.range d, C (b x) * X ^ x).natDegree ≤ Finset.fold max 0 (natDegree ∘ fun i ↦ C (b i) * X ^ i ) (Finset.range d) := by exact Polynomial.natDegree_sum_le (Finset.range d) (fun i ↦ C (b i) * X ^ i )
    simp at hineq
    simp only [← hso] at hineq
    simp only [hcd] at hineq
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

  have htry1 : c1 • P = Qq.comp ((ad * d) • X) := by
    simp
    rw [hQq]
    simp only [eq_intCast, add_comp, pow_comp, X_comp, sum_comp, mul_comp, intCast_comp]
    rw [hbu]
    simp
    refine Eq.symm (ext ?_)
    intro i
    simp
    by_cases hii : i > d
  -- case i > d :
    have hpci : P.coeff i = 0 := by
      rw [hd] at hii
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
    rw [← had, h123]
    have hw : (C ((ad * d) ^ d) * X ^ d).coeff d = (ad * d) ^ d := by
      rw [Polynomial.coeff_C_mul_X_pow]
      simp
    rw [hw]
    have hcoef0 : ∑ b ∈ Finset.range d, ((P.coeff b : ℤ[X]) * (d:ℤ[X]) ^ (d - b) * (ad:ℤ[X]) ^ (d - b - 1) * ((ad:ℤ[X]) * (d:ℤ[X]) * X) ^ b).coeff d = 0 := by
      ring_nf
      simp only [←Polynomial.C_eq_intCast, ←Polynomial.C_eq_natCast, ←Polynomial.C_pow]
      repeat simp only [←Polynomial.C_mul]
      simp only [Int.cast_id]
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp
    rw [hcoef0]
    simp
    rw [hc1]
    ring_nf
    have hadp :  ad * ad ^ (d - 1) = ad ^ d := by
      have had1 : ad * ad ^ (d - 1) = ad ^ 1 * ad ^ (d - 1) := by simp
      rw [had1]
      exact pow_mul_pow_sub ad hd11

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
    rw [h12, hc1]
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
  constructor
  exact fun i ↦ hcd i
  constructor
  exact hqqdeg
  exact htry1


/-- `Rzero_imp_false` proves that the case when a polynomial R, defined in the proof, is
--identically zero leads to contradiction-/
lemma Rzero_imp_false (P : ℤ[X]) (n d : ℕ) (x ad c1 : ℤ) (hdeg : P.degree ≥ 2) (hd : d = P.natDegree)
  (had : ad = P.coeff d) (hdne0 : d ≠ 0) (hadne0 : ad ≠ 0) (hc1 : c1 = d ^ d * ad ^ (d - 1))
  (hii : x ^ d = c1 * n.factorial) (hassume2 : n ≥ 2) (hb : n > 2 * c1) : False := by


  have hd2 : d ≥ 2 := by exact (smalls P hdeg d ad c1 hd had hc1).2.2.2.1
  have hc1ne0 : c1 ≠ 0 := by exact (smalls P hdeg d ad c1 hd had hc1).2.2.2.2.1

  have hc1gt0 : c1 > 0 := by
    by_cases hdpar : Odd d
  -- case Odd d :
    have hadpow : ad ^ (d - 1) > 0 := by
      have hd1e : Even (d - 1) := by exact Nat.Odd.sub_odd hdpar (by exact Nat.odd_iff.mpr rfl)
      exact Even.pow_pos hd1e hadne0
    have hddpow : d ^ d > 0 := by exact Nat.pow_self_pos
    rw [hc1]
    zify at hddpow
    exact Int.mul_pos hddpow hadpow
  -- case Even d :
    rw [Nat.not_odd_iff_even] at hdpar
    have hxvne0 : x ^ d ≠ 0 := by
      rw [hii]
      simp
      constructor
      exact hc1ne0
      exact Nat.factorial_ne_zero n
    have hxv : x ≠ 0 := by exact ne_zero_pow hdne0 hxvne0
    have hxvgt0 : x ^ d > 0 := by exact Even.pow_pos hdpar hxv
    rw [hii] at hxvgt0
    have hfac0 : n.factorial > 0 := by exact Nat.factorial_pos n
    zify at hfac0
    exact (pos_iff_pos_of_mul_pos hxvgt0).2 hfac0


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
  have h5' : (n.factorial).factorization p = 1 := by exact fac_fact_helper_h5' n p hassume2 hp h2'
  zify at hp2
  have hps : c1 < p := by
    refine (mul_lt_mul_left (a := 2) (b := c1) (c := p) (by linarith)).1 ?_
    zify at h2'
    exact Int.lt_trans hb h2'
  have h8 : ¬ ((p:ℤ) ∣ c1) := by
    by_contra hi
    have hc1' : p ≤ c1 := by exact Int.le_of_dvd (b := c1) hc1gt0 hi
    have hcontradi : ¬ (p > c1) := by exact Int.not_lt.mpr hc1'
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
  specialize h9' d hd2
  have hpdiv2 : (p:ℤ) ∣ c1 * n.factorial := by
    zify at hpdiv
    exact dvd_mul_of_dvd_right hpdiv c1
  have h3 : (p:ℤ) ∣ x ^ d := by
    rw [hii]
    exact hpdiv2
  have h4 : (p:ℤ) ∣ x := by exact Int.Prime.dvd_pow' hp1 h3
  have h5 : ∃ k : ℤ, x = k * (p:ℤ) := by exact exists_eq_mul_left_of_dvd h4
  obtain ⟨k, h5⟩ := h5
  have h6 : x ^ d = k ^ d * p ^ d := by
    rw [h5]
    ring
  have h7 : (p:ℤ) ^ d ∣ c1 * n.factorial := by
    rw [h6] at hii
    rw [←hii]
    exact Int.dvd_mul_left (k ^ d) (↑p ^ d)
  have h9 : ¬ ((p : ℤ) ^ d ∣ c1 * n.factorial) := by
    by_contra hcc
    have hpint : Prime (p : ℤ) := by exact Nat.prime_iff_prime_int.mp hp1
    have h_c : (p : ℤ) ^ d ∣ n.factorial := by exact Prime.pow_dvd_of_dvd_mul_left hpint d h8 hcc
    zify at h9'
    absurd h_c
    exact h9'

  absurd h9
  exact h7




/-!
* The final intermediate results needed to conclude the main proof. They involve algebraic manipulations
to the terms of the abc-triple to which the integer abc-conjecture, `abc_Z` will be applied.
* `forabc` is the only lemma in this category which depends on the abc-conjecture. It is used
to extract the bounds on set the of solutions using `abc_Z`.
-/

lemma eq25 (Q : ℤ[X]) (d j : ℕ) (c1 : ℤ) (hdne0 : d ≠ 0) (C6 : ℝ → ℝ)
(hc6gt0 : ∀ ε > 0, ε ≠ 1 → ∀ (n : ℕ) (z : ℤ), n ≥ 2 → ↑n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → C6 ε > 0)
: ∃ (ε C9 C10 : ℝ), ∀ (n : ℕ) (z : ℤ), (ε > 0 ∧ C10 > 0 ∧ ε ≠ 1) ∧ (n ≥ 2 → n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → |z| > 1 → |z| ^ (1 + ε - ε * (d - j)) < (C6 ε) * 4 ^ (n * (1 + ε)) → d * log |z| < C9 * n + C10) := by

  set e := (1 : ℝ) / (2 * d) with he
  have he0 : e > 0 := by
    unfold e
    simp
    exact Nat.zero_lt_of_ne_zero hdne0
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
    absurd hdne0
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

  intro hn2 hn2c1 hz heval hzabs1 h
  specialize hc6gt0 e he0 hene1 n z hn2 hn2c1 hz heval

  have hzabs0 : 0 < |z| := by exact abs_pos.mpr hz
  rify at hzabs1
  have hdgt0 : 0 < d := by exact Nat.zero_lt_of_ne_zero hdne0
  rify at hdgt0
  have hhelp1 : 0 < (|z| : ℝ) ^ ((1 : ℝ) / 2) := by
    refine rpow_pos_of_pos ?_ (1 / 2)
    simp
    exact hz
  have hhelp2 : 0 < (C6 e) * 4 ^ (↑n * (1 + e)) := by
    refine mul_pos hc6gt0 ?_
    refine rpow_pos_of_pos (by linarith) ((n:ℝ) * (1 + e))
  have hhelp3 : (4 : ℝ) ^ (↑n * (1 + e)) ≠ 0 := by
    refine (rpow_ne_zero (by linarith) ?_).mpr (by simp)
    simp
    constructor
    exact very_simple n hn2
    push_neg
    refine Ne.symm (ne_of_lt ?_)
    exact lt_trans he0 (lt_one_add e)
  have hdinv : (d : ℝ) * (d : ℝ)⁻¹ = 1 := by exact CommGroupWithZero.mul_inv_cancel (d : ℝ) (by exact Nat.cast_ne_zero.mpr hdne0)
  have h1 : (|z| : ℝ) ^ ((1 : ℝ) / 2) < |z| ^ (1 + e - e * (d - j)) := by
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
    have hh1 : (d:ℝ)⁻¹ * 2⁻¹ + (↑d)⁻¹ * ↑j * 2⁻¹ = (↑d)⁻¹ * 2⁻¹ * (1 + j) := by ring
    rw [hh1]
    refine mul_pos ?_ ?_
    simp at hdgt0 ⊢
    exact hdgt0
    have hj00 : 0 ≤ j := by exact Nat.zero_le j
    rify at hj00
    have hj01 : (j:ℝ) > -1 := by exact gt_of_ge_of_gt hj00 (by linarith)
    exact neg_lt_iff_pos_add'.mp hj01
  rify at hzabs0
  have h2 : (|z| : ℝ) ^ ((1 : ℝ) / 2) < (C6 e) * 4 ^ (↑n * (1 + e)) := by exact gt_trans h h1
  rw [←Real.log_lt_log_iff hhelp1 hhelp2] at h2
  rw [Real.log_mul (by exact Ne.symm (ne_of_lt hc6gt0)) hhelp3] at h2
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
      exact Nat.zero_lt_of_ne_zero hdne0
      exact le_abs_self (log c6)
    have hh2 : 2 * ↑d * log c6 = 2 * ↑d * log c6 + 0 := by simp
    rw [hh2]
    refine add_le_add hh1 (by linarith)


  have h4 : ↑d * log |↑z| < (2 * ↑d + 1) * log 4 * ↑n + (2 * ↑d * |log c6| + 1) := by exact gt_of_ge_of_gt h3 h2
  exact h4


lemma eq1015 (Q : ℤ[X]) (d : ℕ) (c1 : ℤ) (C1 C2 C9 C10 : ℝ) (hc1 : C1 > 0) (hc10 : C10 > 0) : ∃ C11 : ℝ, ∀ (n : ℕ) (z : ℤ), C11 > 0 ∧ (|z| > C2 → (eval z Q = c1 * ↑n.factorial → |↑d * log |↑z| - log ↑n.factorial| < C1 → d * log |z| < C9 * n + C10 → log (n.factorial) < C9 * n + C11)) := by

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


lemma ygtM (d : ℕ) (x ad adm : ℤ) (hd : d ≠ 0) (had : ad ≠ 0) (M : ℝ) (h : |x| > (M + (|adm| : ℝ)) / (|ad * d| : ℝ)) : |ad * d * x + adm| > M := by
  have hww : ↑|x| = |(x : ℝ)| := by exact Int.cast_abs
  have hw : ↑|adm| = |(adm : ℝ)| := by exact Int.cast_abs
  have hmabs : 0 < |ad * d| := by
    simp
    exact And.intro had hd
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
    exact gt_of_ge_of_gt ht1 ht2
  have hf : M = ↑|ad * ↑d| * w - ↑|adm| := by
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_natCast]
    rw [Eq.symm (b := M)]
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


lemma rad_lt22 (P Q R R1 : ℤ[X]) (d j C3 C4 : ℕ) (ad c1 : ℤ) (D : ℤ → ℕ) (hjd2 : j ≤ d - 2) (hd2 : d ≥ 2) (hd : D = fun z ↦ Int.gcd (z ^ (d - j)) (R1.eval z)) (hC3gt1 : C3 > 1) (hc1ne0 : c1 ≠ 0) (hdeg : P.degree ≥ 2)
(hPd : d = P.natDegree) (had : ad = P.coeff d) (hdne0 : d ≠ 0) (hadne0 : ad ≠ 0) (hc1 : c1 = d ^ d * ad ^ (d - 1)) (hQ : Q = X ^ d + R) (hrjc : R = X ^ j * R1)
(h15 : ∀ z : ℤ, |z| > C4 → |R1.eval z| < (C3:ℝ) * (|z| ^ (d - j - 2)))
: ∀ (n : ℕ) (z : ℤ), z ≠ 0 → |z| > C4 → n ≥ 2 → n > 2 * |c1| → eval z Q = c1 * ↑n.factorial → rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) < |z| * (((C3:ℝ) * |z| ^ (d - j - 2)) / D z) * 4 ^ n := by        --|z| * ((C3 * |z| ^ (d - j - 2)) / D z) * 4 ^ n

  intro n z hz0 hz4 hn2 hnc12abs hqeval

  have hn2c1 : n > 2 * c1 := by
    have hc1abs : 2 * |c1| ≥ 2 * c1 := by
      simp
      exact le_abs_self c1
    exact Int.lt_of_le_of_lt hc1abs hnc12abs

----GENERALS:
  --generals for polynomials:

  have hQeval_at : Q.eval z = z ^ d + R.eval z := by
    have hiii : Q.eval z = (X ^ d + R).eval z := by exact congrArg (eval z) hQ
    simp at hiii
    exact hiii
  have hR1eval : R.eval z = z ^ j * R1.eval z := by
    have h111 : R.eval z = (X ^ j * R1).eval z := by exact congrArg (eval z) hrjc
    simp at h111
    exact h111
  have hR1Qeval : Q.eval z = z ^ d + z ^ j * R1.eval z := by rw [hQeval_at, ←hR1eval]


  have hc3 : C3 > 0 := by exact Nat.zero_lt_of_lt hC3gt1
  have hzpjne0 : z ^ j ≠ 0 := by exact pow_ne_zero j hz0
  have hdzne0 : D z ≠ 0 := by exact Nat.ne_zero_of_lt ((D_gcd_poly R1 d j (D z) z (congrFun hd z)).2.2 hz0)
  have hDgt0 : D z > 0 := by exact Nat.zero_lt_of_ne_zero hdzne0
  have hqdvd : ↑(D z) ∣ eval z R1 := by
    --have hddvdd : ↑(D z) ∣ |eval z R1| := by exact (D_gcd_poly R1 d j (D z) z (congrFun hd z)).2.1
    --have hdesl : |eval z R1| ∣ eval z R1 := by exact abs_dvd_self (eval z R1)
    simp_rw [hd]
    exact Int.gcd_dvd_right _ _
  have hdzdvdzp : ↑(D z) ∣ z ^ (d - j) := by exact (D_gcd_poly R1 d j (D z) z (congrFun hd z)).1
  have hzpowne0 : z ^ (d - j) ≠ 0 := by exact pow_ne_zero (d - j) hz0


  have h19 : rad (Int.natAbs (z ^ (d - j) / D z)) ≤ |z| := by
    set u := z ^ (d - j) / (D z) with hu
    have hune0 : u ≠ 0 := by
      unfold u
      by_contra hco
      have hcon : z ^ (d - j) = 0 := by exact Int.eq_zero_of_ediv_eq_zero hdzdvdzp hco
      absurd hzpowne0
      exact hcon
    have huu : u * (D z) = z ^ (d - j) := by
      unfold u
      rw [mul_comm]
      exact Int.mul_ediv_cancel' ((D_gcd_poly R1 d j (D z) z (congrFun hd z)).1)
    have huabs := congr_arg Int.natAbs huu
    rw [Int.natAbs_mul] at huabs
    rw [Int.natAbs_natCast] at huabs
    have hrad1 : rad (u.natAbs) ≤ rad (u.natAbs * (D z)) := by
      refine rad_dvd_le (u.natAbs * (D z)) u.natAbs ?_ (by simp)
      simp
      exact And.intro hune0 hdzne0
    have hrad2 : rad (u.natAbs * (D z)) ≤ |z| := by
      have hh : (z ^ (d - j)).natAbs = (z.natAbs) ^ (d - j) := by
        zify
        simp
      rw [huabs, hh]
      have h1 : (rad (z.natAbs ^ (d - j))) ≤ z.natAbs := by exact rad_pow_le z.natAbs (d - j) (Int.natAbs_ne_zero.mpr hz0)
      zify at h1
      exact h1
    zify at hrad1
    exact Int.le_trans hrad1 hrad2


  have h20 : rad (R1.eval z / D z).natAbs < ((C3:ℝ) * |z| ^ (d - j - 2)) / D z := by
    by_cases heval : R1.eval z = 0
  -- case R1.eval z = 0 :
    rw [heval] at hR1Qeval
    simp at hR1Qeval
    rw [hqeval] at hR1Qeval
    have hfalse : False := by exact Rzero_imp_false P n d z ad c1 hdeg hPd had hdne0 hadne0 hc1 (id (Eq.symm hR1Qeval)) hn2 hn2c1
    exact False.elim hfalse
  -- case R1.eval z ≠ 0 :
    push_neg at heval
    --Int.lt_ediv_iff_mul_lt
    have h1 : rad (R1.eval z / (D z)).natAbs ≤ |R1.eval z| / (D z) := by
      have hi1 : rad (R1.eval z / (D z)).natAbs ≤ (R1.eval z / (D z)).natAbs := by
        refine radx_le_x (R1.eval z / (D z)).natAbs ?_
        simp
        contrapose heval
        push_neg at heval ⊢
        refine Int.eq_zero_of_ediv_eq_zero (d := (D z)) ?_ heval
        rw [hd]
        exact Int.gcd_dvd_right _ _
      have hexact : |R1.eval z| / (D z) = (R1.eval z / (D z)).natAbs := by
        simp
        refine abs_div_eq_div (R1.eval z) (D z) (Int.ofNat_pos.mpr hDgt0) hqdvd
      rw [hexact]
      simp
      zify at hi1
      exact hi1
    specialize h15 z hz4
    have hineq : |eval z R1| / (D z : ℝ) < ↑C3 * |z| ^ (d - j - 2) / (D z : ℝ) := by exact div_lt_div_of_pos_right h15 (Nat.cast_pos'.mpr hDgt0)
    have hdivcast : ↑(|eval z R1| / (D z : ℤ)) = (|eval z R1| / (D z) : ℝ) := by
      refine Int.cast_div ((D_gcd_poly R1 d j (D z) z (congrFun hd z)).2.1) ?_
      simp
      exact hdzne0
    rw [←hdivcast] at hineq
    rify at h1
    exact lt_of_le_of_lt h1 hineq



  have h21 : rad (Int.natAbs ((c1 * n.factorial) / (z ^ j * D z))) ≤ 4 ^ n := by
    let hcopy := hqeval
    rw [hQeval_at] at hqeval
    rw [hR1eval] at hqeval
    have hdj : d = j + (d - j) := by omega
    rw [hdj] at hqeval
    have hzdj : z ^ (j + (d - j)) = z ^ j * z ^ (d - j) := by ring
    rw [hzdj] at hqeval
    have hfactor : z ^ j * z ^ (d - j) + z ^ j * eval z R1 = z ^ j * (z ^ (d - j) + eval z R1) := by ring
    rw [hfactor, ←hcopy] at hqeval
    have hqzdvd : z ^ j ∣ Q.eval z := by exact Dvd.intro (z ^ (d - j) + eval z R1) hqeval
    let hqevals := hqeval.symm
    apply (Int.ediv_eq_of_eq_mul_right hzpjne0) at hqevals
    have h1 : (eval z Q / z ^ j) / (D z) = (z ^ (d - j) + eval z R1) / (D z) := by exact congrFun (congrArg HDiv.hDiv hqevals) (D z : ℤ)
    rw [Int.add_ediv_of_dvd_right hqdvd] at h1

    have hdivdiv : Q.eval z / z ^ j / (D z : ℤ) = Q.eval z / (z ^ j * (D z : ℤ)) := by  --exact Int.ediv_ediv_eq_ediv_mul
      have hdzqdvdd : (D z : ℤ) ∣ Q.eval z / z ^ j := by
        set fr := z ^ (d - j) / ↑(D z) + eval z R1 / ↑(D z)
        rw [hqevals]
        exact (Int.dvd_add_right hdzdvdzp).mpr hqdvd
      exact Int.ediv_ediv_eq_ediv_mul_dvd (Q.eval z) hdzqdvdd
    rw [hdivdiv] at h1
    have hudvd : (z ^ j * ↑(D z)) ∣ c1 * ↑n.factorial := by
      rw [← hcopy]
      refine Int.mul_dvd_of_dvd_div hqzdvd ?_
      rw [hqevals]
      simp_rw [hd]
      exact (Int.dvd_add_right (Int.gcd_dvd_left _ _)).mpr (Int.gcd_dvd_right _ _)


    set u := c1 * ↑n.factorial / (z ^ j * ↑(D z))
    have hune0 : u ≠ 0 := by
      unfold u
      have hfacne0 : n.factorial ≠ 0 := by exact Nat.factorial_ne_zero n
      zify at hfacne0
      exact int_div_ne_zero hc1ne0 hfacne0 hudvd

    have hu : u * (z ^ j * ↑(D z)) = c1 * n.factorial := by
      unfold u
      rw [mul_comm]
      refine Int.mul_ediv_cancel' ?_
      have hqddvd : z ^ j * ↑(D z) ∣ c1 * ↑n.factorial := by
        rw [← hcopy]
        refine Int.mul_dvd_of_dvd_div hqzdvd ?_
        rw [hqevals]
        simp_rw [hd]
        refine (Int.dvd_add_right ?_).mpr ?_
        exact Int.gcd_dvd_left _ _
        exact Int.gcd_dvd_right _ _
      exact hqddvd
    have huabs := congr_arg Int.natAbs hu
    rw [Int.natAbs_mul] at huabs
    have hrad1 : rad (u.natAbs) ≤ rad (u.natAbs * (z ^ j * ↑(D z)).natAbs) := by
      refine rad_dvd_le (u.natAbs * (z ^ j * ↑(D z)).natAbs) u.natAbs ?_ (Nat.dvd_mul_right u.natAbs (z ^ j * ↑(D z)).natAbs)
      simp
      constructor
      exact hune0
      constructor
      intro hzc
      absurd hz0
      exact hzc
      exact hdzne0
    have hrad2 : rad (u.natAbs * (z ^ j * ↑(D z)).natAbs) = rad ((c1 * ↑n.factorial).natAbs) := by exact congrArg rad huabs
    rw [hrad2] at hrad1
    have hrad3 : rad (c1 * ↑n.factorial).natAbs ≤ 4 ^ n := by
      rw [Int.natAbs_mul]
      have hs : ((n.factorial) : ℤ).natAbs = n.factorial := by exact rfl
      rw [hs]
      have hc1abs : c1.natAbs ≤ n := by
        zify
        have hn11 : n > |c1| := by exact gt_trans hnc12abs (lt_two_mul_self (abs_pos.mpr hc1ne0))
        exact Int.le_of_lt hn11
      rw [rad_le n c1.natAbs (by exact Int.natAbs_ne_zero.mpr hc1ne0) hc1abs]
      rw [rad_eq_primorial]
      exact primorial_le_4_pow n
    exact Nat.le_trans hrad1 hrad3

  have hhelpge0 : 0 ≤ |z| * ((C3:ℝ) * |z| ^ (d - j - 2) / ↑(D z)) := by
    simp
    refine mul_nonneg (by exact abs_nonneg (z:ℝ)) ?_
    refine div_nonneg (mul_nonneg (Nat.cast_nonneg' C3) (pow_nonneg (by exact abs_nonneg (z:ℝ)) (d - j - 2))) (Nat.cast_nonneg' (D z))

  have hrw : (rad (z ^ (d - j) / ↑(D z) * (eval z R1 / ↑(D z)) * (c1 * ↑n.factorial / (z ^ j * ↑(D z)))).natAbs) ≤ rad ((z ^ (d - j) / D z).natAbs) * rad ((R1.eval z / D z).natAbs) * rad (((c1 * n.factorial) / (z ^ j * D z)).natAbs) := by
    rw [Int.natAbs_mul]
    rw [Int.natAbs_mul]
    set a := (z ^ (d - j) / ↑(D z)).natAbs * (eval z R1 / ↑(D z)).natAbs
    set s := (c1 * ↑n.factorial / (z ^ j * ↑(D z))).natAbs
    have h1 : rad (a * s) ≤ rad a * rad s := by exact rad_mul_le a s
    set c := (z ^ (d - j) / ↑(D z)).natAbs
    set w := (eval z R1 / ↑(D z)).natAbs
    have ha : a = c * w := by
      unfold c w
      exact rfl
    have hrad2 : rad (c * w) ≤ rad c * rad w := by exact rad_mul_le c w
    rw [ha] at h1
    have h2 : rad (c * w) * rad s ≤ rad c * rad w * rad s := by exact Nat.mul_le_mul_right (rad s) hrad2
    have h3 : rad (c * w * s) ≤ rad c * rad w * rad s := by exact Nat.le_trans h1 h2
    rw [ha]
    exact h3
  set w := z ^ (d - j) / ↑(D z)
  set r := (eval z R1 / ↑(D z))
  set t := (c1 * ↑n.factorial / (z ^ j * ↑(D z)))
  have h1 : rad w.natAbs * rad r.natAbs < |z| * (((C3:ℝ) * |z| ^ (d - j - 2)) / ↑(D z)) := by
    rify at h19
    set a1 := (rad w.natAbs : ℝ)
    set b1 := (rad r.natAbs : ℝ)
    simp at h20 ⊢
    set d1 := ((C3:ℝ) * |(z:ℝ)| ^ (d - j - 2)) / ↑(D z)
    set c1' := (|z|:ℝ)
    refine mul_lt_mul_of_nonneg_of_pos' h19 h20 ?_ ?_
    unfold b1
    simp
    unfold c1'
    simp
    exact hz0
  have h2 : (rad w.natAbs : ℝ) * rad r.natAbs * rad t.natAbs < |z| * ((C3:ℝ) * |z| ^ (d - j - 2) / ↑(D z)) * 4 ^ n := by
    set a1 := (rad w.natAbs : ℝ) * rad r.natAbs
    set c1' := |z| * ((C3:ℝ) * |z| ^ (d - j - 2) / ↑(D z))
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

/-- `forabc` is the lemma used for extracting the bounds on the set of solutions by
applying `abc_Z` to the desired abc-triple.-/
lemma forabc (P Q R R1 : ℤ[X]) (d j : ℕ) (ad c1 : ℤ) (D : ℤ → ℕ) (hdd : D = fun z ↦ Int.gcd (z ^ (d - j)) (R1.eval z)) (hdeg : P.degree ≥ 2) (hd : d = P.natDegree)  (hdne0 : d ≠ 0) (had : ad = P.coeff d) (hadne0 : ad ≠ 0) (hc1 : c1 = ↑d ^ d * ad ^ (d - 1)) (hR1Qeval : ∀ (z : ℤ), eval z Q = z ^ d + z ^ j * eval z R1)
  (hjd2 : j ≤ d - 2) (hQ : Q = X ^ d + R) (hrjc : R = X ^ j * R1)
  : abc_Z → (∃ (C5 : ℝ → ℝ), ∀ (ε : ℝ) , ε > 0 → ε ≠ 1 → (∀ (n : ℕ) (z : ℤ), n ≥ 2 → n > 2 * c1 → z ≠ 0 → Q.eval z = c1 * n.factorial → C5 ε > 0 ∧ |z ^ (d - j) / D z| < (C5 ε) * rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) ^ (1 + ε))) := by

    unfold abc_Z
    intro abcz
    obtain ⟨C5, habc⟩ := abcz
    use C5
    intro e he hene1 n z hnge2 hngt hz0 heval
    constructor


    specialize habc e he 1 1 2
    simp at habc
    have hcop : IsCoprime (1 : ℤ) 1 := by exact isCoprime_one_left
    specialize habc hcop
    rw [rad2_eq2] at habc
    have htrans : 0 < C5 e * ↑2 ^ (1 + e) := lt_trans (by linarith) habc
    refine (mul_pos_iff_of_pos_right (Real.rpow_pos_of_pos (by linarith) (1 + e))).1 htrans

    specialize habc e he

    set r := z ^ (d - j) / ↑(D z) with hr'
    set t := (eval z R1 / ↑(D z)) with ht
    set s := (c1 * ↑n.factorial / (z ^ j * ↑(D z))) with hs

    --- generals:
    have hzpowne0 : z ^ (d - j) ≠ 0 := by exact pow_ne_zero (d - j) hz0
    have hDne0 : (D z) ≠ 0 := by exact Nat.pos_iff_ne_zero.mp ((D_gcd_poly R1 d j (D z) z (congrFun hdd z)).2.2 hz0)
    have hddvdzpow : (D z : ℤ)∣ z ^ (d - j) := by exact (D_gcd_poly R1 d j (D z) z (congrFun hdd z)).1
    have hddvdr1eval : (D z : ℤ) ∣ R1.eval z := by exact Int.dvd_trans ((D_gcd_poly R1 d j (D z) z (congrFun hdd z)).2.1) (abs_dvd_self (R1.eval z))
    have hqevalne0 : R1.eval z ≠ 0 := by
      by_contra hc
      have heev : Q.eval z = z ^ d + z ^ j * R1.eval z := by exact hR1Qeval z
      rw [hc] at heev
      simp at heev
      rw [heval] at heev
      exact Rzero_imp_false P n d z ad c1 hdeg hd had hdne0 hadne0 hc1 (by exact id (Eq.symm heev)) hnge2 hngt

    specialize habc r t s

    have h1 : r ≠ 0 := by
      unfold r
      rify at hDne0
      by_contra hc
      have hcup : z ^ (d - j) = 0 := by exact Int.eq_zero_of_ediv_eq_zero hddvdzpow hc
      absurd hcup
      exact hzpowne0
    have h2 : t ≠ 0 := by
      unfold t
      rify at hDne0
      by_contra hc
      have hcup : R1.eval z = 0 := by exact Int.eq_zero_of_ediv_eq_zero hddvdr1eval hc
      absurd hcup
      exact hqevalne0

    have h3 : r + t = s := by
      have hqeval : Q.eval z = z ^ d + R.eval z := by
        have hh : Q.eval z = (X ^ d + R).eval z := by exact congrArg (eval z) hQ
        simp at hh
        exact hh
      have hreval : R.eval z = z ^ j * R1.eval z := by
        have hh : R.eval z = (X ^ j * R1).eval z := by exact congrArg (eval z) hrjc
        simp at hh
        exact hh
      rw [hreval] at hqeval
      have hdj : d = j + (d - j) := by omega
      rw [hdj] at hqeval
      have hzdj : z ^ (j + (d - j)) = z ^ j * z ^ (d - j) := by ring
      rw [hzdj] at hqeval
      have hfactor : z ^ j * z ^ (d - j) + z ^ j * eval z R1 = z ^ j * (z ^ (d - j) + eval z R1) := by ring
      rw [hfactor] at hqeval
      have hqdvd : z ^ j ∣ Q.eval z := by exact Dvd.intro (z ^ (d - j) + eval z R1) (Eq.symm (hqeval))
      apply (Int.ediv_eq_of_eq_mul_right (pow_ne_zero j hz0)) at hqeval
      have h1' : (eval z Q / z ^ j) / (D z) = (z ^ (d - j) + eval z R1) / (D z) := by exact congrFun (congrArg HDiv.hDiv hqeval) (D z : ℤ)
      rw [Int.add_ediv_of_dvd_right ?_] at h1'
      swap
      exact hddvdr1eval

      have hdivdiv : Q.eval z / z ^ j / (D z : ℤ) = Q.eval z / (z ^ j * (D z : ℤ)) := by  -------------- update lemma
        have hdzqdvdd : (D z : ℤ) ∣ Q.eval z / z ^ j := by
          set fr := z ^ (d - j) / ↑(D z) + eval z R1 / ↑(D z)
          rw [hqeval]
          exact (Int.dvd_add_right hddvdzpow).mpr hddvdr1eval
        exact Int.ediv_ediv_eq_ediv_mul_dvd (Q.eval z) hdzqdvdd
      rw [hdivdiv] at h1'
      rw [heval] at h1'
      rw [←hr', ←ht, ←hs] at h1'
      exact id (Eq.symm h1')

    have h4 : IsCoprime r t := by
      have hdz : D z = (z ^ (d - j)).gcd (eval z R1) := by exact congrFun hdd z
      rw [hdz] at ht
      set r1 := z ^ (d - j) with hr1
      set t1 := eval z R1 with ht1
      refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
      rw [hr', ht]
      rw [hdz]
      exact Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_left hzpowne0
    specialize habc h1 h2 h3 h4
    refine lt_of_le_of_lt (by simp) habc


lemma forabc22 (Q R1 : ℤ[X]) (d j C3 C4 : ℕ) (hd2 : d ≥ 2) (hdj : j ≤ d - 2) (c1 : ℤ) (C5 : ℝ → ℝ) (D : ℤ → ℕ) (hd : D = fun z ↦ Int.gcd (z ^ (d - j)) (R1.eval z)) (hc3 : C3 > 0) (hC5gt0 : ∀ ε > 0, ε ≠ 1 → ∀ (n : ℕ) (z : ℤ), n ≥ 2 → ↑n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → C5 ε > 0)
 : ∀ ε : ℝ, ∃ (C6 : ℝ), ε > 0 → ε ≠ 1 → ∀ (n : ℕ) (z : ℤ), (n ≥ 2 → n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → (C6 > 0 ∧ (|z| > ↑C4 → |z ^ (d - j) / D z| < (C5 ε) * rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) ^ (1 + ε) → rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) < |z| * (((C3:ℝ) * |z| ^ (d - j - 2)) / D z) * 4 ^ n → ((|z| : ℤ) ^ (d - j) / (D z : ℤ) : ℤ) < C6 * (|z| ^ (d - j - 1) / D z * 4 ^ n) ^ (1 + ε)))) := by

  intro e
  set c6 := (C5 e) * C3 ^ (1 + e)
  use c6
  intro he hegt n z hn2 hngt hz0 heval
  specialize hC5gt0 e he hegt n z hn2 hngt hz0 heval
  have hc3c5 : (C5 e) * C3 ^ (1 + e) > 0 := by
    refine mul_pos ?_ ?_
    exact hC5gt0
    refine rpow_pos_of_pos ?_ (1 + e)
    simp
    exact hc3
  constructor
  unfold c6
  exact hc3c5

  intro hzgt habc' h22'

  --generals:
  have hddjdvd : ↑(D z) ∣ |z| ^ (d - j) := by
    have hinter : ↑(D z) ∣ z ^ (d - j) := by exact (D_gcd_poly R1 d j (D z) z (congrFun hd z)).1
    have hinter2 : z ^ (d - j) ∣ |z| ^ (d - j) := by exact pow_dvd_pow_of_dvd (self_dvd_abs z) (d - j)
    exact Int.dvd_trans hinter hinter2
  have hDgt0 : D z > 0 := by exact (D_gcd_poly R1 d j (D z) z (congrFun hd z)).2.2 hz0
  have hDne0 : D z ≠ 0 := by exact Nat.ne_zero_of_lt hDgt0


  set v := ↑(rad (z ^ (d - j) / (D z : ℤ) * (eval z R1 / (D z : ℤ)) * (c1 * n.factorial / (z ^ j * (D z : ℤ)))).natAbs)
  have hv0 : v > 0 := by
    unfold v
    set vin := ((z ^ (d - j) / (D z : ℤ) * (eval z R1 / (D z : ℤ)) * (c1 * ↑n.factorial / (z ^ j * (D z : ℤ)))).natAbs)
    exact rad_gt_0 vin
  have hee : 1 + e > 0 := by exact lt_trans he (lt_one_add e)

  have habs :  |z ^ (d - j) / (D z : ℤ)| = |z| ^ (d - j) / (D z : ℤ) := by
    have habspow : |z| ^ (d - j) = |z ^ (d - j)| := by exact pow_abs z (d - j)
    rw [habspow]
    exact (abs_div_eq_div (z ^ (d - j)) (D z : ℤ) (Int.ofNat_pos.mpr hDgt0) ((D_gcd_poly R1 d j (D z) z (congrFun hd z)).1)).symm
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
  have hrew : |(z:ℝ)| ^ (1:ℕ) * |(z:ℝ)| ^ (d - j - 2) = |(z:ℝ)| ^  (d - j - 1) := by
    rw [←pow_add]
    have hf : 1 + (d - j - 2) = d - j - 1 := by omega
    rw [hf]
  simp at hrew
  rw [hrew] at h22'
  apply Real.rpow_lt_rpow (z := 1 + e) (Nat.cast_nonneg' v) at h22'
  specialize h22' hee
  apply mul_lt_mul_of_pos_left (a := (C5 e)) at h22'
  specialize h22' hC5gt0
  apply mul_lt_mul_of_pos_right (a := (D z : ℝ)) at h22'
  specialize h22' (Nat.cast_pos'.mpr hDgt0)
  have hf : C5 e * (|↑z| ^ (d - j - 1) * ↑C3 * (↑(D z))⁻¹ * 4 ^ n) ^ (1 + e) * ↑(D z) = C5 e * ↑C3 ^ (1 + e) * (|↑z| ^ (d - j - 1) * (↑(D z))⁻¹ * 4 ^ n) ^ (1 + e) * ↑(D z) := by
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


lemma abcrw (Q R1 : ℤ[X]) (d j C4 : ℕ) (hjd2 : j ≤ d - 2) (hd2 : d ≥ 2) (c1 : ℤ) (C6 : ℝ → ℝ) (D : ℤ → ℕ) (hd : D = fun z ↦ Int.gcd (z ^ (d - j)) (R1.eval z)) (hc6gt0 : ∀ ε > 0, ε ≠ 1 → ∀ (n : ℕ) (z : ℤ), n ≥ 2 → ↑n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → C6 ε > 0)
: ∀ (n : ℕ) (z : ℤ) (ε : ℝ), ε > 0 → ε ≠ 1 → (eval z Q = c1 * ↑n.factorial) → z ≠ 0 → |z| > C4 → n ≥ 2 → n > 2 * c1 → ((|z| : ℤ) ^ (d - j) / (D z : ℤ) : ℤ) < (C6 ε) * (|z| ^ (d - j - 1) / D z * 4 ^ n) ^ (1 + ε) → |z| ^ (1 + ε - ε * (d - j)) < (C6 ε) * 4 ^ (n * (1 + ε)) := by

  intro n z e he hene1 heval hz0 hzc4 hn2 hn2c1 h
  specialize hc6gt0 e he hene1 n z hn2 hn2c1 hz0 heval

  -- generals:
  have hddjdvd : ↑(D z) ∣ |z| ^ (d - j) := by
    have hinter : ↑(D z) ∣ z ^ (d - j) := by exact (D_gcd_poly R1 d j (D z) z (congrFun hd z)).1
    have hinter2 : z ^ (d - j) ∣ |z| ^ (d - j) := by exact pow_dvd_pow_of_dvd (self_dvd_abs z) (d - j)
    exact Int.dvd_trans hinter hinter2
  have hDgt0 : D z > 0 := by exact (D_gcd_poly R1 d j (D z) z (congrFun hd z)).2.2 hz0
  have hDne0 : D z ≠ 0 := by exact Nat.ne_zero_of_lt hDgt0

  rw [Int.cast_div hddjdvd] at h
  swap
  simp
  exact hDne0
  simp at h ⊢
  have h1 : |z| ^ (d - j) < (C6 e) * |z| ^ ((d - j - 1) * (1 + e)) * 4 ^ (n * (1 + e)) := by
    simp at h ⊢
    rw [← inv_mul_eq_div] at h
    set a1 := (D z : ℝ) with ha1
    set b1 := (|z| : ℝ) ^ (d - j)
    set c1' :=  (C6 e) * (|↑z| ^ (d - j - 1) / a1 * 4 ^ n) ^ (1 + e)
    rw[inv_mul_lt_iff₀ ?_] at h
    swap
    unfold a1
    simp
    exact hDgt0
    have h2 : a1 * c1' = (C6 e) * ((((|z| : ℝ) ^ ((d - j - 1) * (1 + e))) * 4 ^ (n * (1 + e))) / ((D z) ^ e)) := by
      rw [mul_comm]
      unfold c1'
      rw [mul_assoc]
      refine mul_eq_mul_left_iff.2 ?_
      constructor
      have hcalc1 : ((|z| : ℝ) ^ (d - j - 1) / a1 * 4 ^ n) ^ (1 + e) * a1 = ((|z| : ℝ) ^ (d - j - 1) / a1) ^ (1 + e) * (4 ^ n) ^ (1 + e) * a1 := by
        refine mul_eq_mul_right_iff.2 ?_
        constructor
        have hr1 : 0 ≤ |↑z| ^ (d - j - 1) / a1 := by
          refine div_nonneg ?_ ?_
          exact pow_nonneg (by exact abs_nonneg (z:ℝ)) (d - j - 1)
          unfold a1
          simp
        refine Real.mul_rpow hr1 (by simp)
      rw [hcalc1]
      have hr2 : (0 : ℝ) ≤ |↑z| ^ (d - j - 1) := by exact pow_nonneg (by exact abs_nonneg (z:ℝ)) (d - j - 1)
      rw [Real.div_rpow (x := |↑z| ^ (d - j - 1)) (y := a1) hr2 ?_ (1 + e)]
      swap
      unfold a1
      simp
      have hr3 : (|↑z| ^ (d - j - 1)) ^ (1 + e) = (|z| : ℝ) ^ ((d - j - 1) * (1 + e)) := by
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
      set zp := (|z| : ℝ) ^ ((↑d - ↑j - 1) * (1 + e))
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
    set up := (((|z| : ℝ) ^ ((d - j - 1) * (1 + e))) * 4 ^ (n * (1 + e)))
    set down := ((D z : ℝ) ^ e)
    have h3 : (C6 e) * (up / down) ≤ (C6 e) * up := by
      refine mul_le_mul_of_nonneg_left ?_ (by exact le_of_lt hc6gt0)
      refine div_le_self ?_ ?_
      unfold up
      have hex : (0 : ℝ) ≤ |↑z| ^ ((↑d - ↑j - 1) * (1 + e)) * 4 ^ (n * (1 + e)) := by
        have hq1 : 0 ≤ (|z| : ℝ) ^ ((↑d - ↑j - 1) * (1 + e)) := by
          set p := ((↑d - ↑j - 1) * (1 + e))
          refine Real.rpow_nonneg ?_ p
          simp
        have hq2 : 0 ≤ (4 : ℝ) ^ (↑n * (1 + e)) := by
          set p := (↑n * (1 + e))
          refine Real.rpow_nonneg ?_ p
          linarith
        exact mul_nonneg hq1 hq2
      exact hex
      unfold down
      have hdge1 : 1 ≤ D z := by exact hDgt0
      rify at hdge1
      have hrew : 1 = (D z : ℝ) ^ (0 : ℝ) := by exact Eq.symm (rpow_zero (D z : ℝ))
      rw [hrew]
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      exact hdge1
      exact le_of_lt he
    have h4 : b1 < (C6 e) * up := by
      rw [h2] at h
      exact gt_of_ge_of_gt h3 h
    unfold up at h4
    rw [←mul_assoc] at h4
    exact h4

  rw [mul_comm, ←mul_assoc] at h1
  set a1 := 4 ^ (↑n * (1 + e)) * (C6 e) with ha1
  simp at h1
  set b1 := (|z| : ℝ) ^ ((↑d - ↑j - 1) * (1 + e))
  set c1' := (|z| : ℝ) ^ (d - j)
  rw [mul_comm] at h1
  have hb1gt0 : b1 > 0 := by
    unfold b1
    refine rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hz0)) (((d:ℝ) - (j:ℝ) - 1) * (1 + e))
  apply (inv_mul_lt_iff₀ hb1gt0).2 at h1
  have hf : b1⁻¹ * c1' = (|z| : ℝ) ^ (1 + e - e * (↑d - ↑j)) := by
    rw [←Real.rpow_neg_one]
    have hr1 : b1 ^ (- (1 : ℝ)) = (|z| : ℝ) ^ (- ((↑d - ↑j - 1) * (1 + e))) := by
      unfold b1
      rw [←Real.rpow_mul (by exact abs_nonneg (z : ℝ))]
      simp
    rw [hr1]
    unfold c1'
    have hcru : ↑(d - j) = ((d - j) : ℝ) := by exact Nat.cast_sub (by omega)
    have hzpoww : |(z:ℝ)| ^ (d - j) = |(z:ℝ)| ^ ((d - j) : ℝ) := by
      rw [← Real.rpow_natCast]
      refine congrArg (HPow.hPow (|z| : ℝ)) hcru
    rw [hzpoww]
    rify at hz0
    rw [←Real.rpow_add (abs_pos.2 hz0)]
    rw [←hcru]
    refine congrArg (HPow.hPow (|z| : ℝ)) (casting_help d j hjd2 hd2 e)
  simp
  conv_rhs => rw [mul_comm]
  rw [←hf, ←ha1]
  exact h1


/-- The logarithmic inequality which implies the boundedness of a natural number n, used as the final
step in proving the main result, `abc_Z_imp_poly_eq_fac_finite_sol`.-/
lemma logn_le_bounded (c9 c11 : ℝ) (hc11 : c11 > 0) : ∃ (c12 : ℝ), ∀ n : ℕ, 4 ≤ n → log (n.factorial) < c9 * n + c11 → n < c12 := by
  set c12 := Nat.ceil (rexp (c9 + c11 + 1))
  use c12
  intro n hn hi'
  have h1 : c9 * n + c11 < c9 * n + c11 * n := by
    simp
    rw [mul_comm]
    rw [lt_mul_iff_one_lt_left]
    refine Nat.one_lt_cast.mpr ?_
    linarith
    exact hc11
  have hi : Real.log (n.factorial) < c9 * n + c11 * n := by
    rify at h1
    exact gt_trans h1 hi'
  clear hi' h1
  have hn_stirling : n.factorial > ((n:ℝ) ^ n * (1 / ((rexp 1) ^ n))) := by
    have hh : n.factorial > 4 * ((n:ℝ) ^ n * (1 / ((rexp 1) ^ n))) := by exact first_ineq n hn
    have hh2 : 4 * ((n:ℝ) ^ n * (1 / ((rexp 1) ^ n))) > ((n:ℝ) ^ n * (1 / ((rexp 1) ^ n))) := by
      change ((n:ℝ) ^ n * (1 / ((rexp 1) ^ n))) < 4 * ((n:ℝ) ^ n * (1 / ((rexp 1) ^ n)))
      rw [lt_mul_iff_one_lt_left]
      linarith
      refine mul_pos ?_ ?_
      refine lt_pow_of_log_lt ?_ ?_
      simp
      linarith
      simp
      refine mul_pos ?_ ?_
      simp
      linarith
      refine (log_pos_iff ?_).mpr ?_
      simp
      simp
      linarith
      simp
      exact exp_pos ↑n
    exact gt_trans hh hh2
  have hi2 : n.factorial < rexp (c9 * n + c11 * n) := by
    refine (log_lt_iff_lt_exp ?_).mp hi
    simp
    exact Nat.factorial_pos n
  have hhs : n ^ n * (1 / rexp 1 ^ n) = (n / rexp 1) ^ n := by ring
  rw [hhs] at hn_stirling
  clear hhs
  have hineq : (n / rexp 1) ^ n < rexp (c9 * n + c11 * n) := by exact gt_trans hi2 hn_stirling
  have hineq' : (n / rexp 1) ^ (n:ℝ) < rexp (c9 * n + c11 * n) := by
    simp
    exact hineq
  clear hineq
  conv_rhs at hineq' =>
    rw [← right_distrib]
    rw [ Real.exp_mul]
  have hineq2 : (n / rexp 1) < rexp (c9 + c11) := by
    have hn1r : 1 < (n:ℝ) := by
      have ht : 1 < n := by linarith
      rify at ht
      exact ht
    apply (Real.rpow_lt_rpow_iff ?_ ?_ ?_).1
    exact hineq'
    rw [le_div_iff₀]
    simp
    exact exp_pos 1
    exact exp_nonneg (c9 + c11)
    simp
    exact Nat.zero_lt_of_lt hn
  clear hineq'
  rw [div_lt_iff₀] at hineq2
  swap
  exact exp_pos 1
  rw [← Real.exp_add] at hineq2
  have hf : n < c12 := by exact Nat.lt_ceil.mpr hineq2
  rify at hf
  exact hf


/-!
* The main theorem: the abc-conjecture implies that there are finitely many integer solutions
of the equation P(x) = n!, for any polynomial P with integer coefficients and of degree at least 2.
* `main_imp_Brocard` proposes another proof of the original Brocard-Ramanujan problem,
by specializing in the general result the polynomial P(x) = x² - 1.
-/




/-- Main Theorem: If P is a polynomial with integer coefficients and of degree at least 2, then the
equation P(x) = n! has finitely many pairs of integer solutions, assuming the abc-conjecture.-/
theorem abc_Z_imp_poly_eq_fac_finite_sol (P : Polynomial ℤ) (hdeg : P.degree ≥ 2) :
  abc_Z → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , (P.eval x = n.factorial) → (n < N) ∧ (|x| < N)) := by

  unfold abc_Z
  intro abcz


  let f (i : ℕ) : ℤ := i.factorial
  refine assume P hdeg f ?_
  unfold f

  set d := P.natDegree with hd
  set ad := P.coeff d with had
  set c1 := d ^ d * ad ^ (d - 1) with hc1

  have hPne0 : P.degree ≠ ⊥ := by exact (smalls P hdeg d ad c1 hd had hc1).1

  have hpdeg : P.degree = P.natDegree := by exact (smalls P hdeg d ad c1 hd had hc1).2.1

  have hd2 : d ≥ 2 := by exact (smalls P hdeg d ad c1 hd had hc1).2.2.2.1
  have hdne0 : d ≠ 0 := by exact very_simple d hd2

  have hadne0 : ad ≠ 0 := by exact (smalls P hdeg d ad c1 hd had hc1).2.2.1

  have hc1ne0 : c1 ≠ 0 := by exact (smalls P hdeg d ad c1 hd had hc1).2.2.2.2.1

  have hc1absne1 : |c1| ≠ 1 := by exact (smalls P hdeg d ad c1 hd had hc1).2.2.2.2.2


  let b (i : ℕ) : ℤ := P.coeff i * d ^ (d - i) * ad ^ (d - i - 1)
  have hbu : b = fun i ↦ P.coeff i * d ^ (d - i) * ad ^ (d - i - 1) := by exact rfl

  set Qq : ℤ[X] := X ^ d + ∑ i ∈ Finset.range d, C (b i) * X ^ i with hQq

  have hcd : ∀ i, (C (b i) * X ^ i).natDegree = if b i ≠ 0 then i else 0 := by exact (polys_changes P Qq hdeg d ad c1 hd hdne0 had hc1 b hbu hQq).1

  have hqqdeg : P.natDegree = Qq.natDegree := by exact (polys_changes P Qq hdeg d ad c1 hd hdne0 had hc1 b hbu hQq).2.1

  have htry1 : c1 • P = Qq.comp ((ad * d) • X) := by exact (polys_changes P Qq hdeg d ad c1 hd hdne0 had hc1 b hbu hQq).2.2



  have hPrw : ∀ x : ℤ, (c1 • P).eval x = (Qq.comp ((ad * d) • X)).eval x := by exact fun x ↦ congrArg (eval x) htry1
  have hQprw : ∀ x : ℤ, P.eval x = ((Qq.comp ((ad * d) • X)).eval x) / c1 := by
    intro x
    specialize hPrw x
    simp at hPrw
    refine Int.eq_ediv_of_mul_eq_right hc1ne0 ?_
    rw [hPrw]
    simp

  set Y : ℤ[X] := X - (P.coeff (d - 1) : ℤ[X]) with hy
  set Q : ℤ[X] := Qq.comp Y with hq
  have hY_degree : Y.natDegree = 1 := by
    rw [hy]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    exact natDegree_X
    simp
  have hQdegree : Q.natDegree = P.natDegree := by
    rw [hq]
    rw [Polynomial.natDegree_comp]
    rw [hY_degree]
    simp
    exact Eq.symm hqqdeg
  have hQdmin1 : Q.coeff (d - 1) = 0 := by
    unfold Y at hq
    exact Q_change_var_cancel_term P hdeg b hbu Qq hQq Q hq


  have hQmonic : Q.Monic := by
    rw [hq]
    refine Polynomial.Monic.comp ?_ ?_ ?_
    refine Monic.add_of_left ?_ ?_
    exact monic_X_pow d
    rw [degree_X_pow]
    simp
    rw [← Fin.sum_univ_eq_sum_range]
    apply Polynomial.degree_sum_fin_lt (fun i : Fin d => b i)
    unfold Y
    change (X - C (P.coeff (d - 1))).Monic
    apply Polynomial.monic_X_sub_C
    rw [hY_degree]
    exact Nat.one_ne_zero


  have hQxe : ∀ x : ℤ, Q.eval (ad * d * x + P.coeff (d - 1)) = Qq.eval (ad * d * x) := by
    intro x
    rw [hq]
    simp
    rw [hy]
    simp
  let xval (x : ℤ) : ℤ := ad * d * x + P.coeff (d - 1)

  have h1asymp : ∃ N : ℕ, ∀ z : ℤ, N > 0 ∧ ((|z| > N) → (|z| ^ Q.natDegree) / (2 : ℝ) < |Q.eval z| ∧ |Q.eval z| < 2 * (|z| ^ Q.natDegree)) := by exact poly_asymp_Z Q hQmonic

  obtain ⟨C2, hz'⟩ := h1asymp
  choose hC2gt0 hz using hz'
  specialize hC2gt0 1


  have hd' : Q.natDegree = d := by exact hQdegree

  rw [hd'] at hz

  have h1 : ∃ C1, ∀ (z : ℤ) (n : ℕ), C1 > 0 ∧ (|z| > C2 → Q.eval z = c1 * n.factorial → |d * log |z| - log (n.factorial)| < C1) := by exact asymp_imp_ineq1 Q C2 d c1 hc1ne0 hc1absne1 hd' hz
  obtain ⟨C1, h1⟩ := h1
  choose hC1gt0 h1 using h1
  specialize hC1gt0 1 1

  have hQ : Q = X ^ Q.natDegree + ∑ i ∈ Finset.range Q.natDegree, C (Q.coeff i) * X ^ i := by exact Monic.as_sum hQmonic
  rw [hQdegree, ←hd] at hQ

  have hQ' : ∑ i ∈ Finset.range d, C (Q.coeff i) * X ^ i = ∑ i ∈ Finset.range (d - 1), C (Q.coeff i) * X ^ i := by
    have hfs : Finset.range d = (Finset.range (d - 1)) ∪ {d - 1} := by
      have hdr : d = (d - 1) + 1 := by omega
      conv_lhs =>
        rw [hdr]
      rw [Finset.range_add_one]
      rw [Finset.insert_eq]
      exact Finset.union_comm {d - 1} (Finset.range (d - 1))
    rw [hfs]
    rw [Finset.sum_union (by simp)]
    have hdm1 : ∑ x ∈ {d - 1}, C (Q.coeff x) * X ^ x = 0 := by
      simp
      exact hQdmin1
    rw [hdm1]
    simp

  rw [hQ'] at hQ


  set R : ℤ[X] := ∑ i ∈ Finset.range (d - 1), C (Q.coeff i) * X ^ i with hr

  have hQeval_at : ∀ z : ℤ, Q.eval z = z ^ d + R.eval z := by
    intro z
    have hiii : Q.eval z = (X ^ d + R).eval z := by exact congrArg (eval z) hQ
    simp at hiii
    exact hiii

  have hqrh : ∀ i ∈ Finset.range (d - 1), Q.coeff i = R.coeff i := by
    intro i hd1
    simp at hd1
    rw [hQ]
    rw [Polynomial.finset_sum_coeff]
    rw [Polynomial.coeff_add]
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
    rw [hr]
    simp



  let hqcopy := hQ


  by_cases hR : R = 0
-- case R = 0:
  rw [hR] at hQ
  simp at hQ
  use (max 2 ((2 * c1).natAbs + 1))
  intro n x h
  by_cases hb : n ≤ 2 * c1
-- case n ≤ 2 * c1:
  simp
  rw [Or.comm]
  constructor
  have ehgttss : 2 * c1 < |2 * c1| + 1 := by
    have h11 : 2 * c1 ≤ |2 * c1| := by exact le_abs_self (2 * c1)
    exact Int.lt_add_one_iff.mpr h11
  zify
  exact Int.lt_of_le_of_lt hb ehgttss
-- case n > 2 * c1:
  push_neg at hb
  by_cases hassume2 : n < 2
-- case n < 2:
  simp
  constructor
  exact hassume2
-- case n ≥ 2:
  push_neg at hassume2
  let hi := h
  rw [hQprw] at hi
  simp at hi
  have hii : Qq.eval (ad * d * x) = c1 * n.factorial := by exact Qq_eval_fac n x P Qq hdeg b d ad c1 hc1ne0 hd hc1 hbu hQq h hQprw



  clear hi
  specialize hQxe x
  rw [←hQxe] at hii
  rw [hQ] at hii
  simp at hii
  have hxrw : xval x = ad * d * x + P.coeff (d - 1) := by exact rfl
  rw [← hxrw] at hii
  set xv := xval x



  have hfalse : False := by exact Rzero_imp_false P n d xv ad c1 hdeg hd had hdne0 hadne0 hc1 hii hassume2 hb
  exact False.elim hfalse

  -- case R ≠ 0:
  push_neg at hR

  set SR := R.support with HSR
  have hsrn : SR.Nonempty := by
    unfold SR
    simp
    push_neg
    exact hR
  have hsrmin : SR.min' hsrn ∈ SR := by exact Finset.min'_mem SR hsrn
  set j := SR.min' hsrn with hjdef
  have hjd : j ≤ d - 1 := by exact (hrj_hrjc R Q d j SR HSR hsrn hjdef hr hqrh).1
  have hjd2 : j ≤ d - 2 := by exact (hrj_hrjc R Q d j SR HSR hsrn hjdef hr hqrh).2.1
  unfold SR at hsrmin



  set cj := R.coeff j

  have hrj : R = ∑ i ∈ (Finset.range (d - 1) \ Finset.range j), C (Q.coeff i) * X ^ i := by exact (hrj_hrjc R Q d j SR HSR hsrn hjdef hr hqrh).2.2.1
  have hrjc : R = X ^ j * ∑ i ∈ (Finset.range (d - 1) \ Finset.range j), C (Q.coeff i) * X ^ (i - j) := by exact (hrj_hrjc R Q d j SR HSR hsrn hjdef hr hqrh).2.2.2


  set R1 := ∑ i ∈ Finset.range (d - 1) \ Finset.range j, C (Q.coeff i) * X ^ (i - j)

  have hR1eval : ∀ z : ℤ, R.eval z = z ^ j * R1.eval z := by
    intro z
    have h111 : R.eval z = (X ^ j * R1).eval z := by exact congrArg (eval z) hrjc
    simp at h111
    exact h111

  have hR1Qeval : ∀ z : ℤ, Q.eval z = z ^ d + z ^ j * R1.eval z := by
    intro z
    rw [(hQeval_at z), ←(hR1eval z)]

  have hnebot : R1.degree ≠ ⊥ := by
    simp
    by_contra hc
    rw [hc] at hrjc
    simp at hrjc
    absurd hR
    exact hrjc



  have h15 : ∃ C4 C3 : ℕ, ∀ z : ℤ, C4 > 1 ∧ C3 > 1 ∧ (|z| > C4 → |R1.eval z| < (C3:ℝ) * (|z| ^ (d - j - 2))) := by exact h15_asymp Q R1 d j hd2 hnebot rfl
  obtain ⟨C4, C3, h15⟩ := h15

  choose hC4gt1 hC3gt1 h15 using h15
  specialize hC4gt1 1
  specialize hC3gt1 1
  have hC4gt0 : C4 > 0 := by exact Nat.zero_lt_of_lt hC4gt1
  have hC3gt0 : C3 > 0 := by exact Nat.zero_lt_of_lt hC3gt1


  let D (x : ℤ) : ℕ := Int.gcd (x ^ (d - j)) (R1.eval x)


  have hforabc : ∃ (C5 : ℝ → ℝ), ∀ (ε : ℝ) , ε > 0 → ε ≠ 1 → (∀ (n : ℕ) (z : ℤ), n ≥ 2 → n > 2 * c1 → z ≠ 0 → Q.eval z = c1 * n.factorial → C5 ε > 0 ∧ |z ^ (d - j) / D z| < (C5 ε) * rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) ^ (1 + ε)) := by exact forabc P Q R R1 d j ad c1 D rfl hdeg hd hdne0 had hadne0 hc1 (fun z ↦ hR1Qeval z) hjd2 hQ hrjc abcz
  obtain ⟨C5, habc⟩ := hforabc
  choose hC5gt0 habc using habc

  have h22 : ∀ (n : ℕ) (z : ℤ), z ≠ 0 → |z| > C4 → n ≥ 2 → n > 2 * |c1| → eval z Q = c1 * ↑n.factorial → rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) < |z| * (((C3:ℝ) * |z| ^ (d - j - 2)) / D z) * 4 ^ n := by exact rad_lt22 P Q R R1 d j C3 C4 ad c1 D hjd2 hd2 rfl hC3gt1 hc1ne0 hdeg hd had hdne0 hadne0 hc1 hQ hrjc h15

  have hforabc22 : ∀ ε : ℝ, ∃ (C6 : ℝ), ε > 0 → ε ≠ 1 → ∀ (n : ℕ) (z : ℤ), (n ≥ 2 → n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → (C6 > 0 ∧ (|z| > ↑C4 → |z ^ (d - j) / D z| < (C5 ε) * rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) ^ (1 + ε) → rad (Int.natAbs ((z ^ (d - j) / D z) * (R1.eval z / D z) * ((c1 * n.factorial) / (z ^ j * D z)))) < |z| * (((C3:ℝ) * |z| ^ (d - j - 2)) / D z) * 4 ^ n → ((|z| : ℤ) ^ (d - j) / (D z : ℤ) : ℤ) < C6 * (|z| ^ (d - j - 1) / D z * 4 ^ n) ^ (1 + ε)))) := by exact forabc22 Q R1 d j C3 C4 hd2 hjd2 c1 C5 D rfl hC3gt0 hC5gt0
  choose C6 hc6gt0 hforabc22 using hforabc22

  have habcrw : ∀ (n : ℕ) (z : ℤ) (ε : ℝ), ε > 0 → ε ≠ 1 → (eval z Q = c1 * ↑n.factorial) → z ≠ 0 → |z| > C4 → n ≥ 2 → n > 2 * c1 → ((|z| : ℤ) ^ (d - j) / (D z : ℤ) : ℤ) < (C6 ε) * (|z| ^ (d - j - 1) / D z * 4 ^ n) ^ (1 + ε) → |z| ^ (1 + ε - ε * (d - j)) < (C6 ε) * 4 ^ (n * (1 + ε)) := by exact abcrw Q R1 d j C4 hjd2 hd2 c1 C6 D rfl hc6gt0

  have h25 : ∃ (ε C9 C10 : ℝ), ∀ (n : ℕ) (z : ℤ), (ε > 0 ∧ C10 > 0 ∧ ε ≠ 1) ∧ (n ≥ 2 → n > 2 * c1 → z ≠ 0 → eval z Q = c1 * ↑n.factorial → |z| > 1 → |z| ^ (1 + ε - ε * (d - j)) < (C6 ε) * 4 ^ (n * (1 + ε)) → d * log |z| < C9 * n + C10) := by exact eq25 Q d j c1 hdne0 C6 hc6gt0
  obtain ⟨e, C9, C10, h25⟩ := h25
  choose hcombo h25 using h25
  specialize hcombo 1 2
  let hegt0 := hcombo.1
  let hC10gt0 := hcombo.2.1
  let hene1 := hcombo.2.2

  have h1025 : ∃ C11 : ℝ, ∀ (n : ℕ) (z : ℤ), C11 > 0 ∧ (|z| > (C2 : ℝ) → (eval z Q = c1 * ↑n.factorial → |↑d * log |↑z| - log ↑n.factorial| < C1 → d * log |z| < C9 * n + C10 → log (n.factorial) < C9 * n + C11)) := by exact eq1015 Q d c1 C1 C2 C9 C10 hC1gt0 hC10gt0
  obtain ⟨C11, h1025⟩ := h1025
  choose hc11gt0 h1025 using h1025
  specialize hc11gt0 1 1


  obtain ⟨C12, hfinal⟩ := logn_le_bounded C9 C11 hc11gt0

  let M := (max C2 C4 : ℝ)
  let w := (M + |P.coeff (d - 1)|) / |ad * d|
  refine assume_x_gt P (Nat.ceil w) ?_
  let Nuse := max (max (c1.natAbs + 1) (max (Nat.ceil C12) 4)) ((2 * c1).natAbs + 1)
  use Nuse
  intro n x hx h

  set y := xval x
  have hqeval : Q.eval y = c1 * n.factorial := by
    unfold y
    unfold xval
    rw [hQxe]
    exact Qq_eval_fac n x P Qq hdeg b d ad c1 hc1ne0 hd hc1 hbu hQq h hQprw

  have hgeuse : |y| > M := by
    unfold y xval
    have hxr : (|x| : ℝ) > w := by
      rify at hx
      have htr : w ≤ Nat.ceil w := by exact Nat.le_ceil w
      exact lt_of_le_of_lt htr hx
    unfold w at hxr
    set adm := P.coeff (d - 1)
    simp only [Int.cast_abs, Int.cast_mul, Int.cast_natCast] at hxr
    conv_lhs at hxr => simp only [←Int.cast_abs]
    exact ygtM d x ad adm hdne0 hadne0 M hxr

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

  specialize h1 y n hyc2 hqeval
  specialize h15 y hyc4

  by_cases hn4 : n < 4
-- case n < 4:
  unfold Nuse
  simp
  right; right; left
  exact hn4
-- case n ≥ 4:
  push_neg at hn4
  have hn2 : n ≥ 2 := by exact Nat.le_trans (by linarith) hn4

  by_cases hn2c1a : n ≤ 2 * |c1|
--case n ≤ 2 * c1:
  unfold Nuse
  simp
  rw [Or.comm]
  constructor
  zify
  have hasbs : |2 * c1| = 2 * |c1| := by exact abs_mul 2 c1
  rw [← hasbs] at hn2c1a
  right; right
  exact Int.lt_of_le_of_lt hn2c1a (Int.lt_succ |2 * c1|)
-- case n > 2 * |c1|:
  push_neg at hn2c1a
  by_cases hnc1a : n ≤ |c1|
-- case n ≤ |c1|:
  unfold Nuse
  simp
  constructor
  zify
  exact Int.lt_add_one_iff.mpr hnc1a

--  n ≥ 4 ∧ n > |c1| ∧ n > 2 * |c1|:
  push_neg at hnc1a

  have hn2c1 : n > 2 * c1 := by
    have hc1abs : 2 * |c1| ≥ 2 * c1 := by
      simp
      exact le_abs_self c1
    exact Int.lt_of_le_of_lt hc1abs hn2c1a
  have hnc1 : n > c1 := by exact Int.lt_of_le_of_lt (le_abs_self c1) hnc1a

  specialize habc e hegt0 hene1 n y hn2 hn2c1 hyne0 hqeval

  specialize h22 n y hyne0 hyc4 hn2 hn2c1a hqeval
  specialize hforabc22 e hegt0 hene1 n y hn2 hn2c1 hyne0 hqeval hyc4 habc h22
  specialize habcrw n y e hegt0 hene1 hqeval hyne0 hyc4 hn2 hn2c1 hforabc22
  specialize h25 n y hn2 hn2c1 hyne0 hqeval hy1 habcrw

  rify at hyc2
  simp only [Int.cast_abs] at h1025
  specialize h1025 n y hyc2 hqeval h1 h25

  specialize hfinal n hn4 h1025

  unfold Nuse
  simp
  right; left
  convert Nat.lt_ceil.2 hfinal


--#print axioms abc_Z_imp_poly_eq_fac_finite_sol


/-- The original Brocard-Ramanujan problem, this time proven using the main result, `abc_Z_imp_poly_eq_fac_finite_sol`-/
theorem main_imp_Brocard : abc_Z → (∃ (N : ℕ) , ∀ (x y : ℕ) , (x.factorial + 1 = y^2) → (x ≤ N) ∧ (y ≤ N)) := by

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
  use M
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
  constructor
  exact le_of_lt hpol.1
  exact le_of_lt hpol.2


--#print axioms main_imp_Brocard
