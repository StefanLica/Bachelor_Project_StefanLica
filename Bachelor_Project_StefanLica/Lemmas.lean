import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.Rify
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination'

open Polynomial
open Real


/-!
# Main lemmas used for proving theorems

This file consists of most of the 'basic' lemmas used for proving the theorems.
None of the lemmas proven in this file depend on the abc-conjecture.
The radical of a natural number, `rad`, is defined as the product of prime factors.

## Main statements

-/




/-- The radical of a natural number, defined as the product of its prime factors.-/
def rad (a : ℕ) : ℕ := a.primeFactors.prod id


/-!
## Basic lemmas about the radical of a natural number, divisibility and casting.
-/


lemma rad2_eq2 : rad 2 = 2 := by
  unfold rad
  unfold Nat.primeFactors
  unfold Nat.primeFactorsList
  unfold Nat.primeFactorsList
  decide


lemma abs_div_eq_div (a b : ℤ) (hb : b > 0) (hd : b ∣ a) : |a| / b = |a / b| := by
  cases abs_choice a with
  | inl hl =>
    rw [hl]
    have hpos : a / b ≥ 0 := by exact Int.ediv_nonneg (abs_eq_self.mp hl) (Int.le_of_lt hb)
    exact Eq.symm (abs_of_nonneg hpos)
  | inr hr =>
    rw [hr]
    have negd : -a / b = -(a / b) := by exact Int.neg_ediv_of_dvd hd
    rw [negd]
    have hneg : a / b ≤ 0 := by
      refine Int.ediv_le_of_le_mul hb ?_
      simp
      exact abs_eq_neg_self.mp hr
    exact Eq.symm (abs_of_nonpos hneg)


/--A slight variation of an already existing lemma in Mathlib: `Int.ediv_ediv_eq_ediv_mul`.
Instead of assuming n to be nonnegative, another sufficient condition was found, namely : k ∣ m / n. -/
lemma Int.ediv_ediv_eq_ediv_mul_dvd (m : ℤ) {n k : ℤ} (hdvd : k ∣ m / n) : m / n / k = m / (n * k) := by
  by_cases hn : 0 ≤ n
  exact Int.ediv_ediv_eq_ediv_mul m hn
  push_neg at hn
  set v := - n
  have hvpos : v > 0 := by
    unfold v
    simp
    exact hn
  have hvn : n = - v := by
    unfold v
    simp
  rw [hvn]
  have hnegmul : (-v * k) = - (v * k) := by simp
  rw [hnegmul]
  rw [Int.ediv_neg]
  conv_rhs => rw [Int.ediv_neg]
  rw [Int.neg_ediv_of_dvd]
  simp
  exact Int.ediv_ediv_eq_ediv_mul m (Int.le_of_lt hvpos)
  unfold v
  simp
  exact hdvd


lemma int_div_ne_zero {a b c d : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hdvd : c * d ∣ a * b) : (a * b) / (c * d) ≠ 0 := by
  by_contra hco
  have hab : a * b = 0 := by exact Int.eq_zero_of_ediv_eq_zero hdvd hco
  apply Int.mul_eq_zero.mp at hab
  cases hab with
  | inl h => exact ha h
  | inr h => exact hb h


lemma casting_help (d j : ℕ) (hjd2 : j ≤ d - 2) (hd : d ≥ 2) (e : ℝ) : -((↑(d - j) - 1) * (1 + e)) + ↑(d - j) = 1 + e - e * ↑(d - j) := by
  have hj : d ≥ j := by omega
  simp [hj]
  ring


lemma very_simple (d : ℕ) : d ≥ 2 → d ≠ 0 := by
  intro h
  by_contra hc
  rw [hc] at h
  simp at h


lemma nat_lt_two_iff {n : ℕ} : n < 2 ↔ n = 0 ∨ n = 1 := by
  constructor
  intro hn
  refine Nat.le_and_le_add_one_iff.1 ?_
  constructor
  exact Nat.zero_le n
  simp
  exact Nat.le_of_lt_succ hn
  intro hor
  cases hor with
  | inl h => exact Nat.lt_succ_of_lt (Nat.lt_one_iff.2 h)
  | inr h => linarith


lemma rad_ne_0 (x : ℕ) : rad x ≠ 0 := by
    unfold rad
    rw [Finset.prod_ne_zero_iff]
    aesop


lemma rad_gt_0 (x : ℕ) : 0 < rad x := by
  have h_rad_ne_0 : rad x ≠ 0 := by
    unfold rad
    rw [Finset.prod_ne_zero_iff]
    aesop
  exact Nat.zero_lt_of_ne_zero h_rad_ne_0


lemma rad_gt_1 (x : ℕ) (hx : 2 ≤ x) : 1 < rad x := by
  by_contra hc
  push_neg at hc
  have hrad_gt_0 : 0 < rad x := by exact rad_gt_0 x
  have h_eq : 1 ≤ rad x := by exact Nat.add_one_le_of_lt hrad_gt_0
  have h1 : 1 = rad x := by exact le_antisymm h_eq hc
  have h_ge2 : rad x ≥ 2 := by
    unfold rad
    cases x with
    | zero => contradiction
    | succ x' =>
      cases x' with
      | zero => contradiction
      | succ n =>
        set a := n + 1 + 1 with ha
        have hhh : a.primeFactors.Nonempty := by
          exact (Nat.nonempty_primeFactors).2 hx
        rcases hhh with ⟨p, hp⟩
        have hprime : Nat.Prime p := by exact Nat.prime_of_mem_primeFactors hp
        apply Nat.le_trans (Nat.Prime.two_le hprime)
        simp
        have hneed : ∀ i ∈ a.primeFactors, 1 ≤ id i := by
          intro i hii
          simp
          have hiprime : Nat.Prime i := by exact Nat.prime_of_mem_primeFactors hii
          exact Nat.Prime.one_le hiprime
        apply Finset.single_le_prod' hneed hp
  linarith


lemma y_odd (x y : ℕ) (hx : 4 ≤ x) (ha : x.factorial + 1 = y^2) : Odd y := by
  have h03 : 2 ≤ x := by linarith
  have hxf_even : ¬(Odd x.factorial) := by
      simp
      have hxf_div : 2 ∣ x.factorial := by
        apply Nat.factorial_dvd_factorial h03
      apply even_iff_two_dvd.2 hxf_div
  have hx1_odd : Odd (x.factorial + 1) := by
    have hh : ¬(Odd x.factorial) → Odd (x.factorial + 1) := by
      exact Nat.odd_add_one.2
    exact hh hxf_even
  have hy_sq_odd : Odd (y^2) := by
    rw [← ha]
    exact hx1_odd
  have ht2 : 2 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one 1)
  have hyi_odd : Odd (y^2) → Odd y := by
    contrapose!
    simp
    intro hye
    exact (Nat.even_pow' ht2).2 hye
  exact hyi_odd (ha ▸ hx1_odd)


lemma gcd_xy (x y : ℕ) (ha : x.factorial + 1 = y^2) : Nat.gcd x.factorial (y^2) = 1 := by
  rw [←ha]
  apply Nat.coprime_self_add_right.2
  exact Nat.gcd_one_right x.factorial


lemma rad_eq_2_pow_2 (x p : ℕ) (hx : x ≠ 0) (hp : Nat.Prime p) : p = rad x ↔ ∃ n : ℕ, x = p ^ n ∧ n ≠ 0 := by
  constructor
  · intro hrad
    have hp' : Prime p := by exact Nat.prime_iff.mp hp
    unfold rad at hrad
    have hdiv : ∀ q ∈ x.primeFactors, q ∣ p := by
      intro q hq
      rw [hrad]
      exact Finset.dvd_prod_of_mem id hq
    have hqeq : ∀ q ∈ x.primeFactors, q = p := by
      intro q hq
      specialize hdiv q hq
      have qprime : Nat.Prime q := by exact Nat.prime_of_mem_primeFactors hq
      exact (Nat.prime_dvd_prime_iff_eq qprime hp).1 hdiv
    have hpf : x.primeFactors = {p} := by
      apply Finset.ext
      intro q
      constructor
      · intro hq
        rw [Finset.mem_singleton]
        specialize hqeq q hq
        exact hqeq
      · intro hq
        rw [Finset.mem_singleton] at hq
        refine (Nat.mem_primeFactors_of_ne_zero hx).mpr ?_
        constructor
        rw [hq]
        exact hp
        rw [hq, hrad]
        simp
        exact Nat.prod_primeFactors_dvd x
    have hx_prime_fac : x = x.factorization.prod fun p i ↦ p ^ i := by exact Eq.symm (Nat.factorization_prod_pow_eq_self hx)
    have h_prime_fac : x = ∏ p ∈ x.factorization.support, p ^ (x.factorization p) := by
      simp
      conv => --nth_rw
        lhs
        rw [hx_prime_fac]
      rw [Finsupp.prod_of_support_subset]
      exact fun ⦃a⦄ a ↦ a
      exact fun i a ↦ rfl
    clear hx_prime_fac
    simp at h_prime_fac
    rw [hpf] at h_prime_fac
    simp at h_prime_fac
    use x.factorization p
    constructor
    exact h_prime_fac
    apply Ne.symm
    apply Nat.ne_of_lt
    have hpdiv : p ∣ x := by
      have  hpinpf : p ∈ x.primeFactors := by
        rw [hpf]
        exact Finset.mem_singleton.mpr rfl
      exact Nat.dvd_of_mem_primeFactors hpinpf
    exact Nat.Prime.factorization_pos_of_dvd hp hx hpdiv
  · intro hpow
    obtain ⟨n, hpow⟩ := hpow
    let hnpow := hpow.1
    let hn := hpow.2
    unfold rad
    have hpf : x.primeFactors = {p} := by
      rw [hnpow]
      exact Nat.primeFactors_prime_pow hn hp
    rw [hpf]
    exact Eq.symm (Finset.prod_singleton id p)




/-!
## Lemmas establishing inequalities which follow from Stirling's inequality.
* Used for proving the Brocard-Ramanujan problem (`abc_imp_Brocard`), and for proving
the `logn_le_bounded` lemma used as the final step of proving the main result,
`abc_imp_poly_eq_fac_finite_sol`.
-/


lemma stirling (n : ℕ) (hn : 1 ≤ n) : Stirling.stirlingSeq n ≥ √π := by
  rw [(Nat.sub_eq_iff_eq_add hn).mp rfl]
  have h_dec : Antitone (Stirling.stirlingSeq ∘ Nat.succ) := Stirling.stirlingSeq'_antitone
  have h_limit : Filter.Tendsto (Stirling.stirlingSeq ∘ Nat.succ) Filter.atTop (nhds √π) := by
    rw [← Filter.tendsto_map'_iff]
    convert Stirling.tendsto_stirlingSeq_sqrt_pi
    exact Filter.map_add_atTop_eq_nat 1
  apply Antitone.le_of_tendsto h_dec h_limit


lemma gt_0_helper (n : ℕ) (hn : 1 ≤ n) : 0 < √(2 * ↑n) * (↑n / rexp 1) ^ n := by
  have h1 : √(2*n) > 0 := by
    refine sqrt_pos_of_pos ?_
    exact mul_pos (by simp) (by exact Nat.cast_pos'.2 (by exact hn))
  have h2 : (n / rexp 1)^n > 0 := by
    refine pow_pos ?_ n
    refine div_pos (by exact Nat.cast_pos'.2 (by exact hn)) (by exact exp_pos 1)
  exact mul_pos h1 h2


lemma stirling2 (n : ℕ) (hn : 1 ≤ n) : n.factorial ≥ √(2 * n * π) * n^n * 1/((Real.exp 1)^n) := by
  have H : Stirling.stirlingSeq n ≥ √π := stirling n hn
  unfold Stirling.stirlingSeq at H
  rw [ge_iff_le, le_div_iff₀'] at H
  rw [← ge_iff_le] at H
  convert H using 1
  simp
  field_simp
  ring
  exact gt_0_helper n hn


lemma first_ineq (x : ℕ) (hx : 4 ≤ x) : x.factorial > 4 * ((x:ℝ) ^ x * (1 / ((rexp 1) ^ x))) := by
  have h_gt0 : 0 < x := by linarith
  have h_rgt0 : 0 < (x:ℝ) := by exact Nat.cast_pos'.mpr h_gt0
  have h_ge0 : 0 ≤ (x:ℝ) := by linarith
  have h_le1 : 1 ≤ x := by linarith
  have hxc := hx
  rify at hx
  have h0 : 0 ≤ 2 * 4 * π := by positivity
  have h_4 : (0:ℝ) ≤ 4 := by linarith
  have h_4' : (0:ℝ) < 4 := by linarith
  have h1 : √(2 * 4 * π) ≤ √(2 * x * π) := by
    have h' : 2 * 4 * π ≤ 2 * x * π := by nlinarith
    apply Real.sqrt_le_sqrt h'
  have h2 : 4 < √(2 * 4 * π) := by
    rw [Real.lt_sqrt h_4]
    norm_num
    have h8 : 0 < (0.125 : ℝ) := by norm_num
    rw [← mul_lt_mul_left h8]
    norm_num
    rw [← mul_assoc]
    have h' : 3 < π := by apply Real.pi_gt_three
    have h'' : 2 < 3 := by norm_num
    linarith
  have h3 : 4 < √(2 * x * π) := by linarith
  have h4' : Stirling.stirlingSeq x ≥ √π := by apply stirling x (by omega)
  unfold Stirling.stirlingSeq at h4'
  have h4 : √π ≤ ↑x.factorial / (√(2 * ↑x) * (↑x / rexp 1) ^ x) := by exact h4'
  rw [le_div_iff₀ (gt_0_helper x h_le1)] at h4
  have h6 : ↑x / rexp 1 > 0 := by
    refine div_pos (by exact Nat.cast_pos'.2 (by exact h_gt0)) (by exact exp_pos 1)
  have h5 : (↑x / rexp 1) ^ x > 0 := by
    refine pow_pos ?_ x
    exact h6
  --have h7 : 0 ≤ 1 / rexp 1 := by refine one_div_nonneg.2 (by exact exp_nonneg 1)
  --have h8 : (0:ℝ) < ↑x ^ x := by exact pow_pos h_rgt0 x
  have h9 : (1/rexp 1) ^ x = 1/(rexp 1)^x := by
    calc
      (1/rexp 1) ^ x
      = 1^x / (rexp 1)^x := by exact div_pow 1 (rexp 1) x
      _= 1 / (rexp 1)^x := by ring
  have hf : (↑x) ^ x * (1/rexp 1) ^ x = (↑x) ^ x * (1/((rexp 1)^x)) := by exact congrArg (HMul.hMul ((x:ℝ) ^ x)) h9
  calc
    x.factorial
      ≥ √π * (√(2 * ↑x) * (↑x / rexp 1) ^ x) := by exact h4
    _ = (√π * √(2 * ↑x)) * (↑x / rexp 1) ^ x := by rw [mul_assoc]
    _ = √(π * (2 * ↑x)) * (↑x / rexp 1) ^ x := by rw [Real.sqrt_mul Real.pi_nonneg]
    _ = √((2 * ↑x) * π) * (↑x / rexp 1) ^ x := by rw [mul_comm π]
    _ > 4 * (↑x / rexp 1) ^ x := by refine mul_lt_mul_of_pos_right h3 h5
    _ = 4 * (↑x * (1/rexp 1)) ^ x := by rw [div_eq_mul_one_div]
    _ = 4 * ((↑x) ^ x * (1/rexp 1) ^ x) := by rw [mul_pow]
    _ = 4 * ((↑x) ^ x * (1/((rexp 1)^x))) := by exact congrArg (HMul.hMul 4) hf



/-!
## General lemmas involving the factorial, primality, the radical, factorizations.
* Used for proving identities between the radical, the factorial and the primorial.
-/


lemma descent (a b p n : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hp : Nat.Prime p) : a * b = p ^ n → ∃ (n1 n2 : ℕ), (a = p ^ n1) ∧ (b = p ^ n2) ∧ (n1 ≠ 0) ∧ (n2 ≠ 0) ∧ (n1 + n2 = n) := by
  intro hi
  have hadivpn : a ∣ p ^ n := by exact Dvd.intro b hi
  have hbdivpn : b ∣ p ^ n := by exact Dvd.intro_left a hi
  have hane0 : a ≠ 0 := by exact Nat.ne_zero_of_lt ha
  have hbne0 : b ≠ 0 := by exact Nat.ne_zero_of_lt hb
  have ha_prime_fac' : a = a.factorization.prod fun p i ↦ p ^ i := by exact Eq.symm (Nat.factorization_prod_pow_eq_self hane0)
  have ha_prime_fac : a = ∏ p ∈ a.factorization.support, p ^ (a.factorization p) := by
      simp
      conv => --nth_rw
        lhs
        rw [ha_prime_fac']
      rw [Finsupp.prod_of_support_subset]
      exact fun ⦃a⦄ a ↦ a
      exact fun i a ↦ rfl
  have hb_prime_fac' : b = b.factorization.prod fun p i ↦ p ^ i := by exact Eq.symm (Nat.factorization_prod_pow_eq_self hbne0)
  have hb_prime_fac : b = ∏ p ∈ b.factorization.support, p ^ (b.factorization p) := by
      simp
      conv => --nth_rw
        lhs
        rw [hb_prime_fac']
      rw [Finsupp.prod_of_support_subset]
      exact fun ⦃a⦄ a ↦ a
      exact fun i a ↦ rfl
  have hadivisor : ∀ q ∈ a.primeFactors, q ∣ p ^ n := by
    intro q hq
    have hqdiva : q ∣ a := by exact Nat.dvd_of_mem_primeFactors hq
    exact Nat.dvd_trans hqdiva hadivpn
  have haqdivp : ∀ q ∈ a.primeFactors, q = p := by
    intro q hq
    have hqprime : Nat.Prime q := by exact Nat.prime_of_mem_primeFactors hq
    have hqdiva : q ∣ a := by exact Nat.dvd_of_mem_primeFactors hq
    specialize hadivisor q hq
    exact Nat.prime_eq_prime_of_dvd_pow hqprime hp hadivisor
  have hpdiva : p ∣ a := by
    have hapfnonempty : a.primeFactors.Nonempty := by exact Nat.nonempty_primeFactors.2 ha
    obtain ⟨q, hq⟩ := hapfnonempty
    have hqeqp : q = p := by exact haqdivp q hq
    rw [←hqeqp]
    exact Nat.dvd_of_mem_primeFactors hq
  have hbdivisor : ∀ q ∈ b.primeFactors, q ∣ p ^ n := by
    intro q hq
    have hqdivb : q ∣ b := by exact Nat.dvd_of_mem_primeFactors hq
    exact Nat.dvd_trans hqdivb hbdivpn
  have hbqdivp : ∀ q ∈ b.primeFactors, q = p := by
    intro q hq
    have hqprime : Nat.Prime q := by exact Nat.prime_of_mem_primeFactors hq
    have hqdivb : q ∣ b := by exact Nat.dvd_of_mem_primeFactors hq
    specialize hbdivisor q hq
    exact Nat.prime_eq_prime_of_dvd_pow hqprime hp hbdivisor
  clear hadivisor hbdivisor
  have hpdivb : p ∣ b := by
    have hbpfnonempty : b.primeFactors.Nonempty := by exact Nat.nonempty_primeFactors.2 hb
    obtain ⟨q, hq⟩ := hbpfnonempty
    have hqeqp : q = p := by exact hbqdivp q hq
    rw [←hqeqp]
    exact Nat.dvd_of_mem_primeFactors hq
  have haprimefactors : a.primeFactors = {p} := by
    apply Finset.ext
    intro q
    constructor
    · intro hq
      rw [Finset.mem_singleton]
      specialize haqdivp q hq
      exact haqdivp
    · intro hqinp
      rw [Finset.mem_singleton] at hqinp
      specialize haqdivp q
      have hqprime : Nat.Prime q := by
        rw [hqinp]
        exact hp
      have hqdiva : q ∣ a := by
        rw [hqinp]
        exact hpdiva
      exact (Nat.mem_primeFactors_of_ne_zero hane0).2 (And.intro hqprime hqdiva)
  have hbprimefactors : b.primeFactors = {p} := by
    apply Finset.ext
    intro q
    constructor
    · intro hq
      rw [Finset.mem_singleton]
      specialize hbqdivp q hq
      exact hbqdivp
    · intro hqinp
      rw [Finset.mem_singleton] at hqinp
      specialize haqdivp q
      have hqprime : Nat.Prime q := by
        rw [hqinp]
        exact hp
      have hqdivb : q ∣ b := by
        rw [hqinp]
        exact hpdivb
      exact (Nat.mem_primeFactors_of_ne_zero hbne0).2 (And.intro hqprime hqdivb)
  clear ha_prime_fac'
  have haf : a = p ^ (a.factorization p) := by
    simp at ha_prime_fac
    conv_lhs =>
      rw [ha_prime_fac]
    rw [haprimefactors]
    rw [Finset.prod_singleton]
  clear hb_prime_fac'
  have hbf : b = p ^ (b.factorization p) := by
    simp at hb_prime_fac
    conv_lhs =>
      rw [hb_prime_fac]
    rw [hbprimefactors]
    rw [Finset.prod_singleton]
  clear ha_prime_fac hb_prime_fac
  use a.factorization p
  use b.factorization p
  constructor
  · exact haf
  · constructor
    · exact hbf
    · constructor
      · by_contra hc
        rw [hc] at haf
        simp at haf
        have hac : 1 < a := by exact ha
        have hac' : 1 ≠ a := by exact Nat.ne_of_lt ha
        have hac'' : ¬ (1 = a) := by exact hac'
        have haf' : 1 = a := by exact id (Eq.symm haf)
        contradiction
      · constructor
        · by_contra hc
          rw [hc] at hbf
          simp at hbf
          have hbc : 1 < b := by exact hb
          have hbc' : 1 ≠ b := by exact Nat.ne_of_lt hb
          have hbc'' : ¬ (1 = b) := by exact hbc'
          have hbf' : 1 = b := by exact id (Eq.symm hbf)
          contradiction
        · rw [haf] at hi
          rw [hbf] at hi
          rw [← Nat.pow_add] at hi
          apply Nat.pow_right_injective at hi
          exact hi
          exact Nat.Prime.two_le hp


lemma mul_pow2_even (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : (∃ n : ℕ, n ≠ 0 ∧ a * b = 2 ^ n) → Even a ∧ Even b := by
  intro hex
  obtain ⟨n, hn, hi⟩ := hex
  have h_descent : ∃ (n1 n2 : ℕ), (a = 2 ^ n1) ∧ (b = 2 ^ n2) ∧ (n1 ≠ 0) ∧ (n2 ≠ 0) ∧ (n1 + n2 = n) := by exact descent a b 2 n ha hb  (Nat.prime_two) hi
  obtain ⟨n1, n2, h2a, h2b, hn1ne0, hn2ne0, hn1n2len⟩ := h_descent
  constructor
  · rw [h2a]
    exact (Nat.even_pow' hn1ne0).2 even_two
  · rw [h2b]
    exact (Nat.even_pow' hn2ne0).2 even_two


lemma abc_ne_pow2 (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 2 ≤ a ∨ 2 ≤ b) (hsum: a + b = c) (hcop: Nat.Coprime a b) : ¬ (∃ n : ℕ, a * b * c = 2 ^ n ∧ n ≠ 0) := by
  by_contra hc
  choose n hex hn0 using hc
  have h112 : 2 = 1 * 2 := by simp
  have hab2 : 2 ≤ a * b := by
    cases hab with
    | inl h =>
      rw [h112]
      exact le_mul_of_le_of_one_le h hb
    | inr h =>
      rw [h112]
      exact Nat.mul_le_mul ha h
  have hc2 : 2 ≤ c := by
    have h111 : 2 = 1 + 1 := by simp
    rw [h111, ← hsum]
    exact Nat.add_le_add ha hb
  obtain ⟨n1, n2, hdescent⟩ := descent (a * b) c 2 n hab2 hc2 (by exact Nat.prime_two) hex
  choose hab2p hc2p hn10 hn20 hn1n2 using hdescent
  by_cases haa : a = 1
  rw [haa] at hsum hex hab2 hab2p
  simp at hex hab2 hab2p
  clear hcop haa
  have hbccop : Nat.Coprime b c := by
    rw [← hsum]
    simp
  have hcd2 : 2 ∣ c := by
    rw [hc2p]
    exact dvd_pow_self 2 hn20
  have hbd2 : 2 ∣ b := by
    rw [hab2p]
    exact dvd_pow_self 2 hn10
  have hgcdd : 2 ∣ b.gcd c := by exact Nat.dvd_gcd_iff.2 (And.intro hbd2 hcd2)
  absurd hbccop
  simp
  push_neg
  by_contra hgcc
  rw [hgcc] at hgcdd
  simp at hgcdd
  push_neg at haa
  have haa2 : 2 ≤ a := by exact (Nat.two_le_iff a).mpr (And.intro (Nat.ne_zero_of_lt ha) haa)
  by_cases hbb : b = 1
  rw [hbb] at hab2p hsum
  simp at hab2p
  have haccop : Nat.Coprime a c := by
      rw [← hsum]
      simp
  have hcd2 : 2 ∣ c := by
    rw [hc2p]
    exact dvd_pow_self 2 hn20
  have had2 : 2 ∣ a := by
    rw [hab2p]
    exact dvd_pow_self 2 hn10
  have hgcdd : 2 ∣ a.gcd c := by exact Nat.dvd_gcd_iff.2 (And.intro had2 hcd2)
  absurd haccop
  simp
  push_neg
  by_contra hgcc
  rw [hgcc] at hgcdd
  simp at hgcdd
  push_neg at hbb
  have hbb2 : 2 ≤ b := by exact (Nat.two_le_iff b).mpr (And.intro (Nat.ne_zero_of_lt hb) hbb)
  clear hab haa hbb ha hb
  have heven : Even a ∧ Even b := by exact mul_pow2_even a b haa2 hbb2 (Filter.frequently_principal.mp fun a ↦ a hn10 hab2p)
  have hgcd : a.gcd b ≥ 2 := by
    choose hae hbe using heven
    have had2 : 2 ∣ a := by exact even_iff_two_dvd.mp hae
    have hbd2 : 2 ∣ b := by exact even_iff_two_dvd.mp hbe
    have hgcdd : 2 ∣ a.gcd b := by exact Nat.dvd_gcd_iff.2 (And.intro had2 hbd2)
    refine Nat.le_of_dvd ?_ hgcdd
    exact Nat.lt_of_sub_eq_succ hcop
  have hgcd1 : a.gcd b = 1 := by exact hcop
  absurd hgcd
  push_neg
  rw [hgcd1]
  simp


lemma rad_abc_ge_3 (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 2 ≤ a ∨ 2 ≤ b) (hsum : a + b = c) (hcp : Nat.Coprime a b) : rad (a * b * c) ≥ 3 := by
  have hc : 2 ≤ c := by
    conv_lhs =>
      rw [← one_add_one_eq_two]
    conv_rhs =>
      rw [←hsum]
    exact Nat.add_le_add ha hb
  have habcne0 : a * b * c ≠ 0 := by
    apply Ne.symm
    refine Nat.ne_of_lt ?_
    change a * b * c > 0
    calc
      a * b * c
      ≥ a * b * 2 := by exact Nat.mul_le_mul_left (a * b) hc
      _= a * (b * 2) := by exact Nat.mul_assoc a b 2
      _≥ 1 * (b * 2) := by exact Nat.mul_le_mul_right (b * 2) ha
      _= b * 2 := by ring
      _≥ 1 * 2 := by exact Nat.mul_le_mul_right 2 hb
      _= 2 := by ring
      _> 0 := by linarith
  have h122 : 1 * 2 = 2 := by rfl
  by_contra h
  push_neg at h
  by_cases h0 : rad (a * b * c) = 0
  · clear h
    have h0neg : 0 ≠ rad (a * b * c) := by exact Ne.symm (rad_ne_0 (a * b * c))
    exact h0neg (Eq.symm h0)
  · push_neg at h0
    apply Nat.pos_of_ne_zero at h0
    apply Nat.succ_le_of_lt at h0
    simp at h0
    by_cases h1 : rad (a * b * c) = 1
    · clear h h0
      have habcge2 : 2 ≤ a * b * c := by
        have h1ab : 1 ≤ a * b := by
          have h111 : 1 * 1 = 1 := by rfl
          conv_lhs =>
            rw [←h111]
          exact Nat.mul_le_mul ha hb
        conv_lhs =>
          rw [←h122]
        exact Nat.mul_le_mul h1ab hc
      have hgt1 : 1 < rad (a * b * c) := by exact rad_gt_1 (a * b * c) habcge2
      have h1neg : 1 ≠ rad (a * b * c) := by exact Nat.ne_of_lt hgt1
      exact h1neg (Eq.symm h1)
    · push_neg at h1
      have h1' : 1 < rad (a * b * c) := by apply Nat.lt_of_le_of_ne h0 (Ne.symm h1)
      apply Nat.succ_le_of_lt at h1'
      simp at h1'
      have h2 : 2 = rad (a * b * c) := by exact Eq.symm (Nat.eq_of_le_of_lt_succ h1' h)
      clear h h0 h1 h1'
      have habcpow : ∃ n : ℕ, a * b * c = 2 ^ n ∧ n ≠ 0 := by exact (rad_eq_2_pow_2 (a * b * c) 2 habcne0 (Nat.prime_two)).1 h2
      have habcpow_neg : ¬ (∃ n : ℕ, a * b * c = 2 ^ n ∧ n ≠ 0) := by exact abc_ne_pow2 a b c ha hb hab hsum hcp
      contradiction


lemma unique_fac (x : ℕ) (hx : x ≠ 0) : x = ∏ p ∈ x.factorization.support, p ^ (x.factorization p) := by
  have hx_prime_fac : x = x.factorization.prod fun p i ↦ p ^ i := by exact Eq.symm (Nat.factorization_prod_pow_eq_self hx)
  simp
  conv_lhs =>
    rw [hx_prime_fac]
  rw [Finsupp.prod_of_support_subset]
  exact fun ⦃a⦄ a ↦ a                   -- ????????
  exact fun i a ↦ rfl                  -- ????????


lemma radx_le_x (x : ℕ) (hx : x ≠ 0) : rad x ≤ x := by
  unfold rad
  have h_prime_fac : x = ∏ p ∈ x.factorization.support, p ^ (x.factorization p) := by exact unique_fac x hx                  -- ????????
  conv =>
    rhs
    rw [h_prime_fac]
  have hh : x.primeFactors.prod id = ∏ p ∈ x.primeFactors, p := by rfl
  rw [hh]
  simp
  refine Finset.prod_le_prod ?_ ?_
  exact fun i a ↦ Nat.zero_le i
  intro p hpi
  have hppow : p = p ^ 1 := by exact Eq.symm (Nat.pow_one p)
  conv =>
    lhs
    rw [hppow]
  refine Nat.pow_le_pow_right ?_ ?_
  exact Nat.pos_of_mem_primeFactors hpi
  exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hpi) hx (Nat.dvd_of_mem_primeFactors hpi)


lemma div_prime_rad (n m : ℕ) (hm : m ≠ 0) (hp : ∀ (p : ℕ), p ∈ n.primeFactors → p ∣ m) : rad n ∣ rad m := by
  have hh : n.primeFactors ⊆ m.primeFactors := by
    intro d hdn
    have h_div : d ∣ m := by exact hp d hdn
    have hdp : Nat.Prime d := Nat.prime_of_mem_primeFactors hdn
    apply (Nat.mem_primeFactors_of_ne_zero hm).2
    exact And.intro hdp h_div
  exact Finset.prod_dvd_prod_of_subset n.primeFactors m.primeFactors id hh


lemma set_sqfree (S : Finset ℕ) : Squarefree (∏ p ∈ {p ∈ S | Nat.Prime p}, p) := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a s ha ih
    by_cases hc : Nat.Prime a
    · simp [Finset.filter_insert, hc]
      have haa : a ∉ Finset.filter (fun p ↦ Nat.Prime p) s := by simp [ha]
      rw [Finset.prod_insert haa]
      rw [Nat.squarefree_mul_iff]
      constructor
      · rw [Nat.Prime.coprime_iff_not_dvd hc]
        apply Prime.not_dvd_finset_prod
        exact Nat.prime_iff.mp hc
        intro p hp
        simp at hp
        intro hc_div
        rw [(Nat.prime_dvd_prime_iff_eq hc hp.2).1 hc_div] at ha
        exact ha hp.1
      · constructor
        exact Irreducible.squarefree hc
        exact ih
    · simp [Finset.filter_insert, hc]
      exact ih


lemma primorial_sqfree (x : ℕ) : Squarefree (primorial x) := by
  let S := (Finset.range (x + 1))
  apply set_sqfree S


lemma rad_helper (x : ℕ) (hx : x ≠ 0) : (rad x).primeFactors = x.primeFactors := by
  have h_rad_ne_0 : rad x ≠ 0 := by
    unfold rad
    rw [Finset.prod_ne_zero_iff]
    aesop
  apply Finset.ext
  intro p
  constructor
  intro hp
  have h_prime : Nat.Prime p := ((Nat.mem_primeFactors_of_ne_zero h_rad_ne_0).1 hp).1
  have h_div : p ∣ (rad x) := ((Nat.mem_primeFactors_of_ne_zero h_rad_ne_0).1 hp).2
  have hr : rad x ∣ x := Nat.prod_primeFactors_dvd x
  have hx_div : p ∣ x := by exact dvd_trans h_div hr
  exact (Nat.mem_primeFactors_of_ne_zero hx).2 (And.intro h_prime hx_div)
  intro hp
  have h_prime : Nat.Prime p := ((Nat.mem_primeFactors_of_ne_zero hx).1 hp).1
  have h_div : p ∣ x := ((Nat.mem_primeFactors_of_ne_zero hx).1 hp).2
  have hp_div : p ∣ rad x := by
    unfold rad
    apply Finset.dvd_prod_of_mem id hp
  exact (Nat.mem_primeFactors_of_ne_zero h_rad_ne_0).2 (And.intro h_prime hp_div)


lemma rad_eq_x (x : ℕ) (hx : x ≠ 0) : rad (rad x) = rad x := by
  have h_rad_ne_0 : rad x ≠ 0 := by
    unfold rad
    rw [Finset.prod_ne_zero_iff]
    aesop
  have h_pf_eq : (rad x).primeFactors = x.primeFactors := by apply rad_helper x hx
  have hu : ∀ t ∈ x.primeFactors, id t = id t := by aesop
  apply Finset.prod_congr h_pf_eq hu


lemma rad_primorial_eq_primorial (x: ℕ) : rad (primorial x) = primorial x := by
    apply Nat.prod_primeFactors_of_squarefree (primorial_sqfree x)


lemma div_fac (x p : ℕ) (hx : x ≠ 0) (hp : Nat.Prime p) : p ∣ rad x ↔ p ∣ x := by
  constructor
  · intro h
    unfold rad at h
    have hprime : Prime p := by exact Nat.prime_iff.mp hp
    have he : ∃ a ∈ x.primeFactors, p ∣ id a := by
      apply (Prime.dvd_finset_prod_iff hprime id).1 h
    obtain ⟨a, ha⟩ :=  he
    let ha1 := ha.1
    let ha2 := ha.2
    simp at ha2
    have hf : a ∣ x := ((Nat.mem_primeFactors_of_ne_zero hx).1 ha1).2
    exact Nat.dvd_trans ha2 hf
  · intro h
    have h_rad_helper : (rad x).primeFactors = x.primeFactors := rad_helper x hx
    have hx_factor : p ∈ x.primeFactors := (Nat.mem_primeFactors_of_ne_zero hx).2 (And.intro hp h)
    have hxrad_factor : p ∈ (rad x).primeFactors := by aesop
    exact Nat.dvd_of_mem_primeFactors hxrad_factor


lemma rad_eq_primorial (x : ℕ) : rad x.factorial = primorial x := by
  have h_rad_ne_0 : rad x ≠ 0 := by
    unfold rad
    rw [Finset.prod_ne_zero_iff]
    aesop
  have h_fac_ne_0 : x.factorial ≠ 0 := by exact Nat.factorial_ne_zero x
  have h_radfac_ne_0 : rad x.factorial ≠ 0 := by
    unfold rad
    rw [Finset.prod_ne_zero_iff]
    aesop
  have h_primorial_ne_0 : primorial x ≠ 0 := by
    unfold primorial
    rw [Finset.prod_ne_zero_iff]
    aesop
  have H1 : ∀ (p : ℕ), p ∈ (rad x.factorial).primeFactors → p ∣ primorial x := by
    have h_fac_ne_0 : x.factorial ≠ 0 := by exact Nat.factorial_ne_zero x
    intro p hp
    simp at hp
    let hp1 := hp.1
    let hp2 := (hp.2).1
    let hp3 := (hp.2).2
    push_neg at hp3
    have h_div : p ∣ x.factorial := by apply (div_fac x.factorial p h_fac_ne_0 hp1).1 hp2
    have hh : p ∈ Finset.filter (fun q ↦ Nat.Prime q) (Finset.range (x + 1)) := by
      rw [Finset.mem_filter]
      have H1 : p ∈ Finset.range (x + 1) := by
        rw [Finset.mem_range]
        rw [Nat.lt_add_one_iff]
        apply (Nat.Prime.dvd_factorial hp1).1 h_div
      exact And.intro H1 hp1
    unfold primorial
    have hprime : Prime p := by exact Nat.prime_iff.mp hp1
    let s := Finset.range (x + 1)
    let S := {p ∈ s | Nat.Prime p}
    have h_eq : p ∣ S.prod id := by
      rw [Prime.dvd_finset_prod_iff hprime id]
      simp
      use p
    have h_id : primorial x = S.prod id := by rfl
    exact h_eq
  have H2 : ∀ (p : ℕ), p ∈ (primorial x).primeFactors → p ∣ rad x.factorial := by
    intro p hp
    simp at hp
    let hp1 := hp.1
    let hp2 := (hp.2).1
    let hp3 := (hp.2).2
    push_neg at hp3
    unfold primorial at hp2
    have hprime : Prime p := by exact Nat.prime_iff.mp hp1
    have h_lex : p ≤ x := by
      rw [Prime.dvd_finset_prod_iff hprime] at hp2
      obtain ⟨a, ha⟩ :=  hp2
      let ha1 := ha.1
      let ha2 := ha.2
      have haprime : Nat.Prime a := by exact Nat.prime_of_mem_primesBelow ha1
      have hap : p = a := by apply (Nat.prime_dvd_prime_iff_eq hp1 haprime).1 ha2
      have hpF : p ∈ Finset.filter (fun p ↦ Nat.Prime p) (Finset.range (x + 1)) := by aesop -- is use of aesop neccesary?
      simp at hpF
      exact Nat.lt_succ_iff.1 hpF.1
    have hdiv_fac : p ∣ x.factorial := by apply (Nat.Prime.dvd_factorial hp1).2 h_lex
    apply (div_fac x.factorial p h_fac_ne_0 hp1).2
    exact hdiv_fac
  have hf1 : rad (rad x.factorial) ∣ rad (primorial x) := div_prime_rad (rad x.factorial) (primorial x) h_primorial_ne_0 H1
  have hf2 : rad (primorial x) ∣ rad (rad x.factorial) := div_prime_rad (primorial x) (rad x.factorial) h_radfac_ne_0 H2
  have HH : rad (rad x.factorial) = rad (primorial x) := Nat.dvd_antisymm hf1 hf2
  have HF1 : rad (rad x.factorial) = rad x.factorial := by apply rad_eq_x x.factorial h_fac_ne_0
  have HF2 : rad (primorial x) = primorial x := by
    apply Nat.prod_primeFactors_of_squarefree (primorial_sqfree x)
  linarith


lemma rad_sqfree (x : ℕ) : Squarefree (rad x) := by
  unfold rad
  let S := x.divisors
  have hhelp : x.primeFactors = {p ∈ x.divisors | Nat.Prime p} := by exact Nat.primeFactors_eq_to_filter_divisors_prime x
  have hh : ∏ p ∈ x.primeFactors, p = ∏ p ∈ {p ∈ S | Nat.Prime p}, p := by exact congrFun (congrArg Finset.prod hhelp) fun p ↦ p
  simp
  rw [hh]
  exact set_sqfree S


lemma fac_as_prod (x : ℕ) (hx : x ≥ 2) : x.factorial = ∏ i ∈ {i ∈ Finset.range (x + 1) | i ≠ 0}, i := by
  induction x with
  | zero => contradiction
  | succ k hi' =>
    simp at hx
    by_cases hk : k = 1
    · rw [hk]
      simp
      aesop
    · push_neg at hk
      have hk2 : k ≥ 2 := by
        refine (Nat.two_le_iff k).mpr ?_
        constructor
        exact Nat.ne_zero_of_lt hx
        exact hk
      clear hx hk
      have hi : k.factorial = ∏ i ∈ Finset.filter (fun i ↦ i ≠ 0) (Finset.range (k + 1)), i := by exact hi' hk2
      clear hi'
      have hfacstep : (k + 1).factorial = (k + 1) * k.factorial := by exact rfl
      rw [hfacstep]
      clear hfacstep
      have hhelp : Finset.range (k + 2) = insert (k + 1) (Finset.range (k + 1)) := by exact Finset.range_add_one
      have hhhelp : (Finset.filter (fun i ↦ i ≠ 0)) (Finset.range (k + 2)) = insert (k + 1) ((Finset.filter (fun i ↦ i ≠ 0)) (Finset.range (k + 1))) := by aesop
      have hh' : (Finset.filter (fun i ↦ i ≠ 0)) (Finset.range (k + 1)) = ((Finset.filter (fun i ↦ i ≠ 0)) (Finset.range (k + 2))).erase (k + 1) := by aesop
      have hknb' : k + 1 ∉ Finset.range (k + 1) := by exact Finset.not_mem_range_self
      have hknb : k + 1 ∉ (Finset.filter (fun i ↦ i ≠ 0)) (Finset.range (k + 1)) := by aesop
      have hprodstep : ∏ i ∈ Finset.filter (fun i ↦ i ≠ 0) (Finset.range (k + 1 + 1)), id i = (id (k + 1)) * (∏ i ∈ Finset.filter (fun i ↦ i ≠ 0) (Finset.range (k + 1)), id i) := by
        rw [← Finset.prod_insert hknb]
        rw [hhhelp]
      change (k + 1) * k.factorial = ∏ i ∈ Finset.filter (fun i ↦ i ≠ 0) (Finset.range (k + 1 + 1)), id i
      rw [hprodstep]
      simp
      exact hi


lemma two_elems_dvd_prod (a b : ℕ) (ha0 : a ≠ 0) (hab : b ≠ a) (S : Finset ℕ) (ha : a ∈ S) (hb : b ∈ S) : a * b ∣ S.prod id := by
  simp
  have haS : S.prod id = (id a) * ∏ x ∈ S.erase a, id x := by exact Eq.symm (Finset.mul_prod_erase S id ha)
  have hbS : S.prod id = (id b) * ∏ x ∈ S.erase b, id x := by exact Eq.symm (Finset.mul_prod_erase S id hb)
  have hS : ∏ x ∈ S.erase a, id x = (S.prod id) / a  := by refine Nat.eq_div_of_mul_eq_right ha0 (id (Eq.symm haS))
  have hbinea : b ∈ S.erase a := by
    refine Finset.mem_erase_of_ne_of_mem hab hb
  have habS : ∏ x ∈ S.erase a, id x = ((id b) * (∏ x ∈ (S.erase a).erase b, id x)) := by exact Eq.symm (Finset.mul_prod_erase (S.erase a) id hbinea)
  rw [habS] at haS
  simp at haS
  rw [← mul_assoc] at haS
  simp at haS hbS
  exact Dvd.intro (∏ x ∈ (S.erase a).erase b, x) (id (Eq.symm haS))


lemma rad_eq_4 (x : ℕ) (hx : 4 ≤ x) : rad x.factorial = rad (x.factorial / 4) := by
  have hfacge24 : x.factorial ≥ (4).factorial := by exact Nat.factorial_le hx
  have h4fac : Nat.factorial 4 = 24 := by aesop
  rw [h4fac] at hfacge24
  have hfacne0 : x.factorial ≠ 0 := by exact Nat.factorial_ne_zero x
  have hfac4ne0 : x.factorial / 4 ≠ 0 := by
    refine Nat.div_ne_zero_iff.2 ?_
    constructor
    norm_num
    exact le_of_add_le_right hfacge24
  have hx0 : x ≠ 0 := by exact Nat.ne_zero_of_lt hx
  have hufx : x = ∏ p ∈ x.factorization.support, p ^ (x.factorization p) := by exact unique_fac x hx0
  simp at hufx
  unfold rad
  have hradpri : (x.factorial / 4).primeFactors = (x.factorial).primeFactors := by
    have hfac4divv : (x.factorial / 4) ∣ x.factorial := by
      refine (Nat.div_dvd_iff_dvd_mul ?_ ?_).mpr ?_
      · refine Nat.dvd_factorial (by norm_num) hx
      · norm_num
      · exact Nat.dvd_mul_left x.factorial 4
    have hss4 : (x.factorial / 4).primeFactors ⊆ (x.factorial).primeFactors := by refine Nat.primeFactors_mono hfac4divv hfacne0
    have hss : (x.factorial).primeFactors ⊆ (x.factorial / 4).primeFactors := by
      refine Finset.subset_iff.2 ?_
      intro p hpf
      have hp : Nat.Prime p := by exact Nat.prime_of_mem_primeFactors hpf
      have hpdiv : p ∣ x.factorial := by exact Nat.dvd_of_mem_primeFactors hpf
      refine (Nat.mem_primeFactors_of_ne_zero hfac4ne0).mpr ?_
      constructor
      exact hp
      refine Nat.dvd_div_of_mul_dvd ?_
      by_cases hp2 : p = 2
      · rw [hp2]
        simp
        have hfacdef : x.factorial = ∏ i ∈ {i ∈ Finset.range (x + 1) | i ≠ 0}, i := by exact fac_as_prod x (by exact le_of_add_le_right hx)
        rw [hfacdef]
        have h2in : 2 ∈ Finset.filter (fun i ↦ i ≠ 0) (Finset.range (x + 1)) := by
          refine Finset.mem_filter.mpr ?_
          constructor
          refine Finset.mem_range_succ_iff.mpr ?_
          exact le_of_add_le_right hx
          norm_num
        have h4in : 4 ∈ Finset.filter (fun i ↦ i ≠ 0) (Finset.range (x + 1)) := by
          refine Finset.mem_filter.mpr ?_
          constructor
          exact Finset.mem_range_succ_iff.mpr hx
          norm_num
        conv_lhs =>
          change 2 * 4
        apply two_elems_dvd_prod
        norm_num
        norm_num
        exact h2in
        exact h4in
      · push_neg at hp2
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hpdiv
        have hpcp2 : Nat.Coprime 2 p := by
          refine Nat.coprime_two_left.mpr ?_
          exact Nat.Prime.odd_of_ne_two hp hp2
        have hexact : p.Coprime 4 := by
          change p.Coprime (2 ^ 2)
          refine Nat.Coprime.pow_right 2 ?_
          exact Nat.coprime_comm.mp hpcp2
        exact Nat.coprime_comm.mp hexact
        refine Nat.dvd_factorial (by norm_num) hx
    exact Finset.Subset.antisymm hss4 hss
  have hhelp : (x.factorial / 4).primeFactors.prod id = (x.factorial).primeFactors.prod id := by exact congrFun (congrArg Finset.prod hradpri) id
  rw [hhelp]


lemma rad_eq_4_primorial (x : ℕ) (hx : 4 ≤ x) : rad (x.factorial / 4) = primorial x := by
  have hx' : x ≠ 0 := by exact Nat.ne_zero_of_lt hx
  have h_helper : rad x.factorial = rad (x.factorial / 4) := by exact rad_eq_4 x hx
  have h_help : rad x.factorial = primorial x := by exact rad_eq_primorial x
  rw [id (Eq.symm h_helper)]
  exact h_help


lemma rad_dvd_le (x y : ℕ) (hx : x ≠ 0) (hdvd : y ∣ x) : rad y ≤ rad x := by
  have h1 : y.primeFactors ⊆ x.primeFactors := by
    refine Finset.subset_iff.2 ?_
    intro k ky
    simp at ky ⊢
    constructor
    exact ky.1
    let kydvd := ky.2.1
    constructor
    exact Nat.dvd_trans kydvd hdvd
    exact hx
  unfold rad
  refine Finset.prod_le_prod_of_subset_of_one_le' h1 ?_
  intro i hxi hyi
  simp
  simp at hxi
  let hex := hxi.1
  exact Nat.Prime.one_le hex


lemma rad_pow_le (x i : ℕ) (hx : x ≠ 0) : rad (x ^ i) ≤ x := by
  by_cases hi : i = 0
  rw [hi]
  simp
  have hrad1 : rad 1 = 1 := by
    unfold rad
    simp
  rw [hrad1]
  exact Nat.one_le_iff_ne_zero.mpr hx
  have h1 : rad (x ^ i) = rad (x) := by
    unfold rad
    simp
    refine Eq.symm (Finset.prod_congr ?_ fun x_1 ↦ congrFun rfl)
    refine Eq.symm (Nat.primeFactors_pow x hi)
  rw [h1]
  exact radx_le_x x hx


lemma rad_le (n c : ℕ) (hc0 : c ≠ 0) (hc : c ≤ n) : rad (c * n.factorial) = rad n.factorial := by
  have hcd : c ∣ n.factorial := by exact Nat.dvd_factorial (Nat.zero_lt_of_ne_zero hc0) (hc)
  unfold rad
  simp
  refine congrFun (congrArg Finset.prod ?_) fun x ↦ x
  have hfacc : ∃ k, n.factorial = c * k := by exact hcd
  obtain ⟨k, hfacc⟩ := hfacc
  rw [hfacc]
  refine Finset.ext_iff.mpr ?_
  intro i
  constructor
  intro hi
  simp at hi ⊢
  constructor
  exact hi.1
  constructor
  swap
  exact hi.2.2
  let hicf := hi.2.1
  have hor : i ∣ c ∨ i ∣ c * k := by exact (Nat.Prime.dvd_mul hi.1).mp hicf
  cases hor with
  | inl hor1 => exact Dvd.dvd.mul_right hor1 k
  | inr hor2 => exact hor2
  intro hi
  simp at hi ⊢
  let hidd := hi.2.1
  have hicdi : i ∣ c * (c * k) := by exact Dvd.dvd.mul_left hidd c
  exact And.intro hi.1 (And.intro hicdi (And.intro hi.2.2.1 hi.2.2.2))


lemma rad_mul_le (a b : ℕ) : rad (a * b) ≤ rad a * rad b := by
  have hrad : ∀ n, rad n ≥ 1 := by
    intro n
    unfold rad
    refine Nat.one_le_iff_ne_zero.mpr ?_
    refine Finset.prod_ne_zero_iff.2 ?_
    intro t ht
    simp at ht ⊢
    let hp := ht.1
    exact Nat.Prime.ne_zero hp
  have hrad0 : rad 0 = 1 := by
    unfold rad
    simp
  by_cases ha : a = 0
  rw [ha]
  simp
  rw [hrad0]
  simp
  exact hrad b
  by_cases hb : b = 0
  rw [hb]
  simp
  rw [hrad0]
  simp
  exact hrad a
  unfold rad
  simp
  rw [←Finset.prod_union_inter]
  have hun : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by exact Nat.primeFactors_mul ha hb
  rw [← hun]
  refine Nat.le_mul_of_pos_right (∏ x ∈ (a * b).primeFactors, x) ?_
  refine Nat.zero_lt_of_ne_zero ?_
  refine Finset.prod_ne_zero_iff.2 ?_
  intro i hi
  simp at hi
  let he := hi.1.1
  exact Nat.Prime.ne_zero he




/-!
## Results about the asymptotic behaviour of polynomials
* Used for proving that for a polynomial P of degree d, for large enough x it is the
case that (x ^ d) / 2 < P(x) < 2 * x ^ d.
* Used for proving the the general Brocard-Ramanujan problem, conditional on the abc-conjecture.
-/

lemma poly_monic_asymp_abs_real (P : ℝ[X]) (hP : P.Monic) : ∃ N : ℕ, ∀ z : ℝ, N > 0 ∧ ((|z| > N) → (|z| ^ P.natDegree) / 2 < |P.eval (|z|)| ∧ |P.eval (|z|)| < 2 * (|z| ^ P.natDegree)) := by

  set d := P.natDegree with hd
  have hrl : P.leadingCoeff = 1 := by exact hP
  have huse : Asymptotics.IsEquivalent Filter.atTop (fun x => eval x P) fun x => P.leadingCoeff * x ^ P.natDegree := by exact isEquivalent_atTop_lead P
  rw [hrl, ←hd] at huse
  simp at huse
  apply Asymptotics.IsEquivalent.exists_eq_mul at huse
  simp only [Filter.tendsto_atTop'] at huse
  obtain ⟨φ, hphi, huse⟩ := huse
  apply Filter.EventuallyEq.eventually at huse
  --apply Filter.eventually_iff.1 at huse
  simp at huse
  obtain ⟨ab, huse⟩ := huse
  --have hh : ∀ᶠ (x : ℝ) in Filter.atTop, 10 < x := by exact Filter.eventually_gt_atTop 10
  -- have hhphi : {1} ∈ nhds 1 := by exact IsOpen.mem_nhds trivial rfl
  have hhphir : Metric.ball 1 0.4 ∈ nhds (1 : ℝ) := by exact Metric.ball_mem_nhds 1 (by norm_num)
  specialize hphi (Metric.ball 1 0.4) hhphir
  obtain ⟨a, hphi⟩ := hphi

  let af := Nat.ceil a
  let abf := Nat.ceil ab
  let Mf := (max af abf) + 1
  use Mf
  intro z
  constructor
  unfold Mf
  simp
  intro hi
  --apply le_of_lt at hi
  -- rify at hi
  change |z| > Mf at hi
  have hzaf : |z| > (af : ℝ) := by
    unfold Mf at hi
    simp at hi
    have hi' : (max af abf) < (max af abf) + 1 := by exact lt_add_one (af ⊔ abf)
    rify at hi'
    have hmax : |z| > (max af abf) := by
      simp only [Nat.cast_max]
      exact gt_trans hi hi'
    simp at hmax
    exact hmax.1
  have hza : |z| > a := by
    have htr : af ≥ a := by exact Nat.le_ceil a
    exact lt_of_le_of_lt htr hzaf
  let hzac := hza
  apply le_of_lt at hza
  specialize hphi |z| hza
  have hzabf : |z| > (abf : ℝ) := by
    unfold Mf at hi
    simp at hi
    have hi' : (max af abf) < (max af abf) + 1 := by exact lt_add_one (af ⊔ abf)
    rify at hi'
    have hmax : |z| > (max af abf) := by
      simp only [Nat.cast_max]
      exact gt_trans hi hi'
    simp at hmax
    exact hmax.2
  have hzab : |z| > ab := by
    have htr : abf ≥ ab := by exact Nat.le_ceil ab
    exact lt_of_le_of_lt htr hzabf
  have hm0 : 0 < |z| ^ d := by
    have hz0 : z ≠ 0 := by
      by_contra hz0
      rw [hz0] at hi
      simp at hi
      have hmc : Mf ≥ 0 := by exact Nat.zero_le Mf
      rify at hmc
      have hcon : ¬ ((Mf : ℝ) < 0) := by exact not_lt_of_ge hmc
      absurd hcon
      exact hi
    refine pow_pos ?_ d
    simp
    exact hz0

  have hzab' : |z| ≥ ab := by exact le_of_lt hzab
  specialize huse |z| hzab'
  simp at hphi
  rw [Real.dist_eq] at hphi
  rw [abs_lt] at hphi
  let hf1 := hphi.1
  let hf2 := hphi.2

  have h2inv : 2⁻¹ = (1 / 2 : ℝ) := by exact inv_eq_one_div 2
  have h1' : φ |z| > 0.6 := by
    rw [lt_sub_iff_add_lt'] at hf1
    have hrf1 : 1 + (-0.4) = (0.6 : ℝ) := by ring
    rw [hrf1] at hf1
    exact hf1
  have h1 : φ |z| > 1/2 := by
    have htr : 0.6 > (1 / 2 : ℝ) := by linarith
    exact gt_trans h1' htr
  have h2 : φ |z| < 2 := by
    rw [sub_lt_iff_lt_add] at hf2
    have hobv : 0.4 + 1 = (1.4 : ℝ) := by ring
    rw [hobv] at hf2
    have htr : 1.4 < (2 : ℝ) := by linarith
    exact gt_trans htr hf2

  have hineq1 : |eval |z| P| < 2 * |z| ^ d := by
    rw [abs_lt]
    constructor
    rw [huse]
    have h1h : -(2 * |z| ^ d) = (- 2) * |z| ^ d := by ring
    rw [h1h]
    refine (mul_lt_mul_iff_of_pos_right ?_).2 ?_
    exact hm0
    have hei : - 2 < (0.6 : ℝ) := by linarith
    exact gt_trans h1' hei
    rw [huse]
    refine (mul_lt_mul_iff_of_pos_right ?_).2 ?_
    exact hm0
    exact h2
  have hineq2 : |z| ^ d / 2 < |eval |z| P| := by
    rw [lt_abs]
    constructor
    have h2h : |z| ^ d / 2 = |z| ^ d * 2⁻¹ := by ring
    rw [h2h]
    rw [mul_comm]
    have h20 : 0 < (2 : ℝ) := by linarith
    refine (inv_mul_lt_iff₀ h20).2 ?_
    rw [huse]
    rw [←mul_assoc]
    have h2hh : |z| ^ d = 1 * |z| ^ d := by ring
    conv_lhs =>
      rw [h2hh]
    refine (mul_lt_mul_iff_of_pos_right ?_).2 ?_
    exact hm0
    refine (inv_mul_lt_iff₀ h20).1 ?_
    simp
    rw [h2inv]
    exact h1
  exact And.intro hineq2 hineq1


lemma poly_asymp_abs_general (P : ℝ[X]) (hp : P.leadingCoeff ≠ 0) : ∃ N : ℕ, ∀ z : ℝ, N > 0 ∧ ((|z| > N) → |P.leadingCoeff| * ((|z| ^ P.natDegree) / 2) < |P.eval (|z|)| ∧ |P.eval (|z|)| < 2 * |P.leadingCoeff| * (|z| ^ P.natDegree)) := by

  set ad := P.leadingCoeff
  set d := P.natDegree
  let Q := P / (C ad)

  have hh : C (ad) = C (ad) * (1 : ℝ[X]) := by exact Eq.symm (MulOneClass.mul_one (C ad))

  have hqd : Q.natDegree = d := by
    unfold Q
    rw [hh]
    rw [Polynomial.div_C_mul]
    simp
    refine natDegree_C_mul ?_
    simp
    exact hp
  have hq : Q.Monic := by
    unfold Q
    rw [hh]
    rw [Polynomial.div_C_mul]
    simp
    refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    unfold ad
    exact inv_mul_cancel₀ hp

  obtain ⟨N, h'⟩ := poly_monic_asymp_abs_real Q hq
  use N
  intro z
  specialize h' z
  let hn0 := h'.1
  constructor
  exact hn0
  let h := h'.2
  intro hz
  specialize h hz

  have heval : |eval |z| Q| = |eval |z| P| * |ad|⁻¹ := by
    unfold Q
    rw [hh]
    rw [Polynomial.div_C_mul]
    simp
    rw [abs_mul]
    rw [mul_comm]
    have habsinv : |ad⁻¹| = |ad|⁻¹ := by exact abs_inv ad
    simp
    constructor
    exact habsinv

  rw [heval] at h

  let h1 := h.1
  let h2 := h.2
  rw [mul_comm, hqd] at h1
  rw [lt_inv_mul_iff₀'] at h1
  swap
  simp
  exact hp
  rw [mul_comm] at h1 h2
  rw [hqd, inv_mul_lt_iff₀'] at h2
  swap
  simp
  exact hp
  rw [mul_comm, ←mul_assoc] at h2
  have h2help : |ad| * 2 = 2 * |ad| := by exact CommMonoid.mul_comm |ad| 2
  rw [h2help] at h2
  exact And.intro h1 h2


lemma poly_asymp_general (P : ℝ[X]) (hp : P.leadingCoeff ≠ 0) : ∃ N : ℕ, ∀ z : ℝ, N > 0 ∧ ((|z| > N) → |P.leadingCoeff| * ((|z| ^ P.natDegree) / 2) < |P.eval z| ∧ |P.eval z| < 2 * |P.leadingCoeff| * (|z| ^ P.natDegree)) := by

  set ad := P.leadingCoeff with hadd
  set d := P.natDegree with hdd
  have hp0 : P ≠ 0 := by exact leadingCoeff_ne_zero.mp hp
  let Q := P.comp (-X)

  have hqd : Q.natDegree = d := by
    unfold Q
    rw [Polynomial.natDegree_comp]
    rw [←hdd]
    have hcd : ((-X) : ℝ[X]).natDegree = 1 := by simp
    rw [hcd]
    simp


  have hqc : |Q.leadingCoeff| = |ad| := by
    by_cases hdpar : Even d
  -- case Even d :
    refine abs_eq_abs.mpr ?_
    constructor
    unfold Q
    simp
    rw [←hdd]
    have hdp : (- 1) ^ d = 1 := by exact Even.neg_one_pow hdpar
    rify at hdp
    rw [hdp]
    simp
    exact hadd
  -- case Odd d :
    refine abs_eq_abs.mpr ?_
    rw [Or.comm]
    constructor
    unfold Q
    simp
    have hdp : (- 1) ^ d = - 1 := by aesop
    rify at hdp
    rw [hdp]
    simp
    exact hadd

  have hql : Q.leadingCoeff ≠ 0 := by
    unfold Q
    simp
    exact hp0
  obtain ⟨N, h⟩ := poly_asymp_abs_general Q hql
  obtain ⟨Npos, hpos'⟩ := poly_asymp_abs_general P hp
  let M := max N Npos
  use M
  intro z
  constructor
  specialize h z
  let hn := h.1
  unfold M
  simp
  constructor
  exact hn
  intro hz
  have hN : |z| > N :=  by
    unfold M at hz
    simp at hz
    exact hz.1
  have hNpos : |z| > Npos := by
    unfold M at hz
    simp at hz
    exact hz.2

  rw [hqd, hqc] at h
  rw [←hadd, ←hdd] at hpos'

  by_cases hz0 : z ≥ 0
-- case z ≥ 0 :
  have hzabs : |z| = z := by exact abs_of_nonneg hz0
  specialize hpos' z
  let hpos := hpos'.2
  specialize hpos hNpos
  rw [hzabs] at hpos ⊢
  exact hpos

-- case z < 0 :
  push_neg at hz0
  specialize h z
  let h' := h.2
  specialize h' hN
  have hzabs : |z| = - z := by exact abs_of_neg hz0
  have hhelp : |Q.eval (|z|)| = |P.eval z| := by
    rw [hzabs]
    refine abs_eq_abs.mpr ?_
    constructor
    unfold Q
    simp
  rw [hhelp] at h'
  exact h'


lemma poly_asymp_Z (P : ℤ[X]) (hpm : P.Monic) : ∃ N : ℕ, ∀ z : ℤ, N > 0 ∧ ((|z| > N) → (|z| ^ P.natDegree) / (2 : ℝ) < |P.eval z| ∧ |P.eval z| < 2 * (|z| ^ P.natDegree)) := by

  set d := P.natDegree with hd
  have had : P.leadingCoeff = 1 := by exact hpm

  let Pr : ℝ[X] := P.map (Int.castRingHom ℝ)
  have hpr : Pr.leadingCoeff ≠ 0 := by
    simp [Pr, leadingCoeff_map]
    push_neg
    exact map_monic_ne_zero hpm
  have hprm : Pr.Monic := by exact Monic.map (Int.castRingHom ℝ) hpm
  have hpad : Pr.leadingCoeff = 1 := by exact hprm
  have hpd : Pr.natDegree = d := by exact Monic.natDegree_map hpm (Int.castRingHom ℝ)

  obtain ⟨N, h⟩ := poly_asymp_general Pr hpr
  use N
  intro z
  constructor
  specialize h z
  let hn := h.1
  exact hn
  intro hz
  rify at hz
  specialize h (z : ℝ)
  let h' := h.2
  specialize h' hz

  rw [hpad, hpd] at h'
  simp at h'
  rify
  have hf1 : |eval (↑z) Pr| = ↑|eval z P| := by
    simp
    refine abs_eq_abs.mpr ?_
    constructor
    unfold Pr
    simp

  rw [hf1] at h'
  simp at h'
  exact h'
