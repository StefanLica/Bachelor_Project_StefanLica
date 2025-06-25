import Bachelor_Project_StefanLica.Lemmas
open Polynomial
open Real

/-!
# The abc-conjecture and some variations of it

This file introduces the main abc-conjecture, `abc`, and proposes some variations of it. We introduce here
the weak form of the abc conjecture, `weak_abc` used for proving the Brocard-Ramanujan problem and the
integer version, `abc_Z` used for proving the main result `abc_Z_poly_eq_fac_fin_sol`. We also propose
alternative versions of `abc` and `weak_abc`, restated in terms of the "quality".

## Main statements

* `abc`: The main abc-conjuctre.
* `weak_abc`: The weaker version of `abc`, used for proving the Brocard-Ramanujan problem.
* `abc_Z`: The integer version of `abc`, used for proving the main result,
the generalization of the Brocard-Ramanujan problem, `abc_Z_poly_eq_fac_fin_sol`.
-/


/-- The abc-conjecture, given as a `def`-/
def abc := ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ) , ∀ (a b c : ℕ) , a + b = c → Nat.Coprime a b → c > (rad (a * b * c) : ℝ ) ^ (ε + 1) → (a < N) ∧ (b < N) ∧ (c < N))


/--A weaker version of the abc-conjecture, used to prove Brocard's problem.-/
def weak_abc := ∃ (s : ℝ), s > 0 ∧ ∀ (a b c : ℕ), a ≠ 0 → b ≠ 0 → a + b = c → Nat.Coprime a b → a * b * c < (rad (a * b * c) : ℝ ) ^ s


/--The version of the abc-conjecture defined for all integers, used to prove the main result: `abc_Z_poly_eq_fac_fin_sol`.
It is worthwile to notice that even if it is defined also for negative integers, it is not a stronger statement than `abc`,
but a mere implication of it.-/
def abc_Z := ∃ (C : ℝ → ℝ), ∀ ε : ℝ , ε > 0 → (∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → (a + b = c) → (IsCoprime a b) → (max (max |a| |b|) |c|) < C ε * rad (Int.natAbs (a * b * c)) ^ (1 + ε))




/--The abc-conjecture implies the weak abc-conjecture.-/
lemma abc_imp_weak_abc : abc → weak_abc := by
  have hrad0 : rad 0 = 1 := by
    unfold rad
    unfold Nat.primeFactors
    unfold Nat.primeFactorsList
    decide
  have hrad2 : rad 2 = 2 := by
    unfold rad
    unfold Nat.primeFactors
    unfold Nat.primeFactorsList
    unfold Nat.primeFactorsList
    decide
  have h3gte : rexp 1 < 3 := by exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h3gee : rexp 1 ≤ 3 := by exact le_of_lt h3gte
  have h1lte : 1 < rexp 1 := by aesop
  have h1lee : 1 ≤ rexp 1 := by refine Real.one_le_exp (by exact zero_le_one' ℝ)
  have hj1 : 0.7 + 1 = (1.7 : ℝ) := by ring

  unfold abc weak_abc
  intro abc
  specialize abc 0.7 (by linarith)
  obtain ⟨B, abc⟩ := abc
  have h1 : ∃ (s' : ℕ), ∀ (a b c : ℕ), a ≠ 0 → b ≠ 0 → a + b = c → a.Coprime b → c > (rad (a * b * c) : ℝ) ^ ((0.7:ℝ) + 1) →  B ≤ (rad (a * b * c) : ℝ) ^ s' := by
    let s'use := Nat.ceil (log B)
    use s'use
    intro a1 b1 c1 hane0 hbne0 hsum hcop hgt
    specialize abc a1 b1 c1 hsum hcop hgt
    have HBgt1 : 1 < B := by
      by_contra HB
      push_neg at HB
      by_cases HB0 : B = 0
      · rw [HB0] at abc
        choose halt hblt hclt using abc
        exact Nat.not_succ_le_zero a1 halt
      · push_neg at HB0
        apply Nat.pos_of_ne_zero at HB0
        apply Nat.succ_le_of_lt at HB0
        simp at HB0
        change B ≥ 1 at HB0
        have HB1 : B = 1 := by exact Nat.le_antisymm HB HB0
        clear HB HB0
        rw [HB1] at abc
        simp at abc
        choose ha0 hb0 hc0 using abc
        rw [ha0, hb0, hc0] at hgt
        simp at hgt
        rw [hrad0] at hgt
        rw [hj1] at hgt
        simp at hgt
        absurd hgt
        simp
    have hBgt1r : 1 < (B : ℝ) := by exact Nat.one_lt_cast.mpr HBgt1
    have hBgt0 : 0 < B := by exact Nat.lt_trans (Nat.zero_lt_one) HBgt1
    have hBgt0r : 0 < (B : ℝ) := by exact Nat.cast_pos'.mpr hBgt0
    have hlogBgt0 : 0 < log B := by exact (log_pos_iff (Nat.cast_nonneg' B)).2 hBgt1r
    have h_sorry : rad (a1 * b1 * c1) ≥ rexp 1 := by
      have ha1ge1 : 1 ≤ a1 := by exact Nat.one_le_iff_ne_zero.mpr hane0
      have hb1ge1 : 1 ≤ b1 := by exact Nat.one_le_iff_ne_zero.mpr hbne0
      have ha1b1or : 2 ≤ a1 ∨ 2 ≤ b1 := by
        by_contra hor
        push_neg at hor
        choose ha1lt2 hb1lt2 using hor
        have ha : a1 = 1 := by exact Nat.eq_of_le_of_lt_succ ha1ge1 ha1lt2
        have hb : b1 = 1 := by exact Nat.eq_of_le_of_lt_succ hb1ge1 hb1lt2
        clear ha1ge1 hb1ge1 ha1lt2 hb1lt2
        rw [ha, hb] at hsum
        simp at hsum
        rw [ha, hb, ←hsum] at hgt
        simp at hgt
        rw [hrad2, hj1] at hgt
        have hj2 : 1 ≤ (1.7 : ℝ) := by linarith
        have h1le2 : 1 ≤ (2 : ℝ ) := by exact one_le_two
        have hj3 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (1.7 : ℝ) := by exact Real.rpow_le_rpow_of_exponent_le h1le2 hj2
        have hcase' : 2 ^ (1.7 : ℝ) ≥ (2 : ℝ) := by
          calc
            (2 : ℝ) ^ (1.7 : ℝ)
            ≥ (2 : ℝ) ^ (1 : ℝ) := by exact hj3
            _= (2 : ℝ) := by exact rpow_one 2
        have hcase'neg : ¬ (2 ^ (1.7 : ℝ) ≥ (2 : ℝ)) := by exact not_le_of_gt hgt
        contradiction
      have hradge3 : rad (a1 * b1 * c1) ≥ 3 := by exact rad_abc_ge_3 a1 b1 c1 ha1ge1 hb1ge1 ha1b1or hsum hcop
      have hradge3' : 3 ≤ rad (a1 * b1 * c1) := by exact hradge3
      rify at hradge3'
      exact Preorder.le_trans (rexp 1) 3 (↑(rad (a1 * b1 * c1))) h3gee hradge3'
    have hh1 : s'use ≥ log B := by exact Nat.le_ceil (log ↑B)
    have hh3 : (rad (a1 * b1 * c1) : ℝ) ^ log B ≥ (rexp 1) ^ log B := by
      have hexpge0 : 0 ≤ rexp 1 := by exact exp_nonneg 1
      have hradge0 : 0 ≤ rad (a1 * b1 * c1) := by exact Nat.zero_le (rad (a1 * b1 * c1))
      rify at hradge0
      exact (rpow_le_rpow_iff hexpge0 hradge0 hlogBgt0).mpr h_sorry
    have hh4 : (rexp 1) ^ log B = B := by
      rw [Real.exp_one_rpow]
      refine Real.exp_log hBgt0r
    rw [hh4] at hh3
    have hh2' : (rad (a1 * b1 * c1) : ℝ) ^ s'use ≥ (rad (a1 * b1 * c1) : ℝ) ^ log B := by
      rw [← Real.rpow_natCast]
      rw [ge_iff_le, Real.rpow_le_rpow_left_iff]
      exact hh1
      exact lt_of_le_of_lt' h_sorry h1lte
    exact le_trans hh3 hh2'
  let M := max (Nat.ceil (log B) : ℝ) 1.9
  use 3 * M
  constructor
  unfold M
  simp
  ;right
  linarith
  intro f g h hfne0 hgne0 hsum hcop
  by_cases hcase : h > (rad (f * g * h) : ℝ) ^ ((0.7:ℝ) + 1)

---------CASE 1 : h > (rad (f * g * h) : ℝ) ^ 1.7 :

  · obtain ⟨s', h1⟩ := h1
    specialize h1 f g h hfne0 hgne0 hsum hcop hcase
    specialize abc f g h hsum hcop hcase
    have HBgt1 : 1 < B := by
      by_contra HB
      push_neg at HB
      by_cases HB0 : B = 0
      · rw [HB0] at abc
        choose hc1 hc2 hc3 using abc
        exact Nat.not_succ_le_zero f hc1
      · push_neg at HB0
        apply Nat.pos_of_ne_zero at HB0
        apply Nat.succ_le_of_lt at HB0
        simp at HB0
        change B ≥ 1 at HB0
        have HB1 : B = 1 := by exact Nat.le_antisymm HB HB0
        clear HB HB0
        rw [HB1] at abc
        simp at abc
        choose hf0 hg0 hh0 using abc
        rw [hf0, hg0] at hcase
        simp at hcase
        rw [hrad0, hj1] at hcase
        have hcalc : (1:ℝ) ^ (1.7 : ℝ) = (1 : ℝ) := by aesop
        simp at hcase
        have h1neg : 0 < h := by exact Nat.zero_lt_of_lt hcase
        have h0neg : 0 ≠ h := by exact Ne.symm (Nat.ne_zero_of_lt hcase)
        absurd h0neg
        exact id (Eq.symm hh0)
    have hBgt1r : 1 < (B : ℝ) := by exact Nat.one_lt_cast.mpr HBgt1
    have hBgt0 : 0 < B := by exact Nat.lt_trans (Nat.zero_lt_one) HBgt1
    have hBgt0r : 0 < (B : ℝ) := by exact Nat.cast_pos'.mpr hBgt0
    have hlogBgt0 : 0 < log B := by exact (log_pos_iff (Nat.cast_nonneg' B)).2 hBgt1r
    have hf : 1 ≤ f := by exact Nat.one_le_iff_ne_zero.mpr hfne0
    have hg : 1 ≤ g := by exact Nat.one_le_iff_ne_zero.mpr hgne0
    have hforg : 2 ≤ f ∨ 2 ≤ g := by
      by_contra hfgc
      push_neg at hfgc
      choose hf' hg' using hfgc
      have Hf : f = 1 := by exact Nat.eq_of_le_of_lt_succ hf hf'
      have Hg : g = 1 := by exact Nat.eq_of_le_of_lt_succ hg hg'
      clear hf hg hf' hg'
      rw [Hf, Hg] at hcase hsum
      simp at hcase hsum
      rw [←hsum] at hcase
      rw [hrad2] at hcase
      rw [hj1] at hcase
      have hj2 : 1 ≤ (1.7 : ℝ) := by linarith
      have h1le2 : 1 ≤ (2 : ℝ ) := by exact one_le_two
      have hj3 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (1.7 : ℝ) := by exact Real.rpow_le_rpow_of_exponent_le h1le2 hj2
      have hcase' : 2 ^ (1.7 : ℝ) ≥ (2 : ℝ) := by
        calc
          (2 : ℝ) ^ (1.7 : ℝ)
          ≥ (2 : ℝ) ^ (1 : ℝ) := by exact hj3
          _= (2 : ℝ) := by exact rpow_one 2
      have hcase'neg : ¬ (2 ^ (1.7 : ℝ) ≥ (2 : ℝ)) := by exact not_le_of_gt hcase
      contradiction
    have hhge2 : 2 ≤ h := by
      conv_lhs => change 1 + 1
      conv_rhs => rw [←hsum]
      exact Nat.add_le_add hf hg
    have hradge3 : rad (f * g * h) ≥ 3 := by exact rad_abc_ge_3 f g h hf hg hforg hsum hcop
    rify at hradge3
    have h_prod_ge2 : 2 ≤ f * g * h := by
      change f * g * h ≥ 2
      calc
        f * g * h
        ≥ f * g * 2 := by exact Nat.mul_le_mul_left (f * g) hhge2
        _= f * (g * 2) := by exact Nat.mul_assoc f g 2
        _≥ 1 * (g * 2) := by exact Nat.mul_le_mul_right (g * 2) hf
        _= g * 2 := by ring
        _≥ 1 * 2 := by exact Nat.mul_le_mul_right 2 hg
        _= 2 := by ring
    have h_gt_sorry : rexp 1 < (rad (f * g * h) : ℝ) := by exact lt_of_le_of_lt' hradge3 h3gte
    have h_sorry : rexp 1 ≤ rad (f * g * h) := by exact le_of_lt h_gt_sorry
    have hh3 : (rexp 1) ^ log B ≤ (rad (f * g * h) : ℝ) ^ log B := by
      refine (Real.rpow_le_rpow_iff ?_ ?_ ?_).mpr ?_
      exact exp_nonneg 1
      have rad_gt_0r : 0 < rad (f * g * h) := by exact rad_gt_0 (f * g * h)
      rify at rad_gt_0r
      have rad_ge_0r : (0 : ℝ) ≤ rad (f * g * h) := by exact Nat.cast_nonneg' (rad (f * g * h))
      exact rad_ge_0r
      exact hlogBgt0
      exact h_sorry
    have hh4 : B = (rexp 1) ^ log B := by
      rw [Real.exp_one_rpow]
      exact Eq.symm (exp_log hBgt0r)
    have hh5 : B ≤ (rexp 1) ^ log B := by exact le_of_eq (id hh4)
    choose hfb hgb hhb using abc
    rify at hhb
    have hh15 : h < (rexp 1) ^ log B := by exact lt_of_lt_of_eq hhb hh4
    have hh156 : h < (rad (f * g * h) : ℝ) ^ log B := by exact lt_of_le_of_lt' hh3 hh15
    have hhf : (rad (f * g * h) : ℝ) ^ log B ≤ (rad (f * g * h) : ℝ) ^ M := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      exact Preorder.le_trans 1 (rexp 1) (↑(rad (f * g * h))) h1lee h_sorry
      have hB_ceil : log B ≤ Nat.ceil (log B) := by exact Nat.le_ceil (log ↑B)
      have hBceil_le_M : Nat.ceil (log B) ≤ M := by exact le_max_left (⌈log ↑B⌉₊ : ℝ) 1.9
      exact le_sup_of_le_left hB_ceil
    set r := (rad (f * g * h) : ℝ)
    have ht1 : f * g * h ≤ h ^ 3 := by
      have hh1 : h ^ 3 = h * h * h := by ring
      rw [hh1]
      refine Nat.mul_le_mul_right h ?_
      refine Nat.mul_le_mul ?_ ?_
      rw [← hsum]
      simp
      rw [← hsum]
      simp
    rify at ht1
    have ht2 := lt_of_lt_of_le hh156 hhf
    have hr0 : 0 ≤ r := by
      unfold r
      simp
    have ht3 : h ^ 3 < (r ^ M) ^ (3:ℝ) := by
      rw [←Real.rpow_natCast]
      have h33 : 0 < (3:ℝ) := by linarith
      refine Real.rpow_lt_rpow ?_ ?_ h33
      simp
      exact ht2
    have ht4 : (r ^ M) ^ (3:ℝ) = r ^ (3 * M) := by
      conv_rhs => rw [mul_comm]
      rw [Real.rpow_mul hr0]
    rw [ht4] at ht3
    exact lt_of_le_of_lt ht1 ht3

------------ CASE 2 : h ≤ (rad (f * g * h)) ^ 1.7
  · push_neg at hcase
    rw [hj1] at hcase
    clear abc
    have hf : 1 ≤ f := by exact Nat.one_le_iff_ne_zero.mpr hfne0
    have hg : 1 ≤ g := by exact Nat.one_le_iff_ne_zero.mpr hgne0
    have hhge2 : 2 ≤ h := by
      conv_lhs => change 1 + 1
      conv_rhs => rw [←hsum]
      exact Nat.add_le_add hf hg
    have h_prod_ge2 : 2 ≤ f * g * h := by
      change f * g * h ≥ 2
      calc
        f * g * h
        ≥ f * g * 2 := by exact Nat.mul_le_mul_left (f * g) hhge2
        _= f * (g * 2) := by exact Nat.mul_assoc f g 2
        _≥ 1 * (g * 2) := by exact Nat.mul_le_mul_right (g * 2) hf
        _= g * 2 := by ring
        _≥ 1 * 2 := by exact Nat.mul_le_mul_right 2 hg
        _= 2 := by ring
    have hradgt1 : 1 < (rad (f * g * h)) := by exact rad_gt_1 (f * g * h) h_prod_ge2
    rify at hradgt1
    have hj2 : (rad (f * g * h)) ^ (1.7 : ℝ) < (rad (f * g * h) : ℝ) ^ (1.8 : ℝ) := by exact Real.rpow_lt_rpow_of_exponent_lt hradgt1 (by linarith)
    have hj3 : h < (rad (f * g * h) : ℝ) ^ (1.8 : ℝ) := by exact lt_of_le_of_lt hcase hj2
    have hj4 : (rad (f * g * h) : ℝ) ^ (1.8 : ℝ) < (rad (f * g * h) : ℝ) ^ M := by
      refine Real.rpow_lt_rpow_of_exponent_lt hradgt1 ?_
      have hBceil_le_M : 1.9 ≤ M := by exact le_max_right (⌈log ↑B⌉₊ : ℝ) 1.9
      have h1819 : 1.8 < (1.9 : ℝ) := by linarith
      exact lt_sup_of_lt_right h1819
    have ht1 := lt_trans hj3 hj4
    clear hj2 hj3 hj4
    have ht2 : f * g * h ≤ h ^ 3 := by
      have hh1 : h ^ 3 = h * h * h := by ring
      rw [hh1]
      refine Nat.mul_le_mul_right h ?_
      refine Nat.mul_le_mul ?_ ?_
      rw [← hsum]
      simp
      rw [← hsum]
      simp
    rify at ht2
    set r := (rad (f * g * h) : ℝ)
    refine lt_of_le_of_lt ht2 ?_
    have hr0 : 0 ≤ r := by
      unfold r
      simp
    have ht4 : (r ^ M) ^ (3:ℝ) = r ^ (3 * M) := by
      conv_rhs => rw [mul_comm]
      rw [Real.rpow_mul hr0]
    rw [← ht4]
    rw [←Real.rpow_natCast]
    have h33 : 0 < (3:ℝ) := by linarith
    refine Real.rpow_lt_rpow ?_ ?_ h33
    simp
    exact ht1



/--The abc-conjecture implies the integer version of the abc-conjecture.-/
lemma abc_imp_abc_Z : abc → abc_Z := by

  unfold abc abc_Z
  intro habc
  choose N habc using habc
  let C (x : ℝ) : ℝ := if h : x > 0 then (↑(N x h) + 2) else 0
  use C

  intro e he a b c ha0 hb0 hsum hcop
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · by_cases hc : c ≤ 0
      · have hs : a.natAbs + b.natAbs = c.natAbs := by
          zify
          rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos hc]
          omega
        have hco : a.natAbs.Coprime b.natAbs := by exact Int.isCoprime_iff_nat_coprime.1 hcop
        specialize habc e he a.natAbs b.natAbs c.natAbs hs hco
        have hmax : (max (max |a| |b|) |c|) = |c| := by
          simp
          have hm1 : max |b| |c| = |c| := by
            simp
            rw [abs_of_nonpos hb, abs_of_nonpos hc, ←hsum]
            simp
            exact ha
          rw [hm1]
          simp
          rw [abs_of_nonpos ha, abs_of_nonpos hc, ←hsum]
          simp
          exact hb
        simp only [Int.cast_max, Int.cast_abs]
        rify at hmax
        rw [hmax]
        unfold C
        split_ifs
        by_cases hg : c.natAbs > (rad (a.natAbs * b.natAbs * c.natAbs) : ℝ) ^ (e + 1)
        --
        specialize habc hg
        choose halt hblt hclt using habc
        rify at hclt
        refine lt_of_lt_of_le hclt ?_
        set n := N e he
        conv_lhs => rw [←one_mul (a := (n:ℝ)), mul_comm]
        refine mul_le_mul (by simp) ?_ (by simp) (by linarith)
        refine one_le_rpow ?_ (by linarith)
        simp
        refine Nat.succ_le_of_lt (rad_gt_0 (a * b * c).natAbs)
        --
        push_neg at hg
        have hhelp : c.natAbs = |(c:ℝ)| := by
          have h1 : c.natAbs = |c| := by simp
          rw [←Int.cast_abs, ←h1]
          exact rfl
        rw [←hhelp]
        refine lt_of_le_of_lt hg ?_
        have : e + 1 = 1 + e := by ring
        rw [this]
        clear this
        have hreq : (rad (a.natAbs * b.natAbs * c.natAbs) : ℝ) ^ (1 + e) = (rad (a * b * c).natAbs) ^ (1 + e) := by
          congr
          zify
          have hh2 : |a| * |b| = |a * b| := by exact Eq.symm (abs_mul a b)
          rw [hh2]
          exact Eq.symm (abs_mul (a * b) c)
        rw [←hreq]
        set r := (rad (a.natAbs * b.natAbs* c.natAbs) : ℝ) ^ (1 + e)
        set n := N e he
        have hr0 : 0 < r := by
          unfold r
          refine rpow_pos_of_pos ?_ (1 + e)
          simp
          exact rad_gt_0 (a.natAbs * b.natAbs* c.natAbs)
        refine (lt_mul_iff_one_lt_left hr0).mpr ?_
        linarith
      · push_neg at hc
        rw [← hsum] at hc
        have hco : a + b ≤ 0 := by exact Int.add_nonpos ha hb
        absurd hc
        push_neg
        exact hco
    · push_neg at hb
      by_cases hc : c ≤ 0
      · have hs : b.natAbs + c.natAbs = a.natAbs := by
          zify
          rw [abs_of_pos hb, abs_of_nonpos ha, abs_of_nonpos hc]
          omega
        have hco : b.natAbs.Coprime c.natAbs := by
          have h1 : IsCoprime b c := by
            rw [←hsum]
            rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
            simp
            rw [Int.gcd_comm]
            exact hcop
          exact Int.isCoprime_iff_nat_coprime.1 h1
        specialize habc e he b.natAbs c.natAbs a.natAbs hs hco
        have hmax : (max (max |a| |b|) |c|) = |a| := by
          simp
          constructor
          rw [abs_of_pos hb, abs_of_nonpos ha]
          refine Int.add_le_zero_iff_le_neg'.mp ?_
          rw [hsum]
          exact hc
          rw [abs_of_nonpos hc, abs_of_nonpos ha]
          simp
          rw [← hsum]
          omega
        simp only [Int.cast_max, Int.cast_abs]
        rify at hmax
        rw [hmax]
        unfold C
        split_ifs
        by_cases hg : a.natAbs > (rad (b.natAbs * c.natAbs * a.natAbs) : ℝ) ^ (e + 1)
        --
        specialize habc hg
        choose hblt hclt halt using habc
        rify at halt
        refine lt_of_lt_of_le halt ?_
        set n := N e he
        conv_lhs => rw [←one_mul (a := (n:ℝ)), mul_comm]
        refine mul_le_mul (by simp) ?_ (by simp) (by linarith)
        refine one_le_rpow ?_ (by linarith)
        simp
        refine Nat.succ_le_of_lt (rad_gt_0 (a * b * c).natAbs)
        --
        push_neg at hg
        have hhelp : a.natAbs = |(a:ℝ)| := by
          have h1 : a.natAbs = |a| := by simp
          rw [←Int.cast_abs, ←h1]
          exact rfl
        rw [←hhelp]
        refine lt_of_le_of_lt hg ?_
        have : e + 1 = 1 + e := by ring
        rw [this]
        clear this
        have hreq : (rad (b.natAbs * c.natAbs * a.natAbs) : ℝ) ^ (1 + e) = (rad (a * b * c).natAbs) ^ (1 + e) := by
          congr
          zify
          rw [mul_comm]
          conv_rhs => rw [mul_assoc]
          have hh2 : |b| * |c| = |b * c| := by exact Eq.symm (abs_mul b c)
          rw [hh2]
          exact Eq.symm (abs_mul a (b * c))
        rw [←hreq]
        set r := (rad (b.natAbs * c.natAbs* a.natAbs) : ℝ) ^ (1 + e)
        set n := N e he
        have hr0 : 0 < r := by
          unfold r
          refine rpow_pos_of_pos ?_ (1 + e)
          simp
          exact rad_gt_0 (b.natAbs * c.natAbs* a.natAbs)
        refine (lt_mul_iff_one_lt_left hr0).mpr ?_
        linarith
      · push_neg at hc
        have hs : a.natAbs + c.natAbs = b.natAbs := by
          zify
          rw [abs_of_pos hb, abs_of_pos hc, abs_of_nonpos ha]
          omega
        have hcop2 : a.natAbs.Coprime c.natAbs := by
          have h1 : IsCoprime a c := by
            rw [←hsum]
            rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
            simp
            exact hcop
          exact Int.isCoprime_iff_nat_coprime.1 h1
        specialize habc e he a.natAbs c.natAbs b.natAbs hs hcop2
        have hmax : (max (max |a| |b|) |c|) = |b| := by
          simp
          have h1 : max |b| |c| = |b| := by
            simp
            zify at hs
            rw [← hs]
            exact Int.le_add_of_nonneg_left (abs_nonneg a)
          rw [h1]
          simp
          zify at hs
          rw [←hs]
          exact Int.le_add_of_nonneg_right (abs_nonneg c)
        simp only [Int.cast_max, Int.cast_abs]
        rify at hmax
        rw [hmax]
        unfold C
        split_ifs
        by_cases hg : b.natAbs > (rad (a.natAbs * c.natAbs * b.natAbs) : ℝ) ^ (e + 1)
        --
        specialize habc hg
        choose halt hclt hblt using habc
        rify at hblt
        refine lt_of_lt_of_le hblt ?_
        set n := N e he
        conv_lhs => rw [←one_mul (a := (n:ℝ)), mul_comm]
        refine mul_le_mul (by simp) ?_ (by simp) (by linarith)
        refine one_le_rpow ?_ (by linarith)
        simp
        refine Nat.succ_le_of_lt (rad_gt_0 (a * b * c).natAbs)
        --
        push_neg at hg
        have hhelp : b.natAbs = |(b:ℝ)| := by
          have h1 : b.natAbs = |b| := by simp
          rw [←Int.cast_abs, ←h1]
          exact rfl
        rw [←hhelp]
        refine lt_of_le_of_lt hg ?_
        have : e + 1 = 1 + e := by ring
        rw [this]
        clear this
        have hreq : (rad (a.natAbs * c.natAbs* b.natAbs) : ℝ) ^ (1 + e) = (rad (a * b * c).natAbs) ^ (1 + e) := by
          congr
          zify
          have hh2 : |c| * |b| = |c * b| := by exact Eq.symm (abs_mul c b)
          rw [mul_assoc, hh2]
          conv_lhs => rw [mul_comm c b]
          conv_rhs => rw [mul_assoc]
          exact Eq.symm (abs_mul a (b * c))
        rw [←hreq]
        set r := (rad (a.natAbs * c.natAbs* b.natAbs) : ℝ) ^ (1 + e)
        set n := N e he
        have hr0 : 0 < r := by
          unfold r
          refine rpow_pos_of_pos ?_ (1 + e)
          simp
          exact rad_gt_0 (a.natAbs * c.natAbs* b.natAbs)
        refine (lt_mul_iff_one_lt_left hr0).mpr ?_
        linarith
  · push_neg at ha
    by_cases hb : b ≤ 0
    · by_cases hc : c ≤ 0
      · push_neg at hc
        set an := a.toNat
        set bn := b.natAbs
        set cn := c.natAbs
        have hbp : b = - bn := by
          unfold bn
          simp
          rw [abs_of_nonpos hb]
          simp
        have hcp : c = - cn := by
          unfold cn
          simp
          rw [abs_of_nonpos hc]
          simp
        have hcsum : an + cn = bn := by
          zify
          rw [Int.eq_neg_comm] at hbp hcp
          rw [hbp, hcp]
          have hh1 : an = a := by
            unfold an
            simp
            exact Int.le_of_lt ha
          rw [hh1]
          omega
        have haccop : an.Coprime cn := by
          have hh1 : IsCoprime a c := by
            rw [←hsum]
            rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
            simp
            exact hcop
          unfold an cn
          have hh3 : a.toNat = a.natAbs := by
            zify
            simp
            rw [max_eq_left_of_lt ha]
            exact Eq.symm (abs_of_pos ha)
          rw [hh3]
          exact Int.isCoprime_iff_nat_coprime.1 hh1
        specialize habc e he an cn bn hcsum haccop
        have heq : (max (max |a| |b|) |c|) = |b| := by
          simp
          have hh1 : (max |b| |c|) = |b| := by
            simp
            rw [abs_of_nonpos hb, abs_of_nonpos hc]
            simp
            rw [←hsum]
            omega
          rw [hh1]
          simp
          rw [abs_of_pos ha, abs_of_nonpos hb]
          omega
        have hbeq : |b| = bn := by
          unfold bn
          zify
        rw [heq, hbeq]
        simp only [Int.cast_natCast]
        unfold C
        split_ifs
        by_cases hg : bn > (rad (an * cn * bn) : ℝ) ^ (e + 1)
        --
        specialize habc hg
        choose halt hclt hblt using habc
        rify at hblt
        refine lt_of_lt_of_le hblt ?_
        set n := N e he
        conv_lhs => rw [←one_mul (a := (n:ℝ)), mul_comm]
        refine mul_le_mul (by simp) ?_ (by simp) (by linarith)
        refine one_le_rpow ?_ (by linarith)
        simp
        refine Nat.succ_le_of_lt (rad_gt_0 (a * b * c).natAbs)
        --
        push_neg at hg
        refine lt_of_le_of_lt hg ?_
        have : e + 1 = 1 + e := by ring
        rw [this]
        clear this
        have hreq : (rad (an * cn * bn) : ℝ) ^ (1 + e) = (rad (a * b * c).natAbs) ^ (1 + e) := by
          congr
          unfold an bn cn
          zify
          have hh1 : a.toNat = |a| := by
            simp
            rw [max_eq_left_of_lt ha]
            exact Eq.symm (abs_of_pos ha)
          rw [hh1]
          have hh2 : |c| * |b| = |c * b| := by exact Eq.symm (abs_mul c b)
          rw [mul_assoc, hh2]
          conv_lhs => rw [mul_comm c b]
          conv_rhs => rw [mul_assoc]
          exact Eq.symm (abs_mul a (b * c))
        rw [←hreq]
        set r := (rad (an * cn * bn) : ℝ) ^ (1 + e)
        set n := N e he
        have hr0 : 0 < r := by
          unfold r
          refine rpow_pos_of_pos ?_ (1 + e)
          simp
          exact rad_gt_0 (an * cn * bn)
        refine (lt_mul_iff_one_lt_left hr0).mpr ?_
        linarith
      · push_neg at hc
        set an := a.toNat
        set bn := b.natAbs
        set cn := c.natAbs
        have hceq : |a| = an := by
          unfold an
          simp
          rw [max_eq_left_of_lt ha]
          exact abs_of_pos ha
        have hssum : bn + cn = an := by
          unfold bn cn
          zify
          have hh1 : |b| = - b := by exact abs_of_nonpos hb
          have hh2 : |c| = c := by exact abs_of_pos hc
          have hh3 : |a| = a := by exact abs_of_pos ha
          rw [hh1, hh2, ←hceq, hh3]
          omega
        have heq : (max (max |a| |b|) |c|) = |a| := by
          have hh1 : max |a| |b| = |a| := by
            simp
            rw [abs_of_pos ha, abs_of_nonpos hb]
            omega
          rw [hh1]
          simp
          rw [abs_of_pos hc, abs_of_pos ha]
          unfold bn cn at hssum
          zify at hssum
          rw [abs_of_pos hc, ←hceq, abs_of_pos ha] at hssum
          rw [←hssum]
          exact Int.le_add_of_nonneg_left (abs_nonneg b)
        rw [heq, hceq]
        simp only [Int.cast_natCast]
        unfold C
        split_ifs
        have hcbcop : bn.Coprime cn := by
          have hh1 : IsCoprime b c := by
            rw [←hsum]
            rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
            simp
            rw [Int.gcd_comm]
            exact hcop
          unfold bn cn
          exact Int.isCoprime_iff_nat_coprime.1 hh1
        by_cases hg : an > (rad (bn * cn * an) : ℝ) ^ (e + 1)
      --
        specialize habc e he bn cn an hssum hcbcop hg
        choose halt hclt hblt using habc
        rify at hblt
        refine lt_of_lt_of_le hblt ?_
        set n := N e he
        conv_lhs => rw [←one_mul (a := (n:ℝ)), mul_comm]
        refine mul_le_mul (by simp) ?_ (by simp) (by linarith)
        refine one_le_rpow ?_ (by linarith)
        simp
        refine Nat.succ_le_of_lt (rad_gt_0 (a * b * c).natAbs)
        --
        push_neg at hg
        refine lt_of_le_of_lt hg ?_
        have : e + 1 = 1 + e := by ring
        rw [this]
        clear this
        have hreq : (rad (bn * cn * an) : ℝ) ^ (1 + e) = (rad (a * b * c).natAbs) ^ (1 + e) := by
          congr
          unfold an bn cn
          zify
          have haa : a.toNat = |a| := by
            simp
            rw [max_eq_left_of_lt ha]
            exact Eq.symm (abs_of_pos ha)
          rw [haa]
          have hbc1 : |b| * |c| = |b * c| := by exact Eq.symm (abs_mul b c)
          rw [hbc1]
          conv_rhs => rw [mul_assoc, mul_comm]
          exact Eq.symm (abs_mul (b * c) a)
        rw [←hreq]
        set r := (rad (bn * cn * an) : ℝ) ^ (1 + e)
        set n := N e he
        have hr0 : 0 < r := by
          unfold r
          refine rpow_pos_of_pos ?_ (1 + e)
          simp
          exact rad_gt_0 (bn * cn * an)
        refine (lt_mul_iff_one_lt_left hr0).mpr ?_
        linarith
    · push_neg at hb
      by_cases hc : c ≤ 0
      · rw [← hsum] at hc
        have habsu : a + b > 0 := by exact Int.add_pos ha hb
        absurd hc
        push_neg
        exact habsu
      · push_neg at hc
        have h1 : a.toNat = a := by exact Int.toNat_of_nonneg (Int.le_of_lt ha)
        have h2 : b.toNat = b := by exact Int.toNat_of_nonneg (Int.le_of_lt hb)
        have h3 : c.toNat = c := by exact Int.toNat_of_nonneg (Int.le_of_lt hc)
        set an := a.toNat
        set bn := b.toNat
        set cn := c.toNat
        have hsumnat : an + bn = cn := by
          unfold an bn cn
          zify
          rw [h1, h2, h3]
          exact hsum
        have hcopnat : an.Coprime bn := by
          have h1 : an = a.natAbs := by
            unfold an
            zify
            simp
            rw [max_eq_left_of_lt ha]
            exact Eq.symm (abs_of_pos ha)
          have h2 : bn = b.natAbs := by
            unfold bn
            zify
            simp
            rw [max_eq_left_of_lt hb]
            exact Eq.symm (abs_of_pos hb)
          rw [h1, h2]
          exact Int.isCoprime_iff_nat_coprime.1 hcop
        specialize habc e he
        specialize habc an bn cn hsumnat hcopnat
        have hradeq : rad (a * b * c).natAbs = rad (an * bn * cn) := by
          congr
          unfold an bn cn
          zify
          have ha1 : |a * b * c| = a * b * c := abs_of_pos (Int.mul_pos (Int.mul_pos ha hb) hc)
          rw [ha1, h1, h2, h3]
        have heq : (max (max |a| |b|) |c|) = |c| := by
          simp
          have hm1 : max |b| |c| = |c| := by
            simp
            rw [abs_of_pos hb, abs_of_pos hc, ←hsum]
            exact Int.le_add_of_nonneg_left (Int.le_of_lt ha)
          rw [hm1]
          simp
          rw [abs_of_pos ha, abs_of_pos hc, ←hsum]
          exact Int.le_add_of_nonneg_right (Int.le_of_lt hb)
        have hceq : |c| = cn := by
          unfold cn
          simp
          rw [max_eq_left_of_lt hc]
          exact abs_of_pos hc
        rw [heq, hceq, hradeq]
        simp only [Int.cast_natCast]
        unfold C
        split_ifs
        by_cases hg : ↑cn > (rad (an * bn * cn) : ℝ) ^ (e + 1)
        --
        specialize habc hg
        choose halt hblt hclt using habc
        rify at hclt
        refine lt_of_lt_of_le hclt ?_
        set n := N e he
        conv_lhs => rw [←one_mul (a := (n:ℝ)), mul_comm]
        refine mul_le_mul (by simp) ?_ (by simp) (by linarith)
        refine one_le_rpow ?_ (by linarith)
        simp
        refine Nat.succ_le_of_lt (rad_gt_0 (an * bn * cn))
        --
        push_neg at hg
        refine lt_of_le_of_lt hg ?_
        have : e + 1 = 1 + e := by ring
        rw [this]
        clear this
        set r := (rad (an * bn * cn) : ℝ) ^ (1 + e)
        set n := N e he
        have hr0 : 0 < r := by
          unfold r
          refine rpow_pos_of_pos ?_ (1 + e)
          simp
          exact rad_gt_0 (an * bn * cn)
        refine (lt_mul_iff_one_lt_left hr0).mpr ?_
        linarith




/-!
* `abc_q` is a reformulation of the abc-conjecture in terms of the quality, proven as an implication `abc`.
* `abc_Qmax` shows the existance of a maximum quality. Proven as an implication of `weak_abc`.
-/



/-- The quality of 3 natural numbers a, b and c, defined as the natural
logarithm of c divided by the natural logarithm of the radical of the product of a, b and c.-/
noncomputable def quality (a b c : ℕ) := (Real.log c) / ((Real.log (rad (a * b * c))))


/--A version of the abc_conjecture, formulated in terms of the quality of the abc-triple. -/
lemma abc_q : abc → (∀ Q : ℝ, Q > 1 → (∃ (N : ℕ) , ∀ (a b c : ℕ) , a ≠ 0 → b ≠ 0 → a + b = c → Nat.Coprime a b → quality a b c > Q → (a < N ∧ b < N ∧ c < N))) := by
  intro h Q hQ
  specialize h (Q - 1) (by linarith)
  obtain ⟨N, h⟩ := h
  have hh : Q - 1 + 1 = Q := by ring
  rw [hh] at h
  use N
  intro a b c hane0 hbne0 hsum hcop hq
  have ha1 : 1 ≤ a := by exact Nat.one_le_iff_ne_zero.mpr hane0
  have hb1 : 1 ≤ b := by exact Nat.one_le_iff_ne_zero.mpr hbne0
  have hab1 : 1 ≤ a * b := by exact Right.one_le_mul ha1 hb1
  have hc2 : 2 ≤ c := by
    rw [←hsum]
    have h112 : 2 = 1 + 1 := by simp
    rw [h112]
    exact Nat.add_le_add ha1 hb1
  have hrad1 : 1 < rad (a * b * c) := by exact rad_gt_1 (a * b * c) (by exact le_mul_of_one_le_of_le hab1 hc2)
  have h01 : 0 < (1 : ℝ) := by linarith
  have hc0 : 0 < c := by exact Nat.zero_lt_of_lt hc2
  unfold quality at hq
  rw [div_eq_mul_inv] at hq
  change Q < log ↑c * (log ↑(rad (a * b * c)))⁻¹ at hq
  rw [lt_mul_inv_iff₀'] at hq
  swap
  refine (log_pos_iff ?_).mpr ?_
  swap
  rify at hrad1
  exact hrad1
  exact Nat.cast_nonneg' (rad (a * b * c))
  rw [mul_comm] at hq
  rw [← Real.log_rpow] at hq
  rw [Real.log_lt_log_iff] at hq
  swap
  refine rpow_pos_of_pos ?_ Q
  rify at hrad1
  exact gt_trans hrad1 h01
  swap
  rify at hc0
  exact hc0
  swap
  rify at hrad1
  exact gt_trans hrad1 h01
  change c > (rad (a * b * c) : ℝ) ^ Q at hq
  specialize h a b c hsum hcop hq
  exact h



/--A proof for the existence of a maximum quality, 'Qmax', assuming `weak_abc`.-/
lemma abc_Qmax : weak_abc → (∃ (Qmax : ℝ), (Qmax > 1) ∧ ∀ (a b c : ℕ) , a ≠ 0 → b ≠ 0 → a + b = c → Nat.Coprime a b → quality a b c ≤ Qmax) := by

  unfold weak_abc
  intro wabc
  obtain ⟨s, hs, wabc⟩ := wabc

  use (s + 1)
  constructor
  simp
  exact hs
  intro a b c an0 bn0 hsum hcop
  specialize wabc a b c an0 bn0 hsum hcop
  have hcpos : 0 < c := by
    rw [← hsum]
    exact Nat.add_pos_left (Nat.zero_lt_of_ne_zero an0) b
  unfold quality
  ring_nf
  set u := (17:ℝ) / 10
  have hradpos : 0 < rad (a * b * c) := by exact rad_gt_0 (a * b * c)
  have hpos : 0 < log ↑(rad (a * b * c)) := by
    refine (log_pos_iff (Nat.cast_nonneg' (rad (a * b * c)))).mpr ?_
    simp
    refine rad_gt_1 (a * b * c) ?_
    apply Nat.one_le_iff_ne_zero.mpr at an0
    apply Nat.one_le_iff_ne_zero.mpr at bn0
    have h2sum : 1 + 1 ≤ a + b := by exact Nat.add_le_add an0 bn0
    rw [hsum] at h2sum
    simp at h2sum
    have hff : 1 * 1 * 2 ≤ a * b * c := by exact mul_le_mul_three an0 bn0 h2sum
    simp at hff
    exact hff
  rw [mul_inv_le_iff₀ hpos]
  rw [←Real.log_rpow]
  swap
  rify at hradpos
  exact hradpos
  refine Real.log_le_log (Nat.cast_pos'.mpr hcpos) ?_
  have hf : (rad (a * b * c) : ℝ) ^ s < (rad (a * b * c)) ^ (1 + s) := by
    rw [Real.rpow_lt_rpow_left_iff]
    simp
    refine (log_pos_iff (Nat.cast_nonneg' (rad (a * b * c)))).mp hpos
  have ht1 := lt_trans wabc hf
  refine le_of_lt (lt_of_le_of_lt ?_ ht1)
  refine le_mul_of_one_le_left ?_ ?_
  simp
  refine one_le_mul_of_one_le_of_one_le ?_ ?_
  simp
  exact Nat.one_le_iff_ne_zero.mpr an0
  simp
  exact Nat.one_le_iff_ne_zero.mpr bn0
