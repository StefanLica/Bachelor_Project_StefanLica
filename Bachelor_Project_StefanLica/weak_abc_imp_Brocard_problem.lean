import Bachelor_Project_StefanLica.abc_variants
open Polynomial
open Real


/-!
# The weak version of the abc-conjecture implies there are finitely many integer solutions to the equation x! + 1 = y².

* This file proposes a proof of the Brocard-Ramanujan problem, `weak_abc_imp_Brocard`, conditional on a weak
version of the abc-conjecture, `weak_abc`.
-/






/-- The original Brocard-Ramanujan problem, proven assuming a weaker form of the abc-conjecture : `weak_abc` -/
theorem weak_abc_imp_Brocard : weak_abc → (∃ (N : ℕ) , ∀ (x y : ℕ) , (x.factorial + 1 = y^2) → x < N ∧ y < N) := by

  unfold weak_abc
  intro wabc
  refine assume_nat ?_
  have h4gt0 : 0 < 4 := by simp
  have h4ge0 : (0:ℝ) ≤ 4 := by simp
  have h2ne0 : 2 ≠ 0 := by norm_num
  have h1 : ∃ (s : ℝ), s > 0 ∧ ∀ (r : ℕ), r ≠ 0 → r * 1 * (r + 1) < (rad (r * 1 * (r + 1)) : ℝ ) ^ s := by
    obtain ⟨t, ht, wabc⟩ := wabc
    use t
    constructor
    exact ht
    intro r hr0
    specialize wabc r 1 (r+1) hr0 (by simp) (by simp) (Nat.gcd_one_right r)
    simp at wabc ⊢
    exact wabc
  obtain ⟨t, ht1, ht2⟩ := h1
  let M := Nat.floor ((rexp 1) * 4 ^ t) + 1
  use M
  intro x y hi
  have hx : 4 ≤ x := by exact fac_sq_imp_ge_4 x y hi
  have hx' : x ≠ 0 := by exact Nat.ne_zero_of_lt hx
  have h_rw_y : ∃ (k : ℕ), y = 2 * k + 1 := by exact (y_odd x y hx hi)
  obtain ⟨k, h_rw_y⟩ := h_rw_y
  have hkn : k ≠ 0 := by
    by_contra hkc
    rw [hkc] at h_rw_y
    simp at h_rw_y
    rw [h_rw_y] at hi
    simp at hi
    absurd hi
    exact Nat.factorial_ne_zero x
  specialize ht2 k hkn
  simp at ht2
  have h_rw : x.factorial = 4 * k * (k + 1) := by
    calc
      x.factorial
      = y^2 - 1 := by exact Nat.eq_sub_of_add_eq hi
      _= (2 * k + 1)^2 -1 := by exact congrFun (congrArg HSub.hSub (congrFun (congrArg HPow.hPow h_rw_y) 2)) 1 -- maybe some better way??
      _= 4 * k^2 + 4 * k + 1 - 1 := by ring_nf
      _= 4 * k^2 + 4 * k := by exact rfl
      _= 4 * k * (k + 1) := by ring
  rw [mul_assoc] at h_rw
  have h_rw' : x.factorial/4 = k * (k + 1) := by refine Nat.div_eq_of_eq_mul_right h4gt0 h_rw
  have hf_helper : ((x:ℝ) ^ x * (1 / ((rexp 1) ^ x))) < x.factorial / 4 := by
    rw [mul_comm, lt_div_iff₀ (by norm_num : (4 : ℝ) > 0)]
    have hf_helper' : 4 * (↑x ^ x * (1 / rexp 1 ^ x)) = 1 / rexp 1 ^ x * ↑x ^ x * 4 := by ring
    rw [← hf_helper']
    exact first_ineq x hx
  have h_rw'' : (x.factorial : ℝ) / 4 = (k * (k + 1) : ℝ) := by aesop
  have hrad_helper : rad (k * (k + 1)) = rad (x.factorial / 4) := by exact congrArg rad (id (Eq.symm h_rw')) -- ????
  have hf_ineq : ((x:ℝ) ^ x) * (1 / ((rexp 1) ^ x)) ≤ (4:ℝ) ^ (t * x) := by
    have hf_ineq1 : ((x:ℝ) ^ x) * (1 / ((rexp 1) ^ x)) < (primorial x) ^ t := by
      calc
        ((x:ℝ) ^ x) * (1 / ((rexp 1) ^ x))
        < x.factorial / 4 := by exact hf_helper
        _= k * (k + 1) := by exact h_rw''
        _< (rad (k * (k + 1))) ^ t := by exact ht2
        _= (rad (x.factorial / 4)) ^ t := by exact congrFun (congrArg HPow.hPow (congrArg Nat.cast hrad_helper)) t -- ????
        _= (primorial x) ^ t := by rw [rad_eq_4_primorial x hx] --congrFun (congrArg HPow.hPow (congrArg (Nat.cast (rad_eq_4_primorial x hx)))) t
    have h_primorial_ge_0 : 0 ≤ primorial x := by exact Nat.zero_le (primorial x)
    rify at h_primorial_ge_0
    have hf_ineq_helper : (4:ℝ) ^ (t * ↑x) = (↑4 ^ ↑x) ^ t := by
      rw [mul_comm]
      exact Real.rpow_natCast_mul h4ge0 x t
    have hf_ineq2 : ((primorial x) : ℝ) ^ t ≤ (↑4 ^ ↑x) ^ t := by
      rw [Real.rpow_le_rpow_iff h_primorial_ge_0 (pow_nonneg h4ge0 x) ht1]
      exact_mod_cast primorial_le_4_pow x
    apply le_of_lt at hf_ineq1
    rw [hf_ineq_helper]
    exact le_trans hf_ineq1 hf_ineq2
  have hf_ge_0 : 0 ≤ rexp 1 * 4 ^ t := by
    apply mul_nonneg
    exact exp_nonneg 1
    exact rpow_nonneg h4ge0 t
  have hf : x ≤ (rexp 1) * 4 ^ t := by
    rw [one_div] at hf_ineq
    rw [mul_inv_le_iff₀] at hf_ineq
    have h_pow_mul_eq_mul_mul : 4 ^ (t * x) = ((4 ^ t) ^ x : ℝ) := by exact rpow_mul_natCast h4ge0 t x
    rw [h_pow_mul_eq_mul_mul] at hf_ineq
    have h_mul_rpow : (4 ^ t) ^ x * rexp 1 ^ x = ((4 ^ t) * rexp 1) ^ x := by exact Eq.symm (mul_pow (4 ^ t) (rexp 1) x)
    rw [h_mul_rpow] at hf_ineq
    rw [pow_le_pow_iff_left₀] at hf_ineq
    rw [mul_comm] at hf_ineq
    exact hf_ineq
    exact Nat.cast_nonneg' x
    rw [mul_comm]
    exact hf_ge_0
    exact hx'
    refine pow_pos ?_ x
    exact exp_pos 1
  apply (Nat.le_floor_iff hf_ge_0).2 at hf
  unfold M
  exact Order.lt_add_one_iff.2 hf
