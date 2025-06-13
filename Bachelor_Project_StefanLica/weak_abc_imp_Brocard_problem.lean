import Bachelor_Project_StefanLica.abc_variants
open Polynomial
open Real


/-!
# The weak version of the abc-conjecture implies there are finitely many integer solutions to the equation x! + 1 = y².

This file proposes a proof of the Brocard-Ramanujan problem, `weak_abc_imp_Brocard`, conditional on a weak
version of the abc-conjecture, `weak_abc`.

-/







/-- The original Brocard-Ramanujan problem, proven assuming a weaker form of the abc-conjecture : `weak_abc` -/
theorem weak_abc_imp_Brocard : weak_abc → (∃ (N : ℕ) , ∀ (x y : ℕ) , (x.factorial + 1 = y^2) → x ≤ N ∧ y ≤ N) := by

  unfold weak_abc
  intro wabc

  have h4gt0 : 0 < 4 := by simp
  have h4ge0 : (0:ℝ) ≤ 4 := by simp
  have h2ne0 : 2 ≠ 0 := by norm_num
  have h1 : ∃ (s : ℝ), s > 0 ∧ ∀ (l : ℕ), l ≠ 0 → l * 1 * (l + 1) < (rad (l * 1 * (l + 1)) : ℝ ) ^ s := by
    obtain ⟨t, ht, hig⟩ := wabc
    use t
    constructor
    exact ht
    intro l hln
    specialize hig l 1 (l+1) hln (by simp) (by simp) (Nat.gcd_one_right l)
    simp at hig ⊢
    exact hig
  obtain ⟨t, ht1, ht2⟩ := h1
  let n := Nat.floor ((rexp 1) * 4 ^ t)
  let n' := Nat.floor (√(n.factorial + 1))
  let M := max n n'
  use M
  intro x y hi
  have hx : 4 ≤ x := by exact fac_sq_imp_ge_4 x y hi
  have hx' : x ≠ 0 := by exact Nat.ne_zero_of_lt hx
  have h_y_odd : Odd y := by exact y_odd x y hx hi
  have h_rw_y : ∃ (k : ℕ), y = 2 * k + 1 := by exact h_y_odd
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
  have hk_gcd : Nat.gcd k (k + 1) = 1 := by
    apply Nat.coprime_self_add_right.2
    exact Nat.gcd_one_right k
  have hk_add : k + 1 = (k + 1) := by rfl
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

  -- prove bound for y:
  have hy_R : 0 < y := by exact Nat.lt_of_sub_eq_succ h_rw_y
  rify at hy_R
  have hy_ineq1 : y ≤ √(x.factorial + 1) := by
    have hi_ineq : (y ^ 2 : ℝ) = x.factorial + 1  := by
      norm_cast
      exact id (Eq.symm hi)
    apply le_of_eq at hi_ineq
    rw [Real.le_sqrt' hy_R]
    exact hi_ineq
  have hy_ineq2 : √(x.factorial + 1) ≤ √(n.factorial + 1) := by
    refine (sqrt_le_sqrt_iff (by linarith)).2 ?_
    simp
    exact Nat.factorial_le hf
  have hy_ineq : y ≤ √(n.factorial + 1) := by apply le_trans hy_ineq1 hy_ineq2
  have hy_ineq_ge_0 : 0 ≤ √(n.factorial + 1) := by exact sqrt_nonneg (↑n.factorial + 1)
  apply (Nat.le_floor_iff hy_ineq_ge_0).2 at hy_ineq
  have HFx : x ≤ M := by exact le_sup_of_le_left hf
  have HFy : y ≤ M := by exact le_sup_of_le_right hy_ineq
  let HF := And.intro HFx HFy
  exact HF
