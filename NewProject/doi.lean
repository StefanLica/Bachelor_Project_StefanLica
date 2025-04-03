import Mathlib
open Classical



example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left


def no_prime_divisors (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p ∣ n ∧ p<n)

example : ¬no_prime_divisors 4 := by
  intro h
  have h_prime := Nat.prime_two
  have h_divides := Nat.dvd_of_mod_eq_zero (by norm_num : 4 % 2 = 0)
  exact h 2 h_prime h_divides

example : no_prime_divisors 3 := by
  intro p hp hp2
  have h3prime : Nat.Prime 3 := by norm_num
  have := Nat.Prime.eq_one_or_self_of_dvd h3prime p hp2.1
  cases this with
  | inl hp3 =>
    have := Nat.Prime.ne_one hp;
    contradiction
  | inr hp4 =>
    have := hp2.2
    have := ne_of_lt this
    contradiction
