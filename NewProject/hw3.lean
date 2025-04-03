import Mathlib

open Real


theorem add_neg_cancel_right_2 (a b : ℝ) : a + b + -b = a := by
  rewrite [add_assoc]
  rewrite [add_comm]
  rewrite [add_comm b (-b)]
  rewrite [neg_add_cancel]
  rewrite [zero_add]
  rfl



theorem add_left_cancel_2 {a b c : ℝ} (h : a + b = a + c) : b = c := by
  rewrite [←zero_add b]
  rewrite [←neg_add_cancel a]
  rewrite [add_assoc]
  rewrite [h]
  rewrite [←add_assoc]
  rewrite [neg_add_cancel]
  rewrite [zero_add]
  rfl




example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rewrite [mul_comm]



example (x : ℕ) (h : x>6) : x>5 := by
  have eq : 5<6 ↔ 6>5 := Iff.rfl
  have h2 : 6>5 := Nat.lt_succ_self 5
  have eq2: x>6 ↔ 6<x := Iff.rfl
  apply lt_trans h2 h
