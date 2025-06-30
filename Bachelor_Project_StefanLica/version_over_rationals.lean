import Bachelor_Project_StefanLica.abc_Z_imp_general_Brocard
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Basic
open Polynomial



/-!
# A version over the rationals

* In this file, we prove a seemingly stronger result, namely that the abc-conjecture implies that
for any polynomial P ∈ ℚ[X] of degree at least 2, the equation P(x) = n! has finitely many solutions
(x,n) ∈ ℚ × ℕ. This problem can be reduced to the integer case, `abc_Z_poly_eq_fac_fin_sol`.
* We first prove a helping statement, namely for all polynomials P ∈ ℤ[X] of degree at least 2,
and for all non-zero c ∈ ℤ, the equation P(x) = c * n! has finitely many solutions (x,n) ∈ ℤ × ℕ.
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



/-!
## Main statements

* `abc_Z_poly_eq_fac_fin_sol_rat` is the main statement of this file.
* `abc_Z_poly_eq_const_fac_fin_sol`: for all polynomials P ∈ ℤ[X] of degree at least 2,
and for all non-zero c ∈ ℤ, the equation P(x) = c * n! has finitely many solutions (x,n) ∈ ℤ × ℕ,
under the abc-conjecture.
-/

/-- Helping lemma for `abc_Z_poly_eq_const_fac_fin_sol`, which treats the case when c divides x. -/
lemma abc_Z_poly_eq_const_dvd_fac_fin_sol (P : ℤ[X]) (hdeg : P.degree ≥ 2) (c : ℤ) (hcne0 : c ≠ 0) :
  abc_Z → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , c ∣ x → P.eval x = c * n.factorial → n < N ∧ |x| < N) := by

  set d := P.natDegree with hd
  intro abcz
  let Q : ℤ[X] := P.comp (C c * X)
  let Qc : ℤ[X] := (∑ i ∈ Finset.range (d + 1) \ {0}, C (c ^ (i - 1)) * (C (P.coeff i)) * X ^ i) + C (P.coeff 0 / c)
  have hqcdeg : Qc.degree ≥ 2 := by exact Qc_degree P Qc d c hcne0 hdeg hd rfl
  obtain ⟨M, hng⟩ := abc_Z_poly_eq_fac_fin_sol Qc hqcdeg abcz
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


/-- Lemma used for proving the main result, `abc_Z_poly_eq_fac_fin_sol_rat`.-/
lemma abc_Z_poly_eq_const_fac_fin_sol (P : ℤ[X]) (hdeg : P.degree ≥ 2) (c : ℤ) (hcne0 : c ≠ 0) :
  abc_Z → (∃ (N : ℕ) , ∀ (n : ℕ) (x : ℤ) , P.eval x = c * n.factorial → n < N ∧ |x| < N) := by

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

  let N (i : Fin cn) : ℕ := by exact (abc_Z_poly_eq_const_dvd_fac_fin_sol (Q i) (hqd i) c hcne0 abcz).choose
  have hn : ∀ (i : Fin cn) (n : ℕ) (x : ℤ), c ∣ x → eval x (Q i) = c * ↑n.factorial → n < N i ∧ |x| < N i := fun i ↦ (abc_Z_poly_eq_const_dvd_fac_fin_sol (Q i) (hqd i) c hcne0 abcz).choose_spec
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



section rational_case_lemmas
variable (P : ℚ[X])

lemma Pnez (hdeg : P.degree ≥ 2) : P ≠ 0 := ne_zero_of_coe_le_degree hdeg


def g' : ℕ := P.support.prod (fun i => (P.coeff i).den)
local notation "g" => g' P


lemma hgnez : g ≠ 0 := by
  unfold g'
  apply Finset.prod_ne_zero_iff.2 ?_
  intro i his
  exact (P.coeff i).den_nz

lemma hgdvd : ∀ i, (P.coeff i).den ∣ g := by
  intro i
  unfold g'
  by_cases his : i ∈ P.support
  exact Finset.dvd_prod_of_mem (fun i ↦ (P.coeff i).den) his
  have hpcoef0 : P.coeff i = 0 := by exact notMem_support_iff.mp his
  rw [hpcoef0]
  simp

lemma hgdvdlc : P.leadingCoeff.den ∣ g := by
  have hex : P.leadingCoeff = P.coeff P.natDegree := rfl
  rw [hex]
  exact hgdvd P P.natDegree


noncomputable def Q'' : ℤ[X] := ∑ i ∈ P.support, C ((P.coeff i).num * (g / (P.coeff i).den)) * X ^ i
local notation "Q" => Q'' P


noncomputable def d'' : ℕ := (Q).natDegree
local notation "d" => d'' P


lemma hqpndeg (hdeg : P.degree ≥ 2) : d = P.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  unfold Q''
  refine natDegree_sum_le_of_forall_le P.support (fun i ↦ C ((P.coeff i).num * (↑g / ↑(P.coeff i).den)) * X ^ i) ?_
  intro i hi
  rw [Polynomial.natDegree_C_mul_X_pow]
  exact le_natDegree_of_mem_supp i hi
  simp
  constructor
  exact mem_support_iff.mp hi
  by_contra hco
  have := Int.eq_zero_of_ediv_eq_zero (Int.ofNat_dvd.mpr (hgdvd P i)) hco
  absurd hgnez P
  exact Int.ofNat_eq_zero.mp this
  unfold Q''
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  simp
  constructor
  exact Pnez P hdeg
  by_contra hco
  have := Int.eq_zero_of_ediv_eq_zero (Int.ofNat_dvd.mpr (hgdvdlc P)) hco
  absurd hgnez P
  exact Int.ofNat_eq_zero.mp this

lemma hqnz (hdeg : P.degree ≥ 2) : Q ≠ 0 := by
  refine support_nonempty.mp ?_
  unfold Finset.Nonempty
  use P.natDegree
  refine mem_support_iff.mpr ?_
  unfold Q''
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  simp
  constructor
  exact Pnez P hdeg
  by_contra hco
  have := Int.eq_zero_of_ediv_eq_zero (Int.ofNat_dvd.mpr (hgdvdlc P)) hco
  absurd hgnez P
  exact Int.ofNat_eq_zero.mp this

lemma hqpeval : ∀ i ∈ P.support, (Q).coeff i = g * (P.coeff i) := by
  intro i hi
  unfold Q''
  --let co (i : ℕ) : ℤ := (P.coeff i).num * (↑g / ↑(P.coeff i).den)
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  simp
  split_ifs with hpcoef
  rw [hpcoef]
  simp
  have hr1 : ↑((g : ℤ) / ↑(P.coeff i).den) = (g : ℚ) / ((P.coeff i).den : ℚ) := by
    set nu := (g : ℤ)
    set de := ((P.coeff i).den : ℤ)
    have hqr : (g : ℚ) = ↑nu := by
      unfold nu
      simp
    have hqr2 : ((P.coeff i).den : ℚ) = ↑de := by
      unfold de
      simp
    rw [hqr, hqr2]
    refine Rat.intCast_div nu de ?_
    unfold de nu
    unfold g'
    simp
    refine Finset.dvd_prod_of_mem (fun i => ((P.coeff i).den : ℤ)) hi
  rw [hr1, mul_div_assoc']
  conv_lhs => rw [mul_comm, ←mul_div_assoc']
  simp
  left;
  exact Rat.num_div_den (P.coeff i)


noncomputable def ad'' : ℤ := (Q).leadingCoeff
local notation "ad" => ad'' P


lemma had (hdeg : P.degree ≥ 2) : ad ≠ 0 := by exact leadingCoeff_ne_zero.mpr (hqnz P hdeg)

lemma hring (hdeg : P.degree ≥ 2) (i : ℕ) (hi : i ∈ P.support) (hid : i ≤ d - 1) : ad ^ (d - i - 1) * ad ^ i = ad ^ (d - 1) := by
  have hii : i ≤ P.natDegree := by exact le_natDegree_of_mem_supp i hi
  rw [←hqpndeg] at hii
  rw [←pow_add]
  have h2 : d - i - 1 + i =  d - 1 := by omega
  exact congrArg (HPow.hPow ad) h2
  exact hdeg


noncomputable def Qq'' := (Q).map (Int.castRingHom ℚ)
local notation "Qq" => Qq'' P


noncomputable def b'' (i : ℕ) : ℤ := (Q).coeff i * ad ^ (d - i - 1)
local notation "b" => b'' P


noncomputable def R'' : ℤ[X] := X ^ d + ∑ i ∈ P.support \ {d}, C (b i) * X ^ i
local notation "R" => R'' P


lemma hrdeg (hdeg : P.degree ≥ 2) : (R).natDegree = P.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  unfold R''
  rw [natDegree_add_eq_left_of_natDegree_lt]
  simp
  rw [hqpndeg P hdeg]
  have ht1 : (∑ i ∈ P.support \ {d}, C (b i) * X ^ i).natDegree ≤ d - 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr ?_
    intro i hi
    rw [finset_sum_coeff]
    simp only [coeff_C_mul_X_pow]
    simp
    intro hc hcc
    unfold b''
    simp
    left;
    by_contra hco
    have hqdc : i ∈ (Q).support := by exact mem_support_iff.mpr hco
    have h1 : i ≤ (Q).natDegree := by exact le_natDegree_of_ne_zero hco
    have ho : (Q).natDegree = d := rfl
    rw [ho] at h1
    have h2 : i ≥ d := by exact Nat.le_of_pred_lt hi
    have h3 : i = d := by exact Nat.le_antisymm h1 h2
    absurd hcc
    exact h3
  simp
  refine lt_of_le_of_lt ht1 ?_
  simp
  rw [hqpndeg P hdeg]
  refine natDegree_pos_iff_degree_pos.mpr ?_
  exact lt_of_lt_of_le (zero_lt_two) hdeg
  unfold R''
  rw [←hqpndeg P hdeg, coeff_add (X^d)]
  simp

lemma huse (hdeg : P.degree ≥ 2) : (R).coeff P.natDegree ≠ 0 := by
  unfold R''
  rw [coeff_add, finset_sum_coeff]
  simp
  split_ifs with h1 h2 h3
  absurd h1
  exact h2.2
  simp
  simp
  have := hqpndeg P hdeg
  absurd h1
  exact id (Eq.symm this)
  have := hqpndeg P hdeg
  absurd h1
  exact id (Eq.symm this)

lemma hr0 (hdeg : P.degree ≥ 2) : R ≠ 0 := by
  refine support_nonempty.mp ?_
  unfold Finset.Nonempty
  use P.natDegree
  refine mem_support_iff.mpr (huse P hdeg)

lemma hrd (hdeg : P.degree ≥ 2) : (R).degree ≥ 2 := by
  have h1 : (R).natDegree ≥ 2 := by
    rw [hrdeg]
    exact le_natDegree_of_coe_le_degree hdeg
    exact hdeg
  have h2 : (R).natDegree = (R).degree := by refine Eq.symm (degree_eq_natDegree (hr0 P hdeg))
  rw [←h2]
  simp
  exact h1


noncomputable def c'' := g * ad ^ (d - 1)
local notation "c" => c'' P


lemma hcnez (hdeg : P.degree ≥ 2) : c ≠ 0 := by
  unfold c''
  simp only [ne_eq, mul_eq_zero]
  push_neg
  constructor
  exact Int.ofNat_ne_zero.mpr (hgnez P)
  exact Int.pow_ne_zero (had P hdeg)


variable (n : ℕ) (x : ℚ)


noncomputable def yq' := ad * x
local notation "yq" => yq' P x


lemma hyqnez (hdeg : P.degree ≥ 2) (hx : x ≠ 0) : yq ≠ 0 := by
  unfold yq'
  simp
  constructor
  exact had P hdeg
  exact hx

lemma hreval0 (hdeg : P.degree ≥ 2) (hi : P.eval 0 = n.factorial) : (R).eval 0 = c * n.factorial := by
  have h1 : (R).eval 0 = (R).coeff 0 := Eq.symm (coeff_zero_eq_eval_zero R)
  have h2 : P.eval 0 = P.coeff 0 := Eq.symm (coeff_zero_eq_eval_zero P)
  rw [h1]
  unfold R''
  simp
  have hcon : d ≥ 2 := by
    rw [hqpndeg P hdeg]
    exact le_natDegree_of_coe_le_degree hdeg
  rw [h2] at hi
  split_ifs with hs1 hs2 hs3
  · absurd hs1
    exact hs2.2
  · rw [← hs1] at hcon
    contradiction
  · unfold b''
    simp
    qify
    rw [hqpeval P 0 (mem_support_iff.mpr hs3.1), ← hi]
    conv_lhs => rw [mul_comm, ←mul_assoc]
    simp
    left;
    unfold c''
    simp
    rw [mul_comm]
  · have hsf : P.coeff 0 = 0 ∨ 0 = d := by exact Decidable.or_iff_not_not_and_not.mpr hs3
    clear hs3
    cases hsf with
    | inl hsf =>
      rw [hsf] at hi
      qify
      rw [← hi]
      simp
    | inr hsf =>
      absurd hs1
      exact hsf


noncomputable def Qy' : ℤ[X] := R - c * n.factorial
local notation "Qy" => Qy' P n


lemma hyqhelp (hdeg : P.degree ≥ 2) : yq ^ d = ↑c * (P.coeff d * x ^ d) := by
  unfold yq' c''
  ring_nf
  conv_lhs => rw [mul_comm]
  conv_rhs => rw [mul_assoc]
  simp
  left;
  conv_rhs => rw [mul_comm, ←mul_assoc, mul_comm (a := P.coeff d)]
  rw [←hqpeval P d ?_]
  have hr1 : ad ^ d = ad ^ (d - 1) * ad ^ 1 := by
    rw [←pow_add]
    have hr2 : d - 1 + 1 = d := by
      have hcon : d ≥ 2 := by
        rw [hqpndeg P hdeg]
        exact le_natDegree_of_coe_le_degree hdeg
      have hcon2 : d ≥ 1 := by exact Nat.one_le_of_lt hcon
      omega
    rw [hr2]
  qify at hr1
  rw [hr1, mul_comm]
  simp
  left;
  unfold ad'' d''
  exact rfl
  rw [hqpndeg P hdeg]
  simp
  exact Pnez P hdeg

lemma hqyroot (hdeg : P.degree ≥ 2) (hi : P.eval x = n.factorial) : (Qy).aeval yq = 0 := by
  have dP := as_sum_support_C_mul_X_pow P
  have dp : P.eval x = ∑ i ∈ P.support, (P.coeff i) * x ^ i := by
    apply congrArg (eval x) at dP
    rw [dP, Polynomial.eval_finset_sum]
    simp
  unfold Qy'
  simp
  refine Lean.Grind.IntModule.sub_eq_zero_iff.mpr ?_
  rw [← hi, dp, Finset.mul_sum]
  unfold R''
  simp
  have hrw : P.support = (P.support \ {d}) ∪ {d} := by
    simp
    rw [hqpndeg P hdeg]
    simp
    exact Pnez P hdeg
  conv_rhs => rw [hrw]
  rw [Finset.sum_union (by simp)]
  simp
  have h1 : yq ^ d = ↑c * (P.coeff d * x ^ d) := by exact hyqhelp P x hdeg
  rw [add_comm, h1]
  simp
  refine Finset.sum_bijective id (Function.bijective_id) (by simp) ?_
  intro i hisp
  unfold b''
  simp
  rw [Finset.mem_sdiff] at hisp
  rw [hqpeval P i hisp.1]
  unfold yq'
  ring_nf
  conv_lhs => rw [mul_assoc, mul_assoc, mul_comm, ← mul_assoc, ← mul_assoc]
  have : i ≤ d - 1 := by
    choose h4 h5 using hisp
    simp at h5
    have h6 : i ≤ P.natDegree := by exact le_natDegree_of_mem_supp i h4
    rw [←hqpndeg P hdeg] at h6
    have hf : i < d := by exact Nat.lt_of_le_of_ne h6 h5
    exact Nat.le_sub_one_of_lt hf
  conv_rhs => rw [mul_assoc, mul_comm]
  simp
  left;
  conv_lhs => rw [mul_comm, ←mul_assoc, mul_comm]
  simp
  left;
  unfold c''
  simp
  left;
  have bl := hring P hdeg i hisp.1 this
  qify at bl
  exact bl

lemma hqymonic (hdeg : P.degree ≥ 2) : (Qy).Monic := by
  unfold Qy'
  refine Monic.sub_of_left ?_ ?_
  swap
  simp
  rw [←Polynomial.C_eq_intCast, ←Polynomial.C_eq_natCast]
  rw [Polynomial.degree_C (by exact (hcnez P hdeg))]
  rw [Polynomial.degree_C]
  swap
  simp
  exact Nat.factorial_ne_zero n
  simp
  refine lt_of_lt_of_le (by exact zero_lt_two) (hrd P hdeg)
  refine Monic.def.mpr ?_
  rw [←Polynomial.coeff_natDegree, hrdeg, ←hqpndeg]
  unfold R''
  simp
  exact hdeg
  exact hdeg

lemma heval (hdeg : P.degree ≥ 2) (hi : P.eval x = n.factorial) (y : ℤ) (hy : y = yq) : (R).eval y = c * n.factorial := by
  have dP := as_sum_support_C_mul_X_pow P
  have dp : P.eval x = ∑ i ∈ P.support, (P.coeff i) * x ^ i := by
    apply congrArg (eval x) at dP
    rw [dP, Polynomial.eval_finset_sum]
    simp
  unfold R''
  simp
  rw [Polynomial.eval_finset_sum]
  simp
  qify
  rw [← hi]
  conv_rhs => rw [dp, Finset.mul_sum]
  have hrw : P.support = (P.support \ {d}) ∪ {d} := by
    simp
    rw [hqpndeg P hdeg]
    simp
    exact Pnez P hdeg
  conv_rhs => rw [hrw]
  rw [Finset.sum_union (by simp)]
  simp
  have hr1 : y ^ d = ↑c * (P.coeff d * x ^ d) := by
    rw [hy]
    exact hyqhelp P x hdeg
  rw [hr1, add_comm]
  simp
  refine Finset.sum_bijective id (Function.bijective_id) (by simp) ?_
  intro i hisup
  simp
  rw [hy]
  unfold b'' c'' yq'
  simp
  ring_nf
  conv_lhs => rw [mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc, mul_assoc]
  rw [Finset.mem_sdiff] at hisup
  have : i ≤ d - 1 := by
    choose h4 h5 using hisup
    simp at h5
    have h6 : i ≤ P.natDegree := by exact le_natDegree_of_mem_supp i h4
    rw [←hqpndeg P hdeg] at h6
    have hf : i < d := by exact Nat.lt_of_le_of_ne h6 h5
    exact Nat.le_sub_one_of_lt hf
  conv_lhs => rw [mul_comm, mul_assoc]
  have bl := hring P hdeg i hisup.1 this
  qify at bl
  rw [bl]
  set cancel := ad ^ (d - 1) * x ^ i
  conv_rhs => rw [mul_assoc, mul_comm]
  refine mul_eq_mul_right_iff.mpr ?_
  left;
  exact hqpeval P i hisup.1


end rational_case_lemmas


/-- Main result: `abc_Z` implies that for any polynomial P ∈ ℚ[X] of degree at least 2,
the equation P(x) = n! has finitely many rational solutions x and finitely many
integer solutions n. Even though it may seem like a stronger statement that `abc_Z_poly_eq_fac_fin_sol`,
the problem can be reduced, and the previous result can be applied.-/
theorem abc_Z_poly_eq_fac_fin_sol_rat (P : ℚ[X]) (hdeg : P.degree ≥ 2) :
  abc_Z → Set.Finite {⟨n, x⟩ : ℕ × ℚ | P.eval x = n.factorial} := by

  intro abcz
  let Pr (n : ℕ) (x : ℚ) : Prop := P.eval x = n.factorial
  refine (set_sol_fin_iff_ex_bound Pr).2 ?_
  unfold Pr

  have dP := as_sum_support_C_mul_X_pow P
  set g := g' P
  set Q := Q'' P
  set Qq := Qq'' P
  set d := d'' P
  set ad := ad'' P
  let b (i : ℕ) : ℤ := b'' P i
  set R : ℤ[X] := R'' P
  set c := c'' P

  obtain ⟨N, hn⟩ := abc_Z_poly_eq_const_fac_fin_sol R (hrd P hdeg) c (hcnez P hdeg) abcz

  let M := max (N + 1) ((ad).natAbs + 1)
  use M
  intro n x hi
  set yq := yq' P x
  by_cases hx : x = 0
--
  rw [hx] at hi ⊢
  specialize hn n 0 (hreval0 P n hdeg hi)
  simp
  constructor
  unfold M
  simp only [lt_sup_iff]
  left;
  exact Nat.lt_add_right 1 hn.1
  constructor
  unfold M
  simp only [lt_sup_iff]
  left;
  simp
  unfold M
  simp only [lt_sup_iff]
  right;
  simp
  exact had P hdeg
--

  set Qy := Qy' P n
  obtain ⟨y, hyy, hydvd⟩ := exists_integer_of_is_root_of_monic (hqymonic P n hdeg) (hqyroot P n x hdeg hi)
  have hy : y = yq := by exact id (Eq.symm hyy)

  specialize hn n y (heval P n x hdeg hi y hy)

  have hxratdiv : x = Rat.divInt y ad := by
    have hyqq : yq' P x = ad * x := rfl
    rw [hyy] at hyqq
    simp at hyqq
    have hyyq : x = y / ad := by
      refine eq_div_of_mul_eq ?_ ?_
      simp
      exact had P hdeg
      rw [mul_comm]
      exact hyy
    rw [hyyq]
    exact Rat.intCast_div_eq_divInt y ad

  have hxnl : x.num ∣ y := by convert Rat.num_dvd y (b := ad) (had P hdeg)
  have hxnlabs : |x.num| ∣ |y| := (abs_dvd_abs x.num y).mpr hxnl
  have hxdl : ↑x.den ∣ ad := by convert Rat.den_dvd y ad
  have hxdlabs : |↑x.den| ∣ |ad| := (abs_dvd_abs (↑x.den) ad).mpr hxdl

  constructor
  unfold M
  simp only [lt_sup_iff]
  left;
  exact Nat.lt_add_right 1 hn.1

  constructor
  unfold M
  simp only [Nat.cast_add, Nat.cast_max, Int.natCast_natAbs, Nat.cast_one, lt_sup_iff]
  left;
  refine Int.le_iff_lt_add_one.mp ?_
  refine le_trans ?_ hn.2
  refine Int.le_add_one ?_
  refine Int.le_of_dvd ?_ hxnlabs
  simp
  by_contra hco
  rw [hco] at hy
  simp at hy
  absurd hy
  apply Ne.symm
  exact hyqnez P x hdeg hx

  unfold M
  simp only [Nat.cast_add, Nat.cast_max, Int.natCast_natAbs, Nat.cast_one, lt_sup_iff]
  right;
  zify
  have hle := Int.le_of_dvd (abs_pos.mpr (had P hdeg)) hxdlabs
  refine Int.le_iff_lt_add_one.mp ?_
  simp at hle
  exact hle
