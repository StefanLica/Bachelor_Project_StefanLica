# Bachelor Project - Generalized Brocard-Ramanujan Problem: A Lean Formalization via the abc-conjecture 
## Stefan Lica -- VU Amsterdam

This is the Lean code for my Bachelor Project.

ABSTRACT:
A well-known, yet unsolved problem in number theory is whether or not there are infinitely many pairs of solutions (x,y) with x a natural number and y an integer to the equation x! + 1 = y^2. In this thesis, we set out to formalize in the proof assistant Lean, the result that under the assumption of the abc-conjecture, there are only finitely many such solutions to the given equation. Moreover, the main goal is to formalize the proof of a stronger statement: for any polynomial P with integer coefficients and of degree at least 2, there are only finitely many pairs of solutions, (x,n) with x an integer and n a natural number, that satisfy P(x) = n!. We will base the formalization on Florian Luca's proof.

Finally, we will improve Luca's result by extending it over the rationals: for all polynomials P with rational coefficients and of degree at least 2, the equation P(x) = n! has finitely many pairs of solutions (x,n) with x a rational number and n a natural number. As we will show, this is an equivalent statement to the integer version.
