# Vectors generated from the vacuum

Let $H$ be a Hilbert space, $L$ a space of field labels,
$\mathcal S(\mathbb R^4)$ the space of Schwartz test functions, and
$(D, \Omega, \varphi)$ a field system on $H$ and $L$, with domain $D$, vacuum
$\Omega$ and smeared fields $\varphi(a,f) : D \to D$.

A **word** is a finite sequence $w = \big((a_1,f_1), \dots, (a_k,f_k)\big)$ of
letters, each letter a pair $(a_i, f_i)$ of a label $a_i \in L$ and a Schwartz
test function $f_i \in \mathcal S(\mathbb R^4)$. Every length $k \ge 0$ is
allowed; the empty word, of length $0$, is written $\varnothing$.

The **vector generated from the vacuum** by a word $w$ is the vector
$\Phi(w) \in D$ defined by recursion on the length of $w$:

$$
\Phi(\varnothing) = \Omega, \qquad
\Phi\big((a,f)\,w\big) = \varphi(a,f)\,\Phi(w),
$$

where $(a,f)\,w$ is the word whose first letter is $(a,f)$, followed by the
letters of $w$. Unwinding the recursion,

$$
\Phi\big((a_1,f_1), \dots, (a_k,f_k)\big)
= \varphi(a_1,f_1)\,\varphi(a_2,f_2) \cdots \varphi(a_k,f_k)\,\Omega ,
$$

so the smeared field of the first letter stands leftmost and is applied last.

## Depends on

- [Field system](../wightman/field-system.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)

## Sources

- [PublicTheory.lean ledger: field vectors](../../sources/public-theory.md#field-vectors)
