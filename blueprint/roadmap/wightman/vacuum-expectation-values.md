# Vacuum expectation values

Let $H$ be a Hilbert space with inner product $\langle\cdot,\cdot\rangle$, $L$
a space of field labels, $\mathcal S(\mathbb R^4)$ the space of Schwartz test
functions, and $(D, \Omega, \varphi)$ a field system on $H$ and $L$, with domain
$D$, vacuum $\Omega$ and smeared fields $\varphi(a,f) : D \to D$. For a word
$w$, a finite sequence of label and test-function pairs, let $\Phi(w) \in D$ be
the vector it generates from the vacuum.

For every $n \ge 0$, labels $a = (a_0, \dots, a_{n-1})$ in $L$ and Schwartz test
functions $f = (f_0, \dots, f_{n-1})$ in $\mathcal S(\mathbb R^4)$, the
**vacuum expectation value** of the ordered product of smeared fields is the
complex number

$$
\begin{aligned}
\mathcal W(a;f)
&= \Big\langle \Omega,\ \Phi\big((a_0,f_0), (a_1,f_1), \dots, (a_{n-1},f_{n-1})\big) \Big\rangle \\
&= \big\langle \Omega,\ \varphi(a_0,f_0)\,\varphi(a_1,f_1) \cdots \varphi(a_{n-1},f_{n-1})\,\Omega \big\rangle .
\end{aligned}
$$

The word lists the pairs $(a_i, f_i)$ in increasing order of $i$, so the field
with index $0$ stands leftmost and is applied last. The vacuum occupies the
first argument of the inner product, in which the inner product is
conjugate-linear.

## Depends on

- [Field system](../wightman/field-system.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)
- [Vectors generated from the vacuum](../wightman/field-vectors.md)

## Sources

- [PublicTheory.lean ledger: vacuum expectation values](../../sources/public-theory.md#vacuum-expectation-values)
