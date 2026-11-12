# Axiom W3: locality

Let $H$ be a Hilbert space, $L$ a space of field labels,
$\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime $\mathbb R^4$, and $T$ a
Wightman theory on $H$ and $L$. W3 concerns the field system
$(D, \Omega, \varphi)$ of $T$, made of the domain $D$, a complex linear
subspace of $H$, the vacuum $\Omega \in D$ and the smeared fields
$\varphi(a, f) : D \to D$ for labels $a \in L$ and
$f \in \mathcal S(\mathbb R^4)$.

The closed support of a function $f$ on $\mathbb R^4$ is the closure in
$\mathbb R^4$ of the set $\{x \in \mathbb R^4 : f(x) \neq 0\}$. A vector
$v = (v_0, v_1, v_2, v_3)$ of $\mathbb R^4$, whose last coordinate $v_3$ is
time, is spacelike when $v_3^2 - (v_0^2 + v_1^2 + v_2^2) < 0$. Two Schwartz
test functions $f$ and $g$ are spacelike separated when $x - y$ is spacelike
for every point $x$ of the closed support of $f$ and every point $y$ of the
closed support of $g$.

The theory $T$ **satisfies axiom W3** when its field system satisfies local
commutativity: for all labels $a, b \in L$, all Schwartz test functions
$f, g \in \mathcal S(\mathbb R^4)$ such that $f$ and $g$ are spacelike
separated, and every vector $\psi \in D$,

$$
\varphi(a, f)\,\varphi(b, g)\,\psi = \varphi(b, g)\,\varphi(a, f)\,\psi .
$$

This is the only condition of W3, and W3 adds no data. The condition applies
to every pair of labels and asks for plain commutation of the two smeared
fields on $D$: no sign, grading or anticommutator enters.

## Depends on

- [Wightman theory data](../wightman/wightman-theory.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Local commutativity](../wightman/local-commutativity.md)

## Sources

- [PublicTheory.lean ledger: axiom W3](../../sources/public-theory.md#axiom-w3)
