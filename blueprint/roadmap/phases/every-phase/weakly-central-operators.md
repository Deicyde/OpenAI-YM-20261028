# Weakly central bounded operators

Fix a Wilson family and a Euclidean correlation table $S$ for its tokens,
with common label space $\mathbb F$, and let $\mathcal S(\mathbb R^4)$ be
the space of Schwartz test functions $f : \mathbb R^4 \to \mathbb C$. For a test function
$f$, write $\bar f$ for its complex conjugate, $\bar f(x) = \overline{f(x)}$.

Let $\mathfrak W$ be Wightman data for $S$. Of these data the definition uses
the following:

- the field system: a Hilbert space $H$, whose inner product
  $\langle \cdot, \cdot \rangle$ is conjugate-linear in its first argument; a
  complex linear subspace $D \subseteq H$, the domain; and, for every label
  $a \in \mathbb F$ and every $f \in \mathcal S(\mathbb R^4)$, a complex-linear
  map $\varphi(a, f) : D \to D$, the smeared field, depending complex-linearly
  on $a$ and on $f$;
- the star operation: a conjugate-linear map $a \mapsto a^\star$ from
  $\mathbb F$ to itself.

No condition on these data is assumed. A bounded complex-linear operator
$B : H \to H$ is **weakly central** for $\mathfrak W$ when, for every label
$a \in \mathbb F$, every test function $f \in \mathcal S(\mathbb R^4)$ and all
vectors $\chi, \psi \in D$,

$$
\big\langle \varphi(a^\star, \bar f)\, \chi,\ B \psi \big\rangle
= \big\langle \chi,\ B\, \varphi(a, f)\, \psi \big\rangle .
$$

The condition does not require $B$ to map $D$ into itself: $B \psi$ and
$B\,\varphi(a, f)\,\psi$ are vectors of $H$ that need not lie in $D$. On the left
the field with the starred label and the conjugated test acts on $\chi$ inside
$D$; no Hilbert-space adjoint enters.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Irreducible](../../../sources/every-phase.md#irreducible)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
