# Axiom W1: fields on a common dense domain

Let $H$ be a Hilbert space, with norm $\lVert \cdot \rVert$ and inner product
$\langle \cdot, \cdot \rangle$ conjugate-linear in its first argument, $L$ a
space of field labels, $\mathcal S(\mathbb R^4)$ the space of Schwartz test
functions $f : \mathbb R^4 \to \mathbb C$ on spacetime, and $T$ a Wightman
theory on $H$ and $L$. W1 concerns two parts of $T$: its field system
$(D, \Omega, \varphi)$, made of the domain $D$, a complex linear subspace of
$H$, the vacuum $\Omega \in D$ and the smeared fields
$\varphi(a, f) : D \to D$ for labels $a \in L$ and
$f \in \mathcal S(\mathbb R^4)$; and its conjugate-linear map
$a \mapsto a^\dagger$ from $L$ to $L$.

A word is a finite sequence $w = \big((a_1, f_1), \dots, (a_k, f_k)\big)$ of
pairs of a label $a_j \in L$ and a Schwartz test function $f_j$, of any length
$k \ge 0$. The vector it generates from the vacuum is
$\Phi(w) = \varphi(a_1, f_1)\,\varphi(a_2, f_2) \cdots \varphi(a_k, f_k)\,\Omega \in D$,
and $\Phi(w) = \Omega$ for the empty word. For
$f \in \mathcal S(\mathbb R^4)$, $\bar f$ is its complex conjugate,
$\bar f(x) = \overline{f(x)}$ for every $x \in \mathbb R^4$.

The theory $T$ **satisfies axiom W1** when the following two conditions hold.
They are conditions only; W1 adds no data.

1. *Domain axioms:* the field system satisfies the domain axioms, which are
   the following four conditions.

    - *Normalized vacuum:* $\lVert \Omega \rVert = 1$.
    - *Dense domain:* $D$ is dense in $H$ for the norm topology.
    - *Cyclic vacuum:* $D$ is equal to the complex linear span of the vectors
      $\Phi(w)$, $w$ ranging over all words, the empty word included: the set
      of their finite linear combinations with complex coefficients. This is
      an equality of subspaces of $H$; no closure is taken.
    - *Temperedness:* for every label $a \in L$ and every vector
      $\psi \in D$, the map $f \mapsto \varphi(a, f)\,\psi$ from
      $\mathcal S(\mathbb R^4)$, with the topology of the Schwartz seminorms,
      to $H$, with its norm topology, is continuous.

2. *Adjoint axiom:* the field system satisfies the adjoint axiom for the map
   $a \mapsto a^\dagger$ of $T$: for every label $a \in L$, every Schwartz
   test function $f \in \mathcal S(\mathbb R^4)$ and all vectors
   $\psi, \chi \in D$,
   $\langle \varphi(a, f)\,\psi, \chi \rangle = \langle \psi, \varphi(a^\dagger, \bar f)\,\chi \rangle$.

These two conditions are all of W1. Temperedness is continuity with values
in $H$ and its norm topology, for each fixed label and vector of $D$. The
adjoint identity is required only for vectors of $D$, and the map
$a \mapsto a^\dagger$ is not required to be an involution.

## Depends on

- [Wightman theory data](../wightman/wightman-theory.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Domain axioms](../wightman/domain-axioms.md)
- [Adjoint axiom](../wightman/adjoint-axiom.md)

## Sources

- [PublicTheory.lean ledger: axiom W1](../../sources/public-theory.md#axiom-w1)
