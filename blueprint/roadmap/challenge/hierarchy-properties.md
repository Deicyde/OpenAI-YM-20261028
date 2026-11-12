# The four properties of a hierarchy

Let $C$ be a Wilson family for a matrix gauge group, with set of tokens
$\mathcal T$, and let $T$ be a continuum hierarchy over $C$. Write
$\mathbb N = \{0, 1, 2, \dots\}$. The definition reads two components of $T$
directly.

- The map $\pi$, which assigns a graded field $\pi(v)$ to every token
  $v \in \mathcal T$. A graded field is a pair $(d, u)$ of a grade
  $d \in \mathbb N$ and a vector $u$ of the field space $F_d$ of $T$, a
  finite-dimensional complex normed space.
- The unselected correlations: for every $n \in \mathbb N$, every $n$-tuple
  $a = (a_0, \dots, a_{n-1})$ of graded fields and every configuration
  $x = (x_0, \dots, x_{n-1}) \in (\mathbb R^4)^n$ of $n$ points, coincident
  points included, the complex number $S_*(a; x)$, the correlation of $T$ for
  the extra value $*$, which is not a character.

Let $\omega : \mathbb N \to \mathbb N$ be a sequence of volume indices of $C$,
the volume order; no condition is placed on it. For every $n \in \mathbb N$ and
every $n$-tuple $v = (v_0, \dots, v_{n-1}) \in \mathcal T^n$ of tokens, let
$G_v : (\mathbb R^4)^n \to \mathbb C$ be the unselected correlation of the
graded fields that $\pi$ assigns to these tokens:

$$
G_v(x) = S_*\big((\pi(v_0), \dots, \pi(v_{n-1}));\, x\big)
\qquad \text{for } x \in (\mathbb R^4)^n .
$$

The hierarchy $T$ **has the four properties along $\omega$** when the
following four conditions hold.

1. **Wilson origin.** The family $C$ converges along $\omega$ to the functions
   $G_v$, in the sense of the
   [ordered continuum limit](../wilson-lattice/ordered-continuum-limit.md).
2. **Reconstruction.** $T$ satisfies the
   [reconstruction conditions](../continuum-hierarchy/reconstruction.md).
3. **Operator product expansion.** $T$ satisfies the
   [operator product expansion](../operator-product-expansion/operator-product-expansion.md).
4. **Non-freeness.** $T$ passes the
   [trace test](../non-freeness/trace-test.md).

The four properties are conditions on $T$ and $\omega$ and add no data. Only
the first involves $\omega$, and the limits it prescribes are given by the
unselected correlations, not by the correlations of a character. They are what
the [joint existence statement](joint-existence.md) asks of a hierarchy, and
they are named after the four themes of the
[upstream description](../../sources/upstream-readme.md#the-public-challenge),
in its order. That description's first theme also lists the fixed stencil of
each token's insertions and the logarithmic running of the couplings, two of
the regularity conditions that the joint existence statement requires of the
family, not conditions on $T$; its third theme also lists permutation symmetry
and smoothness at configurations of pairwise distinct points, which are two of
the reconstruction conditions and so part of the second property.

## Depends on

- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Ordered continuum limit](../wilson-lattice/ordered-continuum-limit.md)
- [Reconstruction conditions](../continuum-hierarchy/reconstruction.md)
- [Operator product expansion](../operator-product-expansion/operator-product-expansion.md)
- [Trace test](../non-freeness/trace-test.md)

## Sources

- [ChallengeSpec.lean ledger: hierarchy properties](../../sources/challenge-spec.md#hierarchy-properties)
- [Upstream description: the public challenge](../../sources/upstream-readme.md#the-public-challenge)
