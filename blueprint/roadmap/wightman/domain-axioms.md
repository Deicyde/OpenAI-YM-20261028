# Domain axioms

Let $H$ be a Hilbert space with norm $\lVert\cdot\rVert$, $L$ a space of field
labels, $\mathcal S(\mathbb R^4)$ the space of Schwartz test functions, and
$(D, \Omega, \varphi)$ a field system on $H$ and $L$, with domain $D$, vacuum
$\Omega$ and smeared fields $\varphi(a,f) : D \to D$. For a word $w$, a finite
sequence of label and test-function pairs, the empty word included, let
$\Phi(w) \in D$ be the vector it generates from the vacuum.

The field system **satisfies the domain axioms** when the following four
conditions hold. They are conditions only; no further data is given.

1. *Normalized vacuum:* $\lVert \Omega \rVert = 1$.
2. *Dense domain:* $D$ is dense in $H$ for the norm topology.
3. *Cyclic vacuum:* $D$ is equal to the complex linear span of the set
   $\{\Phi(w) : w \text{ a word}\}$, that is, to the set of all finite linear
   combinations $c_1\,\Phi(w_1) + \dots + c_m\,\Phi(w_m)$ with $m \ge 0$,
   complex numbers $c_j$ and words $w_j$. This is an equality of subspaces of
   $H$; no closure is taken.
4. *Temperedness:* for every label $a \in L$ and every vector $\psi \in D$, the
   map $f \mapsto \varphi(a,f)\,\psi$ from $\mathcal S(\mathbb R^4)$, with the
   topology of the Schwartz seminorms, to $H$, with its norm topology, is
   continuous.

## Depends on

- [Field system](../wightman/field-system.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Vectors generated from the vacuum](../wightman/field-vectors.md)

## Sources

- [PublicTheory.lean ledger: domain axioms](../../sources/public-theory.md#domain-axioms)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
