# Weak commutant with the Hilbert-space adjoint

Fix a Wilson family and a Euclidean correlation table $S$ for its tokens,
with common label space $\mathbb F$, and let $\mathcal S(\mathbb R^4)$ be
the space of Schwartz test functions $f : \mathbb R^4 \to \mathbb C$.

Let $\mathfrak W$ be Wightman data for $S$. Of these data the definition uses
only the field system: a Hilbert space $H$, whose inner product
$\langle \cdot, \cdot \rangle$ is conjugate-linear in its first argument; a
complex linear subspace $D \subseteq H$, the domain; and, for every label
$a \in \mathbb F$ and every $f \in \mathcal S(\mathbb R^4)$, a complex-linear
map $\varphi(a, f) : D \to D$, depending complex-linearly on $a$ and on $f$.
No condition on these data is assumed.

For a label $a$ and a test function $f$, let $T_{a,f}$ be the operator in $H$
with domain $D$ given by $T_{a,f}\, \psi = \varphi(a, f)\, \psi$ for
$\psi \in D$. Its Hilbert-space adjoint $T_{a,f}^*$ has as its domain the set
of vectors $\chi \in H$ for which the functional
$\psi \mapsto \langle \chi, T_{a,f}\, \psi\rangle$ is continuous on $D$. When
$D$ is dense in $H$, $T_{a,f}^*\, \chi$ is, for $\chi$ in that domain, the
unique vector with
$\langle T_{a,f}^*\, \chi, \psi \rangle = \langle \chi, T_{a,f}\, \psi \rangle$
for all $\psi \in D$; when $D$ is not dense, the convention is
$T_{a,f}^*\, \chi = 0$ on the same domain.

A bounded complex-linear operator $B : H \to H$ **belongs to the weak
commutant** of $\mathfrak W$ when, for every label $a \in \mathbb F$, every
test function $f \in \mathcal S(\mathbb R^4)$ and all vectors $\chi, \psi \in D$,

1. $\chi$ lies in the domain of $T_{a,f}^*$, and
2. $\big\langle T_{a,f}^*\, \chi,\ B \psi \big\rangle = \big\langle \chi,\ B\, \varphi(a, f)\, \psi \big\rangle .$

The definition uses the Hilbert-space adjoint of the operator $T_{a,f}$ and
its domain. It does not require $B$ to map $D$ into itself: $B \psi$ and
$B\,\varphi(a, f)\,\psi$ are vectors of $H$ that need not lie in $D$.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Extension](../../sources/every-phase.md#extension)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
