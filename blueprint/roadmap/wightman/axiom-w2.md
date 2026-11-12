# Axiom W2: Poincaré covariance

Let $H$ be a Hilbert space, $L$ a space of field labels,
$\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime $\mathbb R^4$, and $T$ a
Wightman theory on $H$ and $L$. W2 concerns two parts of $T$. The first is its
field system $(D, \Omega, \varphi)$, made of the domain $D$, a complex linear
subspace of $H$, the vacuum $\Omega \in D$ and the smeared fields
$\varphi(a, f) : D \to D$ for labels $a \in L$ and
$f \in \mathcal S(\mathbb R^4)$. The second is its Poincaré action, which
gives a set $\mathcal G$ of symmetries with a distinguished element $e$ and a
product $(g, h) \mapsto gh$; for every $g \in \mathcal G$, a bounded operator
$V(g)$ on $H$, a complex-linear bijection $a \mapsto g \cdot a$ of $L$ and a
map $f \mapsto g \cdot f$ of $\mathcal S(\mathbb R^4)$ to itself; and a map
$\tau : \mathbb R^4 \to \mathcal G$, where $\tau(x)$ is the pure
translation by $x$. It also gives a topology on $\mathcal G$ and a
homeomorphism $c$ from $\mathcal G$ onto the Poincaré coordinates; write
$c(g) = (\Lambda_g, b_g)$, with $\Lambda_g$ a proper orthochronous Lorentz
transformation and $b_g \in \mathbb R^4$. By the conditions of a Poincaré
action, $(g \cdot f)(x) = f\big(\Lambda_g^{-1}(x - b_g)\big)$ for every
$g \in \mathcal G$, $f \in \mathcal S(\mathbb R^4)$ and $x \in \mathbb R^4$.

The theory $T$ **satisfies axiom W2** when the following five conditions hold
for all symmetries $g, h \in \mathcal G$, every label $a \in L$, every
Schwartz test function $f \in \mathcal S(\mathbb R^4)$ and every vector
$\psi \in D$. They are conditions only; W2 adds no data.

1. *Identity on labels:* $e \cdot a = a$.
2. *Composition on labels:* $(gh) \cdot a = g \cdot (h \cdot a)$.
3. *Invariant domain:* $V(g)$ maps $D$ into $D$, that is,
   $V(g)\,\psi \in D$.
4. *Invariant vacuum:* $V(g)\,\Omega = \Omega$.
5. *Covariant fields:*
   $V(g)\big(\varphi(a, f)\,\psi\big) = \varphi(g \cdot a,\, g \cdot f)\big(V(g)\,\psi\big)$.
   The right side is defined because $V(g)\,\psi$ lies in $D$ by
   condition 3.

These five conditions are all of W2. Condition 5 is an equality of vectors of
$H$, required for each vector $\psi$ of $D$; no inverse of $V(g)$ enters it.
Conditions 1 and 2 concern the action on labels of every symmetry, the pure
translations included: W2 does not require the pure translations to act
trivially on labels.

## Depends on

- [Wightman theory data](../wightman/wightman-theory.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Poincaré action](../wightman/poincare-action.md)
- [Field system](../wightman/field-system.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)

## Sources

- [PublicTheory.lean ledger: axiom W2](../../sources/public-theory.md#axiom-w2)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
