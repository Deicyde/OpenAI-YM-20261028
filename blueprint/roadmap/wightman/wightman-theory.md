# Wightman theory data

Let $H$ be a Hilbert space, $L$ a space of field labels, and
$\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime $\mathbb R^4$. A
**Wightman theory** on $H$ and $L$ consists of five pieces of data, each
satisfying the conditions of its own definition, and one further condition.
The data are:

1. a **field system** $(D, \Omega, \varphi)$ on $H$ and $L$: a complex linear
   subspace $D$ of $H$, the domain; a vector $\Omega \in D$, the vacuum; and,
   for every label $a \in L$ and every Schwartz test function
   $f \in \mathcal S(\mathbb R^4)$, a complex-linear map
   $\varphi(a, f) : D \to D$, the smeared field, which depends
   complex-linearly on $a$ and complex-linearly on $f$;
2. a **conjugate-linear map** $a \mapsto a^\dagger$ from $L$ to $L$: for all
   labels $a, b \in L$ and every complex number $c$,
   $(a + b)^\dagger = a^\dagger + b^\dagger$ and
   $(c\,a)^\dagger = \bar c\, a^\dagger$, where $\bar c$ is the complex
   conjugate of $c$;
3. a **translation representation** on $H$, which assigns to every
   $x \in \mathbb R^4$ a bounded operator $U(x)$ on $H$;
4. an **energy–momentum measure** on $H$, which assigns to every subset $A$
   of $\mathbb R^4$ a bounded operator $E(A)$ on $H$, and to every vector
   $\psi \in H$ a finite measure $\mu_\psi$ on the Borel sets of
   $\mathbb R^4$;
5. a **Poincaré action** on $H$ and $L$, which consists of a set
   $\mathcal G$ of symmetries with a distinguished element $e$, a product
   $(g, h) \mapsto gh$ and a topology; for every $g \in \mathcal G$, a bounded
   operator $V(g)$ on $H$, a complex-linear bijection $a \mapsto g \cdot a$ of
   $L$ and a map $f \mapsto g \cdot f$ of $\mathcal S(\mathbb R^4)$ to itself;
   a map $\tau : \mathbb R^4 \to \mathcal G$, where $\tau(x)$ is the pure
   translation by $x$; and a homeomorphism from $\mathcal G$ onto the
   Poincaré coordinates.

The further condition, **translation compatibility**, says that the Poincaré
action represents each pure translation on $H$ by the operator of the
translation representation:

$$
V(\tau(x)) = U(x) \qquad \text{for every } x \in \mathbb R^4,
$$

an equality of bounded operators on $H$.

Apart from translation compatibility, no condition relates the five pieces to
one another. In particular, no condition of a Wightman theory relates the
translation representation to the energy–momentum measure; axiom W0 does. The
Wightman axioms W0–W3 are separate conditions on a Wightman theory, not part
of it. The source describes these data as the observable data of a
relativistic quantum field theory.

## Depends on

- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Field system](../wightman/field-system.md)
- [Translation representation](../wightman/translation-representation.md)
- [Energy–momentum measure](../wightman/energy-momentum-measure.md)
- [Poincaré action](../wightman/poincare-action.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [PublicTheory.lean ledger: Wightman theory](../../sources/public-theory.md#wightman-theory)
