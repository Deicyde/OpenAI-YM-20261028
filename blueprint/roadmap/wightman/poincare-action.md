# Poincaré action

Let $H$ be a Hilbert space with norm $\lVert\cdot\rVert$, $L$ a space of field
labels, and $\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime $\mathbb R^4$, whose points are
written $x = (x_0, x_1, x_2, x_3)$ with time the last coordinate $x_3$. A
bounded operator on $H$ is a continuous complex-linear map $H \to H$; $1$
denotes the identity operator, and $ST$ the composite of bounded operators $S$
and $T$, with $T$ applied first.

Let $\mathcal L$ be the set of proper orthochronous Lorentz transformations: the
continuous real-linear maps $\Lambda : \mathbb R^4 \to \mathbb R^4$ that have a
continuous linear two-sided inverse $\Lambda^{-1}$, have determinant one,
preserve the Minkowski square $x_3^2 - x_0^2 - x_1^2 - x_2^2$, and map a vector
into the closed forward light cone
$\{x \in \mathbb R^4 : (x_0^2 + x_1^2 + x_2^2)^{1/2} \le x_3\}$ exactly when the
vector lies in it. For $\Lambda, \Lambda' \in \mathcal L$, $\Lambda\Lambda'$ is
the composite map, with $\Lambda'$ applied first, and $\mathrm{id}$ is the
identity map of $\mathbb R^4$. The Poincaré coordinates are the pairs
$(\Lambda, b)$ with $\Lambda \in \mathcal L$ and $b \in \mathbb R^4$, with the
product of two topologies: on $\mathcal L$ the topology induced by
$\Lambda \mapsto (\Lambda, \Lambda^{-1})$ from pairs of continuous linear maps
of $\mathbb R^4$, each with its operator-norm topology, and on $\mathbb R^4$ the
Euclidean topology.

A **Poincaré action** on $H$ and $L$ consists of the following data:

- a set $\mathcal G$, whose elements are called symmetries, with a distinguished
  element $e \in \mathcal G$, a binary operation $(g, h) \mapsto gh$ on
  $\mathcal G$, and a topology on $\mathcal G$;
- for every $g \in \mathcal G$, a bounded operator $V(g)$ on $H$;
- for every $g \in \mathcal G$, a complex-linear bijection $a \mapsto g \cdot a$
  of $L$ onto itself;
- for every $g \in \mathcal G$, a map $f \mapsto g \cdot f$ of
  $\mathcal S(\mathbb R^4)$ to itself;
- a map $\tau : \mathbb R^4 \to \mathcal G$, where $\tau(x)$ is called the pure
  translation by $x$;
- a homeomorphism $c$ of $\mathcal G$ onto the Poincaré coordinates, that is, a
  bijection that is continuous and has a continuous inverse; write
  $c(g) = (\Lambda_g, b_g)$, with $\Lambda_g \in \mathcal L$ and
  $b_g \in \mathbb R^4$.

These data are subject to ten conditions, for all symmetries
$g, h \in \mathcal G$, vectors $\psi \in H$, Schwartz test functions
$f \in \mathcal S(\mathbb R^4)$ and points $x, y \in \mathbb R^4$:

1. $V(e) = 1$.
2. $V(gh) = V(g)\,V(h)$.
3. $\lVert V(g)\,\psi \rVert = \lVert \psi \rVert$.
4. The map $g \mapsto V(g)\,\psi$ from $\mathcal G$ to $H$ is continuous, for
   the given topology of $\mathcal G$ and the norm topology of $H$.
5. $\Lambda_e = \mathrm{id}$ and $b_e = 0$.
6. $\Lambda_{gh} = \Lambda_g \Lambda_h$ and $b_{gh} = \Lambda_g b_h + b_g$.
7. $\Lambda_{\tau(x)} = \mathrm{id}$ and $b_{\tau(x)} = x$.
8. $(g \cdot f)(x) = f\big(\Lambda_g^{-1}(x - b_g)\big)$.
9. $\tau(0) = e$.
10. $\tau(x + y) = \tau(x)\,\tau(y)$.

No group axiom is listed as a condition of its own; the operation of
$\mathcal G$ enters only conditions 2, 6 and 10, and its distinguished element
$e$ only conditions 1, 5 and 9. The maps on labels are subject to no
condition beyond being complex-linear bijections. The maps on test functions are
data, but condition 8 fixes each of their values.

## Depends on

- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)
- [Proper orthochronous Lorentz transformations and Poincaré coordinates](../spacetime/lorentz-and-poincare.md)

## Sources

- [PublicTheory.lean ledger: Poincaré action](../../sources/public-theory.md#poincare-action)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
