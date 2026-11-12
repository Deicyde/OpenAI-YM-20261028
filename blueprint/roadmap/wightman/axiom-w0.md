# Axiom W0: spectrum condition and unique vacuum

Let $H$ be a Hilbert space, with inner product $\langle \cdot, \cdot \rangle$
conjugate-linear in its first argument, $L$ a space of field labels, and $T$ a
Wightman theory on $H$ and $L$. W0 concerns three parts of $T$: the vacuum
$\Omega \in H$ of its field system; its translation representation, which
assigns to every $x \in \mathbb R^4$ a bounded operator $U(x)$ on $H$; and its
energy–momentum measure, which assigns to every subset $A$ of $\mathbb R^4$ a
bounded operator $E(A)$ on $H$, and to every vector $\psi \in H$ a finite
measure $\mu_\psi$ on the Borel sets of $\mathbb R^4$, the diagonal measure of
$\psi$.

For points $p = (p_0, p_1, p_2, p_3)$ and $b = (b_0, b_1, b_2, b_3)$ of
$\mathbb R^4$, write $p \cdot b = \sum_{k=0}^{3} p_k b_k$ for their Euclidean
inner product. The closed forward light cone, with time the last coordinate,
is

$$
\overline V_+ = \Big\{ p \in \mathbb R^4 :
\big( p_0^2 + p_1^2 + p_2^2 \big)^{1/2} \le p_3 \Big\},
$$

and its complement is
$\mathbb R^4 \setminus \overline V_+ = \{ p \in \mathbb R^4 : p_3 < (p_0^2 + p_1^2 + p_2^2)^{1/2} \}$.

The theory $T$ **satisfies axiom W0** when the following three conditions
hold. They are conditions only; W0 adds no data.

1. *Spectral representation of the translations:* for every vector
   $\psi \in H$ and every translation vector $b \in \mathbb R^4$,
   $\int_{\mathbb R^4} e^{\,i\, p \cdot b} \, d\mu_\psi(p) = \langle \psi, U(b)\,\psi \rangle$,
   where $i$ is the imaginary unit and $p$ is the variable of integration.
   The left side is the integral of the complex-valued function
   $p \mapsto e^{\,i\, p \cdot b}$ against the measure $\mu_\psi$, the
   characteristic function of $\mu_\psi$ at $b$. The exponent is $+i$ times
   the Euclidean inner product $p \cdot b$; no Minkowski product enters.
2. *Spectrum condition:* $E(\mathbb R^4 \setminus \overline V_+) = 0$, the
   zero operator on $H$: the energy–momentum measure assigns the zero operator
   to the complement of the closed forward light cone.
3. *Unique vacuum:* for every vector $\psi \in H$, if $U(x)\,\psi = \psi$ for
   every $x \in \mathbb R^4$, then $\psi = c\,\Omega$ for some complex number
   $c$.

These three conditions are all of W0. In particular, W0 does not itself
require $U(x)\,\Omega = \Omega$.

## Depends on

- [Wightman theory data](../wightman/wightman-theory.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)
- [Energy–momentum measure](../wightman/energy-momentum-measure.md)
- [Translation representation](../wightman/translation-representation.md)
- [Closed forward light cone](../spacetime/forward-light-cone.md)
- [Field system](../wightman/field-system.md)

## Sources

- [PublicTheory.lean ledger: axiom W0](../../sources/public-theory.md#axiom-w0)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
