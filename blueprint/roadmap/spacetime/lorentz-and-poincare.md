# Proper orthochronous Lorentz transformations and Poincaré coordinates

Write points of spacetime $\mathbb R^4$ as $x = (x_0, x_1, x_2, x_3)$, with
time the last coordinate $x_3$. Let $m(x) = x_3^2 - x_0^2 - x_1^2 - x_2^2$ be
the Minkowski square and
$\overline{V}_+ = \{ x \in \mathbb R^4 : (x_0^2 + x_1^2 + x_2^2)^{1/2} \le x_3 \}$
the closed forward light cone.

A proper orthochronous Lorentz transformation is a continuous real-linear map
$\Lambda : \mathbb R^4 \to \mathbb R^4$ that has a continuous linear two-sided
inverse $\Lambda^{-1}$ and satisfies three conditions:

1. its determinant is one: $\det \Lambda = 1$;
2. it preserves the Minkowski square: $m(\Lambda x) = m(x)$ for every
   $x \in \mathbb R^4$;
3. for every $x \in \mathbb R^4$, $\Lambda x \in \overline{V}_+$ if and only if
   $x \in \overline{V}_+$.

The invertible map is the data and the three conditions are required of it.
The set $\mathcal L$ of these transformations carries the topology induced by
the map $\Lambda \mapsto (\Lambda, \Lambda^{-1})$ into pairs of continuous
linear maps of $\mathbb R^4$, each factor with its operator-norm topology.

The Poincaré coordinates are the pairs $(\Lambda, b)$ of a proper orthochronous
Lorentz transformation $\Lambda \in \mathcal L$ and a vector
$b \in \mathbb R^4$, that is, the product $\mathcal L \times \mathbb R^4$ with
the product topology. Only this set of pairs and its topology are defined; the
definition puts no multiplication on the pairs.

## Depends on

- [Spacetime and space](spacetime-coordinates.md)
- [Minkowski square](minkowski-square.md)
- [Closed forward light cone](forward-light-cone.md)

## Sources

- [PublicTheory.lean ledger: Lorentz and Poincaré](../../sources/public-theory.md#lorentz-and-poincare)
