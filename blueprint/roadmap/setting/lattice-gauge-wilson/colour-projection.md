# Projection of matrices onto colours

Let $(n, G)$ be a gauge group with Lie algebra
$\mathfrak g \subseteq M_{n+1}(\mathbb C)$, a real linear subspace of the
complex $(n+1) \times (n+1)$ matrices regarded as a real vector space. Let
$\langle X, Y \rangle_F = \operatorname{Re} \operatorname{tr}(X Y^*)$ be the
real Frobenius inner product of $M_{n+1}(\mathbb C)$, let $d$ be the number
of colours, let $T_0, \dots, T_{d-1}$ be the fixed orthonormal basis of
$\mathfrak g$ for $\langle \cdot, \cdot \rangle_F$, and let
$\mathbb R^d \to \mathfrak g$, $c \mapsto \sqrt{n+1} \sum_k c_k T_k$, be the
colour frame of the gauge group.

Let $P_{\mathfrak g} : M_{n+1}(\mathbb C) \to \mathfrak g$ be the orthogonal
projection onto $\mathfrak g$ for $\langle \cdot, \cdot \rangle_F$. The
**colour projection** of the gauge group is the real linear map
$\Pi : M_{n+1}(\mathbb C) \to \mathbb R^d$ that sends a matrix $A$ to the
colour whose image under the colour frame is $P_{\mathfrak g} A$:

$$
\Pi A = (\text{colour frame})^{-1} \big( P_{\mathfrak g} A \big) \in \mathbb R^d ,
\qquad A \in M_{n+1}(\mathbb C) .
$$

So $\Pi$ is the orthogonal projection onto $\mathfrak g$ followed by the
inverse of the colour frame.

## Depends on

- [Colour coordinates on the Lie algebra](colour-frame.md)

## Sources

- [YM/Gauge ledger: Colors](../../../sources/lattice-gauge-wilson.md#colors)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
