# Real Frobenius inner product

Let $q$ be a natural number ($q = 0$ included), and let $M_q(\mathbb C)$ be
the space of complex $q \times q$ matrices, regarded as a real vector space,
with real numbers acting entrywise. Give it the Frobenius norm

$$
\|X\|_F = \Big( \sum_{i,j} |X_{ij}|^2 \Big)^{1/2} ,
$$

and write $Y^*$ for the conjugate transpose of $Y$ and $\operatorname{tr}$ for
the trace.

The **real Frobenius inner product** on $M_q(\mathbb C)$ is the real inner
product

$$
\langle X, Y \rangle_F = \operatorname{Re} \operatorname{tr}(X Y^*) ,
\qquad X, Y \in M_q(\mathbb C) .
$$

The definition makes $M_q(\mathbb C)$, with the Frobenius norm, a real inner
product space for this pairing: it includes the facts that for all
$X, X', Y \in M_q(\mathbb C)$ and every real $t$,

$$
\|X\|_F^2 = \langle X, X \rangle_F , \qquad
\langle Y, X \rangle_F = \langle X, Y \rangle_F ,
$$

$$
\langle X + X', Y \rangle_F = \langle X, Y \rangle_F + \langle X', Y \rangle_F ,
\qquad
\langle t X, Y \rangle_F = t \, \langle X, Y \rangle_F .
$$

The inner product is not normalized: there is no factor $1/q$.

## Depends on

This node has no prerequisites.

## Sources

- [YM/Gauge ledger: Colors](../../../sources/lattice-gauge-wilson.md#colors)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
