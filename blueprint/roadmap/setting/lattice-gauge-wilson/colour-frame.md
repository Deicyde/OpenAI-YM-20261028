# Colour coordinates on the Lie algebra

Let $(n, G)$ be a gauge group, so that $G$ is a closed subgroup of the unitary
group $U(n+1)$, and let $\mathfrak g$ be its Lie algebra: the real linear
subspace of $M_{n+1}(\mathbb C)$, regarded as a real vector space, made of the
matrices $X$ with $\exp(tX) \in G$ for every real $t$. Give $\mathfrak g$ the
restriction of the real Frobenius inner product
$\langle X, Y \rangle_F = \operatorname{Re} \operatorname{tr}(X Y^*)$ of
$M_{n+1}(\mathbb C)$.

The colour coordinates of the gauge group are the following objects.

- The **number of colours** is the real dimension $d = \dim_{\mathbb R} \mathfrak g$.
- The **colour indices** are the natural numbers $k$ with $0 \le k < d$ (there are none when $d = 0$, which happens when $\mathfrak g = \{0\}$).
- The **colour space** is $\mathbb R^d$, whose points $c = (c_0, \dots, c_{d-1})$
  are called colours, with its standard inner product and norm

    $$
    \langle c, c' \rangle = \sum_{k=0}^{d-1} c_k c'_k , \qquad |c| = \langle c, c \rangle^{1/2} .
    $$

- The **colour scale** is the real number $\sqrt{n+1}$.
- Let $T_0, \dots, T_{d-1}$ be the orthonormal basis of $\mathfrak g$ for
  $\langle \cdot, \cdot \rangle_F$ that is fixed once and for all by a
  choice; the definition does not say which orthonormal basis it is, but it is
  one fixed basis, not an arbitrary one. The **colour frame** is the real
  linear isomorphism

    $$
    \mathbb R^d \to \mathfrak g , \qquad
    c \mapsto \sqrt{n+1} \, \sum_{k=0}^{d-1} c_k \, T_k .
    $$

- The **colour matrix** of a colour $c$ is the same element regarded as a
  matrix,

    $$
    X_c = \sqrt{n+1} \, \sum_{k=0}^{d-1} c_k \, T_k \in M_{n+1}(\mathbb C) ,
    $$

    so that $c \mapsto X_c$ is the real linear map
    $\mathbb R^d \to M_{n+1}(\mathbb C)$ obtained by following the colour
    frame with the inclusion of $\mathfrak g$ into $M_{n+1}(\mathbb C)$.

## Depends on

- [Real Frobenius inner product](frobenius-inner-product.md)
- [Lie algebra of a gauge group](gauge-lie-algebra.md)

## Sources

- [YM/Gauge ledger: Colors](../../../sources/lattice-gauge-wilson.md#colors)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
