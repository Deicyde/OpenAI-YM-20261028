# Regularity of a Wilson family

Let $C$ be a Wilson family for a matrix gauge group whose group of matrices is
$G$, with side lengths $L_p$ and denominators $m_N$ (positive integers,
$p, N \in \mathbb N = \{0, 1, 2, \dots\}$), real couplings $\beta_{N,p}$, a set
$\mathcal T$ of tokens and, for all $N$ and $p$, every token $v$ and every site
$x$ of the periodic lattice $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ of side
$M = L_p m_N$, an insertion $O^{N,p}_{v,x}$: a complex-valued function on the
set $\mathcal C_M$ of configurations on $\Lambda_M$ with values in $G$. Write
$a_N = 1/m_N$ for the
lattice spacing, $e_i \in \Lambda_M$ for the site with coordinate $1$ on the
axis $i$ and $0$ on the other three axes, and $U(y, i) \in G$ for the value of
a configuration $U$ on the link $(y, i)$ leaving the site $y$ along the axis
$i \in \{0, 1, 2, 3\}$. Sites are added coordinatewise modulo $M$.

The family $C$ is **regular** when it satisfies the following four
conditions. Regularity is a property of the family and adds no data.

1. **Logarithmic running of the coupling.** There is a real number $b > 0$,
    the slope, such that for every real $\varepsilon > 0$ there is an
    $N_0 \in \mathbb N$ with
    $\bigl|\beta_{N,p}/\log(1/a_N) - b\bigr| < \varepsilon$ for every
    $N \ge N_0$ and every $p \in \mathbb N$. Here $\log$ is the natural
    logarithm, and $\log(1/a_N) = \log m_N$. In other words,
    $\beta_{N,p}/\log(1/a_N) \to b$ as $N \to \infty$, uniformly in the volume
    index $p$.
2. **Continuity.** For all $N, p \in \mathbb N$, every token $v$ and every site
    $x$ of $\Lambda_M$, the insertion $O^{N,p}_{v,x}$ is continuous for the
    product topology on $\mathcal C_M$, $G$ carrying the topology it inherits
    from the complex matrices.
3. **Gauge invariance.** For all $N, p \in \mathbb N$, every token $v$, every
    site $x$ of $\Lambda_M$, every map $g : \Lambda_M \to G$ and every
    configuration $U$ on $\Lambda_M$,
    $O^{N,p}_{v,x}(U^g) = O^{N,p}_{v,x}(U)$, where $U^g$ is the configuration
    with $U^g(y, i) = g(y)\, U(y, i)\, g(y + e_i)^{-1}$ on every link $(y, i)$,
    the products and the inverse taken in $G$. The map $g$ is arbitrary.
4. **Fixed stencil.** For every token $v$ there is a finite set
    $\Sigma_v \subseteq \mathbb Z^4$ of offsets such that the following holds for
    all $N, p \in \mathbb N$ and every site $x$ of $\Lambda_M$. Let
    $P = \{\bar z + x : z \in \Sigma_v\} \subseteq \Lambda_M$, where
    $\bar z \in \Lambda_M$ reduces each of the four coordinates of $z$ modulo
    $M$. If two configurations $U$ and $V$ on $\Lambda_M$ satisfy
    $U(y, i) = V(y, i)$ for every link $(y, i)$ with $y \in P$ and
    $y + e_i \in P$, then $O^{N,p}_{v,x}(U) = O^{N,p}_{v,x}(V)$. The set
    $\Sigma_v$ depends on the token $v$ alone, not on $N$, $p$ or $x$, and only
    links with both endpoints in $P$ are required to agree.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](wilson-family.md)
- [Lattice spacing and positions of sites](lattice-spacing-and-positions.md)
- [Periodic lattice](periodic-lattice.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [Declaration ledger of the joint target source: Wilson regularity](../../sources/challenge-spec.md#wilson-regularity)
- [Upstream description of the public challenge: Wilson origin](../../sources/upstream-readme.md#wilson-origin)
