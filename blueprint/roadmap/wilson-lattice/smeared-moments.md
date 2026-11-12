# Smeared lattice moments

Let $C$ be a Wilson family for a matrix gauge group, with side lengths $L_p$
and denominators $m_N$ (positive integers,
$p, N \in \mathbb N = \{0, 1, 2, \dots\}$) and a set $\mathcal T$ of tokens.
Write $\Lambda_{L_p m_N} = (\mathbb Z/L_p m_N\mathbb Z)^4$ for the periodic
lattice of side $L_p m_N$, $a_N = 1/m_N$ for the lattice spacing,
$\mathrm{pos}_{N,p}(y) \in \mathbb R^4$ for the position of a site $y$ of
$\Lambda_{L_p m_N}$, and $\mathcal M_{N,p}(v; x)$ for the finite moment at an
$n$-tuple $v$ of tokens and an $n$-tuple $x = (x_0, \dots, x_{n-1})$ of sites
of $\Lambda_{L_p m_N}$, where $x_i$ is the $i$-th site of the tuple.

For $N, p, n \in \mathbb N$, an $n$-tuple of tokens $v \in \mathcal T^n$ and a
separated test function $t \in \mathcal D(\mathrm{Sep}_n)$ on configurations
of $n$ points (an infinitely differentiable function
$t : (\mathbb R^4)^n \to \mathbb C$ whose closed support is compact and
contained in the set $\mathrm{Sep}_n$ of configurations of $n$ pairwise
distinct points), the **smeared moment** is the complex number

$$
\widetilde{\mathcal M}_{N,p}(v; t) = a_N^{4n} \sum_{x} t\bigl(\mathrm{pos}_{N,p}(x_0), \dots, \mathrm{pos}_{N,p}(x_{n-1})\bigr)\, \mathcal M_{N,p}(v; x),
$$

where the sum runs over all $n$-tuples $x = (x_0, \dots, x_{n-1})$ of sites of
$\Lambda_{L_p m_N}$, tuples with coincident sites included. The only
normalization is the factor $a_N^{4n}$. This is a definition, not a
condition.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](wilson-family.md)
- [Test functions on separated configurations](../spacetime/separated-test-functions.md)
- [Lattice spacing and positions of sites](lattice-spacing-and-positions.md)
- [Periodic lattice](periodic-lattice.md)
- [Finite lattice moments](finite-moments.md)

## Sources

- [Declaration ledger of the Wilson lattice source: smeared moments](../../sources/public-wilson.md#smeared-moments)
