# Finite lattice moments

Let $C$ be a Wilson family for a matrix gauge group whose group of matrices is
$G$. Among its data are side lengths $L_p$ and denominators $m_N$ (positive
integers, $p, N \in \mathbb N = \{0, 1, 2, \dots\}$), real couplings
$\beta_{N,p}$, a Haar probability measure $h$ on $G$, a set $\mathcal T$ of
tokens, and, for all $N$ and $p$, every token $v$ and every site $x$ of the
periodic lattice $\Lambda_{L_p m_N} = (\mathbb Z/L_p m_N\mathbb Z)^4$, an
insertion $O^{N,p}_{v,x}$: a complex-valued function on the set
$\mathcal C_{L_p m_N}$ of configurations on $\Lambda_{L_p m_N}$ with values in
$G$.

For $N, p, n \in \mathbb N$, an $n$-tuple of tokens
$v = (v_0, \dots, v_{n-1}) \in \mathcal T^n$ and an $n$-tuple of sites
$x = (x_0, \dots, x_{n-1})$ of $\Lambda_{L_p m_N}$ (here $x_i$ is the $i$-th
site of the tuple, not a coordinate), the **finite moment** is the complex
number

$$
\mathcal M_{N,p}(v; x) = \int \prod_{i=0}^{n-1} O^{N,p}_{v_i, x_i}(U)\, d\mu_{N,p}(U),
$$

where $U$ runs over $\mathcal C_{L_p m_N}$ and
$\mu_{N,p} = \mu_{L_p m_N, \beta_{N,p}, h}$ is the Wilson measure on
$\mathcal C_{L_p m_N}$ for the side $L_p m_N$, the coupling $\beta_{N,p}$ and
the measure $h$. This is a definition, not a condition.

The integral is the Bochner integral of a complex-valued function, which by
convention is $0$ when the integrand is not integrable with respect to
$\mu_{N,p}$. The tuples are arbitrary: tokens may repeat and sites may
coincide. For $n = 0$ the product is empty and equals $1$.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](wilson-family.md)
- [Periodic lattice](periodic-lattice.md)
- [Wilson measure](wilson-measure.md)

## Sources

- [Declaration ledger of the Wilson lattice source: finite moments](../../sources/public-wilson.md#finite-moments)
- [Upstream description of the public challenge: Wilson origin](../../sources/upstream-readme.md#wilson-origin)
