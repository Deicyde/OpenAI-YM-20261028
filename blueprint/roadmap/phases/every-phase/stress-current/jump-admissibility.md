# Admissible base points for the current jump

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$, and space
has the axes $0, 1, 2$. A vector $y \in \mathbb R^4$ is spacelike when
$|y_3| < \|\vec y\|$, where $y_3$ is its time coordinate and
$\vec y = (y_0, y_1, y_2)$ its spatial part. A
[base point](integrated-current-jump.md) for $n$ points is a triple
$p = (\xi, u, t)$ with $\xi \in (\mathbb R^3)^n$, $u \in \mathbb C^n$ and
$t \in \mathbb R$.

**Spatial derivatives.** For a Schwartz function $g$ on $\mathbb R^3$ and a
spatial axis $i \in \{0, 1, 2\}$, $\partial_i g$ is the derivative of $g$ in
the direction of the $i$-th standard basis vector of $\mathbb R^3$.

**Spacelike room.** A base point $p = (\xi, u, t)$ for $n$ points **allows** $g$
at the slot $k \in \{0, \dots, n-1\}$ when, for every spatial axis $i$ and
every $r$ in the closed support of $\partial_i g$,

$$
|t| < \|r - \xi_k\| .
$$

**Tied heights.** The tied heights of $p$ at $k$ are the $n + 1$ real numbers

$$
\eta(p, k) = \operatorname{ins}_{k+1}\big( (\operatorname{Im} u_0, \dots, \operatorname{Im} u_{n-1});\ \operatorname{Im} u_k \big) \in \mathbb R^{n+1},
$$

obtained by inserting $\operatorname{Im} u_k$ again into slot $k + 1$
([insertion into a slot](slot-insertion.md)); its entries $k$ and $k+1$ are
both $\operatorname{Im} u_k$. The adjacent pair at $k$ is the pair of slots
$(k, k+1)$ in $\{0, \dots, n\}$.

**Exchange data.** Let $N = n + 1$, let $W$ be boundary distributions over a
Euclidean correlation table with common label space $\mathbb F$, and $Z$
a Laplace family for them, with continued function $\widetilde Z$, as in the
[spatially integrated current](integrated-current-jump.md). Write
$\mathcal T_N$ for the forward tube (complex configurations whose imaginary
parts have consecutive differences in the open forward cone
$\{y \in \mathbb R^4 : \|\vec y\| < y_3\}$) and $\overline\Gamma_N$ for the configurations
$y \in (\mathbb R^4)^N$ with consecutive differences in the closed forward
cone $\{y \in \mathbb R^4 : \|\vec y\| \le y_3\}$. For heights $h \in \mathbb R^N$, $(0, h)$ is
the configuration of the points with spatial part $0$ and times $h_m$. Let
$\sigma$ exchange the entries $k$ and $k + 1$ of a tuple (of labels, of points,
or of complex points). For labels $v \in \mathbb F^N$ and heights
$h \in \mathbb R^N$, **exchange data** of $Z$ for the pair $(k, k+1)$ at $v$
and $h$ consist of the following.

1. $h_k = h_{k+1}$, and $h_m < h_{m'}$ for all $m < m'$ with
   $(m, m') \neq (k, k+1)$.
2. $(0, h) \in \overline\Gamma_N$ and $\sigma(0, h) \in \overline\Gamma_N$.
3. For every real configuration $x$, the point $x + \mathrm i(0, h)$ lies in
   the closure of $\mathcal T_N$ and in the closure of
   $\{\zeta : \sigma\zeta \in \mathcal T_N\}$.
4. For every real configuration $x$ such that $x_{k+1} - x_k$ is spacelike, a
   function $A_x$ on $(\mathbb C^4)^N$, complex analytic at
   $x + \mathrm i(0, h)$, that agrees with $\widetilde Z(v; \cdot)$ on the
   intersection of $\mathcal T_N$ with some neighbourhood of
   $x + \mathrm i(0, h)$.
5. For every such $x$, a function $A'_x$, complex analytic at
   $x + \mathrm i(0, h)$, that agrees with
   $\zeta \mapsto \widetilde Z(\sigma v; \sigma\zeta)$ on the intersection of
   $\{\zeta : \sigma\zeta \in \mathcal T_N\}$ with some neighbourhood of
   $x + \mathrm i(0, h)$.

The two orders **agree** when, for every such $x$ whose points all have time
$0$, the functions $A_x$ and $A'_x$ coincide on a neighbourhood of
$x + \mathrm i(0, h)$. The family $Z$ **has exchange data at the heights $h$
for the slot $k$** when for every $v \in \mathbb F^{N}$ there are exchange
data of $Z$ for the pair $(k, k+1)$ at $v$ and $h$ for which the two orders
agree.

## Depends on

- [Spatially integrated current and its jump](integrated-current-jump.md)
- [Insertion into a slot](slot-insertion.md)

## Sources

- [YM/EveryPhase ledger: Docks](../../../../sources/every-phase.md#docks)
- [YM/EveryPhase ledger: Slots](../../../../sources/every-phase.md#slots)
- [YM/EveryPhase ledger: Strip](../../../../sources/every-phase.md#strip)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
