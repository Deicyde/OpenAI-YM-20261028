# Exchange heights for every adjacent pair

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$x \in \mathbb R^4$, $t(x) = x_3$ is its time and
$\vec x = (x_0, x_1, x_2)$ its spatial part.
Configurations of $n$ points are elements of $(\mathbb R^4)^n$, with the
Euclidean inner product $\langle q, y\rangle = \sum_i \sum_a (q_i)_a (y_i)_a$
and its norm and distance. For heights $h \in \mathbb R^n$, $(0, h)$ is the
configuration whose point $i$ has spatial part $0$ and time $h_i$. Let
$\overline\Gamma_n$ be the set of configurations $y$ whose consecutive
differences $y_{i+1} - y_i$ ($0 \le i < n - 1$) lie in the closed forward cone
$\{x \in \mathbb R^4 : \|\vec x\| \le t(x)\}$.

**Spectral cone.** A proper orthochronous Lorentz transformation is a linear
map $\Lambda$ of $\mathbb R^4$ of determinant $1$ that preserves
$t(x)^2 - \|\vec x\|^2$ and maps the closed forward cone onto itself. Let $P$
be the spatial reflection $P(x) = (-\vec x, t(x))$. The **spectral cone**
$C_n \subseteq (\mathbb R^4)^n$ is the set of configurations $p$ such that for
every proper orthochronous Lorentz transformation $\Lambda$ and every
nondecreasing $h \in \mathbb R^n$ ($h_0 \le h_1 \le \dots \le h_{n-1}$),

$$
\sum_{i=0}^{n-1} h_i\ t\big(P \Lambda P\, p_i\big) \ \ge\ 0 .
$$

**Data.** Fix a Wilson family and let $S$ be a Euclidean correlation table
for its tokens, with common label space $\mathbb F$. Let $W$ be boundary
distributions over $S$: for every $n$, a complex-multilinear map
$v \mapsto W_n(v)$ from $\mathbb F^n$ to tempered distributions on
$(\mathbb R^4)^n$. The Fourier
transform of a tempered distribution $u$ on $(\mathbb R^4)^n$ is
$\widehat u(f) = u(\widehat f)$, with
$\widehat f(p) = \int e^{-\mathrm i \langle q, p\rangle} f(q)\, dq$. For every
$n$ let $\chi_n$ be a cutoff for $n$ points: a real function on
$(\mathbb R^4)^n$ of temperate growth, equal to $1$ at every point at distance
less than $1$ from $C_n$, whose support (the closure of the set where it is
not zero) lies in the set of points at distance less than $3$ from $C_n$. Let $Z$ be a Laplace family for $W$ and these
cutoffs: for every $n$ and every complex configuration
$\zeta \in (\mathbb C^4)^n$, a Schwartz function $\ell_n(\zeta)$ on
$(\mathbb R^4)^n$, equal to
$q \mapsto e^{\mathrm i\langle q, \operatorname{Re}\zeta\rangle} e^{-\langle \operatorname{Im}\zeta, q\rangle}\chi_n(q)$
whenever $\operatorname{Im}\zeta$ has consecutive differences in the open
forward cone $\{x \in \mathbb R^4 : \|\vec x\| < t(x)\}$. Its continued function is
$\widetilde Z(v; \zeta) = (2\pi)^{-4n}\, \widehat{W_n(v)}\big(\ell_n(\zeta)\big)$
for $v \in \mathbb F^n$.

The cutoff $\chi_n$ is **attenuable** when for every $y \in \overline\Gamma_n$
the function $q \mapsto e^{-\langle y, q\rangle}\chi_n(q)$ has temperate
growth, and for every Schwartz function $f$ on $(\mathbb R^4)^n$ the map

$$
y \longmapsto \big( q \mapsto e^{-\langle y, q\rangle}\chi_n(q)\, f(q) \big)
$$

from $\overline\Gamma_n$ to the Schwartz space of $(\mathbb R^4)^n$ is
continuous.

**Exchange heights.** The pair $(W, Z)$ has **exchange heights for every
adjacent pair** when the following three conditions hold.

1. *Attenuable cutoffs.* For every $n$, the cutoff $\chi_n$ is attenuable.
2. *Spectral support.* For every $n$ and every $v \in \mathbb F^n$, the
   support of $\widehat{W_n(v)}$ is contained in $C_n$.
3. *Tied heights for each pair.* For every $n$ and every slot
   $k \in \{0, \dots, n-1\}$ there is a sequence
   $(h^{(m)})_{m \in \mathbb N}$ of heights $h^{(m)} \in \mathbb R^{n+1}$ such
   that $(0, h^{(m)}) \to 0$ in $(\mathbb R^4)^{n+1}$ as $m \to \infty$ and,
   for every $m$, $Z$ has exchange data at the heights $h^{(m)}$ for the slot
   $k$, in the sense of
   [admissible base points for the current jump](../stress-current/jump-admissibility.md): for
   every $v \in \mathbb F^{n+1}$ there are exchange data of $Z$ for the pair
   of slots $(k, k+1)$ at $v$ and $h^{(m)}$ for which the two orders agree.

In condition 3 one sequence serves all labels $v$; the sequence depends only on
$n$ and $k$. The conditions add no data.

## Depends on

- [Admissible base points for the current jump](../stress-current/jump-admissibility.md)

## Sources

- [YM/EveryPhase ledger: Decree](../../../../sources/every-phase.md#decree)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
