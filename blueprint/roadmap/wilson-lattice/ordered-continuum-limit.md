# Ordered continuum limit

Let $C$ be a Wilson family for a matrix gauge group, with side lengths $L_p$
(positive integers, $p \in \mathbb N = \{0, 1, 2, \dots\}$) and a set
$\mathcal T$ of tokens. For $n \in \mathbb N$, a separated test function
$t \in \mathcal D(\mathrm{Sep}_n)$ on configurations of $n$ points is an
infinitely differentiable function $t : (\mathbb R^4)^n \to \mathbb C$ whose
closed support, the closure of $\{x : t(x) \neq 0\}$, is compact and
contained in the set $\mathrm{Sep}_n$ of configurations of $n$ pairwise
distinct points. Such a $t$ is suitable for a volume index $p$ when its closed
support lies in the open box of configurations $x = (x_0, \dots, x_{n-1})$
with $-L_p/2 < x_i^a < L_p/2$ for every $i \in \{0, \dots, n-1\}$ and every
$a \in \{0, 1, 2, 3\}$, where $x_i^a$ is the coordinate $a$ of the point
$x_i$. For $N, p \in \mathbb N$ and $v \in \mathcal T^n$,
$\widetilde{\mathcal M}_{N,p}(v; t)$ denotes the smeared moment of $v$ and
$t$.

Besides the family, the data of the definition are a sequence
$\omega : \mathbb N \to \mathbb N$ of volume indices and, for every
$n \in \mathbb N$ and every
$v \in \mathcal T^n$, a function $G_v : (\mathbb R^4)^n \to \mathbb C$. The
definition places no condition on $\omega$ or on the functions $G_v$. The family
$C$ **converges along $\omega$ to the functions $G_v$** when, for every
$n \in \mathbb N$, every $v \in \mathcal T^n$ and every
$t \in \mathcal D(\mathrm{Sep}_n)$, both of the following hold:

1. there is a $k_0 \in \mathbb N$ such that $t$ is suitable for $\omega(k)$ for
    every $k \ge k_0$;
2. there are complex numbers $R_p$, one for each $p \in \mathbb N$, such that
    - for every $p \in \mathbb N$ for which $t$ is suitable,
      $\widetilde{\mathcal M}_{N,p}(v; t) \to R_p$ as $N \to \infty$, and
    - $R_{\omega(k)} \to \int_{(\mathbb R^4)^n} t(x)\, G_v(x)\, dx$ as
      $k \to \infty$.

The numbers $R_p$ may depend on $n$, $v$ and $t$. At each volume index $p$
for which $t$ is suitable, the limit is taken first along all
$N \in \mathbb N$; only then does the volume index run along $\omega$. The integral
is taken against Lebesgue measure on $(\mathbb R^4)^n = \mathbb R^{4n}$; it is
the Bochner integral, which by convention is $0$ when
$x \mapsto t(x)\, G_v(x)$ is not integrable.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](wilson-family.md)
- [Configurations of n points](../spacetime/point-configurations.md)
- [Test functions on separated configurations](../spacetime/separated-test-functions.md)
- [Tests suited to a volume](suitable-tests.md)
- [Smeared lattice moments](smeared-moments.md)

## Sources

- [Declaration ledger of the Wilson lattice source: ordered continuum limit](../../sources/public-wilson.md#ordered-continuum-limit)
- [Upstream description of the public challenge: Wilson origin](../../sources/upstream-readme.md#wilson-origin)
