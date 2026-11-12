# Test functions on separated configurations

For a natural number $n$, let $(\mathbb R^4)^n$ be the space of configurations
of $n$ points of spacetime, which the coordinates $x_i^a$ identify with the
Euclidean space $\mathbb R^{4n}$, and let $\mathrm{Sep}_n \subseteq (\mathbb R^4)^n$
be the open set of separated configurations, those whose points are pairwise
distinct. A **separated test function** on configurations of $n$ points is a
function $t : (\mathbb R^4)^n \to \mathbb C$, defined at every configuration,
those with coincident points included, that satisfies three conditions:

1. $t$ is infinitely differentiable ($C^\infty$) on
   $(\mathbb R^4)^n = \mathbb R^{4n}$ in the real sense, $\mathbb C$ being
   regarded as the real vector space $\mathbb R^2$;
2. $t$ has compact support: its closed support $\operatorname{supp} t$, the
   closure in $(\mathbb R^4)^n$ of the set $\{x : t(x) \neq 0\}$, is compact;
3. $\operatorname{supp} t \subseteq \mathrm{Sep}_n$.

The function $t$ is the data and the three properties are conditions on it.
Write $\mathcal D(\mathrm{Sep}_n)$ for the set of separated test functions on
configurations of $n$ points.

## Depends on

- [Separated configurations](separated-configurations.md)

## Sources

- [PublicWilson.lean ledger: separated test functions](../../sources/public-wilson.md#separated-test-functions)
