# Separated configurations

For a natural number $n$, let $(\mathbb R^4)^n$ be the space of configurations
$x = (x_0, \dots, x_{n-1})$ of $n$ points of spacetime, with the topology of
its Euclidean norm. The set of **separated configurations** of $n$ points is

$$
\mathrm{Sep}_n = \big\{ x \in (\mathbb R^4)^n :
x_i = x_j \text{ only if } i = j, \text{ for all } i, j \in \{0, \dots, n-1\} \big\},
$$

the configurations whose points are pairwise distinct, that is, for which the
map $i \mapsto x_i$ from $\{0, 1, \dots, n-1\}$ to $\mathbb R^4$ is injective.
In other words, $\mathrm{Sep}_n$ is the complement in $(\mathbb R^4)^n$ of the
collision diagonals $\{x : x_i = x_j\}$ with $i \neq j$. Pairwise
distinctness is the only requirement: no lower bound on the distances between
the points is imposed. The definition presents $\mathrm{Sep}_n$ as an open
subset of $(\mathbb R^4)^n$: it is data, the set together with the fact that
this set is open.

## Depends on

- [Configurations of n points](point-configurations.md)

## Sources

- [PublicWilson.lean ledger: separated configurations](../../sources/public-wilson.md#separated-configurations)
- [Upstream description: all-orders separated OPE](../../sources/upstream-readme.md#all-orders-separated-ope)
