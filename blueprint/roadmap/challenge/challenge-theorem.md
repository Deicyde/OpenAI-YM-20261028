# The main theorem

The [joint existence statement](joint-existence.md) holds. Written out, with
$\mathbb N = \{0, 1, 2, \dots\}$: for every matrix gauge group that is simple,
there is a Wilson family $C$ for this gauge group such that

1. $C$ is regular, and
2. for every strictly increasing sequence $p : \mathbb N \to \mathbb N$ there
   are a strictly increasing sequence $q : \mathbb N \to \mathbb N$ and a
   continuum hierarchy $T$ over $C$ such that $T$ has the four properties
   along the volume order $p \circ q$.

Here a sequence $p : \mathbb N \to \mathbb N$ is strictly increasing when
$p(k) < p(l)$ for all $k, l \in \mathbb N$ with $k < l$, and $p \circ q$ is
the sequence $k \mapsto p(q(k))$.

## Depends on

- [Joint existence statement](joint-existence.md)

## Sources

- [Solution.lean ledger: the main theorem](../../sources/solution.md#the-main-theorem)
