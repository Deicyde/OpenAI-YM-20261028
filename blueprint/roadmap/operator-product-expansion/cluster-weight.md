# Weight of a cluster

Let $T$ be a continuum hierarchy over a Wilson family for a matrix gauge
group. For each grade $d \in \mathbb N$, where
$\mathbb N = \{0, 1, 2, \dots\}$, the hierarchy has the finite-dimensional
complex normed space $F_d$ of its fields of grade $d$, and a graded field of
$T$ is a pair $(d, u)$ of a grade $d \in \mathbb N$ and a vector $u \in F_d$.

Let $I$ be a finite set and let $a = (a_i)_{i \in I}$ be a family of graded
fields of $T$ indexed by $I$, with $a_i = (d_i, u_i)$ for each $i \in I$. The
**weight** of $a$ is the real number

$$
w(a) = \sum_{i \in I} d_i ,
$$

the sum over $I$ of the grades $d_i$, each taken as a real number. When $I$ is
empty the sum is empty and $w(a) = 0$. Only the grades enter: the weight does
not depend on any positions.

## Depends on

- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)

## Sources

- [ChallengeSpec.lean ledger: cluster weight](../../sources/challenge-spec.md#cluster-weight)
