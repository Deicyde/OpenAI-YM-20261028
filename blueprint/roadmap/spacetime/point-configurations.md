# Configurations of n points

For a natural number $n$, zero included, a **configuration of $n$ points** is
an $n$-tuple

$$
x = (x_0, x_1, \dots, x_{n-1})
$$

of points $x_i$ of spacetime $\mathbb R^4$, indexed by
$i \in \{0, 1, \dots, n-1\}$. The configurations of $n$ points form the real
vector space $(\mathbb R^4)^n$, with addition and multiplication by real
numbers taken point by point. Write $x_i^a$ for coordinate
$a \in \{0, 1, 2, 3\}$ of the point $x_i$, coordinate $3$ being time.
Configurations carry the norm

$$
\|x\| = \Big(\sum_{i=0}^{n-1} \|x_i\|^2\Big)^{1/2}
= \Big(\sum_{i=0}^{n-1} \sum_{a=0}^{3} \big(x_i^a\big)^2\Big)^{1/2},
$$

where $\|x_i\|$ is the Euclidean norm of $\mathbb R^4$, so that through the
$4n$ coordinates $x_i^a$ the space $(\mathbb R^4)^n$ is the Euclidean space
$\mathbb R^{4n}$. Topological notions on configurations (open sets, closures,
compactness, continuity) and differentiability refer to this norm, and
integrals over configurations are taken with respect to Lebesgue measure on
$\mathbb R^{4n}$ in the coordinates $x_i^a$.

## Depends on

- [Spacetime and space](spacetime-coordinates.md)

## Sources

- [PublicWilson.lean ledger: point configurations](../../sources/public-wilson.md#point-configurations)
- [ChallengeSpec.lean ledger: euclidean configurations](../../sources/challenge-spec.md#euclidean-configurations)
