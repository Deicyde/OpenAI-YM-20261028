# Clusters and clear spectators

The points below are points of spacetime $\mathbb R^4$, and the distance
between two points $q, q' \in \mathbb R^4$ is the Euclidean distance

$$
\|q - q'\| = \Big( \sum_{\mu=0}^{3} \big(q_\mu - q'_\mu\big)^2 \Big)^{1/2}.
$$

A family of points indexed by a set $I$ is a map $i \mapsto x_i$ from $I$ to
$\mathbb R^4$, written $x = (x_i)_{i \in I}$. The two notions defined here are
conditions on the data they name, which are real numbers, a point and a family
of points; they involve no other structure.

**Clusters.** Let $I$ be a set, let $r$, $M$ and $\eta$ be real numbers, let
$x = (x_i)_{i \in I}$ be a family of points of $\mathbb R^4$, and let
$o \in \mathbb R^4$ be a point, called the centre. The family $x$ is an
**$(r, M, \eta)$-cluster around $o$** when both of the following hold:

1. $\|x_i - o\| \le M r$ for every $i \in I$;
2. $\eta r \le \|x_i - x_{i'}\|$ for all $i, i' \in I$ with $i \ne i'$.

**Clear spectators.** Let $J$ be a set, let $o \in \mathbb R^4$ be a point,
let $y = (y_m)_{m \in J}$ be a family of points of $\mathbb R^4$, and let $c$
be a real number. The family $y$ is **$c$-clear of $o$** when both of the
following hold:

1. $c \le \|o - y_m\|$ for every $m \in J$;
2. $c \le \|y_m - y_{m'}\|$ for all $m, m' \in J$ with $m \ne m'$.

The index sets $I$ and $J$ are arbitrary: they need not be finite, and they
may be empty. No sign condition is placed on $r$, $M$, $\eta$ or $c$. The
centre $o$ is an arbitrary point of $\mathbb R^4$ and need not be one of the
points $x_i$. In each second condition, $i \ne i'$ and $m \ne m'$ mean that
the two indices are different. The clearance condition involves only the
centre $o$, the points $y_m$ and the number $c$, and no cluster.

## Depends on

- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: clusters and spectators](../../sources/challenge-spec.md#clusters-and-spectators)
