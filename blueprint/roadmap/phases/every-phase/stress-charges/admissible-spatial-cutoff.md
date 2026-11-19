# Admissible spatial cutoff

A point of spacetime is $x = (x_0, x_1, x_2, x_3) \in \mathbb R^4$; its time
is $t(x) = x_3$, the last coordinate, and its spatial part is
$\vec x = (x_0, x_1, x_2) \in \mathbb R^3$. For $y \in \mathbb R^3$ and
$\tau \in \mathbb R$, $(y, \tau)$ is the point of $\mathbb R^4$ with spatial
part $y$ and time $\tau$. A point $v \in \mathbb R^4$ is spacelike when
$t(v)^2 < \|\vec v\|^2$, that is, when $|t(v)| < \|\vec v\|$. The support
$\operatorname{supp} f$ of a function is the closure of the set where it is
not zero, and $B(y_0, d) = \{ y \in \mathbb R^3 : \|y - y_0\| < d \}$ is the
open ball of $\mathbb R^3$ with center $y_0$ and radius $d$.

Let $\mathcal O \subseteq \mathbb R^4$ be a set of spacetime points and
$f \in \mathcal S(\mathbb R)$ a complex-valued Schwartz function on the real
line. A Schwartz function $g \in \mathcal S(\mathbb R^3)$, with complex
values, is an **admissible spatial cutoff** for $\mathcal O$ and $f$ when the
following two conditions hold.

1. *Compact support.* $g$ has compact support.
2. *Equal to one on a ball with spacelike exterior.* There are a center
   $y_0 \in \mathbb R^3$ and a real radius $d > 0$ such that $g(y) = 1$ for
   every $y \in B(y_0, d)$, and such that for every
   $\tau \in \operatorname{supp} f$, every
   $y \in \mathbb R^3 \setminus B(y_0, d)$ and every $x \in \mathcal O$, the
   point $(y, \tau) - x$ is spacelike: $|\tau - t(x)| < \|y - \vec x\|$.

Here $\mathcal O$ is an arbitrary set of spacetime points and $f$ an arbitrary
Schwartz function. The cutoff $g$ may take complex values. The spacelike
condition concerns every point $y$ outside the ball, not only the points of
the support of $g$.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Charge](../../../../sources/every-phase.md#charge)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
