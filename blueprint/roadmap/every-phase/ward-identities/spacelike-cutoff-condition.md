# Spacelike condition on cutoff and profile

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$x \in \mathbb R^4$, $t(x) = x_3$ is its time and
$\vec x = (x_0, x_1, x_2) \in \mathbb R^3$ its spatial part. The support
$\operatorname{supp} h$ of a function $h$ is the closure of the set where $h$
is not zero, and $\|\cdot\|$ is the Euclidean norm of $\mathbb R^3$. For a
Schwartz function $g$ on $\mathbb R^3$ and a spatial axis
$i \in \{0, 1, 2\}$, $\partial_i g$ is the derivative of $g$ in the direction
of the $i$-th standard basis vector of $\mathbb R^3$.

Let $g \in \mathcal S(\mathbb R^3)$ be a complex-valued Schwartz function of
space (the spatial cutoff), $f \in \mathcal S(\mathbb R)$ a complex-valued
Schwartz function of time (the time profile) and $x \in \mathbb R^4$ a point.
The cutoff $g$ and the profile $f$ satisfy the **spacelike condition at $x$**
when the following two conditions hold.

1. *Equal to one near the point.* There is a neighbourhood of $\vec x$ in
   $\mathbb R^3$ on which $g$ is constantly $1$.
2. *Spacelike to the point on the derivative supports at the profile's
   times.* For every $\tau \in \operatorname{supp} f$, every spatial axis
   $i \in \{0, 1, 2\}$ and every $r \in \operatorname{supp} \partial_i g$,

    $$
    |\tau - t(x)| < \|r - \vec x\| .
    $$

The second condition says that every point of spacetime with spatial part $r$
in the support of a first derivative of $g$ and time $\tau$ in the support of
$f$ is spacelike to $x$. No support, reality or integral condition on $g$ or
$f$ is part of the definition.

## Depends on

- [Admissible base points for the current jump](../stress-current/jump-admissibility.md)

## Sources

- [YM/EveryPhase ledger: Decree](../../../sources/every-phase.md#decree)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
