# Complex shift of a configuration

For a natural number $n$, zero included, let $(\mathbb R^4)^n$ be the space of
Euclidean configurations $x = (x_0, \dots, x_{n-1})$ of $n$ points
$x_k \in \mathbb R^4$, and let $\mathbb C^n$ be the space of $n$-tuples of
complex times. For a point $y \in \mathbb R^4$, $t(y)$ denotes its time, the
last of its four coordinates (coordinate $3$). The imaginary unit is written
$\mathrm i$.

For a real number $r$, an $n$-tuple $h = (h_0, \dots, h_{n-1}) \in \mathbb R^n$
of real heights and a configuration $x \in (\mathbb R^4)^n$, the
**complex shift** of $x$ by $r$ and $h$ is the $n$-tuple of complex times
$z_{r,h}(x) = (z_0, \dots, z_{n-1}) \in \mathbb C^n$ given by

$$
z_k = t(x_k) + \mathrm i\, r\, h_k, \qquad k = 0, 1, \dots, n-1 .
$$

The real part of $z_k$ is the time of the point $x_k$ and its imaginary part
is the product $r h_k$; the spatial coordinates of the points do not enter.
The source describes the complex shift as continuing a real configuration into
ordered imaginary-time directions, but the definition places no condition on
its arguments: $n$, $r$, $h$ and $x$ are arbitrary, $r$ may be negative or
zero, and the heights need not be ordered or distinct.

## Depends on

- [Configurations of n points](../spacetime/point-configurations.md)
- [Complex times and spatial positions](continuation-variables.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: complex shift](../../sources/challenge-spec.md#complex-shift)
