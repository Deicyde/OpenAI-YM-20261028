# Imaginary times and spatial positions of a configuration

For a natural number $n$, zero included, let $(\mathbb R^4)^n$ be the space of
Euclidean configurations $x = (x_0, \dots, x_{n-1})$ of $n$ points
$x_k \in \mathbb R^4$. For a point $y = (y_0, y_1, y_2, y_3)$ of
$\mathbb R^4$, its time is its last coordinate, $t(y) = y_3$, and its spatial
part is the point $\vec y = (y_0, y_1, y_2)$ of $\mathbb R^3$ formed by its
first three coordinates. The imaginary unit is written $\mathrm i$.

For a configuration $x \in (\mathbb R^4)^n$, the **imaginary times** of $x$
are the $n$-tuple of complex times

$$
\mathrm i\,t(x) = \big(\mathrm i\,t(x_0), \mathrm i\,t(x_1), \dots, \mathrm i\,t(x_{n-1})\big) \in \mathbb C^n ,
$$

whose entry $\mathrm i\,t(x_k)$ is the purely imaginary number with imaginary
part the time $t(x_k)$ of the point $x_k$, and the **spatial positions** of
$x$ are the $n$-tuple

$$
\vec x = (\vec x_0, \vec x_1, \dots, \vec x_{n-1}) \in (\mathbb R^3)^n
$$

of the spatial parts of its points. These are two definitions with no
conditions: the configuration is arbitrary, and its points may coincide.

## Depends on

- [Configurations of n points](../spacetime/point-configurations.md)
- [Complex times and spatial positions](continuation-variables.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: imaginary times](../../sources/challenge-spec.md#imaginary-times)
