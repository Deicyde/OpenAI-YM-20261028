# Complex times and spatial positions

For a natural number $n$, zero included, the **complex times** of $n$ points
are the $n$-tuples $z = (z_0, z_1, \dots, z_{n-1})$ of complex numbers,
indexed by $k \in \{0, 1, \dots, n-1\}$; they form $\mathbb C^n$. The
**spatial positions** of $n$ points are the $n$-tuples
$\xi = (\xi_0, \xi_1, \dots, \xi_{n-1})$ of points $\xi_k$ of space
$\mathbb R^3$, indexed in the same way; they form $(\mathbb R^3)^n$. The
source describes them as the complex time coordinates and the spatial
coordinates of an analytically continued correlation.

Both are plain tuples, with addition and scalar multiplication taken
coordinatewise and with the product topology. Neither carries the Euclidean
norm of the whole tuple: the norm of $z \in \mathbb C^n$ is
$\max_k |z_k|$, and the norm of $\xi \in (\mathbb R^3)^n$ is
$\max_k \lVert \xi_k \rVert$, where $\lVert \xi_k \rVert$ is the Euclidean
norm of $\mathbb R^3$; both norms are $0$ when $n = 0$. Both definitions
introduce spaces and impose no condition.

## Depends on

- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: continuation variables](../../sources/challenge-spec.md#continuation-variables)
