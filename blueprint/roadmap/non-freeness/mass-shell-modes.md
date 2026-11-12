# Mass-shell modes and their kernels

Space is $\mathbb R^3$, with the Euclidean norm
$\lVert p \rVert = \bigl(p_0^2 + p_1^2 + p_2^2\bigr)^{1/2}$ of a point
$p = (p_0, p_1, p_2)$ and the topology of that norm. The natural numbers are
$0, 1, 2, \dots$.

A **mode** $\mu = (m, k, \ell, P)$ consists of six components, four of them
data and two of them conditions on the data:

1. a real number $m \ge 0$, the mass (data);
2. a natural number $k$, the spatial order (data);
3. a natural number $\ell$, the time order (data);
4. a function $P : \mathbb R^3 \to \mathbb R$, the numerator (data);
5. $P$ is continuous (condition);
6. $P(\lambda p) = \lambda^k P(p)$ for every $p \in \mathbb R^3$ and every
   real number $\lambda > 0$ (condition).

The source describes modes as "elementary mass-shell kernels, including finite
differential orders". The mass may be $0$. Nothing is required of the
numerator beyond the two conditions; in particular, it need not be a
polynomial.

The **kernel** of a mode $\mu = (m, k, \ell, P)$ is the function
$K_\mu : \mathbb R \times \mathbb R^3 \to \mathbb R$ defined, for every real
number $r$ and every $p \in \mathbb R^3$, by

$$
K_\mu(r, p) = \frac{1}{2E} \, E^{\ell} \, P(p) \, e^{-rE},
\qquad
E = \sqrt{m^2 + \lVert p \rVert^2},
$$

where $E \ge 0$ is the nonnegative square root and $\frac{1}{2E}$ is read as
$0$ when $E = 0$, which happens exactly when $m = 0$ and $p = 0$. The kernel
is defined for every real $r$, zero and negative values included.

## Depends on

- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: mass-shell modes](../../sources/challenge-spec.md#mass-shell-modes)
