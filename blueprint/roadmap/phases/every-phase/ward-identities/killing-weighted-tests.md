# Test functions weighted by a Killing field

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$x \in \mathbb R^4$, $t(x) = x_3$ is its time and
$\vec x = (x_0, x_1, x_2) \in \mathbb R^3$ its spatial part. For a real normed
space $E$, $\mathcal S(E)$ is the complex vector space of Schwartz functions
$E \to \mathbb C$, with its usual topology.

Let $K = (k, V)$ be a [Killing field](../stress-current/killing-field.md), with real value
$K(x) = k + V x$ at $x \in \mathbb R^4$, and write

$$
K^b(x) = k_b + \sum_{c=0}^{3} V_{bc}\, x_c \in \mathbb R
$$

for its component along the axis $b \in \{0, 1, 2, 3\}$.

**Weighting through a linear map.** Let $E$ be a real normed space and
$\iota : E \to \mathbb R^4$ a continuous real-linear map. The **weighting of
Schwartz functions on $E$ by the component $b$ of $K$ through $\iota$** is the
continuous complex-linear map $\mathcal S(E) \to \mathcal S(E)$ that
multiplies by the real function $e \mapsto K^b(\iota(e))$:

$$
\big(K^b_\iota\, u\big)(e) = K^b\big(\iota(e)\big)\, u(e) \qquad (u \in \mathcal S(E),\ e \in E).
$$

The multiplier is an affine function of $e$, so it has temperate growth and
the product is again a Schwartz function.

**Killing-weighted tests on spacetime.** With $E = \mathbb R^4$ and $\iota$ the
identity, the **Killing-weighted test** of $h \in \mathcal S(\mathbb R^4)$
along $b$ is

$$
\big(K^b h\big)(x) = K^b(x)\, h(x) \qquad (x \in \mathbb R^4).
$$

**Product tests of space and time.** For a Schwartz function
$g \in \mathcal S(\mathbb R^3)$ of space and a Schwartz function
$f \in \mathcal S(\mathbb R)$ of time, $g \otimes f \in \mathcal S(\mathbb R^4)$
is the Schwartz function

$$
(g \otimes f)(x) = g(\vec x)\, f(t(x)) \qquad (x \in \mathbb R^4),
$$

the product $(r, \tau) \mapsto g(r)\, f(\tau)$ on $\mathbb R^3 \times \mathbb R$
composed with the linear isomorphism $x \mapsto (\vec x, t(x))$ of
$\mathbb R^4$ onto $\mathbb R^3 \times \mathbb R$.

## Depends on

- [Killing fields](../stress-current/killing-field.md)

## Sources

- [YM/EveryPhase ledger: Frost](../../../../sources/every-phase.md#frost)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
