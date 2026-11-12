# Wick profiles

For a mode $\mu$, write $K_\mu(r, p)$ for its kernel at a real number $r$ and a
point $p \in \mathbb R^3$.

A **track** $\tau$ consists of a natural number $n$, zero included, and a
family $(\mu_0, \dots, \mu_{n-1})$ of $n$ modes indexed by
$0, 1, \dots, n - 1$. Both are data, and no condition is imposed on them: the
modes of a track may repeat, and for $n = 0$ the family is empty.

Let $\mathbf t = \bigl((c_1, \tau_1), \dots, (c_J, \tau_J)\bigr)$ be a finite
list, with $J \ge 0$ entries, of pairs of a complex number $c_j$ and a track
$\tau_j$ whose $n_j$ modes are $\mu_{j,0}, \dots, \mu_{j,n_j-1}$; entries of
the list may repeat. The **Wick profile** of $\mathbf t$ is the function
$\mathrm{Wick}_{\mathbf t} : \mathbb R \to \mathbb C$ defined, for every real
number $r$, by

$$
\mathrm{Wick}_{\mathbf t}(r)
= \sum_{j=1}^{J} c_j \prod_{i=0}^{n_j-1} \int_{\mathbb R^3} K_{\mu_{j,i}}(r, p) \, dp .
$$

Each integral is taken with respect to Lebesgue measure on $\mathbb R^3$, with
no normalizing factor such as $(2\pi)^{-3}$. It is the Bochner integral of a
real-valued function, which by convention is $0$ when
$p \mapsto K_{\mu_{j,i}}(r, p)$ is not integrable. Each product is a real
number, and it is multiplied by the complex coefficient $c_j$. The product over
a track with no modes is the empty product $1$, and the sum over the empty list
is the empty sum $0$. This is a definition, not a condition.

## Depends on

- [Mass-shell modes and their kernels](mass-shell-modes.md)
- [Spacetime and space](../spacetime/spacetime-coordinates.md)

## Sources

- [ChallengeSpec.lean ledger: Wick profiles](../../sources/challenge-spec.md#wick-profiles)
- [Upstream description: non-freeness test](../../sources/upstream-readme.md#non-freeness-test)
