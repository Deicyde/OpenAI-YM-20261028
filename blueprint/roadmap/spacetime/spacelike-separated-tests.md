# Spacelike separated Schwartz test functions

Let $\mathcal S(\mathbb R^4)$ be the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime $\mathbb R^4$. For
$f \in \mathcal S(\mathbb R^4)$, the closed support $\operatorname{supp} f$ is
the closure in $\mathbb R^4$ of the set $\{x \in \mathbb R^4 : f(x) \neq 0\}$.
A vector $v = (v_0, v_1, v_2, v_3) \in \mathbb R^4$, whose last coordinate
$v_3$ is time, is spacelike when its Minkowski square is strictly negative:

$$
v_3^2 - \big(v_0^2 + v_1^2 + v_2^2\big) < 0 .
$$

Two Schwartz test functions $f, g \in \mathcal S(\mathbb R^4)$ are
**spacelike separated** when

$$
x - y \ \text{ is spacelike for every } x \in \operatorname{supp} f
\text{ and every } y \in \operatorname{supp} g ,
$$

where $x - y$ is the difference of the points $x$ and $y$ as vectors of
$\mathbb R^4$. This is a condition on the pair $(f, g)$, with $x$ taken from
the closed support of the first function and $y$ from the closed support of
the second; it involves no further data. No boundedness of the supports is
required.

## Depends on

- [Schwartz test functions](schwartz-test-functions.md)
- [Spacelike vectors](spacelike-vectors.md)

## Sources

- [PublicTheory.lean ledger: spacelike separated tests](../../sources/public-theory.md#spacelike-separated-tests)
