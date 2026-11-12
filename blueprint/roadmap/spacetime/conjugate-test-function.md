# Complex conjugate of a test function

Let $\mathcal S(\mathbb R^4)$ be the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$ on spacetime, with the topology of the Schwartz
seminorms. For $f \in \mathcal S(\mathbb R^4)$, the **complex conjugate** of
$f$ is the function $\bar f : \mathbb R^4 \to \mathbb C$ obtained by
conjugating each value of $f$:

$$
\bar f(x) = \overline{f(x)} \qquad \text{for every } x \in \mathbb R^4 ,
$$

where $\overline{z}$ denotes the complex conjugate of $z \in \mathbb C$. The
**conjugation of test functions** is the map

$$
\mathcal S(\mathbb R^4) \to \mathcal S(\mathbb R^4), \qquad f \mapsto \bar f ,
$$

defined as a continuous real-linear map. Here $\mathcal S(\mathbb R^4)$ is
regarded as a real vector space, with pointwise addition and multiplication by
real numbers, so real-linearity means $\overline{f + g} = \bar f + \bar g$ and
$\overline{c f} = c\,\bar f$ for all $f, g \in \mathcal S(\mathbb R^4)$ and
$c \in \mathbb R$; continuity refers to the topology of the Schwartz seminorms
on both sides. The definition is data and imposes no condition: it gives the
map $f \mapsto \bar f$ together with the facts that each $\bar f$ is again a
Schwartz test function and that the map is real-linear and continuous.

## Depends on

- [Schwartz test functions](schwartz-test-functions.md)

## Sources

- [PublicTheory.lean ledger: conjugate test function](../../sources/public-theory.md#conjugate-test-function)
