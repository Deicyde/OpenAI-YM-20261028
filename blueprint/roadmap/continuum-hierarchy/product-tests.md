# Product test functions

For a natural number $n$, zero included, let $(\mathbb R^4)^n$ be the space of
Euclidean configurations $x = (x_0, \dots, x_{n-1})$ of $n$ points
$x_k \in \mathbb R^4$, and let $\mathcal S(\mathbb R^4)$ be the space of
Schwartz test functions $f : \mathbb R^4 \to \mathbb C$.

For Schwartz test functions $f_0, \dots, f_{n-1} \in \mathcal S(\mathbb R^4)$,
the **product test** $f_0 \otimes \dots \otimes f_{n-1}$ is the function from
$(\mathbb R^4)^n$ to $\mathbb C$ given by

$$
(f_0 \otimes \dots \otimes f_{n-1})(x)
= \prod_{k=0}^{n-1} f_k(x_k)
= f_0(x_0)\, f_1(x_1) \cdots f_{n-1}(x_{n-1}),
$$

a product of complex numbers, equal to $1$ when $n = 0$: the test function
with index $k$ is evaluated at the point with the same index. The definition
places no condition on the test functions $f_k$, and it defines the product
test only as a complex-valued function on $(\mathbb R^4)^n$: it asserts
nothing further about it, such as smoothness, decay or membership in a space
of test functions on $(\mathbb R^4)^n$. The source describes it as the product
test used to smear an $n$-point correlation.

## Depends on

- [Schwartz test functions](../spacetime/schwartz-test-functions.md)
- [Configurations of n points](../spacetime/point-configurations.md)

## Sources

- [ChallengeSpec.lean ledger: product tests](../../sources/challenge-spec.md#product-tests)
