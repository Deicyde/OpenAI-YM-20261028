# Schwartz test functions

A Schwartz test function on spacetime $\mathbb R^4$ is a function
$f : \mathbb R^4 \to \mathbb C$ that is smooth, that is, continuously
differentiable to every order as a map between real vector spaces, and that
satisfies the following decay condition: for all natural numbers $k$ and $j$,
including $0$, there is a real number $C$ such that

$$
\|x\|^k \, \big\| D^j f(x) \big\| \le C
\qquad \text{for every } x \in \mathbb R^4 .
$$

Here $\|x\|$ is the Euclidean norm of $\mathbb R^4$, $D^j f(x)$ is the $j$-th
Fréchet derivative of $f$ at $x$, a real $j$-linear map from $(\mathbb R^4)^j$
to $\mathbb C$, and $\|D^j f(x)\|$ is its operator norm, taken with the
Euclidean norm on each of its $j$ arguments and the absolute value on
$\mathbb C$. The function is the data; smoothness and the decay condition
are required of it. Its values are complex numbers.

The Schwartz test functions form the Schwartz space $\mathcal S(\mathbb R^4)$,
a complex vector space under pointwise addition and multiplication by complex
scalars. It carries the topology defined by the seminorms

$$
p_{k,j}(f) = \sup_{x \in \mathbb R^4} \|x\|^k \, \big\| D^j f(x) \big\|,
\qquad k, j \in \{0, 1, 2, \dots\}.
$$

## Depends on

- [Spacetime and space](spacetime-coordinates.md)

## Sources

- [PublicTheory.lean ledger: Schwartz test functions](../../sources/public-theory.md#schwartz-test-functions)
