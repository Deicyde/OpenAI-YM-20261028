# Hilbert space and bounded operators

A **Hilbert space** consists of a set $H$, whose elements are called vectors,
two structures on $H$, and one condition.

The first structure is a normed abelian group structure: an addition making $H$
an abelian group, and a function $\lVert\cdot\rVert : H \to \mathbb R$, the
norm, for which $d(\psi,\chi) = \lVert \chi - \psi \rVert$ is a metric on $H$.

The second is a complex inner product space structure compatible with this
norm: a scalar multiplication by complex numbers making $H$ a vector space over
$\mathbb C$, with $\lVert c\psi \rVert \le |c|\,\lVert \psi \rVert$, and an
inner product $\langle \cdot,\cdot \rangle : H \times H \to \mathbb C$ such
that for all $\psi, \chi, \xi \in H$ and $c \in \mathbb C$

$$
\begin{gathered}
\lVert \psi \rVert^2 = \operatorname{Re} \langle \psi, \psi \rangle, \qquad
\langle \psi, \chi \rangle = \overline{\langle \chi, \psi \rangle}, \\
\langle \psi + \chi, \xi \rangle = \langle \psi, \xi \rangle + \langle \chi, \xi \rangle, \qquad
\langle c\psi, \chi \rangle = \bar c \, \langle \psi, \chi \rangle .
\end{gathered}
$$

So the inner product is conjugate-linear in its first argument and linear in its
second; inner products in this book follow this convention.

The condition is completeness: every Cauchy sequence in $H$ for the metric $d$
converges in $H$.

The set and the two structures are data; completeness is a condition.
Topological notions on $H$, such as continuity, density and convergence, refer
to the metric $d$ of the norm. Separability of $H$ is not assumed.

A **bounded operator** on a Hilbert space $H$ is a continuous complex-linear map
$T : H \to H$.

## Depends on

This node has no prerequisites.

## Sources

- [PublicTheory.lean ledger: Hilbert space](../../sources/public-theory.md#hilbert-space)
