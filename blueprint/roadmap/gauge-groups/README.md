# Compact simple matrix gauge groups

The challenge makes a claim about every gauge group in one class, which the
[upstream description](../../sources/upstream-readme.md#the-public-challenge)
introduces with the words "for each closed matrix subgroup with nonabelian
simple real Lie algebra". This chapter defines that class: a matrix gauge
group, made of a group of unitary matrices and a real linear subspace of
matrices called its Lie algebra, and the condition that this Lie algebra be
simple. In the later chapters, the
link variables of the Wilson lattice are elements of the group of a fixed gauge
group, Wilson families and continuum hierarchies are built over that gauge
group, and [the challenge](../challenge/README.md) ranges over every gauge
group that is simple.

A gauge group is given concretely, as a group of matrices. It consists of a
natural number $n$, a subgroup $G$ of the unitary group $U(n+1)$, and a real
linear subspace $\mathfrak g$ of the space $M_{n+1}(\mathbb C)$ of complex
$(n+1)\times(n+1)$ matrices. The formal statement calls $U(n+1)$ the fixed
faithful unitary representation used to describe a gauge group, so the way $G$
sits inside $U(n+1)$ is part of the data. The matrix size is $n+1$, not $n$:
the case $n = 0$ is that of $1\times 1$ matrices.

Two conditions tie the data together. First, $G$ is closed in $U(n+1)$.
Second, $\mathfrak g$ is not arbitrary: a matrix $X$ lies in $\mathfrak g$
exactly when $\exp(tX)$ lies in $G$ for every real number $t$, so
$\mathfrak g$ consists of the matrices whose real one-parameter exponentials
stay in $G$. The part of the formal statement that introduces these groups is
headed "Compact simple matrix gauge groups" and calls each such group compact;
the definition states no compactness condition of its own, and its only
topological condition is that $G$ be closed in $U(n+1)$. Nor is $G$ required
to be connected.

Simplicity is a condition on $\mathfrak g$ alone, with the matrix commutator
$XY - YX$ as the bracket and real linear subspaces as the ideals. The formal
statement describes it as real simplicity of the Lie algebra, including the
nonabelian condition, and both clauses are part of the definition: some two
elements of $\mathfrak g$ do not commute, and every real linear subspace of
$\mathfrak g$ that contains the commutator of each element of $\mathfrak g$
with each of its own elements is $\{0\}$ or $\mathfrak g$. It says nothing
directly about $G$, such as whether it is connected or what its centre is.

## Matrix gauge groups

A matrix gauge group is the data $(n, G, \mathfrak g)$ subject to the
closedness and exponential conditions above. Its matrices have size $n+1$, and
the exponential condition fixes its Lie algebra in terms of $G$.

- [Matrix gauge group](gauge-group.md)

## Simplicity

The challenge's hypothesis on a gauge group is that it is simple: its Lie
algebra is nonabelian and has no real ideal other than $\{0\}$ and itself.

- [Simplicity of the gauge Lie algebra](simple-lie-algebra.md)
