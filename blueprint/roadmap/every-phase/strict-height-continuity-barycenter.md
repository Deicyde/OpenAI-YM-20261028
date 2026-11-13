# Continuations at strict heights: continuity and barycenter in the phase

Let $\mathcal F$ be a record for a Wilson family, an extraction and a limit
table $S$, with common label space $\mathbb F$. Of its data the statement uses
the phase space $X$, a compact metric space with its Borel σ-algebra, whose
points $s$ are called characters, the phase measure $\nu$ on $X$, a
probability measure, and the continuation of $S$ that the record carries:
functions $\mathsf F^{\rm mix}(z, \xi; a_1, \dots, a_n) \in \mathbb C$ of $n$
complex times $z \in \mathbb C^n$, $n$ spatial positions
$\xi \in (\mathbb R^3)^n$ and $n$ labels $a_j \in \mathbb F$, for every $n$,
multilinear in the labels. Let $L$ be a family of reconstructions over the
phases for $\mathcal F$, and write $\mathsf F_s$ for the continuation
functions of its member at the character $s \in X$.

A point of spacetime is $x = (x_0, x_1, x_2, x_3) \in \mathbb R^4$, with time
$t(x) = x_3$ and spatial part $\vec x = (x_0, x_1, x_2)$. For
$n \in \mathbb N$, a configuration $x = (x_1, \dots, x_n) \in (\mathbb R^4)^n$
and real heights $y = (y_1, \dots, y_n)$, put

$$
t(x) + \mathrm i y = \big(t(x_1) + \mathrm i y_1, \dots, t(x_n) + \mathrm i y_n\big) \in \mathbb C^n,
\qquad \vec x = (\vec x_1, \dots, \vec x_n) \in (\mathbb R^3)^n .
$$

**Lemma.** For every record $\mathcal F$, every family of reconstructions
$L$ for $\mathcal F$, every $n \in \mathbb N$, every configuration
$x \in (\mathbb R^4)^n$, all labels $a_1, \dots, a_n \in \mathbb F$ and all
strictly increasing heights $y_1 < y_2 < \dots < y_n$:

1. the function
   $s \mapsto \mathsf F_s\big(t(x) + \mathrm i y,\ \vec x;\ a_1, \dots, a_n\big)$
   from $X$ to $\mathbb C$ is continuous; and
2. its integral over $X$ is the same evaluation of the continuation of $S$:

    $$
    \int_X \mathsf F_s\big(t(x) + \mathrm i y,\ \vec x;\ a_1, \dots, a_n\big)\, d\nu(s)
    = \mathsf F^{\rm mix}\big(t(x) + \mathrm i y,\ \vec x;\ a_1, \dots, a_n\big).
    $$

The configuration $x$ is arbitrary: its points need not be distinct and its
times need not be ordered; only the heights are required to increase strictly,
and the case $n = 0$ is included. The statement is pointwise, for every such
$x$, not only after testing against test functions. The integral is the
Bochner integral of a complex-valued function on $X$ against $\nu$, which by
convention is $0$ when the integrand is not integrable.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)

## Sources

- [YM/EveryPhase ledger: Pages](../../sources/every-phase.md#pages)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
