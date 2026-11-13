# Minkowski stress labels and the stress field

Spacetime axes are numbered $0, 1, 2, 3$; axis $3$ is time and axes $0, 1, 2$
are spatial. For an axis $a$ put

$$
\eta_a = \begin{cases} 1 & a = 3, \\ -1 & a \in \{0, 1, 2\}, \end{cases}
\qquad
\zeta_a = \begin{cases} -\mathrm i & a = 3, \\ 1 & a \in \{0, 1, 2\}, \end{cases}.
$$

Fix a Wilson family and let $S$ be a Euclidean correlation table for its
tokens. For every degree
$d \in \mathbb N$ it has a quotient label space $F_d$, a finite-dimensional
complex vector space: the degree-$d$ labels modulo those whose correlations in
$S$ vanish. Its common label space $\mathbb F$ is the complex linear span
(the sum) of the images of the $F_d$ in the space of complex-valued
functions of exterior data (further labels placed at further points, all
points distinct), where a class is sent to its correlations in $S$ against
these data. For $\beta \in F_d$ we write $[\beta]_d \in \mathbb F$ for the
image of $\beta$; the map $\beta \mapsto [\beta]_d$ is complex linear. A **stress tensor**
of $S$ is a family $T = (T_{ab})$ of elements $T_{ab} \in F_4$, one for each
ordered pair of axes $(a, b)$; the definition asks for no symmetry,
conservation or reality.

The **Minkowski stress labels** of $T$ are

$$
M_{ab} = -\zeta_a \zeta_b\, T_{ab} \in F_4 \qquad (a, b \in \{0, 1, 2, 3\}),
$$

that is, $M_{33} = T_{33}$, $M_{3j} = \mathrm i\, T_{3j}$,
$M_{j3} = \mathrm i\, T_{j3}$ and $M_{jl} = -T_{jl}$ for spatial axes $j, l$.

Let $\mathfrak W$ be Wightman data over $S$. Among its components is a field system: a
Hilbert space $H$, a complex linear subspace $D \subseteq H$ (the domain), a
vacuum vector $\Omega \in D$ and, for every label $\ell \in \mathbb F$ and
every Schwartz test function $h \in \mathcal S(\mathbb R^4)$, a complex-linear
map $\varphi(\ell, h) : D \to D$ that depends complex-linearly on $\ell$ and on
$h$. The **stress field** of $T$ in $\mathfrak W$ is, for each pair of axes $(a, b)$, the
complex-linear map from $\mathcal S(\mathbb R^4)$ to the linear maps of $D$

$$
h \longmapsto T_{ab}(h) = \varphi\big([M_{ab}]_4,\ h\big).
$$

The **test derivative** along an axis $a$ sends $h \in \mathcal S(\mathbb R^4)$
to the Schwartz function

$$
\widetilde\partial_a h = -\,\partial_a h,
$$

where $\partial_a h$ is the derivative of $h$ in the direction of the $a$-th
standard basis vector of $\mathbb R^4$.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Tensor](../../../sources/every-phase.md#tensor)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
