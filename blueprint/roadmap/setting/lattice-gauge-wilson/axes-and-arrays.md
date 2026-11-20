# Axes and four-component arrays

The **axes** are the four natural numbers $0, 1, 2, 3$, the elements of the
four-element set $\{0, 1, 2, 3\}$.

For every set $R$, a **four-component array** over $R$ is a map
$a : \{0, 1, 2, 3\} \to R$, one element of $R$ for each axis. It is written

$$
a = (a_0, a_1, a_2, a_3), \qquad a_i = a(i) \in R ,
$$

and $a_i$ is its component on axis $i$. The arrays over $R$ form the set
$R^4 = R^{\{0, 1, 2, 3\}}$ of all such maps. The definition imposes no condition
on the components and adds no structure to $R^4$; when $R$ is an additive
group, arrays are added componentwise,
$(a + a')_i = a_i + a'_i$, by the pointwise structure on maps.

As in the rest of the book, axes $0, 1, 2$ are read as the spatial axes and
axis $3$ as the time axis. This is a convention of the book, not part of either
definition.

## Depends on

This node has no prerequisites.

## Sources

- [YM/Space ledger: Index](../../../sources/lattice-gauge-wilson.md#index)
- [Armstrong's informalization: unit I.1](../../../sources/armstrong.md#unit-i1-lattice-symmetries-gauge-groups-and-the-wilson-measure)
