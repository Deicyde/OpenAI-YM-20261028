# Insertion into a slot

Let $A$ be a set and $n \in \mathbb N$. For a slot $j \in \{0, 1, \dots, n\}$,
an $n$-tuple $x = (x_0, \dots, x_{n-1}) \in A^n$ and an entry $a \in A$, the
**insertion of $a$ into slot $j$ of $x$** is the $(n+1)$-tuple

$$
\operatorname{ins}_j(x; a) = (x_0, \dots, x_{j-1},\ a,\ x_j, \dots, x_{n-1}) \in A^{n+1},
$$

whose entry with index $m \in \{0, \dots, n\}$ is $x_m$ for $m < j$, $a$ for
$m = j$, and $x_{m-1}$ for $m > j$. Thus $a$ occupies slot $j$ and the entries
of $x$ fill the other $n$ slots in their original order.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Slots](../../../sources/every-phase.md#slots)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
