# Wilson family

Let $(n, G, \mathfrak g)$ be a matrix gauge group, so that $G$ is a group of
unitary $(n+1)\times(n+1)$ complex matrices. Give $G$ the topology it inherits
from the complex $(n+1)\times(n+1)$ matrices with entrywise convergence, and
the Borel σ-algebra of that topology. Write $\mathbb N = \{0, 1, 2, \dots\}$.
For a positive integer $M$, write $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$ for
the periodic lattice of side $M$, and $\mathcal C_M$ for the set of
configurations on it with values in $G$: the maps assigning an element of $G$
to every link $(x, i)$ of a site $x \in \Lambda_M$ and an axis
$i \in \{0, 1, 2, 3\}$.

A **Wilson family** for the gauge group consists of the following data:

- a positive integer $L_p$ for each $p \in \mathbb N$, the side lengths;
- a positive integer $m_N$ for each $N \in \mathbb N$, the denominators;
- a real number $\beta_{N,p}$ for each pair $(N, p)$ of natural numbers, the
  couplings;
- a measure $h$ on $G$;
- a set $\mathcal T$, whose elements are called tokens;
- for all $N, p \in \mathbb N$, every token $v \in \mathcal T$ and every site
  $x$ of the lattice $\Lambda_{L_p m_N}$, a function
  $O^{N,p}_{v,x} : \mathcal C_{L_p m_N} \to \mathbb C$, the insertion of $v$
  at $x$.

These data are subject to four conditions:

1. the side lengths are strictly increasing: $L_p < L_{p'}$ whenever
   $p < p'$;
2. the denominators are strictly increasing: $m_N < m_{N'}$ whenever
   $N < N'$;
3. $h$ is a probability measure: $h(G) = 1$;
4. $h$ is a Haar measure, meaning that every compact subset of $G$ has finite
   measure, that for every $g \in G$ the image of $h$ under the left
   translation $y \mapsto gy$ of $G$ is $h$ itself, and that every nonempty
   open subset of $G$ has positive measure.

At the pair of indices $(N, p)$ the lattice is $\Lambda_{L_p m_N}$, whose side
is the product of the side length $L_p$ and the denominator $m_N$. No
condition is placed on the couplings, the tokens or the insertions.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Periodic lattice](periodic-lattice.md)
- [Link configurations](link-configurations.md)

## Sources

- [PublicWilson.lean ledger: Wilson family](../../sources/public-wilson.md#wilson-family)
- [Upstream description: Wilson origin](../../sources/upstream-readme.md#wilson-origin)
