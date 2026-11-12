# Joint existence statement

Write $\mathbb N = \{0, 1, 2, \dots\}$. A sequence $p : \mathbb N \to \mathbb N$
is strictly increasing when $p(k) < p(l)$ for all $k, l \in \mathbb N$ with
$k < l$. For sequences $p, q : \mathbb N \to \mathbb N$, $p \circ q$ is the
sequence $k \mapsto p(q(k))$.

The **joint existence statement** is the following proposition. For every
matrix gauge group that is simple, there is a Wilson family $C$ for this gauge
group such that

1. $C$ is regular, and
2. for every strictly increasing sequence $p : \mathbb N \to \mathbb N$ there
   are a strictly increasing sequence $q : \mathbb N \to \mathbb N$ and a
   continuum hierarchy $T$ over $C$ such that $T$ has the four properties
   along the volume order $p \circ q$.

The proposition is defined here, not asserted, and it adds no data. The order
of its quantifiers is part of its content. The family $C$, with all of its
data (side lengths, denominators, couplings, Haar probability measure, tokens
and insertions), comes after the gauge group and before $p$, so one regular
family serves every $p$. The sequence $q$ and the hierarchy $T$ come after $p$
and may depend on it, and the one hierarchy $T$ has all four properties along
the one volume order $p \circ q$. Since $q$ is strictly increasing,
$p \circ q$ is a subsequence of $p$. The values of $p$ and of $p \circ q$ are
volume indices of $C$, that is, indices of its side lengths, not side lengths.
In the words of the comment on the formal statement, "One Wilson family per
gauge group, followed by a refinement for every requested volume sequence. All
four conclusions concern a single hierarchy on that refinement."

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Simplicity of the gauge Lie algebra](../gauge-groups/simple-lie-algebra.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Regularity of a Wilson family](../wilson-lattice/wilson-regularity.md)
- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [The four properties of a hierarchy](hierarchy-properties.md)

## Sources

- [ChallengeSpec.lean ledger: joint existence](../../sources/challenge-spec.md#joint-existence)
- [Upstream description: the public challenge](../../sources/upstream-readme.md#the-public-challenge)
