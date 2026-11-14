# The stress tensor in every phase

Fix a gauge group, a Wilson family for it, an extraction order and a
Euclidean correlation table $S$ over the labels of the family, together with
a record $\mathcal F$ of the construction's hypotheses for them. Of the
record the statement uses

- the Euclidean axioms of $S$, among them invariance of $S$ on separated
  configurations under every signed permutation of the coordinate axes
  (acting on the points and on the labels together) and the reality
  condition (conjugating the labels conjugates the value);
- the field algebra of $S$: inclusion and derivative maps for $S$, rotations
  $R$ of $S$, and a stress tensor $T$ of $S$;
- the phase selection: a compact metric space $X$, the phase space, whose
  points $s$ are called characters, and, for every character $s \in X$, a
  phase table $S_s$.

Let $L$ be a [family of reconstructions](../reconstruction-family.md) over the
phases of $\mathcal F$; for every character $s$ it provides a continuation
$(\mathsf F_s, W_s)$ for $S$ (continuation functions and boundary
distributions) and Wightman data $\mathfrak W_s$ over $S$.

**Statement.** For every such $\mathcal F$, every family of reconstructions
$L$ and every character $s \in X$, the data

- the table $S$ and, as the second table, the phase table $S_s$,
- the continuation $(\mathsf F_s, W_s)$ of $L$ at $s$,
- the rotations $R$ and the inclusion and derivative maps of the field
  algebra of $\mathcal F$,
- the hypothesis, from the Euclidean axioms of $S$, that $S$ is invariant
  under signed permutations of the coordinate axes (acting on points and
  labels) and satisfies the reality condition,
- the Wightman data $\mathfrak W_s$ of $L$ at $s$,
- the stress tensor $T$ of the field algebra of $\mathcal F$,

form a [stress tensor of the reconstructed theory](stress-tensor-record.md):
the continuation data, covariance, symmetry, hermiticity and conservation
conditions hold, the charges of the stress field of $T$ in $\mathfrak W_s$
generate the transformations of the fields of $\mathfrak W_s$, and they act
as derivations on finite sums of words.

## Depends on

- [Family of reconstructions over the phases](../reconstruction-family.md)
- [Stress tensor of a reconstructed theory](stress-tensor-record.md)

## Proof depends on

- [The stress charge generates the transformation](stress-charge-commutator.md)
- [Hypotheses for continuing the stress current](../stress-current/stress-continuation-hypotheses.md)
- [Exchange heights for every adjacent pair](../ward-identities/exchange-height-sequences.md)
- [Admissible base points for the current jump](../stress-current/jump-admissibility.md)
- [Charges generate the transformations of fields](charge-generates-transformations.md)
- [Minkowski stress labels and the stress field](../stress-current/minkowski-stress-field.md)
- [Charges act as derivations on sums of words](charge-acts-as-derivation.md)
- [Stress charge and the commutator action](stress-charge.md)
- [Finite sums of words and their vectors](../sums-of-words.md)

## Sources

- [YM/EveryPhase ledger: Implement](../../../sources/every-phase.md#implement)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
