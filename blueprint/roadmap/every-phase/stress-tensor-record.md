# Stress tensor of a reconstructed theory

A point of spacetime is $x = (x_0, x_1, x_2, x_3) \in \mathbb R^4$; the axes
are numbered $0, 1, 2, 3$, with time the axis $3$, the last coordinate. Put
$\eta_3 = 1$ and $\eta_a = -1$ for $a \in \{0, 1, 2\}$. Inner products are
conjugate-linear in their first argument, and $\bar h$ is the complex
conjugate of a test function $h$.

**Data.** Fix

- a Wilson family and Euclidean correlation tables $S$ and $U$ for its
  tokens;
- a continuation $(\mathsf F, W)$ for $S$, made of continuation functions
  $\mathsf F$ and boundary distributions $W$ over the labels of $S$, as in the
  [hypotheses for continuing the stress current](stress-continuation-hypotheses.md);
- rotations $R$ of $S$, inclusion and derivative maps for $S$, and the
  hypothesis that $S$ satisfies the symmetry and reality conditions;
- Wightman data $\mathfrak W$ over $S$, with domain $D$, smeared fields
  $\varphi(\ell, h) : D \to D$ ($\ell$ in the common label space,
  $h \in \mathcal S(\mathbb R^4)$), and action $g \mapsto V(g)$ of
  the Poincaré coordinates $g = (\Lambda, u)$ on its Hilbert space; for such
  $g$, $\Lambda_{ia}$ is the entry of the matrix of $\Lambda$ in row $i$ and
  column $a$, and $(h \circ g^{-1})(x) = h\big(\Lambda^{-1}(x - u)\big)$;
- a stress tensor $T$ of $S$, with
  [stress field](minkowski-stress-field.md) $T_{ab}(h)$ in $\mathfrak W$ and
  test derivative $\widetilde\partial_a h = -\partial_a h$.

**The record.** These data form a **stress tensor of the reconstructed
theory** when the following seven conditions hold.

1. *Continuation data.* There are cutoff functions $\chi_n$ and a Laplace
    family $Z$ for $W$ over them such that $\mathsf F$, $Z$, $U$, the
    inclusion and derivative maps, the symmetry and reality hypothesis and $T$
    satisfy the
    [hypotheses for continuing the stress current](stress-continuation-hypotheses.md),
    and $W$ and $Z$ satisfy the condition of
    [exchange heights for every adjacent pair](exchange-height-sequences.md).

2. *Covariance.* For every Poincaré coordinate $g = (\Lambda, u)$, every
    $h \in \mathcal S(\mathbb R^4)$, all axes $a, b$ and every $\psi \in D$,
    the vector $V(g)\psi$ lies in $D$ and

    $$
    V(g)\, T_{ab}(h)\, \psi
    = \sum_{i=0}^{3}\sum_{j=0}^{3} \Lambda_{ia}\Lambda_{jb}\; T_{ij}\big(h \circ g^{-1}\big)\, V(g)\psi .
    $$

3. *Symmetry.* $T_{ab}(h) = T_{ba}(h)$ for all axes $a, b$ and every
    $h \in \mathcal S(\mathbb R^4)$.

4. *Hermiticity.* For every $h$, all axes $a, b$ and all
    $\psi, \psi' \in D$,

    $$
    \big\langle T_{ab}(h)\psi,\ \psi' \big\rangle = \big\langle \psi,\ T_{ab}(\bar h)\psi' \big\rangle .
    $$

5. *Conservation.* For every axis $b$ and every $h$,

    $$
    \sum_{a=0}^{3} \eta_a\, T_{ab}\big(\widetilde\partial_a h\big) = 0
    $$

    as a map $D \to D$.

6. *Commutator.* $\mathfrak W$, $T$ and $R$ satisfy the condition that
    [charges generate the transformations of fields](charge-generates-transformations.md).

7. *Derivation rule.* $\mathfrak W$, $T$ and $R$ satisfy the condition that
    [charges act as derivations on sums of words](charge-acts-as-derivation.md).

## Depends on

- [Hypotheses for continuing the stress current](stress-continuation-hypotheses.md)
- [Exchange heights for every adjacent pair](exchange-height-sequences.md)
- [Minkowski stress labels and the stress field](minkowski-stress-field.md)
- [Charges generate the transformations of fields](charge-generates-transformations.md)
- [Charges act as derivations on sums of words](charge-acts-as-derivation.md)

## Sources

- [YM/EveryPhase ledger: Implement](../../sources/every-phase.md#implement)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
