# Uniform low-energy bound

Fix a Wilson family, an extraction, a limit table $S$ and a record
$\mathcal F$ for them, with compact metric phase space $X$, whose points are
called characters, and let $L$ be a family of reconstructions over the phases
for $\mathcal F$. For a character $s \in X$ and a finite sum of words $A$ for
$S$, let $\mu^s_A$ be the spectral measure of $A$ at $s$, the diagonal measure
of the energy-momentum measure $E_s$ of the Wightman data at $s$ at the vector
$A\Omega_s$. For real $u$, let $\Lambda_u = \{ p \in \mathbb R^4 : 0 < p_3 \le u \}$
be the low-energy region of height $u$, where $p_3$ is the energy, the last
coordinate.

**Theorem.** For every compactly supported finite sum of words $A$ for $S$,
there is a real number $M \ge 0$ such that

$$
\mu^s_A(\Lambda_u) \le M\, u^2
\qquad \text{for every character } s \in X \text{ and every } u \in (0, 1] .
$$

The constant $M$ depends on $L$ and $A$ only: one $M$ serves all characters
and all heights $u \in (0, 1]$ at once. The measure $\mu^s_A$ is finite, so
$\mu^s_A(\Lambda_u)$ is a real number.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Finite sums of words and their vectors](sums-of-words.md)
- [Compactly supported sums of words](compactly-supported-sums.md)
- [Spectral measure of a finite sum of words](word-spectral-measure.md)
- [Zero-energy and low-energy regions](energy-regions.md)

## Proof depends on

- [Continuations at strict heights: continuity and barycenter in the phase](strict-height-continuity-barycenter.md)

## Sources

- [YM/EveryPhase ledger: Light](../../sources/every-phase.md#light)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
