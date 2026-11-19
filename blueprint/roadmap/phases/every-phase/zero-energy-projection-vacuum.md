# No exceptional phase: zero energy is the vacuum

Fix a Wilson family, an extraction, a limit table $S$ and a record
$\mathcal F$ for them, with compact metric phase space $X$, whose points are
called characters, and let $L$ be a family of reconstructions over the phases
for $\mathcal F$. For every character $s \in X$ the family provides Wightman
data $\mathfrak W_s$ for $S$, with Hilbert space $H_s$, inner product
$\langle \cdot, \cdot \rangle$ conjugate-linear in its first argument, vacuum
$\Omega_s \in H_s$ and energy-momentum measure $E_s$, which assigns a bounded
operator $E_s(B)$ on $H_s$ to every subset $B \subseteq \mathbb R^4$. Let
$Z = \{ p \in \mathbb R^4 : p_3 = 0 \}$ be the zero-energy region, where $p_3$
is the energy, the last coordinate.

**Lemma.** For every character $s \in X$ and every vector $\psi \in H_s$,

$$
E_s(Z)\, \psi = \langle \Omega_s, \psi \rangle\, \Omega_s .
$$

The identity holds at every character $s \in X$, with no exceptional set.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Zero-energy and low-energy regions](energy-regions.md)

## Proof depends on

- [Finite sums of words and their vectors](sums-of-words.md)
- [Compactly supported sums of words](compactly-supported-sums.md)
- [Heat operators pulled back along a bounded map](boundary-heat-semigroup.md)
- [Spectral measure of a finite sum of words](word-spectral-measure.md)
- [Continuations at strict heights: continuity and barycenter in the phase](strict-height-continuity-barycenter.md)
- [Inverse-square heat decay after subtracting zero energy](inverse-square-heat-decay.md)

## Sources

- [YM/EveryPhase ledger: Vacuum](../../../sources/every-phase.md#vacuum)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
