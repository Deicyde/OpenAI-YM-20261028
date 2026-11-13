# Inverse-square heat decay after subtracting zero energy

Fix a Wilson family, an extraction, a limit table $S$ and a record
$\mathcal F$ for them, with compact metric phase space $X$, whose points are
called characters, and let $L$ be a family of reconstructions over the phases
for $\mathcal F$. For every character $s \in X$ the family provides:

- Wightman data $\mathfrak W_s$ for $S$, with Hilbert space $H_s$, inner
  product $\langle \cdot, \cdot \rangle$ conjugate-linear in its first
  argument, vacuum $\Omega_s$, smeared fields $\varphi_s$ and energy-momentum
  measure $E_s$, which assigns a bounded operator $E_s(B)$ on $H_s$ to every
  subset $B \subseteq \mathbb R^4$;
- an Osterwalder–Schrader space $\mathcal H^{\rm OS}_s$ for the time axis, with
  transfer semigroup $\big(e^{-\tau H^{\rm OS}_s}\big)_{\tau \ge 0}$;
- a bounded complex-linear map $J_s : H_s \to \mathcal H^{\rm OS}_s$, the
  boundary map, with Hilbert adjoint $J_s^*$.

For real $\tau \ge 0$, let
$e^{-\tau H_s} = J_s^*\, e^{-\tau H^{\rm OS}_s}\, J_s$ be the heat operator of
the character pulled back by $J_s$. Let
$Z = \{ p \in \mathbb R^4 : p_3 = 0 \}$ be the zero-energy region, where $p_3$
is the energy, the last coordinate, and $E_s(Z)$ the full zero-energy
projection of the character. For a finite sum of words $A$ for $S$, let
$A\Omega_s = \varphi_s(A)\, \Omega_s$ be its vector in $H_s$.

Complex numbers carry their partial order: $z \le w$ means
$\operatorname{Re} z \le \operatorname{Re} w$ and
$\operatorname{Im} z = \operatorname{Im} w$.

**Theorem.** For every compactly supported finite sum of words $A$ for $S$,
there is a real number $M \ge 0$ such that, for every character $s \in X$ and
every real $\tau \ge 1$, the complex number

$$
r_s(\tau) = \big\langle A\Omega_s,\ \big(e^{-\tau H_s} - E_s(Z)\big)\, A\Omega_s \big\rangle
$$

satisfies

$$
0 \le r_s(\tau) \qquad \text{and} \qquad r_s(\tau) \le M\, \tau^{-2}
$$

in the partial order of $\mathbb C$. Both inequalities together say that
$r_s(\tau)$ is a real number with $0 \le r_s(\tau) \le M \tau^{-2}$. The
constant $M$ depends on $L$ and $A$ only, not on $s$ or $\tau$. The subtracted
operator is the whole spectral projection $E_s(Z)$; it is not assumed to be
the projection onto the vacuum line.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Finite sums of words and their vectors](sums-of-words.md)
- [Compactly supported sums of words](compactly-supported-sums.md)
- [Zero-energy and low-energy regions](energy-regions.md)
- [Heat operators pulled back along a bounded map](boundary-heat-semigroup.md)

## Proof depends on

- [Continuations at strict heights: continuity and barycenter in the phase](strict-height-continuity-barycenter.md)
- [Spectral measure of a finite sum of words](word-spectral-measure.md)
- [Uniform low-energy bound](low-energy-bound.md)

## Sources

- [YM/EveryPhase ledger: Decay](../../sources/every-phase.md#decay)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
