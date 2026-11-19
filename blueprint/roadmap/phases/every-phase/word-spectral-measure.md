# Spectral measure of a finite sum of words

Fix a Wilson family, an extraction, a limit table $S$ and a record
$\mathcal F$ for them, let $X$ be the compact metric phase space of
$\mathcal F$, whose points are called characters, and let $L$ be a family of
reconstructions over the phases for $\mathcal F$. For every character
$s \in X$ the family provides Wightman data $\mathfrak W_s$ for $S$, of which
the following parts are used here:

- its field system for $S$: a Hilbert space $H_s$, with inner product
  $\langle \cdot, \cdot \rangle$ conjugate-linear in its first argument, a
  domain $D_s \subseteq H_s$, a vacuum $\Omega_s \in D_s$ and smeared
  fields $\varphi_s(a, f) : D_s \to D_s$;
- its energy-momentum measure $E_s$ on $H_s$: a bounded operator $E_s(B)$ for
  every subset $B \subseteq \mathbb R^4$, and for every vector $\psi \in H_s$ a
  finite measure $\mu^s_\psi$ on the Borel sets of $\mathbb R^4$, the diagonal
  measure of $\psi$, such that
  $\mu^s_\psi(B) = \langle \psi, E_s(B)\, \psi \rangle$ for every Borel set $B$.

Let $A$ be a finite sum of words for $S$, and let
$A\Omega_s = \varphi_s(A)\, \Omega_s \in H_s$ be its vector in the field
system of the character $s$. The **spectral measure** of $A$ at the character
$s$ is the diagonal measure of this vector,

$$
\mu^s_A = \mu^s_{A\Omega_s}, \qquad
\mu^s_A(B) = \big\langle A\Omega_s,\ E_s(B)\, A\Omega_s \big\rangle
\quad \text{for every Borel set } B \subseteq \mathbb R^4 .
$$

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Finite sums of words and their vectors](sums-of-words.md)

## Sources

- [YM/EveryPhase ledger: Light](../../../sources/every-phase.md#light)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
