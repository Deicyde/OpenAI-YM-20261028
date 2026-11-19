# Heat operators pulled back along a bounded map

Fix a Wilson family and a Euclidean correlation table $S$ for its tokens, and
let $\mathfrak W$ be Wightman data for $S$, with Hilbert space $H$; of these
data only the Hilbert space enters the definition below. Inner products are
conjugate-linear in their first argument.

Let $U$ be a second Euclidean correlation table for the tokens of the same
Wilson family, possibly different from $S$, and let $\mathcal H^{\rm OS}$ be an
Osterwalder–Schrader space of $U$ for the time axis. It is a Hilbert space with
a vector for every word of positive times, whose span is dense and whose inner
products are the time-reflected Schwinger functions of $U$, together with its
transfer semigroup: bounded operators $e^{-\tau H^{\rm OS}}$ on
$\mathcal H^{\rm OS}$ for $\tau \ge 0$ (a name for the semigroup; no generator
enters) such that

$$
e^{-0 H^{\rm OS}} = 1, \qquad
e^{-(\tau+\sigma) H^{\rm OS}} = e^{-\tau H^{\rm OS}}\, e^{-\sigma H^{\rm OS}}, \qquad
\big\lVert e^{-\tau H^{\rm OS}} \big\rVert \le 1, \qquad
\big(e^{-\tau H^{\rm OS}}\big)^* = e^{-\tau H^{\rm OS}}
\qquad (\tau, \sigma \ge 0),
$$

and $\tau \mapsto e^{-\tau H^{\rm OS}} \chi$ is continuous for every
$\chi \in \mathcal H^{\rm OS}$; the space also carries unitary spatial
translations commuting with the $e^{-\tau H^{\rm OS}}$, and
$e^{-\tau H^{\rm OS}}$ acts on the vector of a positive-time word as
translation of the word by $\tau$ in time. Let
$J : H \to \mathcal H^{\rm OS}$ be a bounded complex-linear map, and let
$J^* : \mathcal H^{\rm OS} \to H$ be its Hilbert adjoint, the bounded operator
with $\langle J^* \chi, \psi \rangle = \langle \chi, J \psi \rangle$ for all
$\chi \in \mathcal H^{\rm OS}$ and $\psi \in H$.

For every real $\tau \ge 0$, the **heat operator** pulled back by $J$ is the
bounded operator on $H$

$$
e^{-\tau H} = J^*\, e^{-\tau H^{\rm OS}}\, J : H \to H .
$$

Here $e^{-\tau H}$ is a name for this composite, read as a single symbol: no
generator is defined, and no condition is put on $J$.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Projection](../../../sources/every-phase.md#projection)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
