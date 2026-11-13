# Reconstruction in every phase

Fix a Wilson family, an extraction and a limit table $S$, and let
$\mathcal F$ be a record for them: a calibration of the family, the Euclidean
seed of $S$ (cutoff, ordered and point limits, the hierarchy of $S$, and the cell
and corrected-field estimates), a field algebra, a phase selection, the laws
of the field algebra together with a certificate for the phase selection, a
continuation of $S$, a continuation of the selected phase table, selected
Wightman data, and the relativistic reconstruction linking them. Let $X$ be
the phase space of the record, whose points $s$ are called characters, and
$\nu$ its phase measure. A momentum $p \in \mathbb R^4$ has energy $p_3$.

**Theorem.** For every record $\mathcal F$ there is a family of
reconstructions $L$ over the phases for $\mathcal F$ that is
completed.

Spelled out, $L$ assigns to every character $s \in X$, with no exceptional
set, an Osterwalder–Schrader space $\mathcal H^{\rm OS}_s$ of the phase
table $S_s$ with slab operators that satisfy the reconstruction input, a
continuation $(\mathsf F_s, W_s)$ of $S_s$ that is compatible with these
slab operators, the record's field algebra, the Lorentz action of the
selected Wightman data and the time-reflection adjoint of $S$, Wightman data
$\mathfrak W_s$ for $S$ whose star operation and Lorentz action (on labels
and on graded fields) are those of the selected Wightman data, and a bounded
map $J_s$ from the Hilbert space $H_s$ of $\mathfrak W_s$ to
$\mathcal H^{\rm OS}_s$ with the boundary-isometry property (all as in the
definition of a family of reconstructions), agreeing with the selected data
at the selected character, such that:

1. $\mathfrak W_s$ satisfies every Wightman condition relative to $W_s$,
   the rotations of the record's field algebra and the reflection and
   reality symmetry of $S$, uniqueness of the vacuum included;
2. $J_s$ is surjective;
3. the ground space of $\mathcal H^{\rm OS}_s$ is spanned by the Euclidean
   vacuum $\omega_s$;
4. a vector $\psi \in H_s$ satisfies $E_s(\{p_3 = 0\})\, \psi = \psi$ if and only if
   it is a complex multiple of the vacuum $\Omega_s$, where $E_s$ is the
   energy–momentum measure of $\mathfrak W_s$;
5. for every compactly supported finite sum of words $A$ there is $M \ge 0$
   with $\mu^s_A(\{0 < p_3 \le u\}) \le M u^2$ for all $s \in X$ and
   $u \in (0, 1]$, where $\mu^s_A$ is the spectral measure of the vector
   $A\Omega_s$;
6. for every such $A$ there is $M \ge 0$ with
   $0 \le \langle A\Omega_s, (e^{-\tau H_s} - E_s(\{p_3 = 0\}))\, A\Omega_s \rangle \le M \tau^{-2}$
   for all $s \in X$ and real $\tau \ge 1$, where
   $e^{-\tau H_s} = J_s^*\, e^{-\tau H^{\rm OS}_s}\, J_s$ and
   $(e^{-\tau H^{\rm OS}_s})_{\tau \ge 0}$ is the transfer semigroup of
   $\mathcal H^{\rm OS}_s$;
7. a bounded complex-linear operator on $H_s$ belongs to the weak commutant
   of $\mathfrak W_s$ if and only if it is a scalar multiple of the
   identity;
8. the data of the character $s$ and $\mathfrak W_s$ form a stress tensor of
   the reconstructed theory;
9. for all $n$, labels $a_1, \dots, a_n$ and Schwartz functions $g$ on
   $(\mathbb R^4)^n$, $s \mapsto W_s(a_1, \dots, a_n; g)$ is continuous
   and $\int_X W_s(a_1, \dots, a_n; g)\, d\nu(s)$ is the boundary
   distribution of the record's continuation of $S$ at $(a_1, \dots, a_n; g)$;
   and for every word $w$ of pairwise distinct points,
   $\int_X S_s(w)\, d\nu(s) = S(w)$.

The precise meaning of each item is that of the corresponding conditions of
a completed reconstruction (items 1 to 8 are its conditions 1 to 8, and item
9 combines its conditions 9, 10 and 11). The theorem assumes nothing beyond
the record.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Completed reconstruction](completed-reconstruction.md)

## Proof depends on

- [Uniform low-energy bound](low-energy-bound.md)
- [Inverse-square heat decay after subtracting zero energy](inverse-square-heat-decay.md)
- [Irreducibility in every phase](irreducibility.md)
- [The stress tensor in every phase](stress-tensor-every-phase.md)
- [The boundary isometry is onto](boundary-isometry-surjective.md)
- [No exceptional phase: zero energy is the vacuum](zero-energy-projection-vacuum.md)
- [Continuations at strict heights: continuity and barycenter in the phase](strict-height-continuity-barycenter.md)

## Sources

- [YM/EveryPhase ledger: Extension](../../sources/every-phase.md#extension)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
