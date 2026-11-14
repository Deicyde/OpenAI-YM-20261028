# Stress charges and the stress tensor

The stress charge of a Killing field $K$ is
$\mathcal Q_K(f, g) = \sum_b T_{3b}\big(K^b\, (g \otimes f)\big)$, built from a
time profile $f$ and a spatial cutoff $g$: the stress field $T_{3b}$ of a
stress tensor $T$, with first index the time axis $3$, is tested with the
component $K^b$ of $K$ along the axis $b$ times the function $g \otimes f$,
whose value at a point is $g$ at its spatial part times $f$ at its time, and
summed over $b$. A time profile is admissible when
it is real, compactly supported and of integral $1$. A spatial cutoff is
admissible for a set of spacetime points and a profile when it is compactly
supported and equal to $1$ on a ball whose exterior, at the times of the
profile, is spacelike to the set. Under the hypotheses for continuing the
stress current, the Euclidean Ward identities and exchange heights, consider
Wightman data that satisfy every Wightman condition except uniqueness of the
vacuum. For such data, an admissible time profile $f$ and a spatial cutoff
$g$ admissible for a compact set $\mathcal O$ and $f$, the commutator
$\mathrm i\,[\mathcal Q_K(f, g), \cdot\,]$ acts on a field whose test is
supported in $\mathcal O$ as the infinitesimal Poincaré transformation of
the field under $K$. In the proof
the cutoff is replaced by its real part, locality removes the difference,
and matrix elements between word vectors reduce the identity to the Ward
identity with arbitrary spectators.

- [Admissible time profile](admissible-time-profile.md)
- [Admissible spatial cutoff](admissible-spatial-cutoff.md)
- [Stress charge and the commutator action](stress-charge.md)
- [Infinitesimal Poincaré transformation of a field](infinitesimal-field-transformation.md)
- [The stress charge generates the transformation](stress-charge-commutator.md)

The stress tensor of a reconstructed theory is a record of seven
conditions. The first gives continuation data: a Laplace family over cutoffs
satisfying the hypotheses for continuing the stress current, with exchange
heights. Then come covariance of the stress field under the Poincaré
representation, symmetry, hermiticity and conservation. Last come the
commutator identity for all admissible data and the derivation rule on
finite sums of words, for every choice of representatives of the labels. At
every character $s$ the record holds for $\mathfrak W_s$, the Wightman data
of the reconstruction at $s$. Its continuation data
and the commutator identity come from the reconstruction at $s$ and the
results above. Covariance, symmetry and hermiticity come from the laws of
the field algebra and the Wightman conditions of $\mathfrak W_s$;
conservation uses the continuation data as well. The derivation rule
follows from the commutator identity, because a commutator acts on a
product of fields as a derivation.

- [Charges generate the transformations of fields](charge-generates-transformations.md)
- [Charges act as derivations on sums of words](charge-acts-as-derivation.md)
- [Stress tensor of a reconstructed theory](stress-tensor-record.md)
- [The stress tensor in every phase](stress-tensor-every-phase.md)
