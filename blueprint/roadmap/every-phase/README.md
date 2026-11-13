# Reconstruction for every phase

This chapter maps reconstruction for every phase, the third unit of the
part on phases and reconstruction in
[Armstrong's informalization](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase).
The [declaration ledger](../../sources/every-phase.md) lists the declarations
of the original source that the unit consists of. The input of the unit
provides a Wightman reconstruction at one selected character of a phase
decomposition. The unit builds a reconstruction at every character, with no
exceptional set, and shows that each one has a unique vacuum, a trivial weak
commutant, uniform low-energy and heat bounds and a continued stress tensor,
that its boundary distributions depend continuously on the character, and
that they, and the phase tables on words of pairwise distinct points,
average to those of the limit table.

The unit works under fixed hypotheses. Fix a Wilson family, an extraction and
a limit table $S$, a Euclidean correlation table for the tokens of the family.
In this chapter "Wilson family" means the source's internal family of lattice
data, not the Wilson lattice family of the public statement. Fix a record
$\mathcal F$ of the construction's hypotheses for these three objects. Of its
contents the chapter uses the following.

- A calibration of the family, and the Euclidean seed of $S$: the cutoff, the
  ordered and point limits from which $S$ arises, the Euclidean axioms of $S$,
  and cell and corrected-field estimates.
- A field algebra of $S$: derivative maps, rotations and a Euclidean stress
  tensor $T$ on the quotient label spaces $F_d$ of $S$. Its laws include the
  inclusion and derivative laws, the laws of the rotations, the symmetry,
  reality and conservation of $T$, its tensoriality under rotations, and the
  Euclidean Ward identities of $T$.
- A phase selection. It consists of an Osterwalder–Schrader space of $S$ for
  the time axis, with slab operators. It also has a compact metric space $X$
  with its Borel σ-algebra, the phase space, whose points $s$ are called
  characters, and a measure $\nu$ on $X$, the phase measure. For every
  character $s$ it gives a phase table $S_s$. Finally it selects a character
  $s_0$ and gives an Osterwalder–Schrader space of $S_{s_0}$ with slab
  operators.
- A certificate for the selection, with the following clauses.
  - The slab operators of $S$ and of $S_{s_0}$ satisfy the slab laws.
  - Spatial translations fix every vector of the ground space of the
    Osterwalder–Schrader space of $S$.
  - The compressions of the slab operators to that ground space generate a
    commutative C\*-algebra, and the points of $X$ index its characters
    bijectively. Each character is continuous, $s \mapsto \chi_s(M)$ is
    continuous for every element $M$, and $\int_X \chi_s(M)\, d\nu(s)$ is the
    vacuum expectation of $M$.
  - $\nu$ is a probability measure that gives positive measure to every
    nonempty open set.
  - For every character $s$ and every word $w$ of pairwise distinct points,
    $S_s(w)$ is the value at $s$ of the compressed slab operator of every
    translate of $w$ that lies in a time slab.
  - Every $S_s$ satisfies the Euclidean axioms and has the same null spaces as
    $S$ in every degree. The inclusion and derivative laws, covariance under
    the rotations and the Euclidean Ward identities of $T$ hold for $S_s$.
  - The ground space of the selected Osterwalder–Schrader space is spanned by
    its Euclidean vacuum.
- A continuation $(\mathsf F^{\rm mix}, W^{\rm mix})$ of $S$ and a
  continuation of $S_{s_0}$, each made of continuation functions and boundary
  distributions.
- Selected Wightman data for $S$. They realize the boundary distributions of
  the selected continuation with the rotations of the field algebra, and they
  satisfy every Wightman condition, uniqueness of the vacuum included.

These notions belong to units of the source that this version does not map.
Armstrong's outline assigns the Euclidean axioms to his unit IV.1. It assigns
the phase decomposition, the Osterwalder–Schrader realization and the
uniqueness of the Euclidean vacuum at almost every character to V.1. The
reconstruction at a single phase and its analytic estimates go to V.2, the
field algebra and the Euclidean Ward identities to VI.1, and the existence of
the record to VIII.1. The articles below describe these notions in
mathematical words and link only the articles of this chapter.

The chapter's main result says that for every record there is a family of
reconstructions over the phases that is completed. At every character the
family carries a Wightman theory with a unique vacuum. Its boundary isometry
onto the character's Osterwalder–Schrader space is surjective, and the
Euclidean vacuum spans the Euclidean ground space. Zero energy is the vacuum,
and the weak commutant consists of the scalars. Low energies and heat decay
satisfy bounds uniform in the character, and the continued stress tensor
generates the Poincaré transformations of the fields. The boundary
distributions vary continuously with the character, and they, and the phase
tables on words of pairwise distinct points, integrate against $\nu$ to
those of $S$. The rest of the source,
not yet mapped, uses this theorem.

The public statement has its own versions of these notions. A continuum
hierarchy carries one [Wightman theory](../wightman/README.md), and its
[reconstruction conditions](../continuum-hierarchy/reconstruction.md) ask,
among other things, for the Wightman axioms, faithfulness, a phase
probability measure of full support,
continuity of the correlations in the character, and that their integral
against the phase measure be the unselected correlation. This chapter's
notions are the source's internal ones: its Wightman data, families of
reconstructions and completed families are declarations separate from the
public Wightman theories and reconstruction conditions, and no article of
this chapter depends on the public chapters. How the source passes from the internal notions to the public ones belongs
to units not yet mapped.

**Notation.** A point of spacetime is $x = (x_0, x_1, x_2, x_3) \in \mathbb R^4$.
Its time is $t(x) = x_3$, the last coordinate, and its spatial part is
$\vec x = (x_0, x_1, x_2)$. A momentum $p \in \mathbb R^4$ has energy $p_3$.
Axes are numbered $0, 1, 2, 3$, with time the axis $3$. Inner products are
conjugate-linear in the first argument. The common label space $\mathbb F$
of $S$ is the span of the images of its quotient label spaces $F_d$, and
$a \mapsto a^\star$ is the star operation on labels. Objects of the
character $s$ carry the index $s$:

- the phase table $S_s$;
- the Osterwalder–Schrader space $\mathcal H^{\rm OS}_s$, with Euclidean
  vacuum $\omega_s$, slab operators $\Pi_s$ and transfer semigroup
  $e^{-\tau H^{\rm OS}_s}$, $\tau \ge 0$ (a name for the semigroup; no
  generator enters);
- the continuation $(\mathsf F_s, W_s)$;
- the Wightman data $\mathfrak W_s$, with Hilbert space $H_s$, domain $D_s$,
  vacuum $\Omega_s$, smeared fields $\varphi_s(a, f)$, Poincaré
  representation $V_s$ and energy–momentum measure $E_s$;
- the bounded map $J_s : H_s \to \mathcal H^{\rm OS}_s$.

## The family of reconstructions

For every character $s$, the Euclidean axioms of $S_s$ give an
Osterwalder–Schrader space $\mathcal H^{\rm OS}_s$ for the time axis. It is a
Hilbert space spanned densely by the vectors of positive-time words, with
inner products given by the time-reflected Schwinger functions of $S_s$, a
transfer semigroup of time translations, unitary spatial translations and
the Euclidean vacuum $\omega_s$, the vector of the empty word. Slab operators
$\Pi_s$ on it insert a word lying in a time slab in front of a positive-time
word. The first estimate of the unit bounds the norm of every slab operator
of $S_s$ by the norm of the slab operator of $S$ with the same thickness and
the same word lying in the slab. The copy bounds of $S$ therefore hold for
every $S_s$ with the same constants. The reconstruction of the unit not yet
mapped then applies at every character, and its output is recorded as a
family of reconstructions over the phases. At $s$ this is the
Osterwalder–Schrader space and its slab operators, together with a
continuation $(\mathsf F_s, W_s)$ of $S_s$. It also includes Wightman data $\mathfrak W_s$ that satisfy every Wightman
condition except uniqueness of the vacuum, relative to $W_s$, and a bounded
map $J_s$ with the boundary-isometry property. This property says that $J_s$
is isometric, sends $\Omega_s$ to $\omega_s$ and intertwines the
translations. It also says that smeared Euclidean word vectors at small
positive heights converge to $J_s$ of the corresponding Wightman word
vectors. The family takes the selected data at $s_0$ and uses the star
operation and the Lorentz action on labels of the selected Wightman data at
every character. Uniqueness of the vacuum is not part of the definition, and
$J_s$ is not required to be onto. The proof of the main theorem starts from
such a family, which it constructs from the record.

- [Family of reconstructions over the phases](reconstruction-family.md)

The first property is surjectivity of the boundary isometry. The lemma is
general, about any bounded map with the boundary-isometry property between
Wightman data and an Osterwalder–Schrader space, under the analytic
compatibility hypotheses of a reconstruction staging, symmetry and
smoothness of the table of the Osterwalder–Schrader space, inclusion of the
null spaces of $S$ in those of that table, a reflection Gram identity and
non-tangential boundary values. Following Armstrong's
outline, Euclidean word vectors at positive heights lie in the range of $J$.
The range is closed because $J$ is isometric, and the vectors of positive-time
words span a dense subspace. Uniqueness of the vacuum is assumed on neither
side.

- [The boundary isometry is onto](boundary-isometry-surjective.md)

Continuity in the character starts at strictly increasing imaginary heights.
At purely imaginary, strictly ordered times the continuation $\mathsf F_s$
takes Schwinger values of $S_s$, which are character values. They are
therefore continuous in $s$ and integrate against $\nu$ to the values of $S$.
Armstrong's outline carries this to real times: a polynomial bound uniform
in the character and Vitali's theorem propagate continuity along complex
lines, and the identity theorem propagates the integral. The result holds
pointwise, for every configuration and every strictly increasing height
tuple. Testing against Schwartz functions and a Taylor formula with an
integrable remainder then give continuity and the barycenter identity for
the boundary distributions $W_s$ in the main theorem.

- [Continuations at strict heights: continuity and barycenter in the phase](strict-height-continuity-barycenter.md)

## Sums of words and spectral data

The estimates of the next two sections concern vectors built from the
vacuum by finite sums of words. A letter is a pair $(a, f)$ of a label
$a \in \mathbb F$ and a Schwartz test function $f$ on $\mathbb R^4$. A word is
a finite sequence of letters, and a finite sum of words $A$ is a finite
formal sequence of complex coefficients and words. In Wightman data its
operator $\varphi(A)$ is the corresponding linear combination of products of
smeared fields, and its vector is $A\Omega = \varphi(A)\, \Omega$. A sum is
compactly supported when every test function in it has compact support.

- [Finite sums of words and their vectors](sums-of-words.md)
- [Compactly supported sums of words](compactly-supported-sums.md)

At the character $s$ the spectral measure of $A$ is the diagonal measure
$\mu^s_A(B) = \langle A\Omega_s, E_s(B)\, A\Omega_s \rangle$ of the
energy–momentum measure. The zero-energy region is the hyperplane
$Z = \{p : p_3 = 0\}$, and the low-energy region of height $u$ is the slab
$\{p : 0 < p_3 \le u\}$. The heat operator of the character is pulled back
through the boundary map:
$e^{-\tau H_s} = J_s^*\, e^{-\tau H^{\rm OS}_s}\, J_s$ for $\tau \ge 0$. This is
again a name for a bounded operator on $H_s$, defined for any bounded $J_s$.

- [Spectral measure of a finite sum of words](word-spectral-measure.md)
- [Zero-energy and low-energy regions](energy-regions.md)
- [Heat operators pulled back along a bounded map](boundary-heat-semigroup.md)

## Low energy, heat decay and the vacuum

Locality gives a low-energy bound that is uniform in the character. Let $A$
be compactly supported, and let $A^\dagger$ be the reversed sum with starred
labels and conjugated tests. The vacuum expectation of the commutator of
$A^\dagger$ with a translate of $A$ by a spatial vector of large length and a
time of size at most $1$ vanishes, since the two sums have spacelike
separated supports. The supports and the translation are the same at every
character. The time average of this commutator over a unit interval is a
spatial Fourier transform of a positive measure. It is built from
$\mu^s_A$ and $\mu^s_{A^\dagger}$ with the weight $(1 - \cos p_3)/p_3$ in the
energy $p_3$, which is nonnegative at the nonnegative energies where both
measures live. Testing it against a
momentum bump of radius $u$ bounds the spectral mass of the shell
$\{u/2 < p_3 \le u\}$ by a constant times $u^2$: the spatial volume
contributes $u^3$ and the weight one inverse power of $u$. Dyadic summation
gives $\mu^s_A(\{0 < p_3 \le u\}) \le M u^2$ for $0 < u \le 1$, with one $M$
for all characters. The total masses $\|A\Omega_s\|^2$ are bounded in $s$
because they depend continuously on $s$ on the compact space $X$.

- [Uniform low-energy bound](low-energy-bound.md)

Through the boundary isometry, the pulled-back heat form
$\langle \psi, e^{-\tau H_s}\, \psi \rangle$ is the integral of $e^{-\tau p_3}$
against the diagonal measure of $\psi$. After the whole zero-energy projection
$E_s(Z)$ is subtracted, only energies $p_3 > 0$ remain. Laplace integration
of the low-energy bound then gives
$0 \le \langle A\Omega_s, (e^{-\tau H_s} - E_s(Z))\, A\Omega_s \rangle \le M \tau^{-2}$
for $\tau \ge 1$, uniformly in $s$. At this stage $E_s(Z)$ is the full
spectral projection, not yet known to be the projection onto the vacuum line.

- [Inverse-square heat decay after subtracting zero energy](inverse-square-heat-decay.md)

The decay is then passed from almost every character to every character. At
almost every character, by a result of a unit not yet mapped, the Euclidean
vacuum spans the Euclidean ground space. There the zero-energy projection is
the projection onto $\mathbb C\,\Omega_s$, so the bound holds for the
vacuum-subtracted form
$\langle A\Omega_s, e^{-\tau H_s} A\Omega_s \rangle - |\langle \Omega_s, A\Omega_s \rangle|^2$.
This form is continuous in $s$, so the set of characters where it lies in
$[0, M\tau^{-2}]$ is closed and of full measure. Since $\nu$ charges every
nonempty open set, it is all of $X$. As $\tau \to \infty$, $e^{-\tau H_s}$
tends strongly to $E_s(Z)$. Hence
$\langle \psi, E_s(Z)\, \psi \rangle = |\langle \Omega_s, \psi \rangle|^2$ for every
vector $\psi$ of a compactly supported sum of words, and so
$E_s(Z)\, \psi = \langle \Omega_s, \psi \rangle\, \Omega_s$. Approximation of
Schwartz tests by compactly supported ones extends this to every vector of
$H_s$.

- [No exceptional phase: zero energy is the vacuum](zero-energy-projection-vacuum.md)

## Irreducibility

Irreducibility has two forms, which differ in how the adjoint of a field
enters. A bounded operator $B$ on the Hilbert space of Wightman data is
weakly central when it satisfies
$\langle \varphi(a^\star, \bar f)\, \chi, B \psi \rangle = \langle \chi, B\, \varphi(a, f)\, \psi \rangle$
for all labels, tests and vectors $\chi, \psi$ of the domain. On the left the field
of the starred label with the conjugated test acts inside the domain. The
weak commutant uses instead the Hilbert-space adjoint of the field as an
operator with the domain as its domain. It asks that $\chi$ lie in the domain
of that adjoint and that the same identity hold with the adjoint applied to
$\chi$. Neither form asks $B$ to preserve the domain.

- [Weakly central bounded operators](weakly-central-operators.md)

At every character, a bounded operator is weakly central for
$\mathfrak W_s$ exactly when it is a scalar multiple of the identity. In
Armstrong's outline the proof uses time translations. For a weakly central
$B$ the matrix elements of the heat semigroup against $B\Omega_s$ and the
corresponding ones on the other side extend to bounded holomorphic functions
on the two half-planes. They agree on the real line, so Morera's theorem
glues them to an entire function, which Liouville's theorem makes constant.
The large-time limit and the identification of zero energy with the vacuum
give $B\Omega_s = c\,\Omega_s$, and weak centrality then gives $B = c \cdot 1$.
Neither surjectivity of $J_s$ nor invariance of $D_s$ under $B$ is used.

- [Irreducibility in every phase](irreducibility.md)

A completed family states irreducibility with the weak commutant. In the
proof of the main theorem the two forms are matched through the adjoint
relation of the fields. On the domain, the field of the starred label with
the conjugated test is the restriction of the Hilbert-space adjoint of the
field. This step has no article of its own.

- [Weak commutant with the Hilbert-space adjoint](weak-commutant.md)

## The continued stress tensor

The last property of the reconstructed theories concerns the stress
tensor $T$ of the field algebra, read in $\mathfrak W_s$. The Euclidean Ward
identities of $T$ hold for the phase table $S_s$, by the record. They are
continued to Minkowski space through currents integrated over space, giving
an identity for the boundary distributions $W_s$ and then a commutator
identity for stress charges. Every result of this part is a statement about
general data satisfying explicit hypotheses. The main theorem applies them
with the phase table $S_s$, the continuation $(\mathsf F_s, W_s)$ and the
Wightman data $\mathfrak W_s$.

### Conventions

The Wick factors are $\zeta_3 = -\mathrm i$ and $\zeta_a = 1$ for the spatial
axes. The Minkowski stress labels are $-\zeta_a \zeta_b\, T_{ab}$, and the
stress field $T_{ab}(h)$ is the field of the Minkowski label smeared with
$h$. A
Killing field $K(x) = k + V x$ consists of a translation $k$ and an
infinitesimal Lorentz transformation $V$. The infinitesimal transformation
of labels it induces comes from the rotations of the field algebra: the
skew-symmetric part of $V$ acts through the infinitesimal rotations, and the
symmetric part through $-\mathrm i$ times the infinitesimal rotation of the
skew part of its product with the time reflection. Inserting an entry into a
slot of a tuple places a stress label or point next to a given field.
Finally, the hypotheses for continuing the stress current collect the
analytic data the continuation needs. They are the symmetry, reality and
conservation of $T$, the Euclidean axioms of the correlation table, the
permutation symmetry of $S$, and the inclusion and derivative laws. They
also ask that the continuation continue the table, and that a Laplace
family of the boundary distributions extend the continuation
holomorphically to the forward tube, with partial boundary values.

- [Minkowski stress labels and the stress field](minkowski-stress-field.md)
- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)
- [Hypotheses for continuing the stress current](stress-continuation-hypotheses.md)

### The current jump

The current of $K$ contracts the stress insertion with the components of
$K$, continued to complex points. Integrating its time component over the
spatial position of the inserted stress against a spatial test $g$ gives the
integrated current at a complex insertion time. Its jump at a slot $k$ is
the difference between the integrated current with the stress inserted just
after the field in slot $k$ and just before it, at complex times
$u_k + t \pm \mathrm i s$. A base point $(\xi, u, t)$ consists of spatial
positions, complex times and a real shift. It allows $g$ at the slot $k$
when the shift is smaller than the spatial distance from $\xi_k$ to the
support of every first derivative of $g$. The exchange data at tied heights,
in which the heights of the slots $k$ and $k+1$ coincide, are local
holomorphic extensions of the two orders of the adjacent pair. The two
orders agree at real configurations whose points have time $0$ and whose
adjacent pair is spacelike separated.

- [Spatially integrated current and its jump](integrated-current-jump.md)
- [Admissible base points for the current jump](jump-admissibility.md)

At Euclidean points the Ward identities give the value of the jump. Assume
the hypotheses for continuing the stress current and the Euclidean Ward
identities. Fix a configuration with strictly increasing times, a compactly
supported real spatial test equal to $1$ near the spatial position of the
distinguished point, and the purely imaginary times of the configuration
with shift $0$. As $s \to 0^+$ the jump
tends to the Euclidean value. This value is the correlation with the
distinguished label transformed by the label action of $K$, plus the
correlations with its derivative labels weighted by the Euclidean
continuation of the components of $K$.

- [Euclidean value of the current jump](euclidean-jump-value.md)
- [The current jump at Euclidean points](euclidean-current-jump.md)

The continued value is the same expression with the continued function of
the Laplace family in place of the table and the complexified components of
$K$. Under the same hypotheses and conditions on $g$, take a base point with
strictly increasing imaginary parts that allows $g$ at the slot $k$, and at
which the Laplace family has exchange data at the tied heights. There the
jump converges to the continued value jointly in the base point and in
$s \to 0^+$.

- [Continued value of the current jump](continued-jump-value.md)
- [Joint limit of the current jump](joint-current-jump-limit.md)

### Minkowski jump and Ward identities

The passage to boundary distributions needs exchange heights for every
adjacent pair: attenuable cutoffs, spectral support of the boundary
distributions in the cone, and, for every number of points and every slot,
one sequence of tied heights tending to zero at which exchange data exist
for all labels. A spatial cutoff $g$ and a time profile $f$ satisfy the
spacelike condition at a point $x$ when $g = 1$ near $\vec x$ and every point
with spatial part in the support of a first derivative of $g$ and time in
the support of $f$ is spacelike to $x$. Tests weighted by the components of
a Killing field and product tests $g \otimes f$ of space and time give the
tested insertion of the stress current next to a field and the tested value
of the jump.

- [Exchange heights for every adjacent pair](exchange-height-sequences.md)
- [Spacelike condition on cutoff and profile](spacelike-cutoff-condition.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)
- [Tested stress insertion next to a field](tested-current-jump.md)
- [Tested value of the jump](tested-jump-value.md)

Assume the hypotheses for continuing the stress current, the Euclidean Ward
identities, compactly supported tests, a real spatial cutoff, the spacelike
condition at the distinguished point of every configuration in the support
of the joint test, and exchange heights. Then the difference between the
tested insertions just after and just before the distinguished field is the
tested value of the jump times $\int f$. In Armstrong's outline this follows
by integrating the continued jump along the tied heights and passing to the
boundary. The shell identity is the corresponding relation for word
expectations, without the factor $\int f$, with spectator words before and
after the inserted pair. Assume the hypotheses for continuing the stress
current, the Euclidean Ward identities and exchange heights, a compactly
supported real spatial cutoff, a compactly supported time profile of
integral $1$ and a compactly supported test at the distinguished field, with
the spacelike condition at every point of its support. Then the shell
identity holds with spectator words whose tests are arbitrary Schwartz
functions.

- [Minkowski jump identity](minkowski-jump-identity.md)
- [Shell identity for word expectations](shell-identity.md)
- [Ward identity with arbitrary spectators](ward-identity-schwartz-spectators.md)

### Stress charges and the stress tensor

The stress charge of a Killing field $K$ is
$\mathcal Q_K(f, g) = \sum_b T_{3b}\big(K^b\, (g \otimes f)\big)$, built from a
time profile $f$ and a spatial cutoff $g$. A time profile is admissible when
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
every character the record holds for $\mathfrak W_s$. Its continuation data
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

## Reconstruction in every phase

A family of reconstructions is completed when eleven conditions hold at
every character, with no exceptional set:

1. $\mathfrak W_s$ satisfies every Wightman condition relative to $W_s$,
   uniqueness of the vacuum included.
2. $J_s$ is surjective.
3. The Euclidean ground space is spanned by $\omega_s$.
4. $E_s(Z)\, \psi = \psi$ exactly for the multiples $\psi$ of $\Omega_s$.
5. The low-energy bound holds.
6. The heat-decay bound holds.
7. The weak commutant consists of the scalars.
8. The stress-tensor record holds.
9. $W_s$ depends continuously on $s$.
10. The phase tables integrate to $S$ on words of pairwise distinct points.
11. The boundary distributions integrate to $W^{\rm mix}$.

- [Completed reconstruction](completed-reconstruction.md)

The main theorem assembles the results of the chapter. Given a family of
reconstructions:

- surjectivity of $J_s$ and the identification of zero energy with the
  vacuum show that $\omega_s$ spans the Euclidean ground space at every
  character;
- that uniqueness, carried back through the boundary isometry, gives the
  Wightman conditions with a unique vacuum;
- zero energy is the vacuum by the section on low energy, heat decay and
  the vacuum;
- the bounds come from the low-energy and heat-decay theorems;
- the weak commutant is trivial by irreducibility and the adjoint relation;
- the stress-tensor record holds at every character;
- the continuity and the barycenter of the boundary distributions come from
  the strict-height result.

The barycenter of the phase tables on words of distinct points comes from
the character property of the phase selection and the translation
invariance of $S$, in a unit not yet mapped.

- [Reconstruction in every phase](reconstruction-every-phase.md)
