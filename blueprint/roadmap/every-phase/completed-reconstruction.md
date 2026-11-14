# Completed reconstruction

Fix a Wilson family, an extraction and a limit table $S$, with common label
space $\mathbb F$, a record $\mathcal F$ for them and a family of
reconstructions $L$ over the phases for $\mathcal F$. From the record
the definition uses the phase space $X$, whose points $s$ are called
characters, with its phase measure $\nu$, the phase tables $S_s$, the field
algebra (inclusion and derivative maps $\partial$ between the graded fields,
rotations $R$, stress tensor $T$), the reflection and reality symmetry of
the hierarchy of $S$, and the continuation of $S$ with its boundary
distributions $W^{\rm mix}$. From the family it uses, at every character
$s \in X$: the Osterwalder–Schrader space $\mathcal H^{\rm OS}_s$ of
$S_s$, with transfer semigroup $(e^{-\tau H^{\rm OS}_s})_{\tau \ge 0}$ (a
name for the semigroup; no generator enters) and Euclidean vacuum
$\omega_s$; the continuation $(\mathsf F_s, W_s)$; the Wightman data
$\mathfrak W_s$, with Hilbert space $H_s$, field domain $D_s$, vacuum
$\Omega_s$, smeared fields $\varphi_s$, Poincaré representation $V_s$,
whose translation by $b \in \mathbb R^4$ is written $V_s(b)$, and
energy–momentum measure $E_s$; and the bounded map
$J_s : H_s \to \mathcal H^{\rm OS}_s$.

A momentum $p \in \mathbb R^4$ has energy $p_3$. Write
$Z = \{p \in \mathbb R^4 : p_3 = 0\}$ for the zero-energy region and
$\Lambda_u = \{p : 0 < p_3 \le u\}$ for the low-energy region of height $u$.
For a finite sum of words $A$ for $S$, $A\Omega_s$ is its vector in
$\mathfrak W_s$ and $\mu^s_A$ the spectral measure of that vector,
$\mu^s_A(\Delta) = \langle A\Omega_s, E_s(\Delta)\, A\Omega_s \rangle$. For
$\tau \ge 0$, $e^{-\tau H_s} = J_s^*\, e^{-\tau H^{\rm OS}_s}\, J_s$ is the
heat operator pulled back by $J_s$. For a word $w$ of the Wilson family's
tokens (a finite sequence of points of $\mathbb R^4$, each carrying a
token), $S(w)$ and $S_s(w)$ are the Schwinger functions of $S$ and of $S_s$
at the points of $w$ with their tokens. On $\mathbb C$, $\zeta \le \zeta'$ means
$\operatorname{Re} \zeta \le \operatorname{Re} \zeta'$ and
$\operatorname{Im} \zeta = \operatorname{Im} \zeta'$.

**Definition.** The family $L$ is **completed** for $\mathcal F$ when
the following eleven conditions hold.

1. *Wightman theory.* For every $s$, $\mathfrak W_s$ satisfies every
   Wightman condition relative to $W_s$, $R$ and the reflection and
   reality symmetry of $S$: the conditions of a family of reconstructions
   (star operation equal to the time-reflection adjoint, Lorentz action on
   labels descending from the graded fields, unit cyclic vacuum with dense
   domain spanned by word vectors and continuous fields, the adjoint relation
   for fields, vacuum expectation values equal to $W_s$, locality,
   faithfulness, Poincaré covariance, $E_s$ the spectral measure of the
   translations, spectrum in the closed forward cone) and, in addition,
   uniqueness of the vacuum: every $\psi \in H_s$ with $V_s(b)\, \psi = \psi$ for
   all $b \in \mathbb R^4$ is $z\, \Omega_s$ for some $z \in \mathbb C$.
2. *Surjectivity.* For every $s$, $J_s$ is surjective.
3. *Euclidean vacuum.* For every $s$, every vector of the ground space of
   $\mathcal H^{\rm OS}_s$ (the vectors fixed by every
   $e^{-\tau H^{\rm OS}_s}$) is $z\, \omega_s$ for some $z \in \mathbb C$.
4. *Zero energy.* For every $s$ and $\psi \in H_s$, $E_s(Z)\, \psi = \psi$ if and
   only if $\psi = z\, \Omega_s$ for some $z \in \mathbb C$.
5. *Low-energy bound.* For every compactly supported finite sum of words $A$
   there is $M \ge 0$ such that $\mu^s_A(\Lambda_u) \le M u^2$ for every
   $s \in X$ and every $u \in (0, 1]$.
6. *Heat decay.* For every compactly supported finite sum of words $A$ there
   is $M \ge 0$ such that for every $s \in X$ and every real $\tau \ge 1$ the
   number
   $r = \big\langle A\Omega_s,\ (e^{-\tau H_s} - E_s(Z))\, A\Omega_s \big\rangle$
   satisfies $0 \le r$ and $r \le M \tau^{-2}$ in the order of $\mathbb C$; so
   $r$ is real and $0 \le r \le M \tau^{-2}$.
7. *Weak commutant.* For every $s$ and every bounded complex-linear
   operator $B$ on $H_s$: $B$ belongs to the weak commutant of
   $\mathfrak W_s$ if and only if $B = c \cdot 1$ for some $c \in \mathbb C$,
   where $1$ is the identity operator of $H_s$.
8. *Stress tensor.* For every $s$, the data $S$, $S_s$,
   $(\mathsf F_s, W_s)$, $R$, $\partial$, the reflection and reality
   symmetry of $S$, $\mathfrak W_s$ and $T$ form a stress tensor of the
   reconstructed theory.
9. *Continuity in the phase.* For every $n \in \mathbb N$, all labels
   $a_1, \dots, a_n \in \mathbb F$ and every Schwartz function $g$ on
   $(\mathbb R^4)^n$, the map $s \mapsto W_s(a_1, \dots, a_n; g)$ from
   $X$ to $\mathbb C$ is continuous.
10. *Euclidean barycenter.* For every word $w$ of the Wilson family's tokens
    whose points are pairwise distinct,
    $\int_X S_s(w)\, d\nu(s) = S(w)$.
11. *Boundary barycenter.* For every $n \in \mathbb N$, all labels
    $a_1, \dots, a_n \in \mathbb F$ and every Schwartz function $g$ on
    $(\mathbb R^4)^n$,

    $$
    \int_X W_s(a_1, \dots, a_n; g)\, d\nu(s) = W^{\rm mix}(a_1, \dots, a_n; g),
    $$

    the boundary distribution of the record's continuation of $S$.

All integrals are Bochner integrals of complex-valued functions over $X$ with
respect to $\nu$, which by convention are $0$ when the integrand is not
integrable. Every condition is required at every character, with no
exceptional set. Being completed is a property of the family; it adds no
data.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Finite sums of words and their vectors](sums-of-words.md)
- [Compactly supported sums of words](compactly-supported-sums.md)
- [Spectral measure of a finite sum of words](word-spectral-measure.md)
- [Zero-energy and low-energy regions](energy-regions.md)
- [Heat operators pulled back along a bounded map](boundary-heat-semigroup.md)
- [Weak commutant with the Hilbert-space adjoint](weak-commutant.md)
- [Stress tensor of a reconstructed theory](stress-charges/stress-tensor-record.md)

## Sources

- [YM/EveryPhase ledger: Extension](../../sources/every-phase.md#extension)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
