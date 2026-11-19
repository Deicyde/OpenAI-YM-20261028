# Stress conventions and the current jump

## Conventions

The Wick factors are $\zeta_3 = -\mathrm i$ for the time axis $3$ and $\zeta_a = 1$ for the spatial
axes $a$. The Minkowski stress labels of a stress tensor $T = (T_{ab})$ are $-\zeta_a \zeta_b\, T_{ab}$, and the
stress field $T_{ab}(h)$ is the field of the Minkowski label smeared with
a test function $h$. A
Killing field $K(x) = c + V x$ consists of a translation $c$ and an
infinitesimal Lorentz transformation $V$. The infinitesimal transformation
of labels it induces comes from the rotations of the field algebra: the
skew-symmetric part of $V$ acts through the infinitesimal rotations, and the
symmetric part through $-\mathrm i$ times the infinitesimal rotation of the
skew part of its product with the time reflection. Inserting an entry into a
slot of a tuple places a stress label or point next to a given field.
Finally, the hypotheses for continuing the stress current collect the
analytic data the continuation needs. They are the symmetry, reality and
conservation of $T$, the Euclidean axioms of the second correlation table, the
permutation symmetry of the Euclidean correlation table $S$, and the inclusion and derivative laws. They
also ask that the continuation continue the table, and that a Laplace
family of the boundary distributions extend the continuation
holomorphically to the forward tube, with partial boundary values.

- [Minkowski stress labels and the stress field](minkowski-stress-field.md)
- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)
- [Hypotheses for continuing the stress current](stress-continuation-hypotheses.md)

## The current jump

The current of $K$ contracts the stress insertion with the components of
$K$, continued to complex points. Integrating its time component over the
spatial position of the inserted stress against a spatial test $g$ gives the
integrated current at a complex insertion time. Its jump at a slot $k$ is
the difference between the integrated current with the stress inserted just
after the field in slot $k$ and just before it, at complex times
$u_k + t \pm \mathrm i s$, where $s$ is real and the base point $(\xi, u, t)$ consists of spatial
positions $\xi$, complex times $u$ and a real shift $t$. A base point allows $g$ at the slot $k$
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
