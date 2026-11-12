# Two-point function of the centered trace

Spacetime is $\mathbb R^4$, and the coordinates of a point are listed in the
order of the axes $0, 1, 2, 3$, the last coordinate being time. For a real
number $r$, the **time pair** at $r$ is the configuration of two points

$$
\Bigl(\bigl(0, 0, 0, -\tfrac{r}{2}\bigr),\ \bigl(0, 0, 0, \tfrac{r}{2}\bigr)\Bigr):
$$

its first point has spatial part $0 \in \mathbb R^3$ and time $-r/2$, and its
second point has spatial part $0$ and time $r/2$. In the source's words, these
are "two insertions on the time axis at -r/2 and r/2". The time pair is
defined for every real number $r$, zero and negative values included.

Let $(n, G, \mathfrak g)$ be a matrix gauge group, $C$ a Wilson family for it,
and $T$ a continuum hierarchy over $C$. The definition below uses the
following parts of the data of $T$:

- the field space $F_4$ of grade $4$, a finite-dimensional complex normed
  space, and a vector $\Theta \in F_4$, called the **centered trace** of
  $T$; a graded field is a pair $(d, u)$ of a grade $d \in \mathbb N$ and a
  vector $u$ of the field space $F_d$ of grade $d$, so that $(4, \Theta)$ is
  a graded field of grade $4$;
- the space $X$ of characters of $T$ and its selected character
  $s_0 \in X$;
- the two-point correlations of $T$ (its correlations are defined for
  configurations of any number of points; only those of two points are used
  here): for every $s \in X \cup \{*\}$, where $*$ is an extra value, not a
  character, that marks the unselected phase, every pair $(a_0, a_1)$ of
  graded fields and every configuration $(z_0, z_1) \in (\mathbb R^4)^2$ of
  two points, a complex number $S_s(a_0, a_1; z_0, z_1)$.

The **trace two-point function** of $T$ is the function
$\Gamma_T : \mathbb R \to \mathbb C$ given, for every real number $r$, by

$$
\Gamma_T(r) = S_{s_0}\Bigl((4, \Theta), (4, \Theta);\ \bigl(0, 0, 0, -\tfrac{r}{2}\bigr), \bigl(0, 0, 0, \tfrac{r}{2}\bigr)\Bigr),
$$

the correlation, in the phase of the selected character $s_0$, of two copies
of the graded field $(4, \Theta)$ at the time pair at $r$. The phase is the
selected character $s_0$ itself, not the unselected value $*$. The time pair
and the trace two-point function are definitions; neither imposes a condition
on $T$.

## Depends on

- [Continuum hierarchy](../continuum-hierarchy/hierarchy.md)
- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](../wilson-lattice/wilson-family.md)
- [Configurations of n points](../spacetime/point-configurations.md)

## Sources

- [ChallengeSpec.lean ledger: trace two-point function](../../sources/challenge-spec.md#trace-two-point-function)
- [Upstream description: non-freeness test](../../sources/upstream-readme.md#non-freeness-test)
