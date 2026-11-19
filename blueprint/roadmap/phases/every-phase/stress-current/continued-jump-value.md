# Continued value of the current jump

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$. Fix a Wilson
family and let $S$ be a Euclidean correlation table for its tokens, with
quotient label spaces $F_d$ and common label space $\mathbb F$; a graded
label is a pair $(d, \beta)$ with $\beta \in F_d$, and for a tuple
$q = ((d_0, \beta_0), \dots, (d_{m-1}, \beta_{m-1}))$ of graded labels,
$[q]$ is the tuple of the images $[\beta_i]_{d_i} \in \mathbb F$ of its
entries. Let
$Z$ be a Laplace family for boundary distributions over $S$, with continued
function $\widetilde Z$, and let $\langle \xi, u\rangle$ be the complex
configuration with spatial positions $\xi$ and complex times $u$, as in the
[spatially integrated current](integrated-current-jump.md).

**Data.** Fix a [Killing field](killing-field.md) $K$, with matrix part $V$ and
complexified components $w^K_b$; rotations of $S$, with real-linear generator
maps $\lambda_d$ from the skew-symmetric real $4 \times 4$ matrices to the
complex-linear maps of $F_d$; derivative maps
$\partial^{(d)}_b : F_d \to F_{d+1}$; spectator graded labels
$v_0, \dots, v_{n-1}$; a slot $k \in \{0, \dots, n\}$; a graded label
$B = (d, \beta)$; and a pair $(\xi, u)$ of spatial positions
$\xi \in (\mathbb R^3)^{n+1}$ and complex times $u \in \mathbb C^{n+1}$. Put
$\zeta = \langle \xi, u\rangle \in (\mathbb C^4)^{n+1}$, and let $\zeta_k$ be
its point in slot $k$.

With $\theta = \mathrm{diag}(1, 1, 1, -1)$, $A = \tfrac12(V - V^{\mathsf T})$
and $A' = \tfrac12\big((V - A)\theta - ((V - A)\theta)^{\mathsf T}\big)$, the
infinitesimal label action of $K$ in degree $d$ is the complex-linear map
$\Sigma^{(d)}_K = \lambda_d(A) - \mathrm i\,\lambda_d(A') : F_d \to F_d$.

**The value.** The **continued value of the current jump** is

$$
C = \widetilde Z\Big(\big[\operatorname{ins}_k\big(v;\ (d, \Sigma^{(d)}_K\beta)\big)\big];\ \zeta\Big)
+ \sum_{b=0}^{3} w^K_b(\zeta_k)\ \widetilde Z\Big(\big[\operatorname{ins}_k\big(v;\ (d+1, \partial^{(d)}_b\beta)\big)\big];\ \zeta\Big),
$$

the transformed label occupying slot $k$ and the spectators the other slots in
order ([insertion into a slot](slot-insertion.md)).

## Depends on

- [Killing fields](killing-field.md)
- [Insertion into a slot](slot-insertion.md)
- [Spatially integrated current and its jump](integrated-current-jump.md)

## Sources

- [YM/EveryPhase ledger: Through](../../../../sources/every-phase.md#through)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
