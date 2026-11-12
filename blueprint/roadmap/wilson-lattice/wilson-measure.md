# Wilson measure

Let $(n, G, \mathfrak g)$ be a matrix gauge group, so that $G$ is a group of
unitary $(n+1)\times(n+1)$ complex matrices. Give $G$ the topology it inherits
from the complex $(n+1)\times(n+1)$ matrices with entrywise convergence, and
the Borel σ-algebra of that topology. Let $M$ be a positive integer, let
$\beta$ be a real number, and let $h$ be a measure on $G$; no further condition
is placed on $\beta$ or on $h$. Write $\mathcal C_M$ for the set of
configurations on the periodic lattice $\Lambda_M = (\mathbb Z/M\mathbb Z)^4$
with values in $G$, that is, of the maps $U$ assigning an element
$U(x, i) \in G$ to every link $(x, i)$ of a site $x \in \Lambda_M$ and an axis
$i \in \{0, 1, 2, 3\}$, and give $\mathcal C_M$ the product σ-algebra. Write
$S(U)$ for the Wilson action of a configuration $U$.

Let $h^{\otimes}$ be the product measure on $\mathcal C_M$ with one factor $h$
for each link: the largest outer measure on $\mathcal C_M$ that gives every
product $\prod_{(x,i)} A_{x,i}$ of Borel sets $A_{x,i} \subseteq G$ at most
$\prod_{(x,i)} h(A_{x,i})$, restricted to the product σ-algebra. Put

$$\rho(U) = e^{-\beta S(U)}, \qquad Z = \int_{\mathcal C_M} \rho \, dh^{\otimes}.$$

The **Wilson measure** $\mu_{M,\beta,h}$ is the measure on $\mathcal C_M$ with
density $\rho/Z$ with respect to $h^{\otimes}$: for every measurable set
$A \subseteq \mathcal C_M$,

$$\mu_{M,\beta,h}(A) = \int_A \frac{\rho(U)}{Z} \, dh^{\otimes}(U).$$

Two conventions are part of the definition: $Z$ is the Bochner integral of
$\rho$, which is $0$ when $\rho$ is not integrable; and $\rho(U)/Z$ is $0$ when
$Z = 0$.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Link configurations](link-configurations.md)
- [Wilson action](wilson-action.md)

## Sources

- [PublicWilson.lean ledger: Wilson measure](../../sources/public-wilson.md#wilson-measure)
- [Upstream description: Wilson origin](../../sources/upstream-readme.md#wilson-origin)
