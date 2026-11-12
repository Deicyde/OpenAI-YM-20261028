# Tests suited to a volume

Let $C$ be a Wilson family for a matrix gauge group, with side lengths $L_p$,
positive integers indexed by $p \in \mathbb N = \{0, 1, 2, \dots\}$. Let
$n \in \mathbb N$ and let $t \in \mathcal D(\mathrm{Sep}_n)$ be a separated
test function on configurations of $n$ points: an infinitely differentiable
function $t : (\mathbb R^4)^n \to \mathbb C$ whose closed support, the closure
in $(\mathbb R^4)^n$ of the set $\{x : t(x) \neq 0\}$, is compact and
contained in the set $\mathrm{Sep}_n$ of configurations of $n$ pairwise
distinct points. For a configuration
$x = (x_0, \dots, x_{n-1}) \in (\mathbb R^4)^n$, write $x_i^a$ for the
coordinate $a$ of the point $x_i$.

For a volume index $p \in \mathbb N$, the separated test function $t$ is
**suitable** for $p$ when its closed support is contained in the open box

$$
\Bigl\{ x \in (\mathbb R^4)^n : -\frac{L_p}{2} < x_i^a < \frac{L_p}{2}
\ \text{ for every } i \in \{0, \dots, n-1\} \text{ and every } a \in \{0, 1, 2, 3\} \Bigr\}.
$$

For the given family, suitability is a condition on $t$ and $p$; this
containment is all it requires, and both inequalities are strict.

## Depends on

- [Matrix gauge group](../gauge-groups/gauge-group.md)
- [Wilson family](wilson-family.md)
- [Test functions on separated configurations](../spacetime/separated-test-functions.md)
- [Configurations of n points](../spacetime/point-configurations.md)

## Sources

- [Declaration ledger of the Wilson lattice source: suitable tests](../../sources/public-wilson.md#suitable-tests)
