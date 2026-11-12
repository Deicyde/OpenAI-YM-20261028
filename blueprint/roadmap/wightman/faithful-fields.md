# Faithful field system

Let $H$ be a Hilbert space, $L$ a space of field labels,
$\mathcal S(\mathbb R^4)$ the space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$, and $(D, \Omega, \varphi)$ a field system on
$H$ and $L$, with domain $D$, vacuum $\Omega$ and smeared fields
$\varphi(a,f) : D \to D$.

The field system is **faithful** when every nonzero label has a nonzero smeared
field: for every label $a \in L$ with $a \neq 0$ there is a Schwartz test
function $f \in \mathcal S(\mathbb R^4)$ such that $\varphi(a,f)$ is not the
zero map of $D$, that is, such that $\varphi(a,f)\,\psi \neq 0$ for some vector
$\psi \in D$.

Faithfulness is a condition on the field system alone; it involves no further
data.

## Depends on

- [Field system](../wightman/field-system.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)

## Sources

- [PublicTheory.lean ledger: faithful fields](../../sources/public-theory.md#faithful-fields)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
