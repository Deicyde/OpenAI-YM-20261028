# Field system

Let $H$ be a Hilbert space, $L$ a space of field labels, and
$\mathcal S(\mathbb R^4)$ the complex vector space of Schwartz test functions
$f : \mathbb R^4 \to \mathbb C$. A **field system** on $H$ and $L$ consists of
three pieces of data:

- the **domain**, a complex linear subspace $D$ of $H$;
- the **vacuum**, a vector $\Omega \in D$;
- the **smeared fields**: for every label $a \in L$ and every Schwartz test
  function $f \in \mathcal S(\mathbb R^4)$, a complex-linear map
  $\varphi(a,f) : D \to D$, which depends complex-linearly on $a$ and
  complex-linearly on $f$.

Explicitly, for all labels $a, b \in L$, Schwartz test functions
$f, g \in \mathcal S(\mathbb R^4)$, vectors $\psi, \chi \in D$ and complex
numbers $c$,

$$
\begin{gathered}
\varphi(a,f)\,(c\psi + \chi) = c\,\varphi(a,f)\,\psi + \varphi(a,f)\,\chi, \\
\varphi(ca + b, f)\,\psi = c\,\varphi(a,f)\,\psi + \varphi(b,f)\,\psi, \qquad
\varphi(a, cf + g)\,\psi = c\,\varphi(a,f)\,\psi + \varphi(a,g)\,\psi .
\end{gathered}
$$

These linearity requirements are the only conditions. Every smeared field maps
$D$ into $D$, so all of them act on the one common domain $D$. Nothing more is
assumed: $D$ need not be closed or dense in $H$, $\Omega$ need not have norm
$1$, the maps $\varphi(a,f)$ need not be continuous, and no continuity in $f$ is
required. Density of $D$, normalization of $\Omega$, cyclicity of the vacuum and
temperedness are imposed separately, by the [domain axioms](domain-axioms.md).

## Depends on

- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Schwartz test functions](../spacetime/schwartz-test-functions.md)

## Sources

- [PublicTheory.lean ledger: field system](../../sources/public-theory.md#field-system)
