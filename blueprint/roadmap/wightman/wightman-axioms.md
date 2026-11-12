# The Wightman axioms

Let $H$ be a Hilbert space, with inner product $\langle \cdot, \cdot \rangle$
conjugate-linear in its first argument, $L$ a space of field labels, and $T$ a
Wightman theory on $H$ and $L$. Write $(D, \Omega, \varphi)$ for its field
system, made of the domain $D \subseteq H$, the vacuum $\Omega \in D$ and the
smeared fields $\varphi(a, f) : D \to D$ for labels $a \in L$ and Schwartz
test functions $f$ on $\mathbb R^4$; $a \mapsto a^\dagger$ for its
conjugate-linear map on $L$; $U(x)$, for $x \in \mathbb R^4$, for the
operators of its translation representation; $E(A)$, for
$A \subseteq \mathbb R^4$, and $\mu_\psi$, for $\psi \in H$, for the operators
and the measures of its energy–momentum measure; and, for each symmetry $g$
of its Poincaré action, $V(g)$ for the operator on $H$, $a \mapsto g \cdot a$
for the map on labels and $f \mapsto g \cdot f$ for the map on Schwartz test
functions.

The theory $T$ **satisfies the Wightman axioms** when it satisfies each of the
following four conditions.

1. *Axiom W0, spectrum condition and unique vacuum:* for every $\psi \in H$
   and every $b \in \mathbb R^4$,
   $\int_{\mathbb R^4} e^{\,i\, p \cdot b}\, d\mu_\psi(p) = \langle \psi, U(b)\,\psi \rangle$,
   where $p \cdot b$ is the Euclidean inner product of $\mathbb R^4$;
   $E(\mathbb R^4 \setminus \overline V_+) = 0$, where
   $\overline V_+ = \{ p \in \mathbb R^4 : (p_0^2 + p_1^2 + p_2^2)^{1/2} \le p_3 \}$
   is the closed forward light cone, time being the last coordinate; and every
   $\psi \in H$ with $U(x)\,\psi = \psi$ for all $x \in \mathbb R^4$ is a
   complex multiple of $\Omega$.
2. *Axiom W1, fields on a common dense domain:* the field system satisfies the
   domain axioms, and it satisfies the adjoint axiom for the map
   $a \mapsto a^\dagger$.
3. *Axiom W2, Poincaré covariance:* $e \cdot a = a$ and
   $(gh) \cdot a = g \cdot (h \cdot a)$ for all symmetries $g, h$ and every
   label $a$, where $e$ is the distinguished element and $gh$ the product of
   symmetries; and, for every symmetry $g$, the operator $V(g)$ maps $D$ into
   $D$, $V(g)\,\Omega = \Omega$, and
   $V(g)\big(\varphi(a, f)\,\psi\big) = \varphi(g \cdot a,\, g \cdot f)\big(V(g)\,\psi\big)$
   for every label $a$, Schwartz test function $f$ and $\psi \in D$.
4. *Axiom W3, locality:* for all labels $a, b$, all spacelike separated
   Schwartz test functions $f_1, f_2$ and every $\psi \in D$,
   $\varphi(a, f_1)\,\varphi(b, f_2)\,\psi = \varphi(b, f_2)\,\varphi(a, f_1)\,\psi$.
   Here $f_1$ and $f_2$ are spacelike separated when $v = x - y$ satisfies
   $v_3^2 - (v_0^2 + v_1^2 + v_2^2) < 0$ for every point $x$ of the closed
   support of $f_1$ and every point $y$ of the closed support of $f_2$.

Each axiom is stated in full in its own article. The Wightman axioms are a
condition on $T$ and add no data; they consist of these four conditions, each
required separately, and of nothing more.

## Depends on

- [Wightman theory data](../wightman/wightman-theory.md)
- [Hilbert space and bounded operators](../wightman/hilbert-space.md)
- [Field labels](../wightman/field-labels.md)
- [Axiom W0: spectrum condition and unique vacuum](../wightman/axiom-w0.md)
- [Axiom W1: fields on a common dense domain](../wightman/axiom-w1.md)
- [Axiom W2: Poincaré covariance](../wightman/axiom-w2.md)
- [Axiom W3: locality](../wightman/axiom-w3.md)

## Sources

- [PublicTheory.lean ledger: Wightman axioms](../../sources/public-theory.md#wightman-axioms)
- [Upstream description: Wightman reconstruction](../../sources/upstream-readme.md#wightman-reconstruction)
