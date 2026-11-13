# Shell identity for word expectations

Spacetime axes are numbered $0, 1, 2, 3$, with time the axis $3$; for
$x \in \mathbb R^4$, $t(x) = x_3$ is its time and
$\vec x = (x_0, x_1, x_2)$ its spatial part.

**Data.** Fix a Wilson family and let $S$ be a Euclidean correlation table
for its tokens, with quotient label spaces $F_d$ and common label space
$\mathbb F$; for $\beta \in F_d$, $[\beta]_d \in \mathbb F$ is its image.
Let $W$ be boundary
distributions over $S$: for every $n$, a complex-multilinear map
$v \mapsto W_n(v)$ from $\mathbb F^n$ to tempered distributions on
$(\mathbb R^4)^n$. Fix

- rotations of $S$, with generator maps $\lambda_d$ from the skew-symmetric
  real $4 \times 4$ matrices to the complex-linear maps of $F_d$;
- derivative maps $\partial^{(d)}_i : F_d \to F_{d+1}$, complex linear, for
  every degree $d$ and axis $i$;
- a stress tensor $T = (T_{ab})$ of $S$, $T_{ab} \in F_4$;
- a [Killing field](killing-field.md) $K = (k, V)$, with real value
  $K(x) = k + Vx$, its component $K^i(x)$ along the axis $i$, and
  [Killing-weighted tests](killing-weighted-tests.md) $K^i h$,
  $(K^i h)(x) = K^i(x)\, h(x)$;
- a Schwartz function $f \in \mathcal S(\mathbb R)$ of time and a Schwartz
  function $g \in \mathcal S(\mathbb R^3)$ of space, with product test
  $(g \otimes f)(x) = g(\vec x)\, f(t(x))$;
- a graded label $B = (d, \beta)$ and a Schwartz function
  $m \in \mathcal S(\mathbb R^4)$.

Let $\zeta_3 = -\mathrm i$ and $\zeta_i = 1$ for spatial $i$ be the Wick factors
of the [Minkowski stress labels](minkowski-stress-field.md), and let
$\Sigma^{(d)}_K = \lambda_d(A) - \mathrm i\,\lambda_d(A')$ be the infinitesimal
label action of $K$ in degree $d$, where $\theta = \mathrm{diag}(1, 1, 1, -1)$,
$A = \tfrac12(V - V^{\mathsf T})$, $C = \tfrac12(V + V^{\mathsf T})$ and
$A' = \tfrac12\big(C\theta - (C\theta)^{\mathsf T}\big)$.

**Words and their expectations.** A letter is a pair $(c, h)$ of a label
$c \in \mathbb F$ and a Schwartz function $h \in \mathcal S(\mathbb R^4)$, and
a word is a finite sequence of letters; juxtaposition of words and letters
denotes concatenation. The **expectation** of a word
$w = \big((c_1, h_1), \dots, (c_n, h_n)\big)$ under $W$ is

$$
\mathcal E(w) = W_n(c_1, \dots, c_n)\big(h_1 \otimes \dots \otimes h_n\big),
$$

where $h_1 \otimes \dots \otimes h_n$ is the joint test function whose value
at $(y_1, \dots, y_n) \in (\mathbb R^4)^n$ is $h_1(y_1) \cdots h_n(y_n)$ (for
the empty word, the constant function $1$ on the one-point space
$(\mathbb R^4)^0$). The test functions of a word need not have compact support.

**The identity.** Put

$$
\ell = \big([\beta]_d,\ m\big), \qquad
r_i = \big([T_{3i}]_4,\ K^i (g \otimes f)\big) \quad (i = 0, 1, 2, 3).
$$

For words $a$ and $b$, the **shell identity** holds for $a$ and $b$ when

$$
\sum_{i=0}^{3} \zeta_i\, \mathcal E\big(a\, \ell\, r_i\, b\big) - \sum_{i=0}^{3} \zeta_i\, \mathcal E\big(a\, r_i\, \ell\, b\big)
= \mathcal E\Big(a\, \big([\Sigma^{(d)}_K \beta]_d,\ m\big)\, b\Big)
+ \sum_{i=0}^{3} \zeta_i\, \mathcal E\Big(a\, \big([\partial^{(d)}_i \beta]_{d+1},\ K^i m\big)\, b\Big).
$$

On the left, the stress letter $r_i$ stands immediately after the letter
$\ell$ in the first sum and immediately before it in the second. The shell
identity is a condition on $a$ and $b$; it adds no data.

## Depends on

- [Killing fields](killing-field.md)
- [Minkowski stress labels and the stress field](minkowski-stress-field.md)
- [Test functions weighted by a Killing field](killing-weighted-tests.md)

## Sources

- [YM/EveryPhase ledger: Court](../../sources/every-phase.md#court)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
