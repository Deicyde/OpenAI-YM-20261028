# Finite sums of words and their vectors

Fix a Wilson family and a Euclidean correlation table $S$ for its tokens, and
let $\mathbb F$ be the common label space of $S$: the complex linear span (the
sum) of the images of the quotient label spaces $F_d$ of all degrees
$d \in \mathbb N$ in the space of complex-valued functions of exterior data
(further labels placed at further points, all points distinct), where a class
is sent to its correlations in $S$ against these data. Each $F_d$ maps
injectively onto its image. Let $\mathcal S(\mathbb R^4)$ be the complex vector space of
Schwartz test functions $f : \mathbb R^4 \to \mathbb C$.

A **letter** is a pair $(a, f)$ of a label $a \in \mathbb F$ and a Schwartz
test function $f \in \mathcal S(\mathbb R^4)$. A **word** is a finite sequence
of letters,

$$
w = \big((a_1, f_1), (a_2, f_2), \dots, (a_m, f_m)\big), \qquad m \in \mathbb N,
$$

the empty word ($m = 0$) included. A **finite sum of words** for $S$ is a finite
sequence of pairs, each made of a complex coefficient and a word,

$$
A = \big((c_1, w_1), (c_2, w_2), \dots, (c_n, w_n)\big), \qquad c_k \in \mathbb C,\ n \in \mathbb N,
$$

the empty sequence ($n = 0$) included. A finite sum of words is formal data:
the order of its entries counts, an entry may be repeated, a coefficient may be
$0$, and no two different sequences are identified.

A **field system** for $S$ consists of a Hilbert space $H$, whose inner product
$\langle \cdot, \cdot \rangle$ is conjugate-linear in its first argument; a
complex linear subspace $D \subseteq H$, the domain; a vacuum vector
$\Omega \in D$; and, for every label $a \in \mathbb F$ and every Schwartz test
function $f$, a complex-linear map $\varphi(a, f) : D \to D$ that depends
complex-linearly on $a$ and complex-linearly on $f$.

Fix a field system. The **operator of a word** $w$ as above is the composite

$$
\varphi(w) = \varphi(a_1, f_1)\, \varphi(a_2, f_2) \cdots \varphi(a_m, f_m) : D \to D,
$$

in which $\varphi(a_m, f_m)$ is applied first; the operator of the empty word is
the identity map of $D$. The **operator of a finite sum of words** $A$ as above
is the complex-linear map

$$
\varphi(A) = \sum_{k=1}^{n} c_k\, \varphi(w_k) : D \to D,
$$

the zero map of $D$ when $A$ is the empty sequence. The **vector** of $A$ is

$$
A\Omega = \varphi(A)\, \Omega \in D,
$$

regarded as a vector of the Hilbert space $H$.

## Depends on

This node has no prerequisites.

## Sources

- [YM/EveryPhase ledger: Polynomials](../../../sources/every-phase.md#polynomials)
- [Armstrong's informalization: unit V.3](../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
