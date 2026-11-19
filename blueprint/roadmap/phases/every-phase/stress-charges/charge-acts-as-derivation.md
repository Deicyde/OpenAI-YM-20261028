# Charges act as derivations on sums of words

Fix a Wilson family and let $S$ be a Euclidean correlation table for its
tokens, with quotient
label spaces $F_d$, common label space $\mathbb F$, and
$[\beta]_d \in \mathbb F$ the image of $\beta \in F_d$; a graded label is a
pair $(d, \beta)$ with $\beta \in F_d$. Let $\mathfrak W$ be Wightman data
over $S$, with domain $D$ and smeared fields $\varphi(a, h) : D \to D$, let
$T$ be a stress tensor of $S$, and let $R$ be rotations of $S$. The support
$\operatorname{supp} h$ of a function is the closure of the set where it is
not zero. Letters, words and finite sums of words are as in
[Finite sums of words and their vectors](../sums-of-words.md); in this article
a letter is written $(a, h)$ with $a \in \mathbb F$ and
$h \in \mathcal S(\mathbb R^4)$, and the coefficients of a sum are written
$\gamma_j$. The operator of a word $w = ((a_1, h_1), \dots, (a_n, h_n))$ is
$\varphi(w) = \varphi(a_1, h_1) \cdots \varphi(a_n, h_n)$, the identity of $D$
for the empty word, and the operator of a sum
$A = ((\gamma_1, w_1), \dots, (\gamma_r, w_r))$ is
$\varphi(A) = \sum_j \gamma_j\, \varphi(w_j)$, zero for the empty sum.

**Choices of representatives.** A **choice of representatives** is a map $p$
that assigns to every label $a \in \mathbb F$ a graded label
$p(a) = (d_a, \beta_a)$ whose image is $a$: $[\beta_a]_{d_a} = a$.

**Support in a set.** Let $\mathcal O \subseteq \mathbb R^4$. A word is
**supported in** $\mathcal O$ when the test function of each of its letters
has support contained in $\mathcal O$, and a finite sum of words is supported
in $\mathcal O$ when each of its words is.

**Derivation of a word.** Fix a [Killing field](../stress-current/killing-field.md) $K$, the
rotations $R$ and a choice of representatives $p$, and let
$\delta_K(d, \beta; h)$ be the
[infinitesimal transformation](infinitesimal-field-transformation.md) of the
field of $(d, \beta)$ smeared with $h$, built with the infinitesimal rotations
of $R$. The **derivation** of a word is the complex-linear map
$\delta_{K,p}(w) : D \to D$ defined by recursion on the word:
$\delta_{K,p}$ of the empty word is $0$, and

$$
\delta_{K,p}\big((a, h)\, w\big) = \delta_K\big(p(a); h\big)\, \varphi(w) + \varphi(a, h)\, \delta_{K,p}(w),
$$

where $(a, h)\, w$ is the word with first letter $(a, h)$ followed by the
letters of $w$. Unfolded, for $w = ((a_1, h_1), \dots, (a_n, h_n))$,

$$
\delta_{K,p}(w) = \sum_{k=1}^{n} \varphi(a_1, h_1) \cdots \varphi(a_{k-1}, h_{k-1})\;
\delta_K\big(p(a_k); h_k\big)\;
\varphi(a_{k+1}, h_{k+1}) \cdots \varphi(a_n, h_n):
$$

each factor in turn is replaced by its infinitesimal transformation, computed
with the representative $p(a_k)$ of its label, and the other factors keep
their order. The derivation of a finite sum of words
$A = ((\gamma_1, w_1), \dots, (\gamma_r, w_r))$ is

$$
\delta_{K,p}(A) = \sum_{j=1}^{r} \gamma_j\, \delta_{K,p}(w_j),
$$

zero for the empty sum.

**The condition.** $\mathfrak W$, $T$ and $R$ satisfy the condition that
**charges act as derivations** when, for every choice of representatives $p$,
every compact set $\mathcal O \subseteq \mathbb R^4$, every
[admissible time profile](admissible-time-profile.md) $f$, every
[admissible spatial cutoff](admissible-spatial-cutoff.md) $g$ for
$\mathcal O$ and $f$, every finite sum of words $A$ supported in $\mathcal O$
and every Killing field $K$, the [commutator action](stress-charge.md) of the
stress charge $\mathcal Q_K(f, g)$ of $\mathfrak W$, $K$ and $T$ on the
operator of $A$ is the derivation of $A$:

$$
\mathrm i\,\Big[\mathcal Q_K(f, g),\ \varphi(A)\Big] = \delta_{K,p}(A)
$$

as complex-linear maps $D \to D$. The condition is required for every choice
of representatives.

## Depends on

- [Killing fields](../stress-current/killing-field.md)
- [Admissible time profile](admissible-time-profile.md)
- [Admissible spatial cutoff](admissible-spatial-cutoff.md)
- [Stress charge and the commutator action](stress-charge.md)
- [Infinitesimal Poincaré transformation of a field](infinitesimal-field-transformation.md)
- [Finite sums of words and their vectors](../sums-of-words.md)

## Sources

- [YM/EveryPhase ledger: Implement](../../../../sources/every-phase.md#implement)
- [Armstrong's informalization: unit V.3](../../../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
