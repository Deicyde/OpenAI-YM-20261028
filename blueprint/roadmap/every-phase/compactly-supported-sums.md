# Compactly supported sums of words

Fix a Wilson family and a Euclidean correlation table $S$ for its tokens, with
common label space $\mathbb F$. A function $f : \mathbb R^4 \to \mathbb C$ has
**compact support** when the closure of $\{x \in \mathbb R^4 : f(x) \neq 0\}$
is compact.

A word $w = \big((a_1, f_1), \dots, (a_m, f_m)\big)$, with labels
$a_j \in \mathbb F$ and Schwartz test functions
$f_j \in \mathcal S(\mathbb R^4)$, is **compactly supported** when every test
function in it has compact support:

$$
f_j \text{ has compact support for every } j = 1, \dots, m .
$$

A finite sum of words
$A = \big((c_1, w_1), \dots, (c_n, w_n)\big)$ is **compactly supported** when
every word in it is compactly supported:

$$
w_k \text{ is compactly supported for every } k = 1, \dots, n .
$$

The condition is on the formal sequence: it applies to every entry, whatever
its coefficient, an entry with coefficient $c_k = 0$ included. The labels are
unrestricted. The empty word and the empty sum are compactly supported. Every
Schwartz test function is smooth, and every smooth compactly supported function
$\mathbb R^4 \to \mathbb C$ is a Schwartz test function, so the test functions
allowed here are exactly the smooth compactly supported functions
$\mathbb R^4 \to \mathbb C$.

## Depends on

- [Finite sums of words and their vectors](sums-of-words.md)

## Sources

- [YM/EveryPhase ledger: Polynomials](../../sources/every-phase.md#polynomials)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
