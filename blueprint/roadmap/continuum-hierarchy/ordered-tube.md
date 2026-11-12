# Ordered tube

For a natural number $n$, zero included, let $\mathbb C^n$ be the space of
complex times $z = (z_0, \dots, z_{n-1})$, the $n$-tuples of complex numbers
indexed by $k \in \{0, \dots, n-1\}$. The **ordered tube** is the subset

$$
\mathcal T_n = \big\{ z \in \mathbb C^n :
\operatorname{Im} z_k < \operatorname{Im} z_l
\text{ for all } k, l \in \{0, \dots, n-1\} \text{ with } k < l \big\}
$$

of $\mathbb C^n$: the complex times whose imaginary parts strictly increase
with the index,
$\operatorname{Im} z_0 < \operatorname{Im} z_1 < \dots < \operatorname{Im} z_{n-1}$.
The source calls it "the tube of complex times with strictly ordered
imaginary parts". Only the imaginary parts are constrained; the real parts
are arbitrary. For $n = 0$ and $n = 1$ there is no pair of indices $k < l$,
so the condition is empty and $\mathcal T_n = \mathbb C^n$.

## Depends on

- [Complex times and spatial positions](continuation-variables.md)

## Sources

- [ChallengeSpec.lean ledger: ordered tube](../../sources/challenge-spec.md#ordered-tube)
