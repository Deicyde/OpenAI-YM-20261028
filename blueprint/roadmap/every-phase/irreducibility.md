# Irreducibility in every phase

Let $\mathcal F$ be a record for a Wilson family, an extraction and a limit
table $S$, with phase space $X$, whose points $s$ are called characters, and
let $L$ be a family of reconstructions over the phases for $\mathcal F$. For
a character $s \in X$, write $\mathfrak W_s$ for the Wightman data of $L$ at
$s$, $H_s$ for its Hilbert space and $1$ for the identity operator of $H_s$.

**Theorem.** For every record $\mathcal F$, every family of reconstructions
$L$ for $\mathcal F$, every character $s \in X$ and every bounded
complex-linear operator $B : H_s \to H_s$, the following are equivalent:

1. $B$ is weakly central for $\mathfrak W_s$: for every label $a$ of the
   common label space, every Schwartz test function
   $f \in \mathcal S(\mathbb R^4)$ and all vectors $\chi, \psi$ of the field domain
   $D_s$ of $\mathfrak W_s$,

    $$
    \big\langle \varphi_s(a^\star, \bar f)\, \chi,\ B \psi \big\rangle
    = \big\langle \chi,\ B\, \varphi_s(a, f)\, \psi \big\rangle ,
    $$

    where $\varphi_s$ are the smeared fields and $a \mapsto a^\star$ the star
    operation of $\mathfrak W_s$, and $\bar f$ is the complex conjugate of
    $f$;
2. $B = c \cdot 1$ for some complex number $c$.

The statement holds at every character, with no exceptional set, and for
every family of reconstructions. Nothing is assumed about how $B$ acts on
$D_s$.

## Depends on

- [Family of reconstructions over the phases](reconstruction-family.md)
- [Weakly central bounded operators](weakly-central-operators.md)

## Proof depends on

- [Heat operators pulled back along a bounded map](boundary-heat-semigroup.md)
- [Finite sums of words and their vectors](sums-of-words.md)
- [Zero-energy and low-energy regions](energy-regions.md)
- [No exceptional phase: zero energy is the vacuum](zero-energy-projection-vacuum.md)

## Sources

- [YM/EveryPhase ledger: Irreducible](../../sources/every-phase.md#irreducible)
- [Armstrong's informalization: unit V.3](../../sources/armstrong.md#unit-v3-reconstruction-for-every-phase)
