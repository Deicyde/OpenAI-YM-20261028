import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.Further.THRESHOLD_SOURCE_RESTART.Intake
/-!
# Licensing occurrence estimates at the unscaled kernel cuts

Finite derivations. A way to expose analytically meaningful per-entry
rather than final summed hypotheses. In particular marked primitives are
paid from input marked donors; cannot postulate a root bill on the target
atoms. Repetitions can be paid before assembly; distinguishes numbered
(e.g. repeated log estimates with spans) and unnumbered with actual
repeat multiplicities. No `supportExponent` reserve implicitly from
previous cut, need price whole exponents through every application.

No claim that the physical operations meet these tests (or even that the
committed incoming and outgoing support costs in a given schedule will
fit together). For example, in a first-system implementation this permits
asking for projected source variants per donor, unmarked trigger/packet
hits, then product integral bounds also using those, then log occurrence
bounds, selling just the marked portion for the exponent, multiple such
operations for pricing the full hard coefficients. Need a licence BEFORE
the actual kernel consumer here. The syntax of the licence is *only*
about prices on the indicated occurrence lists; asserting provenance in
physics, justification of sharing, etc., would require proofs, including
for instantiating the kernel identity separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter Set MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi Merger Repeated LogTerms
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

section book
variable {α β V : Type*} {m n : Side} {v : α → Finset V} {X : α → Support n} {M : ℕ} {A a b c : ℝ}
    {f : α → ℝ} {w : V → ℝ}



/-- Picking charged occurrences from a market. Cannot change their
markers, or forget costs for stencils. Also permits extraction of a gain
from a pre-boosted market (e.g. forcing at least two parents, or an
unmarked partner). -/
structure Redeem (v : α → Finset V) (X : α → Support n) (f : α → ℝ)
    (s : β → Finset V) (Y : β → Support n) (g : β → ℝ) (ρ : ℝ) : Prop where
  positive i : 0 ≤ g i
  access : ∃ k : β → α, InjOn k {i|0<g i} ∧
    ∀ i,0<g i → s i = v (k i) ∧ Y i ⊆ X (k i) ∧ g i ≤ ρ * f (k i)

variable {s : β → Finset V} {Y : β → Support n} {g : β → ℝ}




end book

/-!
Licence constants always numeric. Unmarked vertex input is still a
*true site hit* test (not generated here). To demonstrate physical use
retain separate licences for classes priced differently, e.g. for the
SOLE-marker-occurrence principal export put a pre-L `q`, for a multi-
occurrence array can spend much higher prices with a later rebate.
Quantify over all `e` of input array in the application to prevent
crediting some fictitious expenditures on zeroes.
-/
section market
variable {G : Gauge} {V : Type*} [DecidableEq V] [Fintype V] {R : Census V}
variable {n m : Side} {P : Rep G n} (M : Bands R P)

inductive Licence (m : Side) (e : Donors V → ℝ) (C : Capital) (B μ : ℕ)
    (o : V → Site m) : {α : Type} → (α → Finset V) → (α → Support m) →
    (α → ℝ) → ℝ → ℝ → ℝ → Prop
  | sail {α : Type} {t : α → Finset V} {Y : α → Support m} {g : α → ℝ} {p a : ℝ}
      (h : Route (fun i => (ticket M i).val) (home M) P.p.B C.a e o t Y B (a+1) g p)
      (hp : 0 ≤ p) :
      Licence m e C B μ o t Y g a (p*C.total) (μ*siteFactor B*(p*C.total))
  | vacuum {α} {Y : α → Support m} {g : α → ℝ} {a c : ℝ} (hp : ∀ i,0 ≤ g i) (h : Ac.Hit Y B g a c) :
      Licence m e C B μ o (fun _ => ∅) Y g a 0 c
  | either {α β} {v : α → Finset V} {X f} {t : β → Finset V} {Y g} {a b b' c c' : ℝ}
      (h : Licence m e C B μ o v X f a b c) (H : Licence m e C B μ o t Y g a b' c') :
      Licence m e C B μ o (Sum.elim v t) (Sum.elim X Y) (Sum.elim f g) a (b+b') (c+c')
  | append {α} {v : α → Finset V} {X f g a b c b' c'}
      (h : Licence m e C B μ o v X f a b c) (H : Licence m e C B μ o v X g a b' c') :
      Licence m e C B μ o v X (fun i => f i+g i) a (b+b') (c+c')
  | reserve {α} {v : α → Finset V} {X f g a b c a' b' c'}
      (h : Licence m e C B μ o v X f a b c) (he : ∀ i,0≤g i) (hi : ∀ i,g i ≤ f i)
      (hz : a' ≤ a) (hb : b ≤ b') (hc : c ≤ c') : Licence m e C B μ o v X g a' b' c'
  | claim {α β} {v : α → Finset V} {X f} {t : β → Finset V} {Y g p a b c}
      (h : Licence m e C B μ o v X f a b c) (h' : Redeem v X f t Y g p) (ha : 0 ≤ a) (hp : 0 ≤ p) :
      Licence m e C B μ o t Y g a (p*b) (p*c)
  | assemble {α β} {v : α → Finset V} {X f} {t : β → Finset V} {Y g} {a b c C' : ℝ}
      (h : Licence m e C B μ o v X f (a+1) b c) (he : Display v X t Y f g C')
      (hg : ∀ i,0 ≤ g i) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hC : 0 ≤ C')
      (H : 8*((B+B+1:ℕ):ℝ)^4*c ≤ 1) : Licence m e C B μ o t Y g a (C'*(2*b)) (C'*(2*c))
  | tuple {α} {v : α → Finset V} {X f g a b c} {coef : Tuple α → ℝ}
      (h : Licence m e C B μ o v X f (a+1) b c)
      (he : ∀ i,0 ≤ g i ∧ (0 < g i → legal v i ∧ g i ≤ Repeated.worth f coef i))
      (hp : ∀ i, 0 ≤ coef i ∧ ∀ r, coef i ≤ (Mayer.spans (Repeated.overlap X i.2) r).card)
      (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : 8*((B+B+1:ℕ):ℝ)^4*c ≤ 1) :
      Licence m e C B μ o (nameSet v) (numbered X) g a (2*b) (2*c)

variable {M} {e : Donors V → ℝ} {C : Capital} {B μ : ℕ} {o : V → Site m} {α : Type}
variable {v : α → Finset V} {X : α → Support m} {g : α → ℝ} {a b c : ℝ}



omit [Fintype V] [DecidableEq V] in
lemma tariff_glue {α β} (t : α → Finset V) (u : β → Finset V) (f : α → ℝ) (g : β → ℝ)
    (w : V → ℝ) : Sum.elim (tariff w t f) (tariff w u g) = tariff w (Sum.elim t u) (Sum.elim f g) :=
  funext (Sum.rec (fun _ => rfl) fun _ => rfl)


end market
end YM.Further.ThresholdSourceRestart
