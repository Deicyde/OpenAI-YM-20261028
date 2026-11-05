import YM.Next.FREE_KERNELS.Calendar
import YM.Push.PRICE_COMPILER.Compiler



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Delivering FlatBill.Estimates

Realization (using the linear kernel theorems of `YM.Next.Free`) of the INPUT ESTIMATES cut
of `YM.Push.PriceCompiler` (see PRICE_COMPILER/Pin and PRICE_COMPILER/Compiler).
Quotes indexed by smoothing stage BEFORE all L. In particular no dependence on N-m.
The real/Hermitian and strip estimates and the `Bleeps` identity used in the repair
come from the *same* per-stage quotes and Horizon that served RRack. No changes to H or
A₀/T on the way to the funded repaired Horizon, no dropped harmonic modes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Pressure
open Push.PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- Dummy stage prices may be nonpositive in MapPrices; FlatBill asks for
strict positivity even there. Inflate on every stage, harmless for Rack. -/
def positiveQuote (X : MapPrices) (i : ℕ) : FlatBound where
  width := X.α i
  lower := X.η i
  price := max 1 (X.Ω i)
  width_pos := X.alpha_pos i
  lower_pos := X.eta_pos i
  price_pos := lt_of_lt_of_le zero_lt_one (le_max_left ..)

/-- PriceCompiler sends j→i (j fine = J of m+1). Same-stage and next/prev
transitions already paid at X, in this index convention. -/
def flatOf (X : MapPrices) : FlatBill :=
  ⟨positiveQuote X, fun j _ => positiveQuote X j⟩

lemma estimates_of_rack {a : Levels G} {B : Horizon a} {X : MapPrices} (h : Rack a X B) :
    (flatOf X).Estimates a B := by
  have hx i : X.Ω i ≤ (positiveQuote X i).price := le_max_right ..
  exact {
    covers := fun N m hm => covered_mono (h.covers N m hm) le_rfl (hx _)
    trace := fun N m hm n => floor_mono (h.traces N m hm n) le_rfl (hx _)
    oath := h.oath
    top := h.top
    crosses := h.crosses
    give := fun N m hm => donate_mono (h.legs N m hm) le_rfl (hx _)
    creak := fun N m hm => by
      obtain ⟨Y,hy,hr,hB⟩ := h.creak N m hm
      exact ⟨Y,strip_mono hy le_rfl (hx _),hr,hB⟩ }

/-- With These numerical quotes, the physical input is delivered. At *any*
Levels honoring the two very specific ex ante demands of `Free.Credit` (on direct
coefficient and block lengths) and holding the actual KernelChoices. Keep the
original X and Present receipts alongside the compiler version. `pledges`
provides Catalog for any given KernelChoices (no Gauge constraints!). -/
theorem delivered {K : KernelChoices} {X : MapPrices} {l γ b} (hX : Next.Free.Catalog K X l γ b)
    (a : Levels G) (he : a.clock.kernel=K) (h : Next.Free.Credit a γ b) :
    ∃ B : Horizon a, Rack a X B ∧ Next.Free.Present a B l ∧ (flatOf X).Estimates a B := by
  obtain ⟨B,hB,hP⟩ := Next.Free.shelves a X l γ b (he.symm ▸ hX) h
  exact ⟨B,hB,hP,estimates_of_rack hB⟩

/-- Narrow consumer interface which also permits Horizon variants that keep
actual linear/Schedule prices and harmonic requirements but come from a variant Bed
construction. E.g. a variation of the Free.pledges l budget at top. -/
structure Motor (P : Before) (a : Levels G) (V : Horizon a) : Prop where
  finalCosts : V.Suffices (P.frozen G)
  swears N m n : m ≤ N → Bid.Sworn (V.H N m) n G

section Permit
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)}
  {M : Preparations P D} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
  {a : Levels G}

/-- Joint physical receipt for downstream consumers; SAME Levels and SAME two
horizons. In particular can call `Permit.called`/`.tickets` on the final one,
or use higher-difference results of Free on these. -/
structure Wired (P : Before) (a : Levels G) (X : MapPrices) (l : ℕ → ℝ) (B V : Horizon a) : Prop where
  numbers : P.flat.Estimates a B
  raw : Rack a X B
  derived : Next.Free.Present a B l
  stayed : Bid.Retained V B
  finalCosts : V.Suffices (P.frozen G)
  sameTrain : Next.Free.Present a V l
  swears N m n : m ≤ N → Bid.Sworn (V.H N m) n G



/-- Consumer of Permit's numerical issuance. No analytic oracle argument
(including no grants argument, nor RLevel glue, nor L-independent estimates
as arguments). Need only honors of these Before projections and floors. Proof
gets FlatBill.Estimates on actual Horizon from Free on EXACTLY these Levels,
then uses Permit.kernel rather than a posteriori pinning. Before's relaxation
worked because freezing depends only on direct and freezing is *late enough*
for this direct to be chosen from Catalog (no using cost that would already
need prices). All obligations here for ALL Rolls qualifying the prices; see
`Order` for making the Before and compiler-and-producer issuance. -/
theorem wire (p : Permit M I a) {K : KernelChoices} {X : MapPrices} {l γ b}
    (hX : Next.Free.Catalog K X l γ b) (hk : P.kernelChoice G = K)
    (hF : P.flat = flatOf X)
    (hC : ∀ i, P.first ≤ i → (P.clip i).direct ≤ γ i)
    (hL : ∀ i, P.first ≤ i → b i ≤ f i) :
    ∃ B V : Horizon a, Wired P a X l B V := by
  have he : Next.Free.Credit a γ b := Next.Free.credit_from_sheet p.paid γ b hC hL
  obtain ⟨B,hR,hP,hB⟩ := delivered hX a (p.paid.kernel.trans hk) he
  rw [← hF] at hB
  obtain ⟨V,hV,hS⟩ := p.kernel hB
  obtain ⟨hm,hW⟩ := Next.Free.retained_presents a X B V hP hR hV
  exact ⟨B,V,hB,hR,hP,hV,hS,hm,hW⟩

end Permit
end YM.UVNext.PricedKernels
