import YM.Extra.MULTISOURCE_BOUNDS.Delays
import YM.Next.FLUCTUATIONS.Grants

/-!
# Pricing both plateaus before issuing the marker-width tests

Theorems of numerical compatibility on arbitrary sufficiently prepriced
profiles, simultaneous with the pressure Ringing grant (Next.Fluctuations)
and the final volume-root `Stock.Priced`. Includes a way of initially buying
the extra factorial cost for I04 if not already included. Other stage costs
(e.g. to actually earn the raw weighted step or to have an appropriate cutoff
gas alphabet with the stronger K exponent, or even to construct `Levels` and
`C.Makes`) are NOT covered by fiat. Extra finite bids/delays allowed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Set Function Filter Lattice RG RG.Supply Source Wilson Overlay Marker Labels Finset Pressure Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {F : Frames G}

namespace Scope

def ask (s : Scope) (j : ℕ) (P : Stage) := Nat.ceil (
    20*(P.supportExponent+s.inflate j)*tilePrice (s.expand j) / P.supportExponent)

theorem shape (s : Scope) {j : ℕ} {P : Stage} {L : Side} (h : s.ask j P ≤ L.val) :
    20*(P.supportExponent + s.inflate j)*tilePrice (s.expand j) ≤ (L.val:ℝ)*P.supportExponent :=
  (div_le_iff₀ P.price_pos).mp ((Nat.le_ceil _).trans (by exact_mod_cast h))

end Scope

/-- Joint recipe of numerical gates, partition-root Tabs included. All depths,
not `∀ᶠ` depths on one period. Further requirements of the source-step method
(including attaining raw support/derivative estimates from the integration)
might need larger bids. Stage `m` is the coarse side of the transition.
-/
structure Prepared (s : Scope) (t : Tariff) (T : Sections F) (a : Levels G) : Prop where
  tabs : Stock.Tabs a
  factorial i : ((a.params i).order.factorial:ℝ) ≤ (a.params i).columns
  here i : Ample T (a.params i) (s.markers (a.clock.J i)) (a.clock.J i) (a.clock.hatBeta i)
  across m : let j := a.clock.J (m+1); let i := a.clock.J m
    steep F (a.params (m+1)) (a.S.block m) t j (a.clock.hatBeta (m+1)) ≤
      Real.exp ((a.clock.coverSize m:ℝ)/(64*s.markers i))
  shapes m : s.ask (a.clock.J (m+1)) (a.params (m+1)) ≤ (a.S.block m).val

variable {p : Sheet G} {w : Rolls p} {P : Protection w} {V : Delays P}

/-- Post-L obligations can be paid prior to actually constructing Levels
(step size at `w.L j`, j on FINE side). -/
structure Gated (V : Delays P) (s : Scope) (t : Tariff) (T : Sections F) : Prop where
  priced : Stock.Priced V
  gates i j x : i ≤ j → j ≤ i+1 → V.betaEntry j ≤ x →
    Ample T (p.profile i) (s.markers i) i x ∧ steep F (p.profile j) (w.L j) t j
        (x + G.slopeConstant * Real.log (w.L j).val) ≤ Real.exp ((Stock.scaleB x:ℝ)/(64*s.markers i))

lemma raise_gates (H : G.Simple) (V : Delays P) (s : Scope) (t : Tariff) (T : Sections F) :
    ∃ W : Delays P, W.shells=V.shells ∧ W.growth=V.growth ∧ V.betaEntry ≤ W.betaEntry ∧
      V.scaleEntry ≤ W.scaleEntry ∧ Gated W s t T := by
  obtain ⟨V',h,h',hs,hg,hp⟩ := Stock.raises V H
  have he i j := (ample_late T (p.profile i) (s.markers i) i).and
    (steep_late (L:=F) (p.profile j) (w.L j) t j (s.markers i) (s.markers_pos i) (G.slopeConstant*Real.log (w.L j).val))
  choose b hb using fun i j => eventually_atTop.mp (he i j)
  let W : Delays P := { V' with betaEntry := fun j => max (V'.betaEntry j) (max (b j j) (b (j-1) j)) }
  have hy : V'.betaEntry ≤ W.betaEntry := fun j => le_max_left ..
  refine ⟨W,hs.symm,hg.symm,h.trans hy,h', ⟨fun j hj x hx => hp.1 j hj x ((hy j).trans hx),hp.2⟩,?_⟩
  intro i j x hi hj hx
  apply hb i j x (le_trans ?_ hx)
  apply le_max_of_le_right
  rcases eq_or_lt_of_le hi with hi|hi
  · subst i; exact le_max_left ..
  nth_rw 1 [show i=j-1 by omega]; exact le_max_right ..

lemma Gated.prepares (V : Delays P) (s : Scope) (t : Tariff) (T : Sections F)
    (hfact : ∀ j : ℕ,((p.profile j).order.factorial:ℝ) ≤ (p.profile j).columns)
    (hs : ∀ j : ℕ,s.ask j (p.profile j) ≤ (w.L j).val) (ht : Gated V s t T) {Y : Bar V} {I : Wait Y} {a : Levels G}
    (h : Paid I a) : Prepared s t T a := by
  have he i : a.S.block i=w.L (a.clock.J (i+1)) := (a.fits.sameFactor i).symm.trans (congr_fun h.lengths _)
  have hg m := ht.gates (a.clock.J m) (a.clock.J (m+1)) (a.clock.hatBeta m) (a.fits.mono (by omega)) (a.fits.stepSlow m)
      (h.pays m)
  refine ⟨Stock.consumes h ht.priced,fun i => by simp only [Levels.params,Calendar.params,h.stage]; apply hfact,
    fun i => by simp only [Levels.params,Calendar.params,h.stage]; exact (hg i).1,fun m => ?_,
    fun m => by simp only [Levels.params,Calendar.params,h.stage,he m]; apply hs⟩
  have hv : a.clock.hatBeta (m+1) = a.clock.hatBeta m + G.slopeConstant*Real.log (a.S.block m).val := by
    unfold Calendar.hatBeta; rw [Schedule.scale_succ]; unfold Levels.S; ring
  simp only [Levels.params,Calendar.params,h.stage,hv,he m]; exact (hg m).2



/-- Combine with the actual unconditional pressure pricing theorem (for the
same kernel and MapPrices). `n` can raise the floor arbitrarily; we also raise
a supplied delay record, preserving its volume and growth bids, and commit
post-L Tariff before that raising. Doesn't supply appropriateness of any
pressures/support alphabets nor strengthen `.shells` for separate calls.
-/
theorem pricing (s : Scope) (T : Sections F) (H : G.Simple) (p : Sheet G) (K : MapPrices)
    (hfact : ∀ j : ℕ,((p.profile j).order.factorial:ℝ) ≤ (p.profile j).columns) :
    ∃ k : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ i,k i ≤ n i) → ∀ D : Rolls {p with floorL := n}, ∀ t : Tariff,
    ∀ m ≥ (0:ℝ), ∀ Θ : Protection D, ∀ V : Supply.Delays Θ, ∃ W : Supply.Delays Θ,
      W.shells=V.shells ∧ W.growth=V.growth ∧ V.scaleEntry ≤ W.scaleEntry ∧ V.betaEntry ≤ W.betaEntry ∧
        ∃ U : ℕ → ℕ → ℝ, Testing.Ringing K U W ∧ (∀ i j,U i j ≥ m) ∧
        ∀ (Y : Bar W) (I : Wait Y) (a : Levels G), Paid I a → Prepared s t T a := by
  obtain ⟨k,hk⟩ := Next.Fluctuations.pressure_pricing p K
  refine ⟨fun i => max (k i) (s.ask i (p.profile i)),fun n hn D t m hm Θ V => ?_⟩
  have hf i := max_le_iff.mp (hn i)
  obtain ⟨V',he,hh,hy,hβ,U,hU,hU'⟩ := hk n (fun i => (hf i).1) D m hm Θ V
  obtain ⟨W,h₁,h₂,h₃,h₄,h₅⟩ := raise_gates H V' s t T
  refine ⟨W,h₁.trans he,h₂.trans hh,hy ▸ h₄,hβ.trans h₃,U,Bid.recheck h₃ hU,hU',fun Y I a ha => ?_⟩
  exact h₅.prepares W s t T hfact (fun j => ((hf j).2.trans (D.large j).need)) ha

/-- Purchasing the factorial before requesting L, if needed. Changes columns,
so must be done upstream of physical constructions using them. -/
def buyFactorial (p : Sheet G) : Sheet G :=
    { p with profile := fun i => { p.profile i with
      columns := max (p.profile i).columns (p.profile i).order.factorial
      columns_ge := (p.profile i).columns_ge.trans (le_max_left ..) } }

theorem bought (p : Sheet G) (i) : (((buyFactorial p).profile i).order.factorial:ℝ) ≤ ((buyFactorial p).profile i).columns := le_max_right ..

end YM.Extra.Multi
