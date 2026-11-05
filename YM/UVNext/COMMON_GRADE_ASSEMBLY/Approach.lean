import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Post
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression

/-! # Countable UV approach demands

The very same normalized W is used across sizes. The entry `Admissible`
still costs estimates simultaneously at the station on arbitrarily high
arities up to n, all smooth tests at the aperture (nonuniform thresholds),
on the ordered regulator tails; see Station.lean. `Stationed` version lets
us defer estimates (keeping sizes/normalizations) to successive inherited
orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter Extraction Table Ward Climb Org Spec
  Next.Extract Next.UVStress Push.Common
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {a : (Bel C.book).RealSpin}

def StationCut (C : Family G) (a : (Bel C.book).RealSpin) (i : ℕ×ℕ) (F : Extraction.Order) : Prop :=
  ∃ X : Station C i.1, X.Admissible F a i.2 (i.2+1) (toll i.2) ∧ X.r ≤ toll i.2



/-- Allow even only a cofinal choice of good sizes for each degree d.
Note, no uniform R cap is thereby imposed. -/
def WeakBill (C : Family G) (a : (Bel C.book).RealSpin) (i : ℕ×ℕ) (F : Extraction.Order) : Prop :=
  ∃ n ≥ i.2, StationCut C a (i.1,n) F

lemma cash_weak (p : ∀ i, WeakBill C a i f) : Stations C f a where
  arbitrarily d N R ε δ hr he hd := by
    have h₁ := eventually_ge_atTop N
    have h₂ : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ)+1 :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).eventually_ge_atTop R
    obtain ⟨m,hm⟩ := eventually_atTop.mp (h₁.and (h₂.and
      ((toll_go.eventually (ge_mem_nhds he)).and (toll_go.eventually (ge_mem_nhds hd)))))
    obtain ⟨n,hn,X,hX,hY⟩ := p (d,m)
    obtain ⟨hn',hR,hE,hD⟩ := hm n hn
    refine ⟨X,{ hX with short := ?_ },hY.trans hD⟩
    intro o ho v hv t ht M hM ht' η hη
    have hwindow : tsupport t ⊆ Scaling.window ((n:ℝ)+1) o := by
      refine ht.trans fun x ⟨ha,hb⟩ => ⟨?_,hb.trans hR⟩
      intro i j hij; exact (inv_anti₀ (zero_lt_one.trans_le hr) hR).trans (ha i j hij)
    have hp := hX.short (ho.trans hn') v hv t hwindow M hM ht' η hη
    apply hp.mono; intro i h; apply h.mono; intro j h
    refine h.trans ?_
    change _ ≤ ε * Station.charge v * M + _
    have : 0 ≤ Station.charge v := Finset.prod_nonneg fun i _ => norm_nonneg _
    gcongr

/-- One genuine common F for weak receipts, if the arbitrarily-deep
station bills can be bought on successive refinements. -/
def WeakStock (C : Family G) (a : (Bel C.book).RealSpin) (f : Extraction.Order) : Prop :=
  Stationed f (WeakBill C a)



lemma stations_paid (H : Stations C f a) : WeakStock C a f := by
  apply already
  rintro ⟨d,n⟩; exact ⟨n,le_rfl,H.arbitrarily d n ((n:ℝ)+1) (toll n) (toll n) (by simp) (toll_pos n) (toll_pos n)⟩


end YM.UVNext.Grade
