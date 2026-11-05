import YM.Push.SECTOR_MEASURE.Presented

/-!
# At the committed step (conditional consumer)

Through the compatible `B`, `T`, prices and each input of the
`Program.advances` question. Doesn't assume the advances. Does assume
B, Ringing as typed. Point charge available on that T; produces the
exact cutEntry equality and the earned estimate with TRUE tails present
and integrated, all on SAME hat threshold and Forest, including before
the choice of endpoints of the β shooting. What still needs paying
is not only leftOver (here with no cross-volume bound); see Budget for
the subsequent Gaussian change & locality, representation of output,
continuations, parameter ledger etc.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure.Consumer

open Lattice RG Wilson Pressure Pressure.Stores Pressure.Testing RG.Supply RG.Shoot
open Precision YM.Input Tree MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge}

private lemma threshold (B : Levels G) (m p : ℕ) :
    fiery G (B.clock.hatBeta m) ((B.clock.op m p).patch.L) = B.clock.threshold (m+1) := by
  have hl : B.clock.hatBeta (m+1)=betaF G (B.clock.hatBeta m) ((B.clock.op m p).patch.L) := by
    unfold Calendar.hatBeta betaF
    rw [Schedule.scale_succ]; change _ = _ + _ * Real.log (B.S.block m).val; unfold Levels.S; ring
  change temp _ = temp _; rw [hl]

variable {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Supply.Delays Θ}
variable {Y : Bar W} {I : Wait Y} {Z : ChartRatio G} {K : MapPrices} {Q : PostCost D}

/-- Consumer at any committed height pair, one constant κ across actual
inputs (whose Bills can still be volume dependent!). `0 < fiery...`
permits use with a single `Chi` over all those inputs. Also gives use
of single-oriented grant via `PointCharge.charged`. Output formulas
relative to probability Haar, V held fixed. -/
theorem bought (B : Directed G I Z K Q) (w : ℕ → ℕ → ℝ) (h : Ringing K w W)
    (j i : ℕ) (u : C.first ≤ i) (hij : i ≤ j) (hv : j ≤ i+1) :
    0 < w j i ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ N m p : ℕ, m < N → B.a.clock.J (m+1) = j → B.a.clock.J m = i →
      let S := B.a.clock.op m p
      let T := ships B N m p
      let x := B.a.clock.hatBeta m
      0 < x ∧ 0 < fiery G x S.patch.L ∧ PointCharge T x (w j i) κ ∧
      ∀ R : Rep G (B.a.S.side (m+1) p), Lives B.bake N (m+1) p R → R.beta ∈ band B.a (m+1) →
        ∀ (F : Forest S.ratio) (d : Allocation G S x (w j i)), Presented.PortionCost d F T κ R := by
  refine ⟨(h.receipts i j hij hv u).pos,?_⟩
  obtain ⟨κ,hκ,H⟩ := notation_ticket K B w h j i u hij hv
  refine ⟨κ,hκ,?_⟩
  intro N m p hm ht hs S T x
  have he : fiery G x S.patch.L = B.a.clock.threshold (m+1) := threshold _ _ _
  have hh : PointCharge T x (w j i) κ := by
    intro F A U k V hl hx; rw [he]; exact H _ _ _ hm ht hs A U V k F hl hx
  refine ⟨zero_lt_one.trans (B.a.fits.delayed m), he.symm ▸ (B.a.budget (m+1)).threshold_pos, hh,?_⟩
  intro R hL hB F d
  refine Presented.portionCost hh (proceeds B N m p hm) hL.valid ?_ ?_ F d
  · have H := B.a.fits.delayed (m+1)
    exact (show 0 ≤ B.a.clock.hatBeta (m+1)/2 by linarith).trans hB.1
  refine ⟨?_,hL.clip,?_⟩
  · rw [hL.path,B.bases]; rfl
  rw [hL.point,he]; rfl

end YM.Push.SectorMeasure.Consumer
