import YM.Push.RELAY_MARK.Budget
import YM.Push.RELAY_MARK.Step

/-!
# Cutoff half of RelayCosts.mark, all weights

In this approach it's the same skeleton/payoff for all queries. Nothing
quantum is hidden in a convergence assumption. Also mark for arbitrary
slices meeting dollar on the ordered tails -- not assuming simultaneous
bounds across all rows, so this re-applies e.g. with a new Order. Here
`Memento.made` is the only conditional input (real calibration & selected
history), apart from choosing our sections. That's a very large red
producer in its own right, not claimed possible with these choices or
even with the schedule obligations in the target. Mark incl close for
this option is actually independent of any of the trajectory gates, once β
nonzero. RShort and the transit and pace (identity and derivative matching)
are NOT assumed for the mark subset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {R : Weave G}

/-- Choice generated at RAuthors before schedule/period/threshold. Sufficient
source instance to request from unmarked side. `f` is the fixed frame list from
this G. Use in negotiating RPaper. -/
lemma commissioned (G : Gauge) (H : Hol G) (f : Frames G) : ∃ (T : ∀ d,SectionData (f.level d)) (R : Weave G),
    ∀ d, Portfolio H (T d) (R d) := by
  choose T R h using fun d=> Portfolio.build H (f.level d)
  exact ⟨T,R,h⟩

/-- Finite-family premises. The Portfolio proofs are available at d=0,…
from `Portfolio.build`; field asks that `C` (to be used all the rest of the proof)
is being constructed with these realizations. In particular the stencil has Honesty
`Sound` and true powers/pop. -/
structure Memento (C : Family G) (R : Weave G) : Prop where
  made : C.Makes
  wrote d : Portfolio C.params (C.localSection d) (R d)

/-- Receipt to WARD (on this extraction and Presentation). `positions`
asks even for rows only eventually in kernel; that's enough to get the
actual `mark`, given separately. `fees` prices the rows physically and in
their actual insertion format at top. -/
structure Half (C : Family G) (F : Extraction.Order) (b : Presentation C) (R : Weave G) : Prop where
  earned : Purse C R b
  positions (d) (x : Rowe C d) : (∀ᶠ j in F.fuse, b.step d j (x j)=0) →
    sober C (upper C x) F ∧ exactOnSep C F (upper C x)
  fees (d) (x : Rowe C d) : dollar C F x → ∃ D,Sized C d x D F
  mark (d) (x : Rowe C d) : (∀ j,b.step d j (x j)=0) → dollar C F x →
    ∃ z, sober C z F ∧ exactOnSep C F z ∧ Bid.close C F (upper C x-z)

variable {b : Presentation C}

theorem awarded (h : Memento C R) (f : Extraction.Order) (hb : Purse C R b) : Half C f b R := by
  have ha d (x : Rowe C d) (hh : ∀ᶠ j in f.fuse, b.step d j (x j)=0) : exactOnSep C f (upper C x) := by
    rw [Extraction.Order.fused] at hh
    intro n q i δ hδ
    have ht := f.mesh.cofinal.eventually (all_probes R (h.wrote d) δ hδ n (fun j=>(q j).1))
    unfold Extraction.Order.late at *; filter_upwards [hh] with p hp; filter_upwards [hp,ht] with N hi hv z hz
    apply hv (f.per p) (Overlay.beta_positive h.made.wilson (le_refl (f.mesh N))).ne' x ?_ q (fun _=>rfl) i z fun j=> hz j i
    rw [← (hb.pure d (f.mesh N) (f.per p)).ker]; exact LinearMap.mem_ker.mpr hi
  refine ⟨hb,fun d x hx=> ⟨sober_all C x f,ha d x hx⟩,fun d x hx=>sizable h.made x hx,?_⟩
  intro d x he hx
  exact ⟨upper C x,sober_all C x f,ha d x (Eventually.of_forall he),by rw [sub_self]; exact rent_zero C f⟩

theorem issue (h : Memento C R) : ∃ b, ∀ f : Extraction.Order, Half C f b R := by
  obtain ⟨b,hb⟩ := present C R; exact ⟨b,fun f=>awarded h f hb⟩

-- exact missing fields named


end YM.Push.Mark
