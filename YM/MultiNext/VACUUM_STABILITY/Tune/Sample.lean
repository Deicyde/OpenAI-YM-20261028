import YM.MultiNext.VACUUM_STABILITY.Tune.Budget

set_option warningAsError false

/-!
# Singleton moves are coherent on this pipeline

Explicit agreement still required on the *unmarked* meter and on actual choices of the
reference airport. Here linear extraction identities and bounds on W/surcharge families
require ONLY the local exchange tickets, no assumption of having W moves at this output level
of any mixed system.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Tune
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {B : Brush V G n} {P : BudgetPoint}

namespace Slicer
variable (S : Slicer B) (x : V) (U : Config G n)

private def touchOne (P : BudgetPoint) (v : SmoothLetter V G n) := if v.stamp.name=spike x then
    masked P.threshold v.zone v.stamp.ink U else 0
private def tagOne (q : Grade V) (v : HardLetter V G n) := if v.stamp.name=q then v.stamp.ink U else 0

private lemma touch_move {T : Finset V} (hx : x∈T) (i : B.Line) : touchOne x U P (B.chapter i) =
    touchOne x U P (S.partL T i) + touchOne x U P (S.partR T i) +
      (if (B.chapter i).stamp.name=spike x then (S.cuts i).fiat else 0) + tagOne U (spike x) (S.flagTerm T P i) := by
  by_cases he : (B.chapter i).stamp.name = spike x
  · have ha : along T (B.chapter i).stamp.name := ⟨x,hx,he⟩
    simp [touchOne,partL,partR,tagOne,flagTerm,Exchange.left,Exchange.right,Exchange.tag,he,show along T (spike x) from he ▸ ha]
  by_cases ha : along T (B.chapter i).stamp.name
  · simp [touchOne,tagOne,partL,partR,flagTerm,he,ha,Exchange.left,Exchange.right,Exchange.tag]
  simp [touchOne,tagOne,partL,partR,flagTerm,quiet,eraseChime,he,ha,masked]

lemma base_checkout (T : Finset V) : showSeal (S.package P T).sticker 0 U=showSeal S.base 0 U := by
  let g := tagOne U (0:Grade V) (G:=G)
  have ht : g (stub V G n)=0 := by simp [g,stub,tagOne]
  refine Eq.trans (Pad.wide_sum (S.jointList T P) _ g ht) (Pad.padding_right (f:=g ∘ S.jointList T P) ?_)
  intro i
  unfold g tagOne Function.comp jointList; dsimp only [Sum.elim_inl]; unfold flagTerm; split
  · rename_i he; obtain ⟨x,hx,hK⟩:=he; exact if_neg (show (B.chapter i).stamp.name ≠0 from hK ▸ spike_neq x)
  simp [eraseChime]

variable [Fintype V]

private lemma scale_line {I : Type} (z : V→ℂ) (i : V) (hz : z i ≠ 0) (q : I → Grade V) (f : I → ℂ) {c : I → ℝ}
    (hh : Summable c) (hQ : ∀ j, ‖beat (q j) z*f j‖ ≤ c j) : Summable fun j => if q j=spike i then f j else 0 := by
  have he := (hh.of_nonneg_of_le (fun j => norm_nonneg _) hQ).of_norm
  refine ((sift he (fun j => q j=spike i)).mul_left (z i)⁻¹).congr fun j => ?_
  by_cases hx : q j=spike i <;> simp [hx,hz, Stamp.beat_spike]

-- Requires only one ordinary point with a paid bound and all needed coordinates nonzero.
private lemma liquid {L : V → Support n → Prop} {T : Finset V} {m χ κ z}
    (hv : S.Ticket P L T m χ) (he : S.Endowed P m χ κ z) (hx : z x≠0) :
    Summable (fun i => touchOne x U P (S.partL T i)) ∧ Summable (fun i => touchOne x U P (S.partR T i)) ∧
      Summable (fun i => if (B.chapter i).stamp.name=spike x then (S.cuts i).fiat else 0) ∧
      Summable (fun i => tagOne U (spike x) (S.flagTerm T P i)) := by
  obtain ⟨f,H,hF⟩:=affordability hv he
  have hp := Absolute.account (fun i => show (S.cuts i).jointly.Nonempty from ⟨_,(S.cuts i).left.origin⟩) H (Rates.inner_pos _).le
  constructor
  · refine scale_line z x hx _ _ hp fun j => ?_
    let w := S.partL T j
    rw [← SmoothLetter.tint]; exact w.rate_echo P z _ ((hF _).1.2 _ w.origin) U
  refine ⟨scale_line z x hx _ _ hp (fun j => ?_),scale_line z x hx _ _ hp fun i => (hF i).2.2.2,
    scale_line z x hx _ _ hp fun i => (hF i).2.2.1 U⟩
  let w := S.partR T j
  rw [←SmoothLetter.tint]; exact w.rate_echo P z _ ((hF _).2.1 _ w.origin) U

lemma payment_time (P : BudgetPoint) {L : V → Support n → Prop} {T : Finset V} {m χ z κ}
    (hv : S.Ticket P L T m χ) (he : S.Endowed P m χ κ z) (hh : x∈T) (hx : z x≠0) :
    let D := S.package P T
    B.pay x+showBulk B.chapter P (spike x) U = D.outgoing x+showBulk D.wrap P (spike x) U+showSeal D.sticker (spike x) U := by
  intro D; obtain ⟨hy,hY,hp,hQ⟩:=S.liquid x U hv he hx
  let i := touchOne x U P; let j := tagOne U (spike x)
  have hb : showBulk D.wrap P (spike x) U=(∑' b,i (S.partL T b))+∑' b,i (S.partR T b) :=
    (Pad.wide_sum (S.brine T) _ i (by simp [i,touchOne,tent,masked])).trans (Absolute.union_tsum (f:=i ∘ S.brine T) hy hY)
  have hZ : showSeal D.sticker (spike x) U=∑' b,j (S.flagTerm T P b) := by
    refine (Pad.wide_sum (S.jointList T P) _ j (by simp [j,tagOne,stub])).trans (Pad.padding_left (f:=j ∘ S.jointList T P) ?_)
    intro b; exact if_neg (show (S.base b).stamp.name≠spike x from hv.zero b ▸ Ne.symm (spike_neq x))
  let k := fun b : B.Line => touchOne x U P (B.chapter b)
  change B.pay x + ∑' b, k b = _
  rw [hb,hZ,tsum_congr (fun b => touch_move S x U (P:=P) hh b)]
  rw [Summable.tsum_add ((hy.add hY).add hp) hQ,Summable.tsum_add (hy.add hY) hp,Summable.tsum_add hy hY]
  rw [show D.outgoing x=B.pay x+S.tribute x from if_pos hh]; unfold i j tribute; ring

/-- What is still required for checkout with the actual P. -/
structure Landed (P : Rep G n) (T : Finset V) (w : V→Pulse G n) : Prop where
  start U : B.base U * Complex.exp (showBulk B.chapter P.p 0 U) =
      (Real.exp (P.exponent U) : ℂ)*Complex.exp (showSeal S.base 0 U)
  equal q U : viewK B (S.package P.p T) P.p q 0 U=incumbent P U q
  formed i : i∈T → ∀ q U, viewK B (S.package P.p T) P.p q (spike i) U=(w i).2 q U
  works i : i∈T → ∀ U, B.pay i + S.tribute i + showBulk (S.package P.p T).wrap P.p (spike i) U = (w i).1 U

lemma loaded {P : Rep G n} {m χ} {L : V→Support n→Prop} {T : Finset V} {w : V→Pulse G n} {κ z}
    (h : S.Ticket P.p L T m χ) (he : S.Endowed P.p m χ κ z) (hr : ∀ x∈T,z x≠0) (hk : S.Landed P T w) :
    Settled B (S.package P.p T) P T w := by
  refine ⟨fun U => ?_,hk.equal,fun x hi U => payment_time S x U P.p h he hi (hr _ hi), fun i hi U => ?_, hk.formed⟩
  · rw [hk.start U,S.base_checkout U]
  have hb := hk.works i hi U
  rw [show (S.package P.p T).outgoing i=B.pay i+S.tribute i from if_pos hi]; exact hb
end Slicer
end YM.Multi.Vacuum.Tune
