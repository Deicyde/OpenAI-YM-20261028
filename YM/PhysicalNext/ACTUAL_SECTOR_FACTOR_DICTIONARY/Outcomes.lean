import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Fabric
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Wires


/-! Means in completion and actual Y. Keep negative Store, trunk and
predictor source answers from the same physical requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Wires
open Schur Completion Geo
variable {G : Gauge} {c f : Side} {S : StepData c f} {A A' : Stores S} {F F' : Forest S.ratio} (T : Tube G S) (x : ℝ)
    (q : Chi) (d : ℝ) {V V' : Config G c} {Y Y' : Config G f} {k k' : S.Choices}

def iced (Y : Config G f) (A : Stores S) (x : ℝ) (F : Forest S.ratio) : LinkArray G (Frozen A x F) :=
  fun i => Y i.val.val

def broken (V : Config G c) (Y : Config G f) (A : Stores S) (F : Forest S.ratio) := input x A F (autoShell q d V (iced Y A x F))

lemma broken_meas (A : Stores S) (F : Forest S.ratio) (hd : 0 < d) (he : 2*d < firstRadius G) :
    Measurable (fun p : Config G c × Config G f => broken x q d p.1 p.2 A F) := by
  refine measurable_pi_lambda _ fun j => ?_
  unfold broken Rows.input autoShell iced
  split
  · split
    next ht hq =>
      have hh : Continuous (fun p : Config G c × Config G f => patched q d (p.2 j * (replica S.ratio p.1 j)⁻¹)) := by
        apply (patched_continuous q hd he).comp
        unfold replica; split <;> fun_prop
      exact hh.measurable
    exact measurable_const
  exact measurable_const

section read
variable {X : Support c} (h : Physical.Reads X A A' F F' V V' k k')
include h
lemma replica_read (e : Bond f) (hl : Shields X (portOf S e) 1) : replica S.ratio V e=replica S.ratio V' e := by
  unfold replica; split
  · rfl
  exact h.configuration _ hl.center (hl _ (Work.E03.sep_step ..))

lemma broken_read (i : Bond f) (ht : Geo.Yreads S X Y Y') (hb : 120≤radiusB x)
    (hl : Shields X (portOf S i) (12*radiusB x)) : broken x q d V Y A F i = broken x q d V' Y' A' F' i := by
  let B := radiusB x
  have hi : Shields X (portOf S i) 1 := hl.shrink (by omega)
  have h1 := h.tree i hi.center (hi _ (Work.E03.parent_step ..))
  by_cases hx : i∉F.trunks
  · have he := mt h1.mpr hx
    have hu : chill A x F ⟨i,hx⟩ ↔ chill A' x F' ⟨i,he⟩ := by
      unfold chill; dsimp only; unfold portOf at hl
      rw [h.dome_agrees (10*radiusB x) _ (hl.shrink (by change _ ≤ 12*B; unfold B; omega)),h.dome_agrees _ _
        (hl.shift (by have ht := Work.E03.parent_step S i.1 i.2; omega))]
    unfold broken Rows.input; rw [dif_pos hx,dif_pos he]; split
    next hm =>
      rw [dif_pos (hu.mp hm)]; unfold autoShell iced
      dsimp only
      rw [replica_read h i hi,ht i hi.center (hi _ (Work.E03.parent_step ..))]
    next hm => rw [dif_neg (mt hu.mpr hm)]
  have hh : i∈F.trunks := Classical.not_not.mp hx
  unfold broken Rows.input; rw [dif_neg hx,dif_neg (by exact Classical.not_not.mpr (h1.mp hh))]

lemma participates (hb : 120≤radiusB x) (hp : Next.SectorChange.span S.patch x ≤ radiusB x/50)
    (i : Slots S) (hi : Shields X (spot S i) (14*radiusB x)) :
    keep x (shots S x) A F i ↔ keep x (shots S x) A' F' i := by
  have he (i : Slots S) : keep x (shots S x) A F i=curb (shots S x) A F x i.1 (slipAt S i) := by
    rcases i with ⟨i,j|j⟩ <;> rfl
  have ht : keep x (shots S x) A' F' i=curb (shots S x) A' F' x i.1 (slipAt S i) := by
    rcases i with ⟨i,j|j⟩ <;> rfl
  rw [he i,ht]
  have hz (A : Stores S) (F : Forest S.ratio) : curb (shots S x) A F x i.1 (slipAt S i) ↔
      ∃ j : Bond f, separation (spot S i) (portOf S j)≤Next.SectorChange.span S.patch x ∧ Physical.openBond A F x j := by
    constructor
    · rintro ⟨j,hj⟩; exact ⟨j.val.val,(contains ..).mp hj,⟨j,rfl⟩⟩
    rintro ⟨j,h₀,hq⟩; exact curb_by hq h₀
  rw [hz,hz]; refine exists_congr fun j=>and_congr_right fun hj=> ?_
  exact h.frozen_bits hb _ (hi.shift (by change separation (spot S i) (portOf S j)+12*radiusB x ≤ _; omega))
end read

def tRow (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (y : Directions G f) : LogArray G (Slots S) :=
  fun i => base T x V k i + FieldJet.bump' T x V k y i

def sources (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio) (Y : Config G f) : Prices G (Slots S) :=
    tape.symm (Rows.restrict x (shots S x) A F (tRow T x V k A F (broken x q d V Y A F)))

lemma sources_meas (k : S.Choices) (A : Stores S) (F : Forest S.ratio) {P : Teller G} (h : P.Funds S T)
    (hd : 0<d) (hr : 2*d<firstRadius G) (i : Receipt G S) :
    Measurable (fun p : Config G c × Config G f => sources T x q d p.1 k A F p.2 i) := by
  let l := fun p : Config G c × Config G f => broken x q d p.1 p.2 A F
  have hl : Measurable l := broken_meas x q d A F hd hr
  have hm := (FieldJet.bump'_meas T x (funds_branch h) k i.1).comp (measurable_fst.prodMk hl)
  have hf : Measurable (fun p : Config G c × Config G f => base T x p.1 k i.1) := (Fabric.core (T:=T) h x k i.1).comp (measurable_fst (β:=Config G f))
  change Measurable (fun p => Rows.restrict _ _ A F (tRow T x p.1 k A F (l p)) i.1 i.2)
  unfold Rows.restrict tRow; split
  · let g (c : G.Color) := c i.2
    have ha : Continuous g := PiLp.continuous_apply ..
    exact ha.measurable.comp (f:=fun p => slip • (base T x p.1 k i.1 + FieldJet.bump' T x p.1 k (l p) i.1))
      ((measurable_const (a:=slip)).smul (hf.add hm))
  exact measurable_const

lemma sources_align (hA : Map.Aperture S T x) (k : S.Choices) (V : Config G c) (Y : Config G f)
    (A : Stores S) (F : Forest S.ratio) {M} (h : Authorized A V F x M) :
    sources T x q d V k A F Y = Rows.source T x V k (shots S x) A F q d (iced Y A x F) := by
  unfold sources Rows.source; congr 1
  funext i; unfold Rows.restrict; split
  next hi => unfold tRow broken; rw [FieldJet.agrees T x V k h _ i hi]; rfl
  rfl

lemma sources_read {X : Support c} (h : Physical.Reads X A A' F F' V V' k k')
    (hA : Map.Aperture S T x) (i : Receipt G S) (ht : Shields X (spot S i.1) (16*radiusB x))
    {Y Y' : Config G f} (hl : Geo.Yreads S X Y Y') : sources T x q d V k A F Y i=sources T x q d V' k' A' F' Y' i := by
  have h₁ : Shields X (spot S i.1) (4*radiusB x+1) := ht.shrink (by have := hA.scale; omega)
  have he := Geo.Reads.visit h h₁; have h2 := Geo.Reads.way h h₁
  have h3 (j) (hj : separation (spot S i.1) (portOf S j)≤radiusB x) : broken x q d V Y A F j=broken x q d V' Y' A' F' j :=
    broken_read _ _ _ h j hl hA.scale (ht.shift (by omega))
  have hz := FieldJet.around T x _ _ i.1 hA he h2 h3
  have hv := (drawn T x k k' V V' hA i.1 he h2).1
  have hh : tRow T x V k A F (broken x q d V Y A F) i.1 = tRow T x V' k' A' F' (broken x q d V' Y' A' F') i.1 := by unfold tRow; rw [hv,hz]
  change Rows.restrict _ _ _ _ _ i.1 i.2=Rows.restrict _ _ _ _ _ i.1 i.2
  unfold Rows.restrict; simp_rw [propext (participates _ h hA.scale hA.spans i.1 (ht.shrink (by omega))), hh]
end Wires
end YM.PhysicalNext.Dictionary
