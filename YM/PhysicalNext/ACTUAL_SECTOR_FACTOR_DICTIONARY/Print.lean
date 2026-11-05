import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Lens
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Bias


/-! Restriction semantics in the physical dictionary; U is reconstructed
from V & **one** mean, one held Y and one Z (which will be sampled only
through actual fog marginals). Including the tree identity and replica on
boundary edges. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Print
open Schur Wires Geo
variable {G : Gauge} {c f : Side} {S : StepData c f} {A A' : Stores S} {F F' : Forest S.ratio}
    (T : Tube G S) (x : ℝ) (q : Chi) (d g : ℝ) {V V' : Config G c} {k k' : S.Choices}

/-- Test frozen at physical index (requires no fabricated proof of
F.Free in common comparisons). -/
def winter (x : ℝ) (A : Stores S) (F : Forest S.ratio) (e : Bond f) : Prop := e∉F.trunks ∧
    (S.ratio.parent e.1∈A.dome (10*radiusB x) ∨ S.ratio.parent (e.1+Lattice.step e.2)∈A.dome (10*radiusB x))

lemma sees_frost (x : ℝ) (A : Stores S) (F : Forest S.ratio) (e : F.Free) : winter x A F e.val ↔ chill A x F e :=
  ⟨fun h => h.2,fun h=>⟨e.property,h⟩⟩
lemma sees_breeze (x : ℝ) (A : Stores S) (F : Forest S.ratio) (e : F.Free) : Physical.openBond A F x e.val ↔ ¬chill A x F e := by
  rw [Physical.mask]; unfold chill
  have h := e.property; grind

lemma winter_read {X : Support c} (h : Physical.Reads X A A' F F' V V' k k') (e : Bond f)
    (hb : 120 ≤ radiusB x) (hp : Shields X (portOf S e) (12*radiusB x)) : winter x A F e ↔ winter x A' F' e := by
  unfold winter portOf at *
  have ht := Work.E03.parent_step S e.1 e.2
  rw [h.tree e hp.center (hp _ (by omega)),h.dome_agrees _ (S.ratio.parent e.1) (hp.shrink (by change 10*radiusB x+8≤_; omega)),
    h.dome_agrees (10*radiusB x) (S.ratio.parent (e.1+Lattice.step e.2)) (hp.shift (by omega))]

def shade (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) (p : Refs G f) : Directions G f :=
    outlook T x q d k V p.1 A F + g • p.2

def printed (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices) (p : Refs G f) : Config G f := fun e =>
    if winter x A F e then p.1 e else if Physical.openBond A F x e then
      G.lieExp (shade T x q d g A F V k p e) * replica S.ratio V e else 1

variable {p p' : Refs G f}

theorem shade_known {P : Teller G} (h : P.Funds S T) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (hd : 0<d) (hr : 2*d<firstRadius G) : Measurable (fun z : Config G c × Refs G f => shade T x q d g A F z.1 k z.2) := by
  exact ((Wires.herald T x q d h k A F hd hr).comp
    (f:=fun z : Config G c × Refs G f => (z.1,z.2.1))
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      (show Measurable (fun z : Config G c × Refs G f => g • z.2.2) from
        (measurable_const (a:=g)).smul (measurable_snd.comp measurable_snd))

lemma shade_meas {P : Teller G} (h : P.Funds S T) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (hd : 0<d) (hr : 2*d<firstRadius G) (e : Bond f) : Measurable (fun z : Config G c × Refs G f => shade T x q d g A F z.1 k z.2 e) :=
  (measurable_pi_apply e).comp (shade_known T x q d g h k A F hd hr)

theorem printed_meas {P : Teller G} (h : P.Funds S T) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (hd : 0<d) (hr : 2*d<firstRadius G) : Measurable (fun z : Config G c × Refs G f => printed T x q d g A F z.1 k z.2) := by
  apply measurable_pi_lambda; intro i
  have hm := shade_meas T x q d g h k A F hd hr i
  unfold printed; split
  · exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  split
  · have hv : Measurable (fun z : Config G c × Refs G f => replica S.ratio z.1 i) := by unfold replica; split <;> fun_prop
    exact (G.lieExp_cont.measurable.comp hm).mul hv
  exact measurable_const

lemma shade_read {X Z : Support c} (h : Physical.Reads X A A' F F' V V' k k') (hA : Map.Aperture S T x)
    (e : Bond f) (hx : Shields X (portOf S e) (18*radiusB x)) (hz : Shields Z (portOf S e) 1)
    (he : Same S X Z p p') : shade T x q d g A F V k p e= shade T x q d g A' F' V' k' p' e := by
  unfold shade; simp only [Pi.smul_apply,Pi.add_apply]
  rw [beam_bias T x q d h hA e hx he.frost,he.windy hz]



/-- Partial evaluator into the actual chart. -/
def see (A : Stores S) (F : Forest S.ratio) (p : Refs G f) :=
    (iced p.1 A x F, tape.symm (fun i : Active A x F => p.2 i.val.val))

/-- Actual readings into a padded field. Zero active values / one Y
on unused slots. Not a law. -/
def backdrop (A : Stores S) (F : Forest S.ratio)
    (p : LinkArray G (Frozen A x F) × Prices G (Active A x F)) : Refs G f :=
    ((fun e => if ht : e∉F.trunks then if h : chill A x F ⟨e,ht⟩ then p.1 ⟨⟨e,ht⟩,h⟩ else 1 else 1),
      fresh x (shots S x) A F (tape p.2))
lemma rollback (A : Stores S) (F : Forest S.ratio)
    (p : LinkArray G (Frozen A x F) × Prices G (Active A x F)) : see x A F (backdrop x A F p) = p := by
  refine Prod.ext ?_ ?_
  · funext i; unfold see backdrop iced; dsimp only
    rw [dif_pos i.val.property, dif_pos (show chill A x F _ from i.property)]
  funext i
  change fresh x (shots S x) A F (tape p.2) _ i.2= _
  unfold fresh; rw [dif_pos i.1.val.property, dif_pos (show ¬chill A x F _ from i.1.property)]; rfl

lemma tinting (k : S.Choices) (i : Active A x F) (V : Config G c)
    (hA : Map.Aperture S T x) {M η} (h : Authorized A V F x M) (hη : 0<η)
    (hp : Gapped (Rows.gram T x V k (shots S x) A F) η) (p : Refs G f) :
    let m := meanLog A F T x V k q d
    let w := see x A F p
    shade T x q d g A F V k p i.val.val = displaced (m w.1) g w.2 i := by
  intro m w
  apply PiLp.ext; intro j
  have he := Wires.station T x q d (k:=k) hA h hη hp p.1 (i,j)
  change _ = (m w.1 (i,j) + _)
  change outlook T x q d k V p.1 A F i.val.val j + _ = _
  rw [show outlook T x q d k V p.1 A F i.val.val j= _ from he]
  rfl

theorem painted (k : S.Choices) (V : Config G c)
    (hA : Map.Aperture S T x) {M η} (h : Authorized A V F x M) (hη : 0<η)
    (hp : Gapped (Rows.gram T x V k (shots S x) A F) η) (p : Refs G f) :
    let m := meanLog A F T x V k q d
    let w := see x A F p
    printed T x q d g A F V k p = physical A F V w.1 (displaced (m w.1) g w.2) := by
  intro m w
  funext e
  unfold printed physical; by_cases he : e∈F.trunks
  · rw [if_neg (show ¬winter x A F e from fun ht=>ht.1 he), if_neg (show ¬ Physical.openBond A F x e from fun ht => (Physical.mask A F x e |>.mp ht).1 he)]
    exact (F.on_tree _ ⟨e,he⟩).symm
  let t : F.Free := ⟨e,he⟩
  rw [show F.drape _ e=_ from F.off_tree _ t]; unfold returned thaw
  by_cases ht : chill A x F t
  · rw [if_pos ((sees_frost x A F t).mpr ht),freeze_held (j:=⟨t,ht⟩)]; rfl
  rw [freeze_regular (j:=⟨t,ht⟩),if_neg (mt (sees_frost x A F t).mp ht),if_pos ((sees_breeze x A F t).mpr ht),
    show shade T x q d g A F V k p e = _ from tinting _ _ _ _ _ k ⟨t,ht⟩ V hA h hη hp p]
  rfl

end Print
end YM.PhysicalNext.Dictionary
