import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Drain
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Scatter
import YM.Next.ROTATIONS.Sources
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Packets
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Paper
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Tarps

/-! Additional protections to matter in the unforced estimates: a
still-held raw drows vertex on the U channel can use a somewhat enlarged
FINE default plateau, e.g. for workF's kept test / workI's actual
predictor. Don't extrapolate just from a broad logarithmic chart, which
can already incur an O(β t²) expense on a missing kept quadratic. Insert
the deterministic guard on an entire ball before dropping anything,
and prove all papers & point identities with it. Only on drows with U.
Aperture receipts do not prove sufficiency of this modification for intended
analytical bounds. This isn't aiming to resolve that killgate here.

Remote E split also here. No trigger-telescope duplication — hold each
whole companion (or direct distant gate complement) for the multiplier's
trigger/point prices. In those tests must obtain a stake, if needed,
at the actual common Z from the *whole* stencil, paying non-repeating
shares e.g. via Stake lease and bounded incidence. The split itself
does not entitle any trigger savings. No operation drops a guard
then seeks to use the dropped guard on each expanded term.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Voice
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice.Check Parcel
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
    (h : Route.Badge.App D)
local notation "t₀" => D.betaHat
local notation "B" => radiusB D.betaHat

namespace Defenses

def warm (S : StepData c f) (N : ℕ) (o : Site c) : Finset (Cell f) := Finset.univ.filter (fun i=> separation o (S.ratio.parent i.1)≤6*N)

def diet (o : Site c) : Formula G S ℝ := fun F A b k V p=>
    ∏ i∈warm S B o,D.profile.innerShare ((fiery G t₀ S.patch.L)/2) (toll (skin D F A b k V p) i)

def wrapRow (i : Spot.Shape c f) : Bool := match i with
    | .inl _ => true
    | .inr (.inl _) => true
    | .inr (.inr (.inr (.inr (.inl _)))) => true -- workL
    | _ => false

-- On any optional h using U, protect before use. V-only path pairs need no U.
def curtain (i : ListID S) : Bool := match i with
    | .letter _ => true
    | .opened (.inl _) => true
    | .row j => wrapRow j.2
    | _ => false

def budget (i : ListID S) : Formula G S ℝ := match i with
    | .row j => if wrapRow j.2 then diet D (j.1.act (hinge S j.2)) else fun _ _ _ _ _ _ => 1
    | _ => fun _ _ _ _ _ _ => 1

def barrier (i : ListID S) : Formula G S ℝ := if curtain i then tarp D (Voice.native D i) else fun _ _ _ _ _ _=>1

def introduce (i : ListID S) : Formula G S ℝ := fun F A b k V p=> (sew D i F A b k V p * budget D i F A b k V p) * barrier D i F A b k V p

include h
lemma diet_paid (o : Site c) : Care D ({o}:Support c) (diet D o) := by
  constructor
  · obtain ⟨P,hP⟩:=h.valid.funds
    intro F A b k
    have ht := Print.printed_meas D.tube t₀ D.broadCut D.radius D.g hP k A F h.valid.positive h.enough
    unfold uncurry diet
    exact Finset.measurable_fun_prod _ fun i _=> D.profile.smooth.continuous.measurable.comp (((toll_meas i ht).div_const _).pow_const _)
  intro F F' A A' b b' k k' V V' p p' H
  have ht0 := h.aperture.scale
  have hl := daily D h H o (Finset.mem_singleton_self _)
  refine Finset.prod_congr rfl fun i hi=> ?_; have ht := (Finset.mem_filter.mp hi).2
  unfold toll; rw [face_near (Work.E03.parent_step S) i _ (skin D F' A' b' k' V' p')
    (hl.shrink (by change separation o (S.ratio.parent i.1)≤6*B at ht; omega))]

lemma guarded (i : ListID S) : Care D (Voice.native D i) (introduce D i) := by
  apply Care.together (Care.together (local_series D h i) ?_)
  · unfold barrier; split
    · exact tarp_care D h _
    exact Care.constant 1
  cases i with
  | row i=> simp only [budget]; split
            · exact diet_paid D h (i.1.act (hinge S i.2))
            exact Care.constant 1
  | _ => exact Care.constant 1

section E
variable {D}

def remote (d : AnalyticBridge.LocalGaussian.Desk G S) (l : Support c) (A : Stores S) : Prop := ¬ recorded S l (600*radiusB d.betaHat) A
-- `scale` caller's requested guard width (in Z units). Need sufficiently
-- small before using any leading-estimate application. No such applications here.
def gamma (l : Support c) (scale : ℝ) : Formula G S ℝ := fun F A _ _ _ p=>
    ∏ i∈zone D l,if Physical.openBond A F t₀ i then broad D.broadCut scale (p.2 i) else 1

def tip (i : ℕ) (scale : ℝ) : Formula G S ℝ :=
  let l:= Voice.native D (.letter i)
  fun F A b k V p=> if remote D l A then
    (Real.exp ((gamma (D:=D) l scale F A b k V p * -D.labels.E i (skin D F A b k V p)) * tarp D l F A b k V p)-1)
    else 0

-- Care of unguarded E formula also even off old good; not assuming
-- derivatives or a Γ price there. Eligibility itself on seeds in a larger halo.
private def mainEvent (i : ℕ) : Formula G S ℝ := fun F A b k V p => D.labels.E i (skin D F A b k V p)
private lemma main_paid (i : ℕ) : Care D (Voice.native D (.letter i)) (mainEvent (D:=D) i) := by
  obtain ⟨n,K,c,κ,b,hi⟩:=h.valid.lawful
  obtain ⟨M,hM⟩:=h.valid.funds
  have ht := hi.labels.regular.smooth i
  constructor
  · intro F A b k; exact ht.borel.comp (Print.printed_meas D.tube t₀ D.broadCut D.radius D.g hM k A F h.valid.positive h.enough)
  intro _ _ _ _ _ _ _ _ _ _ _ _ H
  exact ht.sites _ _ (agrees_mono (ink D h H (Z:=inspected (D.labels.reg i).support) (Finset.Subset.refl _)) (fun x hx=>Finset.mem_union_left _ hx))

lemma gamma_care (l : Support c) (scale : ℝ) : Care D l (gamma (D:=D) l scale) := by
  constructor
  · intro F A b k; unfold uncurry gamma
    refine Finset.measurable_fun_prod _ fun j _ => ?_; split
    next hf =>
      exact (broad_smooth D.broadCut scale).continuous.measurable.comp
        ((measurable_pi_apply j).comp (f:=fun y : Config G c × Refs G f => y.2.2) (measurable_snd.comp measurable_snd))
    exact measurable_const
  intro F F' A A' b b' k k' V V' p p' H
  refine Finset.prod_congr rfl fun j hj=>?_
  obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp hj).2
  have hf := (dress D h H h1 h2).2.2
  have hp := H.input.breeze j h1 h2
  simp only [hp,hf]

lemma tip_meas (i : ℕ) (s : ℝ) (F A b k) : Measurable (uncurry (tip (D:=D) i s F A b k)) := by
  let X:=Voice.native D (.letter i)
  unfold uncurry tip; split
  · exact ((((gamma_care h X s).noted F A b k).mul (main_paid h i|>.noted F A b k).neg).mul
      (tarp_care D h X |>.noted F A b k)).exp.sub measurable_const
  exact measurable_const

lemma tip_read (i : ℕ) (a : ℝ) {F F' A A' b b' k k' V V' p p'} :
    let X:=Voice.native D (.letter i)
    (remote D X A ↔ remote D X A') → Survey D (ambient D X) (floor D X) F F' A A' b b' k k' V V' p p' →
      tip (D:=D) i a F A b k V p=tip (D:=D) i a F' A' b' k' V' p' := by
  intro X he hp
  have hf:= (tarp_care D h X).comp hp; have ht:=(gamma_care h X a).comp hp
  have hx:=(main_paid h i).comp hp
  unfold mainEvent at hx; unfold tip; unfold X at *
  simp only [he,ht,hx,hf]
end E
end Defenses
end YM.PhysicalNext.Dictionary.Voice
