import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Broadsheet

/-! At the actual primitive marker occurrences or none. There are two
variants even when the remote offer cannot be paid, but then tip is
zero. Need sharp scale & derivative margins separately.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Shipment
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art ι D) (s : ℝ) (h : Lit D) (H : Shipment.Valid D ι Z)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat

def answer (f : ℕ → Prop) : Option ℕ := if h : ∃ i,f i then some h.choose else none
def qualifierAt (a : Finset (Bill S ι)) (i : ℕ) : Option ℕ := answer (fun j=>suggest (qualify i j)∈a)

omit [DecidableEq ι] in
lemma qualifierAt_eq {a b : Finset (Bill S ι)} (i : ℕ) (h : ∀ j,suggest (qualify i j)∈a ↔ suggest (qualify i j)∈b) :
    qualifierAt a i=qualifierAt b i := congr_arg answer (funext fun j=>propext (h j))

-- Factors on the same tables, not a stochastic outcome alteration.
def job (i : ℕ) (j : Option ℕ) : Formula G S ℂ := match j with
  | none=>fun F A b k V p=> (intact D i F A b k V p:ℝ)
  | some j=>fun F A b k V p=> (Z.essay i j (skin D F A b k V p)) * (tarp D (custody D i) F A b k V p:ℝ)

def deck (i : ℕ) : Formula G S ℂ := fun F A b k V p=> Z.score i (skin D F A b k V p)
def total (i : ℕ) : Formula G S ℂ := fun F A b k V p=> masked D.input.p.threshold (Z.plot i) (Z.score i) (skin D F A b k V p) * (tarp D (sourceSites D Z i) F A b k V p:ℝ)

def surge (i : ℕ) : Formula G S ℂ := fun F A b k V p=>
    let l:=sourceSites D Z i
    if remote D l A then (gamma (D:=D) l s F A b k V p * tarp D l F A b k V p :ℝ) • Z.score i (skin D F A b k V p) else 0

def shine (i : ListID S) (b : Bool) : Formula G S ℝ := fun F A l k V p =>
  let u:=Real.exp (introduce D i F A l k V p)-1
  match i with
  | .letter j=>let h:=tip (D:=D) j s F A l k V p; if b then u-h else h
  | _=>if b then 0 else u

def choices (i : Bills S ι) : Formula G S ℂ := fun F A l k V p=> match i with
  | .inl i=> ↑((films D i F A l k V p-1) * if bare i then tarp D (post S i) F A l k V p else 1)
  | .inr (.inl i) => (shine D s i.1 i.2 F A l k V p :ℝ)
  | .inr (.inr (.inl (.inl i)))=> Z.units i
  | .inr (.inr (.inl (.inr i)))=> if i.2 then total D Z i.1 F A l k V p - surge D Z s i.1 F A l k V p else surge D Z s i.1 F A l k V p
  | .inr (.inr (.inr _))=> 1

def shutter (i : Bill S ι) (a : Finset (Bill S ι)) : Formula G S ℂ := match i with
  | .inl P=> fun F A b k V p=> ((Booklet.vitalPage D P F A b k V p:ℝ):ℂ)
  | .inr (.inl j)=>job D Z j (qualifierAt a j)
  | .inr (.inr i)=>choices D Z s i





section legality
include h H
lemma basics (i : ℕ) (j : Option ℕ) : Care D (sourceSites D Z i) (deck D Z i) ∧
    Care D (custody D i) (job D Z i j) ∧ Care D (sourceSites D Z i) (total D Z i) := by
  obtain ⟨Q,hQ⟩:=h.valid.funds
  have he (F A b k) : Measurable (uncurry (skin D F A b k)) := Print.printed_meas D.tube t₀ D.broadCut D.radius D.g hQ k A F h.valid.positive h.enough
  let P:=D.labels.forced i; let X:=custody D i; let Y:=sourceSites D Z i
  have h1:=H.bulk i
  refine ⟨⟨fun F A b k=> h1.borel.comp (he F A b k),fun ht => h1.sites _ _ (agrees_mono (ink D h.toApp ht (Z:=inspected (Z.plot i)) (Finset.Subset.refl _)) (fun j hx=>Finset.mem_union_left _ hx))⟩,?_,
    ⟨fun F A b k=> ((masked_measurable _ _ _ h1.borel).comp (he F A b k)).mul
      (Complex.continuous_ofReal.measurable.comp ((tarp_care D h.toApp Y).noted F A b k)), ?_⟩⟩
  · have hx := tarp_care D h.toApp X
    cases j with
    | none=> exact (Care.together (packed D h.toApp i) hx).follows Complex.ofReal Complex.continuous_ofReal.measurable
    | some j=>
      refine ⟨fun F A b k=> ((H.meas i j).comp (he F A b k)).mul (Complex.continuous_ofReal.measurable.comp (hx.noted _ _ _ _)),?_⟩
      intro F F' A A' b b' k k' V V' p p' Hc
      let L:=skin D F A b k V p; let L':=skin D F' A' b' k' V' p'
      have hr := ink D h.toApp Hc (Z:=inspected P.support) (Finset.Subset.refl _)
      exact congr_arg₂ HMul.hMul (H.forced i j L L' (agrees_mono hr (fun i hi=>Finset.mem_union_left _ hi)) (flags_agree _ _ _ _ hr)) (congr_arg Complex.ofReal
        (hx.comp Hc))
  intro _ _ _ _ _ _ _ _ _ _ _ _ ht
  exact congr_arg₂ HMul.hMul (zap h1.sites (ink D h.toApp ht (Z:=inspected (Z.plot i)) (Finset.Subset.refl _)))
    (congr_arg Complex.ofReal ((tarp_care D h.toApp Y).comp ht))

theorem surge_meas (i : ℕ) (F A b k) : Measurable (uncurry (surge D Z s i F A b k)) := by
  unfold uncurry surge; first| dsimp only | skip
  split
  · exact ((((gamma_care h.toApp _ s).noted F A b k).mul ((tarp_care D h.toApp _).noted F A b k))).smul
      ((basics D Z h H i none).1.noted F A b k)
  exact measurable_const

omit H in
private lemma shine_meas (i : ListID S) (u : Bool) (F : Forest S.ratio) (A : Stores S) (b : Finset ℕ) (k : S.Choices) : Measurable (uncurry (shine D s i u F A b k)) := by
  have hv := (((guarded D h.toApp i).noted F A b k).exp.sub (measurable_const (a:=(1:ℝ))))
  cases i with
  | letter i=> cases u <;> first | exact tip_meas h.toApp i s F A b k | exact hv.sub (tip_meas h.toApp i s F A b k)
  | _=>cases u <;> first | exact hv | exact measurable_const

lemma shutter_meas (i : Bill S ι) (a : Finset (Bill S ι)) (F A b k) : Measurable (uncurry (shutter D Z s i a F A b k)) := by
  rcases i with i|i|i|⟨i,t⟩|(i|⟨i,t⟩)|i
  · exact Complex.continuous_ofReal.measurable.comp (Booklet.enrolled D h.toApp i F A b k)
  · exact (basics D Z h H i _).2.1.noted F A b k
  · have ht := (Check.film D h.toApp i).noted F A b k
    have hv := (tarp_care D h.toApp (post S i)).noted F A b k
    unfold shutter choices uncurry; dsimp only; split
    · exact Complex.continuous_ofReal.measurable.comp ((ht.sub measurable_const).mul hv)
    exact Complex.continuous_ofReal.measurable.comp ((ht.sub measurable_const).mul measurable_const)
  · exact Complex.continuous_ofReal.measurable.comp (shine_meas D s h i t F A b k)
  · exact measurable_const
  · cases t
    · exact surge_meas D Z s h H ..
    exact ((basics D Z h H i none).2.2.noted F A b k).sub (surge_meas D Z s h H ..)
  exact measurable_const
end legality
end YM.PhysicalNext.Dictionary.Shipment
