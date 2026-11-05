import YM.Next.SCHEDULE.Stadium
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Folios
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Lines
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Paths
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Vertices



/-! Independent (of A,F,V,k) letter names, retaining multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify

namespace Voice
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
    {F F' : Forest S.ratio} {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices}
local notation "t₀" => D.betaHat
local notation "R" => radiusB D.betaHat
local notation "T" => D.tube

def decodePlace {ι : Type} [Countable ι] (X : ι → Support c) : ℕ→ Support c := Function.extend (barcode ι) X (fun _=>∅)
lemma placed {ι : Type} [Countable ι] (X : ι → Support c) (i : ι) : decodePlace X (barcode ι i)=X i :=
  (barcode ι).injective.extend_apply ..

def offset (d : AnalyticBridge.LocalGaussian.Desk G S) (i j : Bond f) (n : ℕ) : Support c :=
  insert (portOf S i) (insert (portOf S j) (decodePlace (walkLens S (radiusB d.betaHat) i j) n))

/-- independent log address family, Nat still indexes the chosen chain;
don't confuse `folio` Fsct and `starboard` limit. `spark` too carries
the intermediate bond order by its n; off-domain n goes to zero. -/
inductive Legend (c f : Side) (S : StepData c f) : Type
 | row (i : Spot.RowPosts c f)
 | glaze (e : Bond f)
 | deficit (e : Bond f)
 | folio (n : ℕ)
 | starboard (n : ℕ)
 | thin (i : Slots S)
 | surge (e : Bond f)
 | spark (e e' : Bond f) (n : ℕ)
 | opened (i : Spot.BasePosts c f)
 | letter (j : ℕ)

abbrev ListID (_S : StepData c f) := Legend c f _S

instance : Countable (ListID S) := by
  let f₁ : Spot.RowPosts c f ⊕ (Bond f ⊕ Bond f ⊕ ℕ ⊕ ℕ ⊕ Slots S ⊕ Bond f ⊕ (Bond f × Bond f × ℕ) ⊕ Spot.BasePosts c f ⊕ ℕ) → ListID S := Sum.elim Legend.row (Sum.elim Legend.glaze (Sum.elim Legend.deficit (Sum.elim Legend.folio (Sum.elim Legend.starboard (Sum.elim Legend.thin (Sum.elim Legend.surge (Sum.elim (fun p => Legend.spark p.1 p.2.1 p.2.2) (Sum.elim Legend.opened Legend.letter))))))))
  have ht : Function.Surjective f₁ := by
    rintro (i|i|i|i|i|i|i|⟨j,l,n⟩|j|j) <;>
      first | exact ⟨.inl i,rfl⟩ | exact ⟨.inr (.inl i),rfl⟩ |
      exact ⟨.inr (.inr (.inl i)),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inl i))),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inr (.inl i)))),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inr (.inr (.inl i))))),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inl i)))))),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨j,l,n⟩))))))),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))))),rfl⟩ |
      exact ⟨.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr j)))))))),rfl⟩
  letI : Countable (Spot.RowPosts c f) := inferInstance
  letI : Countable (Spot.BasePosts c f) := inferInstance
  exact ht.countable

def columns (d : AnalyticBridge.LocalGaussian.Desk G S) : Dots f→Support c := Sum.elim
    (fun i=> AnalyticBridge.RelativeLogdet.lens (portOf S) 20 (radiusB d.betaHat) i)
    (inventory (portOf S) 20 (radiusB d.betaHat))

def native (i : ListID S) : Support c := match i with
  | .row i => {i.1.act (hinge S i.2)}
  | .glaze e | .deficit e | .surge e => {portOf S e}
  | .folio n => decodePlace (columns D) n
  | .starboard n => decodePlace (ι:=Letter (Bond f) 0) (inventory (portOf S) 20 R) n
  | .thin i => {spot S i}
  | .spark i j n => offset D i j n
  | .opened i => chaperone D i
  | .letter i => (inspected (D.labels.reg i).support).image S.ratio.parent

def written (u : Spot D) : u.Log→ListID S
  | .inl i=>.row i
  | .inr (.inl i)=>.glaze i.val.val
  | .inr (.inr (.inl (.inl i)))=>.deficit i.val.val
  | .inr (.inr (.inl (.inr (.inl i))))=>.folio i
  | .inr (.inr (.inl (.inr (.inr i))))=>.starboard i
  | .inr (.inr (.inr (.inl (.inl i))))=>.thin i
  | .inr (.inr (.inr (.inl (.inr (.inl i)))))=>.surge i.val.val
  | .inr (.inr (.inr (.inl (.inr (.inr (i,j,n))))))=>.spark i.val.val j.val.val n
  | .inr (.inr (.inr (.inr (.inl i))))=>.opened i
  | .inr (.inr (.inr (.inr (.inr i))))=>.letter i

-- all cases, *even if coefficient is zero*, repeated physical
-- occurrences have still distinct addresses.
theorem once (u : Spot D) : Injective (written D u) := by
  rintro (i|i|(i|i|i)|(i|i|⟨i,l,n⟩)|i|i) (j|j|(j|j|j)|(j|j|⟨j,t,m⟩)|j|j) h <;>
    simp only [written,reduceCtorEq,Legend.row.injEq,Legend.glaze.injEq,Legend.folio.injEq,Legend.starboard.injEq, Legend.deficit.injEq,
      Legend.surge.injEq, Legend.thin.injEq,Legend.spark.injEq,Legend.letter.injEq,Legend.opened.injEq,
      Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq,Subtype.val_inj] at h ⊢ <;> first | exact h.elim | exact h

def chainBuy (i j : Bond f) (n : ℕ) : Formula G S ℝ := fun F A b k V p=> if Physical.openBond A F t₀ i ∧ Physical.openBond A F t₀ j then
    ∑ a:G.ColorIndex,∑ z:G.ColorIndex, (p.2 i a*(number (itinerary D F A k V (i,a) (j,z)) n * p.2 j z))/2 else 0

-- Stable across log budgets; no unearned identities for these prices.
def sew (i : ListID S) : Formula G S ℝ := fun F A b k V p=> match i with
  | .row i => Voice.coin D i F A b k V p
  | .glaze i => if Physical.openBond A F t₀ i then logGuard D.broadCut D.chart D.radius (aura D F A b k V p i) else 0
  | .deficit i => if Print.winter t₀ A F i then -Real.log (spare D.chart D.input.beta) else 0
  | .folio n => -(1/2)*(number (dark D F A k V) n)
  | .starboard n => (1/2)*(number (customs D F A k V) n)
  | .thin i => -(slip^2*debit D 0 i F A b k V p)/D.g^2
  | .surge i => smoky D i F A b k V p
  | .spark i j n => chainBuy D i j n F A b k V p
  | .opened i=> cart D i F A b k V p
  | .letter i=> -D.labels.regularOccurrence D.input.p i (skin D F A b k V p)

lemma cream (h : Lit D) (F : Forest S.ratio) (A : Stores S) (k k₀ : S.Choices) (V : Config G c) (b : Finset ℕ)
    (hv : A.flags=RG.flags (temp D.betaHat) V) (p : Refs G f) (i : (chosen D F k₀ A k).Log) :
    let u := chosen D F k₀ A k
    u.price (Notify.packets D F k₀ A k h) i V (Print.see t₀ A F p)=sew D (written D u i) F A b k V p := by
  intro u
  let y := Print.see t₀ A F p
  obtain ⟨C,hC⟩:=h.earns A F V hv; obtain ⟨η,hη,hP⟩:=h.gaps A F V k hv
  have he := Print.painted T t₀ D.broadCut D.radius D.g k V h.aperture hC hη hP p
  have hl : skin D F A b k V p = u.hard V y:=he
  rcases i with i|i|(i|i|i)|(i|i|⟨i,j,n⟩)|i|i
  · exact (agreed_coin D h.toApp i k k₀ b F V hv p).symm
  · unfold price written sew lacquer; dsimp only
    rw [if_pos (show Physical.openBond A F t₀ i.val.val from ⟨i,rfl⟩)]
    exact congr_arg (logGuard D.broadCut D.chart D.radius)
      (Print.tinting T t₀ D.broadCut D.radius D.g k i V h.aperture hC hη hP p).symm
  · unfold price written sew book; dsimp only; exact (if_pos ((Print.sees_frost t₀ A F i.val).mpr i.property)).symm
  · rfl
  · rfl
  · exact thin_paid D h.toApp k V hv p F i b
  · exact (Voice.clouded D h.toApp k V hv p b i).symm
  · unfold written sew chainBuy; dsimp only; rw [if_pos (show Physical.openBond A F t₀ i.val.val ∧ Physical.openBond A F t₀ j.val.val from
      ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩)]; rfl
  · change u.basePost V y i=cart D i F A b k V p
    rcases i with ⟨s,i⟩|i
    · unfold basePost cart; dsimp only; rw [hl]
    rcases i with ⟨s,i,j⟩; rfl
  change -D.labels.regularOccurrence D.input.p i (u.hard V y)=_
  rw [← hl]; rfl
end Voice
end YM.PhysicalNext.Dictionary
