import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Stage

/-! Identification bridge for each run letter. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Lobbies.Casting
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open AnalyticBridge.LocalGaussian Spot Spot.Programme
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel Shipment SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable (D : AnalyticBridge.LocalGaussian.Desk G S) {Z : Art ι D} (t : ℝ) (h : Lit D)
    {F : Forest S.ratio} {A : Stores S} {a : Ensign S ι}

/-- Value at one chosen door; no loss of eligibility. -/
def complement (i : Voice.Check.Test c f) : Formula G S ℝ := fun F A l k V p=>
    (films D i F A l k V p-1)*if Parcel.bare i then tarp D (post S i) F A l k V p else 1

def latch (i : Voice.Check.Test c f ⊕ ℕ) : Formula G S ℝ := fun F A l k V p=> match i with
    | .inl i=>if wanted S D.betaHat A i then films D i F A l k V p else complement D i F A l k V p
    | .inr i=>intact D i F A l k V p

variable {D} (C : Casting D Z a F A) (k₀ k : S.Choices) (V : Config G c) {y : (chosen D F k₀ A k).Visual}
local notation "u₀" => chosen D F k₀ A k
local notation "b₀" => Fleet.kSet a
local notation "Q" => stage C k₀ k h t
local notation "N" => port C k₀ k h t
local notation "l₀" => Print.backdrop D.betaHat A F y

def lounge : Alien (D:=D) (a:=a) (F:=F) (A:=A) → Formula G S ℝ := Sum.elim
    (fun i : major D a A F=>latch D i.val) (fun j : specials a=> shine D t j.val.1 j.val.2)

include C
lemma podium (i : paper D a A F) :
    sew D i F A b₀ k V l₀ = (Q).posted ((N).settled i) V y := by
  have he:= charged C k₀ k i
  change _=receipt D (written D u₀ (Casting.charged C k₀ k i)) F A b₀ k V (Print.backdrop ..)
  rw [paid]; unfold Parcel.receipt; rw [if_pos (press C i.property).2]; rfl
lemma speaks (i : everyday a) : introduce D i.val.1 F A b₀ k V l₀ = (Q).posted ((N).marks i) V y := by
  change _=receipt D (written D u₀ (Casting.column C k₀ k (dial i))) F A b₀ k V (Print.backdrop ..)
  rw [level C]; unfold Parcel.receipt; rw [if_neg (worlds C (dial i).property).2.1]; rfl

lemma stays (i : Alien (D:=D) (F:=F) (A:=A) (a:=a)) :
    lounge t i F A b₀ k V l₀ = (Q).visit ((N).entry i) V y := by
  rcases i with i|i
  · let r := keys C k₀ k i
    let b:=Parcel.stores D b₀ u₀ r
    change latch D i.val F A b₀ k V l₀ = (Q).visit (door C k₀ k h t i) V y
    have hk : b V y=sales D i.val F A b₀ k V l₀ := by
      unfold b stores pushcard
      rw [identity]; rfl
    by_cases he : r∈ (Q).required
    · have hv := (key_on C k₀ k h t i).1 he
      unfold door; dsimp only; rw [dif_pos he]
      change _= b V y
      rw [hk]; unfold latch sales; cases hq : i.val with
      | inr i => rfl
      | inl j=>
        rw [hq] at hv; change wanted S D.betaHat A j at hv
        simp [frontage,hv]
    · have hv := mt (key_on C k₀ k h t i).mpr he
      unfold door; dsimp only; rw [dif_neg he]
      change _ = b V y - 1
      rw [hk]; unfold latch sales; cases hq : i.val with
      | inr i=>rw [hq] at hv; exact False.elim (hv trivial)
      | inl i=>rw [hq] at hv
               change ¬wanted _ _ _ i at hv
               unfold frontage complement; cases hl : Parcel.bare i <;> simp [hv,hl]
  let j:= i.val
  let r:= column C k₀ k (lead i)
  have he : written D u₀ r=j.1 := level C ..
  have hf : (Q).posted r V y= introduce D j.1 F A b₀ k V l₀ := by
    change receipt D (written D u₀ r) F A b₀ k V (Print.backdrop ..) = _
    rw [he]; unfold Parcel.receipt; rw [if_neg (worlds C (lead i).property).2.1]; rfl
  have hz j : pushcard D b₀ u₀ (tip (D:=D) j t) V y=tip (D:=D) j t F A b₀ k V l₀ := rfl
  change shine D t i.val.1 i.val.2 F A b₀ k V l₀=(if (if i.val.2 then (1:Fin 2) else 0).val=0
      then pushcard D b₀ u₀ (tip (D:=D) (title i) t) V y else Real.exp ((Q).posted r V y)-1-pushcard D b₀ u₀ (tip (D:=D) (title i) t) V y)
  unfold j at hf; rw [hf,hz]; unfold shine; rw [title_way i]; cases hq : i.val.2 <;> simp


end YM.PhysicalNext.Dictionary.Lobbies.Casting
