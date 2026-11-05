import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Lists

/-! The actual Run at one local selection. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Lobbies
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp
open AnalyticBridge.LocalGaussian Spot Spot.Programme
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Defenses Voice.Check Parcel Shipment SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f}
variable {D : AnalyticBridge.LocalGaussian.Desk G S} {Z : Art ι D} {t : ℝ} {h : Lit D}
    {F : Forest S.ratio} {A : Stores S} {a : Ensign S ι}

namespace Casting
variable (C : Casting D Z a F A) (k₀ k : S.Choices)
local notation "u₀" => chosen D F k₀ A k
local notation "b₀" => Fleet.kSet a

def stage (h : Lit D) (t : ℝ) := schedule D k₀ b₀ h F A k t C.origins.1

local notation "Q" => stage C k₀ k h t

def keys (i : major D a A F) : (u₀).Gates b₀ := ((controlled D u₀ b₀ i).2 (registered C i.property)).choose -- D arg
lemma identity (i : major D a A F) : historical D (u₀) (keys C k₀ k i)=i := ((controlled D u₀ b₀ i).2 (registered C i.property)).choose_spec

def charged (i : paper D a A F) : (u₀).Log := ((prescribed D u₀ i).2 (press C i.property).1).choose
lemma paid (i : paper D a A F) : written D u₀ (charged C k₀ k i)=i := ((prescribed D u₀ i).2 (press C i.property).1).choose_spec

def column (i : alternates a) : (u₀).Log := ((prescribed D u₀ i.val.1).2 (worlds C i.property).1).choose
lemma level (i : alternates a) : written D u₀ (column C k₀ k i)=i.val.1 := ((prescribed D u₀ i.val.1).2 (worlds C i.property).1).choose_spec

lemma key_on (h : Lit D) (s : ℝ) (i : major D a A F) :
    keys C k₀ k i∈ (stage C k₀ k h s).required ↔ i.val.elim (wanted S D.betaHat A) (fun _=>True) := by
  rw [show (stage C k₀ k h s).required= Parcel.kept D u₀ b₀ from rfl,Parcel.stays D (keys C k₀ k i),identity]; rfl

lemma column_on (h : Lit D) (s : ℝ) (i : alternates a) : column C k₀ k i∉(stage C k₀ k h s).paying := by
  rw [show (stage C k₀ k h s).paying= tapped D u₀ from rfl, Parcel.heated D (column C k₀ k i),level]; exact (worlds C i.property).2.1

lemma paid_on (h : Lit D) (s : ℝ) (i : paper D a A F) : charged C k₀ k i∈(stage C k₀ k h s).paying := by
  rw [show (stage C k₀ k h s).paying= tapped D u₀ from rfl, Parcel.heated D (charged C k₀ k i),paid]; exact (press C i.property).2

abbrev lead (i : specials a) : ↥(alternates a) := ⟨i.val, (Finset.mem_filter.mp i.property).1⟩
abbrev dial (i : everyday a) : ↥(alternates a) := ⟨i.val,(Finset.mem_filter.mp i.property).1⟩
lemma column_injective : Injective (column C k₀ k) := by
  intro i j he
  have ht := congr_arg (written D u₀) he; rw [level C,level C] at ht
  apply Subtype.ext; apply Prod.ext ht
  have hv : (i.val.1, j.val.2) ∈ alternates a := by rw [ht]; exact j.property
  exact variant C i.property hv

def door (h : Lit D) (t : ℝ) (i : major D a A F) : (stage C k₀ k h t).Stamp :=
    let j:=keys C k₀ k i
    if e : j∈(stage C k₀ k h t).required then Stamp.heldGate j e else
      Stamp.billG j (Finset.mem_compl.mpr e) (show Fin 1 from 0)

def manuscript (h : Lit D) (t : ℝ) (i : (u₀).Log) (j : ℕ) : (u₀).Submenu (fun V p => Real.exp ((stage C k₀ k h t).posted i V p)-1) := {
  size := 2
  buy := fun z V p=> if z.val=0 then pushcard D b₀ u₀ (tip j t (D:=D)) V p else Real.exp ((stage C k₀ k h t).posted i V p)-1-pushcard D b₀ u₀ (tip j t (D:=D)) V p
  rebuild := fun V p _=>by simp [Fin.sum_univ_two] }

-- pull Nat out of a *special* name without looking at price.
def title (i : specials a) : ℕ := match i.val.1 with
  | .letter i=>i
  | _=>0
lemma title_way (i : specials a) : i.val.1=Legend.letter (title i) := by
  have h1 := (Finset.mem_filter.mp i.property).2
  unfold title
  split <;> first | assumption | rename_i hh; apply False.elim ?_; -- hh catch
  all_goals -- easier cases on i.val.1
    generalize he : i.val.1=x at *
    cases x <;> simp [hasVersions] at *

def badge (h : Lit D) (t : ℝ) (i : specials a) : (stage C k₀ k h t).Stamp :=
    let j := column C k₀ k (lead i)
    Stamp.billLog j (column_on C k₀ k h t (lead i)) (manuscript C k₀ k h t j (title i)) (by
      have hp : written D u₀ j=Legend.letter (title i) := (level C ..).trans (title_way i)
      change Parcel.columns D b₀ u₀ j t=_
      unfold Parcel.columns; rw [hp]; rfl)
      (show Fin 2 from if i.val.2 then 1 else 0)

abbrev Alien := ↥(major D a A F) ⊕ ↥(specials a)

-- Same q.one_copy even for alternatives chosen in a fused family.
def port (h : Lit D) (t : ℝ) : (stage C k₀ k h t).Run (Alien (D:=D) (A:=A) (F:=F) (a:=a)) ↥(paper D a A F) ↥(everyday a) := by
  refine ⟨Sum.elim (door C k₀ k h t) (badge C k₀ k h t), charged C k₀ k,
    fun i=>column C k₀ k (dial i),paid_on C k₀ k h t, fun i=>column_on C k₀ k h t (dial i),fun i=>?_,?_⟩
  · let j:=column C k₀ k (dial i)
    change Parcel.columns D b₀ u₀ j t=none
    unfold Parcel.columns; rw [show written D u₀ j=i.val.1 from level C k₀ k (dial i)]
    have ht:(hasVersions i.val.1 : Bool)=false := (Finset.mem_filter.mp i.property).2
    cases he : i.val.1 with
    | letter z => rw [he] at ht; exact False.elim (by simpa [hasVersions] using ht)
    | _=>rfl
  have he (i : major D a A F) : (stage C k₀ k h t).atom (door C k₀ k h t i) = Sum.inl (keys C k₀ k i) := by
    unfold door; dsimp only; split <;> rfl
  have hb (i:specials a) : (stage C k₀ k h t).atom (badge C k₀ k h t i)=Sum.inr (column C k₀ k (lead i)) := rfl
  have hp : Injective (keys C k₀ k) := fun i j hz=>Subtype.ext (by rw [← identity C k₀ k i,← identity C k₀ k j,hz])
  have hq : Injective (charged C k₀ k) := fun i j hz=> Subtype.ext (by rw [← paid C k₀ k i,← paid C k₀ k j,hz])
  have ht (i) (j) : column C k₀ k i≠charged C k₀ k j := fun H=>column_on C k₀ k h t i (H ▸ paid_on C k₀ k h t j)
  have hr (i : specials a) (j : everyday a) : column C k₀ k (lead i)≠column C k₀ k (dial j) := (column_injective C k₀ k).ne fun H=>by
    have he1:= (Finset.mem_filter.mp i.property).2; have he2 := (Finset.mem_filter.mp j.property).2
    have he3 : i.val.1=j.val.1:=congr_arg (fun x:↥(alternates a)=>x.val.1) H
    rw [he3,he2] at he1; contradiction
  rintro ((i|i)|i|i) ((j|j)|j|j) hh <;> simp only [Sum.elim_inl,Sum.elim_inr,hb,he,Sum.inl.injEq,Sum.inr.injEq,
    reduceCtorEq] at hh ⊢ <;> first | exact hh.elim | exact hp hh | exact hq hh | exact (hr _ _ hh).elim | exact (hr _ _ hh.symm).elim | exact (ht _ _ hh).elim | exact (ht _ _ hh.symm).elim | exact Subtype.ext (congr_arg (fun x:↥(alternates a)=>x.val) (column_injective C k₀ k hh))
end Casting
end YM.PhysicalNext.Dictionary.Lobbies
