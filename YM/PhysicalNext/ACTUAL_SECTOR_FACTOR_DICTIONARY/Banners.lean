import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Eclipse

/-!
# Syntax for carrying goods into Tryouts

Not separate choices of `R`, carry the SAME R and V on every head. Preserve
actual K indices even when its essay is numerically zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Formal
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.PhysicalNext.Dictionary.Formal
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment Lobbies SectorNext.Reconnect
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]

abbrev Head (I : Type) := Finset I × Finset ℕ × Finset ℕ × Finset (ℕ×ℕ)
-- abbrevivation to ease inference
abbrev coin (i : Head I) := i.1  -- units
abbrev menu (i : Head I) := i.2.1 -- bulk (Bool later)
abbrev team (i : Head I) := i.2.2.1 -- K parents including vacuum
abbrev torn (i : Head I) := i.2.2.2 -- qualified
abbrev Versions (i : Head I) := ↥(menu i)→Bool

variable (i : Head I)

-- Record the Mark-bearing emissions and their sets on R (even before
-- checking censorship).
abbrev Emit (I : Type) := I ⊕ ℕ ⊕ ℕ×ℕ
def emissions : Finset (Emit I) := (coin i).disjSum ((menu i).disjSum (torn i))
def token (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art I D) : Emit I → Finset I := Sum.elim ({·})
    (Sum.elim Z.names fun j=>Z.sig j.1 j.2)

def slide (β : Versions i) : ↥(menu i) ↪ ℕ×Bool := ⟨fun j=>(j.val,β j),fun _ _ e=>Subtype.ext (congr_arg Prod.fst e)⟩
def curtains (β : Versions i) := (menu i).attach.map (slide i β)
variable (D : AnalyticBridge.LocalGaussian.Desk G S) (A : Stores S) (Z : Art I D)
local notation "B"=>radiusB D.betaHat
local notation "Q" => Fleet.packs S (hump B) (Fleet.manifest A)
local notation "T"=>Voice.Check.Test

def shops (β : Versions i) (l : Tryouts S) : Finset (Bills S I) := l.1.disjSum (l.2.disjSum (((coin i).disjSum (curtains i β)).disjSum (torn i)))
def submit (β : Versions i) (l : Tryouts S) := Fleet.draft (hump B) A (team i) (shops i β l)
-- for easier independent instance function use
abbrev Hypothesis (I : Type) := Σ i : Head I,Versions i
def construct (l : Hypothesis I × Tryouts S) : Finset (Bill S I) := submit l.1.1 D A l.1.2 l.2

section
variable (β : Versions i)
omit [DecidableEq I]
lemma slides {j b} : (j,b)∈curtains i β ↔ ∃ hj : j∈menu i, β ⟨j,hj⟩ = b := by
  rw [curtains, Finset.mem_map]
  constructor
  · rintro ⟨p,H,hb⟩
    cases p with
    | mk p hp=>
      simp only [slide,Embedding.coeFn_mk,Prod.mk.injEq] at hb
      obtain ⟨rfl,rfl⟩:=hb; exact ⟨hp,rfl⟩
  exact fun ⟨hj,he⟩=>⟨⟨_,hj⟩, Finset.mem_attach _ _,Prod.ext rfl he⟩
lemma sliding : (curtains i β).image Prod.fst=menu i := by
  ext j; rw [Finset.mem_image]; constructor
  · rintro ⟨⟨b,s⟩,hb,rfl⟩; obtain ⟨hz,hh⟩:=(slides i β).mp hb; exact hz
  exact fun hj=>⟨(j,β ⟨j,hj⟩), (slides i β).mpr ⟨hj,rfl⟩,rfl⟩
lemma one_arrow : Fleet.pure Prod.fst (curtains i β) := by
  rintro ⟨j,s⟩ hj ⟨l,t⟩ hl he; change l=j at he; subst l
  obtain ⟨hq,rfl⟩:=(slides _ _).mp hj; obtain ⟨h0,rfl⟩:=(slides _ _).mp hl; rfl

-- recover every pure bulk choice.
lemma swatches {r : Finset (ℕ×Bool)} (h₁ : Fleet.pure Prod.fst r) (h₂ : r.image Prod.fst= menu i) : ∃ u : Versions i,r=curtains i u := by
  have he (j:menu i) : ∃ t,(j.val,t)∈r := by
    obtain ⟨⟨k,t⟩,hk,hf⟩:=Finset.mem_image.mp (show j.val∈ r.image Prod.fst by rw [h₂]; exact j.property)
    change k=j.val at hf; exact ⟨t,hf ▸ hk⟩
  choose u hu using he; use u; ext ⟨j,t⟩; rw [slides]
  constructor
  · intro hi; have hp : j∈menu i := h₂ ▸ Finset.mem_image_of_mem Prod.fst (by exact hi)
    use hp; exact congr_arg Prod.snd (h₁ _ hi _ (hu ⟨_,hp⟩) rfl)
  rintro ⟨hp,rfl⟩; exact hu ⟨j,hp⟩
end

omit [DecidableEq I]
lemma unweave {i j: Head I} (x : Versions i) (y : Versions j) (b d : Tryouts S) (h : shops i x b=shops j y d) : b = d ∧ coin i=coin j ∧
    curtains i x= curtains j y ∧ torn i=torn j := by
  refine ⟨Prod.ext ?_ ?_,?_,?_,?_⟩
  · simpa only [shops,Finset.toLeft_disjSum] using congr_arg Finset.toLeft h
  · simpa only [shops, Finset.toRight_disjSum,Finset.toLeft_disjSum] using
      congr_arg (fun i : Finset (Bills S I)=>i.toRight.toLeft) h
  · simpa only [shops, Finset.toRight_disjSum,Finset.toLeft_disjSum] using
      congr_arg (fun i : Finset (Bills S I)=>i.toRight.toRight.toLeft.toLeft) h
  · simpa only [shops, Finset.toRight_disjSum,Finset.toLeft_disjSum] using
      congr_arg (fun i : Finset (Bills S I)=>i.toRight.toRight.toLeft.toRight) h
  simpa only [shops, Finset.toRight_disjSum,Finset.toLeft_disjSum] using
      congr_arg (fun i : Finset (Bills S I)=>i.toRight.toRight.toRight) h

lemma build_inj : Injective (construct D A (I:=I)) := by
  rintro ⟨⟨i,x⟩,p⟩ ⟨⟨j,y⟩,q⟩ hi
  have hm := (Fleet.draft_inj (S:=S) (α:=Bills S I) (hump B) (a₁:=(A,team i, shops i x p)) (a₂:=(A,team j, shops j y q)) hi)
  have hh := (Prod.ext_iff.mp (Prod.ext_iff.mp hm).2) -- use congr_arg Prod.snd
  obtain ⟨hr,hx,hk,hl⟩:=unweave x y p q hh.2
  have hq : i=j := Prod.ext hx (Prod.ext (show menu i=menu j by rw [←sliding i x,←sliding j y,hk]) (Prod.ext hh.1 hl))
  subst j q
  suffices h : x=y by rw [h]
  funext k
  have he : (k.val,x k)∈curtains i y := hk ▸ (slides i x).mpr ⟨k.property,rfl⟩
  obtain ⟨_,ht⟩ := (slides _ _).mp he; exact ht.symm

lemma build_range (ρ : Finset (Bill S I)) {v : Activities G f}
    (he : Fleet.draft (hump B) A (Fleet.kSet ρ) (Fleet.addSet ρ)=ρ)
    (hp : Words.permits (Fleet.required S v (hump B) question) ρ) : ρ ∈ Set.range (construct D A) := by
  let u:=Fleet.addSet ρ; let r:=u.toRight.toRight.toLeft.toRight
  let s:Head I := (u.toRight.toRight.toLeft.toLeft, r.image Prod.fst,Fleet.kSet ρ,u.toRight.toRight.toRight)
  have hr : Fleet.pure Prod.fst r := by
    rintro ⟨i,t⟩ hi ⟨j,m⟩ hj ht
    have hx i t (hi : (i,t)∈r) : bead i t∈u := by
      simpa only [r,Finset.mem_toRight,Finset.mem_toLeft] using hi
    have hh := ((Fleet.classified ..).mp hp).2.2 _ (hx i t hi) _ (hx j m hj)
      (show question (ι:=I) (S:=S) (bead j m)=question (bead i t) by change j=i at ht; cases ht; rfl) -- binder ι
    simpa only [bead,Sum.inr.injEq,Sum.inl.injEq] using hh
  obtain ⟨y, hy⟩:=swatches s (r:=r) hr rfl
  refine ⟨(⟨s,y⟩,u.toLeft,u.toRight.toLeft),?_⟩
  change Fleet.draft (hump B) A (Fleet.kSet ρ) _ =_
  rw [shops,← hy]; simp only [coin,s,torn,r,Finset.toLeft_disjSum_toRight]; exact he
end YM.PhysicalNext.Dictionary.Formal
