import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Cue
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Fringe
import YM.SectorNext.RECONNECTED_LOCALITY.Optional

/-!
# Consuming the independent review *if* the support ledger covers these
letters.

A way to compose with the verified `Optional.expanding` even for Logs
which might not be summable when their physical prerequisites have been
expanded: buy it *from the Crude bills on this page* (zero bases don't
consume convergence). `Programme.optional` / `floor.repairs` on their own
are finite cutoff results on the unmarked currency. Here put Opinion
prices on the independent addresses recorded in the spelling.
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
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S) (h : Lit D)
    (F : Forest S.ratio) (A : Stores S) (k₀ k : S.Choices) (V : Config G c) (b : Finset ℕ) (s : ℝ)
local notation "x₀"=>D.betaHat
local notation "B"=>radiusB x₀
local notation "H₀"=>chosen D F k₀ A k
local notation "T"=>Voice.Check.Test

/- Whole A step mandatory list. -/
local notation "P" => Fleet.packs S (hump B) (Fleet.manifest A)

def invoked := (P).biUnion (fun i=>Booklet.checks D i F A)
def volumes := (P).biUnion (fun i=>Booklet.history D i F A)

include k₀ k in
lemma rolled (i : T c f) : i∈invoked D F A ↔ live x₀ F A b (.inl i) ∧ wanted S x₀ A i := by
  rw [← Finset.inl_mem_disjSum (t:=b),invoked, (Booklet.bundled D F A k k₀ b).2,
    Finset.mem_image,← show Sum.inl i ∈Set.range (historical D H₀ (b:=b)) ↔ live x₀ F A b _ from controlled D H₀ b _]
  constructor
  · rintro ⟨j,hj,hp⟩
    have he:=(Parcel.stays D j).mp hj; rw [hp] at he
    exact ⟨⟨j,hp⟩,he⟩
  rintro ⟨⟨j,hj⟩,hi⟩; exact ⟨j,(Parcel.stays D j).mpr (by rw [hj]; exact hi), hj⟩
-- k,k₀ only for A packet lemma above. use include.

-- Masks on the independent addresses.
def trying (i : T c f) : Prop := live x₀ F A b (.inl i) ∧ ¬wanted S x₀ A i
def offering (i : ListID S × Bool) : Prop := present x₀ A F i.1 ∧ ¬wants D A i.1 ∧ (i.2=false ∨ hasVersions i.1=true)

def examFee (p : Refs G f) (i : T c f) : ℝ := if trying D F A b i then Casting.complement D i F A b k V p else 0
def volley (p : Refs G f) (i : ListID S × Bool) : ℝ := if offering D F A i then Shipment.shine D s i.1 i.2 F A b k V p else 0

lemma opens (uPAGE : (H₀).Visual) (i : T c f) :
    poster D F A k₀ k V b uPAGE i = (if i∈invoked D F A then films D i F A b k V (Print.backdrop x₀ A F uPAGE) else 1) *
      (1+ examFee D F A k V b (Print.backdrop x₀ A F uPAGE) i) := by
  simp only [poster,examFee,trying,rolled D F A k₀ k b i,Casting.complement,Parcel.frontage]
  by_cases he : live x₀ F A b (Sum.inl i)
  · by_cases ht : wanted S x₀ A i
    · simp [he,ht]
    cases hj : bare i <;> simp [he,ht,hj]
  simp [he]

lemma portrait (i : ListID S) (p : Refs G f) :
    Optional.factors Prod.fst (Formal.volley D F A k V b s p) i = if present x₀ A F i ∧ ¬wants D A i then Real.exp (introduce D i F A b k V p) else 1 := by
  let f:=Formal.volley D F A k V b s p
  let e : Bool ≃ {x : ListID S × Bool // x.1=i} :=
    { toFun u:=⟨(i,u),rfl⟩
      invFun q:=q.val.2
      left_inv u:=rfl
      right_inv := fun y=> Subtype.ext (Prod.ext (y.property.symm) rfl) }
  unfold Optional.factors; rw [← e.tsum_eq]
  change 1+(∑' u:Bool,f (i,u))=_
  rw [tsum_fintype,Fintype.sum_bool]
  unfold f volley offering; dsimp only
  by_cases hz : present x₀ A F i ∧ ¬wants D A i
  · cases i <;> simp [hz,hasVersions,shine] -- try
  simp only [if_neg hz]
  rw [if_neg (fun hv=>hz ⟨hv.1,hv.2.1⟩), if_neg (fun hv=>hz ⟨hv.1,hv.2.1⟩)]; ring

-- `repository` alignment applied to independent word names; exponent
-- bills only when original fine/tests succeeded (and all doors live so
-- taw=1). Otherwise do NOT purchase price series.
include h
private theorem runs (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (ok : (∏ i : Quizzes D H₀,exam D F A k₀ k V b uPAGE i) ≠0) :
    let p:=Print.backdrop x₀ A F uPAGE
    let t := volumes D F A
    HasSum (fun i=>if present x₀ A F i ∧ ¬wants D A i then introduce D i F A b k V p else 0)
      ((H₀).sumValue V uPAGE - (∑ i∈t,sew D i F A b k V p)) := by
  intro p t
  let r := (written D H₀); let q:=Parcel.tapped D H₀
  let g i := (H₀).price (packets D F k₀ A k h) i V uPAGE
  have he : ∑ i∈q,g i=∑ i∈t,sew D i F A b k V p := by
    rw [show t=q.image r from (Booklet.bundled D F A k k₀ b).1,Finset.sum_image (once D (H₀)).injOn]
    refine Finset.sum_congr rfl fun i hi=>?_ 
    have hs := arranged D h F A k₀ k V b uPAGE hc ok i
    rw [Parcel.receipt,if_pos (show wants D A _ from (Parcel.heated D i).mp hi)] at hs
    exact hs.symm
  let v := (H₀).repository (packets D F k₀ A k h) V hc h.valid uPAGE
  have hq : HasSum (fun i=>if i∈q then g i else 0) (∑ i∈q,g i) := by
    have hi (i) (he:i∉q) : (if i∈q then g i else 0)=0 := if_neg he
    have hh : HasSum _ _ := (hasSum_sum_of_ne_finset_zero (f:=fun i=>if i∈q then g i else 0) (L:=SummationFilter.unconditional _) hi)
    convert! hh using 1
    exact Finset.sum_congr rfl fun i he => (if_pos he).symm
  let t' i:=if i∈q then 0 else g i
  have hr : HasSum t' _ := (show HasSum g _ from v).sub hq |>.congr_fun (fun i=>by by_cases he : i∈q <;> simp [t',he])
  rw [he] at hr
  have ht := (hasSum_extend_zero (once D H₀)).mpr hr
  apply ht.congr_fun
  intro i
  by_cases hf : i ∈ Set.range r
  swap
  · rw [Function.extend_apply' _ _ _ hf,if_neg (fun hv=>hf ((prescribed D H₀ i).mpr hv.1))]; rfl
  obtain ⟨j,rfl⟩:=hf
  have hl : present x₀ A F (r j):=advertised D _
  -- extension first vs second
  rw [(once D H₀).extend_apply _ _ _]
  by_cases hh : wants D A (r j)
  · simp only [hl,hh,not_true_eq_false,and_false,↓reduceIte]
    unfold t'; rw [if_pos ((Parcel.heated D j).mpr hh)]
  rw [if_pos ⟨hl,hh⟩]
  have hq:= arranged D h F A k₀ k V b uPAGE hc ok j
  rw [Parcel.receipt,if_neg hh] at hq -- hh r)
  unfold t'; rw [if_neg (mt (Parcel.heated D j).mp hh)]; exact hq

abbrev Tryouts (S : StepData c f) := Finset (T c f) × Finset (ListID S × Bool)

def sealedBook (p : Refs G f) : ℝ := (∏ i∈ invoked D F A, films D i F A b k V p) * Real.exp (∑ i∈ volumes D F A, sew D i F A b k V p)
def tickets (p : Refs G f) (l : Tryouts S) : ℝ := (∏ j∈l.1,examFee D F A k V b p j) * Optional.subsetTerm Prod.fst (Formal.volley D F A k V b s p) l.2

set_option maxHeartbeats 400000 in
theorem wing (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (hi : D.Nonoverlap b) (χ : ℂ)
    (hs : let p:=Print.backdrop x₀ A F uPAGE
        Summable (fun i=> χ * ((sealedBook D F A k V b p*tickets D F A k V b s p i : ℝ):ℂ))) :
    let p:=Print.backdrop x₀ A F uPAGE
    HasSum (fun i=>χ * ((sealedBook D F A k V b p*tickets D F A k V b s p i : ℝ):ℂ))
      (χ * (( (∏ i,exam D F A k₀ k V b uPAGE i) * Real.exp ((H₀).sumValue V uPAGE) : ℝ):ℂ)) := by
  intro p; dsimp only at hs
  let C := sealedBook D F A k V b p
  let K i := Casting.complement D i F A b k V p
  let q := examFee D F A k V b p
  let e i:= Formal.volley D F A k V b s p i
  let E := ∏ i : T c f,(1+ q i)
  let O := ∏' i,Optional.factors Prod.fst e i
  let Z:=∏ i,exam D F A k₀ k V b uPAGE i
  let P₀ := ∏ i∈invoked D F A,films D i F A b k V p
  have hZ : Z=P₀*E := by
    unfold Z
    rw [← feed D h F A k₀ k V b uPAGE hc hi]
    simp_rw [opens D F A k₀ k V b uPAGE]
    rw [prod_mul_distrib]; refine congr_arg₂ HMul.hMul ?_ rfl
    unfold P₀
    rw [←prod_subset (subset_univ (invoked D F A)) (by intro i _ hi; exact if_neg hi)]
    exact Finset.prod_congr rfl fun i hi=> if_pos hi
  have hzero : Z≠0 → C≠0 := fun hz=>mul_ne_zero (left_ne_zero_of_mul (hZ ▸ hz)) (Real.exp_pos _).ne'
  have hΛ : C*(E*O)= Z * Real.exp ((H₀).sumValue V uPAGE) := by
    unfold C sealedBook; change P₀*_ * (E*O)=_
    rw [mul_mul_mul_comm,← hZ]; by_cases he: Z≠0
    swap; simp [of_not_not he] -- potential dependent rw; bullet
    have ht : O=Real.exp ((H₀).sumValue V uPAGE - (∑ i∈volumes D F A,sew D i F A b k V p)) := by
      have hr := runs D h F A k₀ k V b uPAGE hc he
      have hv i : Optional.factors Prod.fst e i=Real.exp (if present x₀ A F i ∧ ¬wants D A i then introduce D i F A b k V p else 0) := by
        rw [portrait]; split_ifs <;> simp
      unfold O; simp_rw [hv]; exact hr.rexp.tprod_eq
    rw [ht,←Real.exp_add]; congr 2; ring
  let t i := tickets D F A k V b s p i
  change Summable (fun i=>χ*(↑(C*t i):ℂ)) at hs
  change HasSum (fun i=>χ*(↑(C*t i):ℂ)) (χ*(↑(Z*_):ℂ))
  rw [←hΛ]
  simp_rw [Complex.ofReal_mul] at hs ⊢
  simp only [← mul_assoc] at hs ⊢
  let d:=χ*(↑C:ℂ)
  change Summable (fun i=>d*(t i:ℂ)) at hs
  change HasSum _ (d*(↑E:ℂ)*(↑O:ℂ))
  by_cases hd : d=0
  · change HasSum (fun i=>d*(t i:ℂ)) _
    simp_rw [hd,zero_mul]; exact hasSum_zero
  have hb := (summable_mul_left_iff hd).mp hs
  have T₀ : Summable t := by
    exact Complex.reCLM.summable hb
  have pick (j : ListID S × Bool) : t (∅,{j})=e j := by
    unfold t tickets Optional.subsetTerm
    dsimp only; rw [if_pos (show Fleet.pure Prod.fst {j} from fun i hi j hj hu=> Finset.mem_singleton.mp hj |>.trans (Finset.mem_singleton.mp hi).symm)]
    simp [e]
  have hl: Summable e := by
    rw [show e=(fun i=> t (∅,{i})) from funext fun i=> (pick i).symm]
    exact T₀.comp_injective (i:=fun i : ListID S × Bool=> ((∅,{i}) : Tryouts S)) (by intro i u he; exact Finset.singleton_injective (Prod.mk.inj he).2)
  have ha:= (Optional.expanding Prod.fst hl).1
  have hh : HasSum t (E*O) := by
    let f (i : Finset (T c f)) := ∏ j∈i,q j
    have he : HasSum f E := by
      unfold E; rw [prod_one_add]
      convert! hasSum_fintype f using 1
    exact he.mul ha T₀
  rw [mul_assoc d,←Complex.ofReal_mul]; exact (Complex.ofRealCLM.hasSum hh).mul_left d
end YM.PhysicalNext.Dictionary.Formal
