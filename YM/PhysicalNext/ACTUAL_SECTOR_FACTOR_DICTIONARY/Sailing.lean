import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Shadows
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Sound
import YM.Push.ABSOLUTE_SUMS.Breadth

/-!
# Integrate a component family, even when complex markers are live

Specialize Roster.valued/tags to actual Scripts and split price into
real/imag, so no new factorization or stencil criteria necessary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Arbor
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian Spot AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.Push.SectorMeasure
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment Formal Lobbies Route SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (Z : Art I D) (h : Lit D) (F : Forest S.ratio) (k₀ k : S.Choices) (V : Config G c) (t : ℝ)
    (A : Stores S) (m : Finset I) (Q : Finset (Ensign S I))
local notation "x₀"=>D.betaHat
local notation "K"=> icons D Z
local notation "L"=> Shipment.stars D F k₀
local notation "H"=> Shipment.theater D Z h F k₀ V
local notation "ψ"=> lines D Z t h F k₀ V
local notation "g"=> carrier D Z m

def peek (x : Bool) (z : ℂ) := if x then z.im else z.re
def price (x : Bool) := if x then Complex.I else (1:ℂ)

-- finite real licenses; helper for the two purposes and hypotheses differ.
lemma depart {κ : Type*} [DecidableEq κ] [Fintype κ] (t : κ→ℂ) : ∏ i,t i =
    ∑ x:κ→Bool,(∏ i,price (x i))* (↑(∏ i,peek (x i) (t i)):ℝ) := by
  have he (i) : t i=∑ x,price x*(peek x (t i):ℝ) := by rw [Fintype.sum_bool]; simp only [price,peek,↓reduceIte,one_mul,reduceCtorEq]; rw [mul_comm,add_comm,Complex.re_add_im]
  calc
    _ = ∏ i,∑ x,price x*(↑(peek x (t i)):ℂ) := Finset.prod_congr rfl fun i _=>he i
    _ = _ := by rw [Fintype.prod_sum]; simp_rw [Finset.prod_mul_distrib]; push_cast; rfl

variable (hw : Shipment.Valid D I Z) (hp : A.flags=RG.flags (temp D.betaHat) V)
    {b : Ensign S I→ℝ} (he : Letters D h F k₀ V Z t b)

-- no repeated integration-license input for multiple uses of a parent, only per registered component
include hw he
lemma living_cost (i : Ensign S I) k : Integrable (ψ i k) ((H).paper i k):=(he.every k i).mono'
    (ensemble D Z t h hw F k₀ V k).aestronglyMeasurable (Eventually.of_forall fun _=>le_rfl)

private lemma sections (x : Bool) (i : Ensign S I) k :
    let p y:=ψ i k y; let μ:=(H).paper i k
    Integrable (fun y=>peek x (p y)) μ ∧ (∫ y,peek x (p y)∂μ) = peek x (rates D Z h F k₀ k V i t) := by
  intro p μ; have hi := living_cost D Z h F k₀ V t hw he i k
  cases x
  · exact ⟨Integrable.re hi, integral_re hi⟩
  exact ⟨Integrable.im hi, integral_im hi⟩

include hp
set_option maxHeartbeats 400000 in
lemma chapter (hA : (L).Available V) (hQ : (K).Makes A m Q) :
    let μ:=(L).climate V A k
    Integrable (fun y=>plume D Z t h F k₀ V A m Q k y) μ ∧
      (∫ y, plume D Z t h F k₀ V A m Q k y ∂μ)= ∏ i ∈ Q,rates D Z h F k₀ k V i t := by
  intro μ
  let φ (x : Q→ Bool) : (H).Script := fun i k p=>if hz:i∈Q then peek (x ⟨i,hz⟩) (ψ i k p) else 0
  let v (x : Q→Bool) y := ((H).imprint (φ x) hp hQ k y)
  have hr x j : Integrable (φ x j k) ((H).paper j k) := by
    by_cases hk:j∈Q
    · rw [show φ x j k=fun p=>peek (x ⟨j,hk⟩) (ψ j k p) from funext fun p=>dif_pos hk]; exact (sections D Z h F k₀ V t hw he _ j k).1
    unfold φ; simp_rw [dif_neg hk]; exact integrable_zero ..
  have h₁ x := (H).valued hA k (hr x) hp hQ
  let K₁ (x : Q→Bool) := ∏ i,price (x i)
  let χ (x : Q→Bool) (y : Room G x₀ F A):ℂ := K₁ x*↑(v x y)
  have hx (y : Room G x₀ F A) : plume D Z t h F k₀ V A m Q k y=∑ x,χ x y := by
    unfold plume; rw [dif_pos ⟨hp,hQ⟩,depart]; unfold χ v K₁ AnalyticBridge.Sharp.Roster.imprint φ; simp only [dif_pos (Subtype.prop (_:Q))]
  have hf x : Integrable (χ x) μ := by unfold χ; exact Integrable.const_mul (Integrable.ofReal (h₁ x).1) _
  simp_rw [hx]; refine ⟨integrable_finsetSum _ (fun i _=>hf i),?_⟩
  rw [←Finset.prod_coe_sort Q,depart]
  rw [integral_finsetSum _ (fun i _=>hf i)]
  unfold χ; refine Finset.sum_congr (Finset.ext (fun _=>iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)))  fun x _=>?_
  rw [integral_const_mul,integral_complex_ofReal,(show (∫ y,v x y ∂μ)=_ from (h₁ x).2),← Finset.prod_coe_sort Q]
  unfold K₁
  refine congr_arg₂ HMul.hMul rfl (congr_arg Complex.ofReal (Finset.prod_congr rfl fun i _=>?_))
  change (∫ y,φ x i k y ∂_)=_
  unfold φ; simp_rw [dif_pos i.property]; exact (sections D Z h F k₀ V t hw he _ i k).2

private def table (u : Finset (Ensign S I)) := if (K).Makes A m u then ∏ i∈u,rates D Z h F k₀ k V i t else 0

private lemma collected (hA : (L).Available V) (T₁ : Finset (Ensign S I)) : let μ:=(L).climate V A k; let f:=fun y=>plume D Z t h F k₀ V A m T₁ k y
    Integrable f μ ∧ (∫ y,f y ∂μ)=Arbor.table D Z h F k₀ k V t A m T₁ := by
  intro μ f; unfold table
  split
  next H₁=>exact chapter D Z h F k₀ k V t A m T₁ hw hp he hA H₁
  unfold f plume; simp_rw [dif_neg (fun (ht:A.flags=RG.flags (temp x₀) V ∧ (K).Makes A m T₁)=> by exact ‹¬_› ht.2)]
  exact ⟨integrable_zero ..,integral_zero ..⟩

variable [Countable I]

abbrev BodyC (k : S.Choices) (p : Room G x₀ F A) :=↑(Ground.staple D F k₀ k V A p)*carrier D Z m ((chosen D F k₀ A k).hard V p)

-- HasSum after each k. Opaqueness only on value assessments, not on typed identity.
theorem sectors (hA : (L).Available V) (hc : (chosen D F k₀ A k).Clearing V) :
    HasSum (fun Q : Finset (Ensign S I)=> if (K).Makes A m Q then ∏ i∈Q,rates D Z h F k₀ k V i t else 0)
      (∫ p, BodyC D Z F k₀ V A m k p ∂(L).climate V A k) := by
  have hf:= (postings D h F A k₀ k V Z t m hA he hc).2
  let μ:=(L).climate V A k
  let f Q (p:Room G x₀ F A) := plume D Z t h F k₀ V A m Q k p
  have ht := hasSum_integral_of_summable_integral_norm (fun i=> (show Integrable (f i) μ from (collected D Z h F k₀ k V t A m hw hp he hA i).1)) hf
  change HasSum (table D Z h F k₀ k V t A m) _
  rw [← (show (∫ p,∑' i,f i p ∂μ)=(∫ p,BodyC D Z F k₀ V A m k p ∂μ) from
    integral_congr_ae ((dictionary D h F A k₀ k V Z hw t m hA he hc).mono (fun _ h=>h.tsum_eq)))]
  exact ht.congr_fun (fun j=>(collected D Z h F k₀ k V t A m hw hp he hA j).2.symm)
end YM.PhysicalNext.Dictionary.Arbor
