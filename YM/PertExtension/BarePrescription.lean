import YM.PertExtension.CurlSymbol
import YM.PertExtension.FiltrationRule
import YM.PertExtension.PaintTop

/-!
# Nested-cutoff candidate top Wick-corrected Wilson coefficient kernels

Physical engineering and factor powers are not couplings in the unnormalized
vacuum law. This is only the *input* to position renormalization: existence and
identification of renormalized infinite-cutoff coefficients is not part of the
finite volume calculation here.

The real restriction of the symbol matrix is by construction (inverse of the
complex triangular jet solve followed by real-coefficient extraction). If using
it as exactly the conventional top Wick prescription one needs to know the full
matrix is real and its projection is the canonical joint-jet prescription on
contracted columns. No such equivalence estimate is smuggled in by the
nomenclature.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.PertExtension.LatticePT
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory RG Labels Source
open scoped Topology ContDiff Classical BigOperators
open Chart Series Series.Tested Orb Orb.SlotEvaluation

variable {G : Gauge}{d : ℕ}{F : Labels.Frame G d}

def topMatrix (S : SectionData F) (H : Hol G)(h : S.Sound H)(p : Bid.pop S) :=
   Heat.Top.topFrame (Heat.Top.rendered S p).toData H ((Heat.Top.rend_acts h p).harmonious _ h)

def topBasisComplex (S : SectionData F)(H : Hol G)(h : S.Sound H)(p : Bid.pop S)(v : F.Index) : F.Coeff :=
   (topMatrix S H h p).inverse (covarianceSymbol G) (Pi.single v 1)
def topBasis (S : SectionData F)(H : Hol G)(h : S.Sound H)(p : Bid.pop S)(v j : F.Index) : ℝ := (topBasisComplex S H h p v j).re

lemma topBasis_unit (S : SectionData F)(H : Hol G)(h : S.Sound H)(p : Bid.pop S): topBasis S H h p 0= Pi.single (M:=fun _=>ℝ) 0 1 := by
  funext j
  let M:=topMatrix S H h p;let e : F.Coeff := Pi.single (0:F.Index) 1
  have hR:M.slots 0=0:= congr_arg Prod.snd F.zero_degree
  let Q:=covarianceSymbol G
  have hw (i : F.Index) (hi:i≠0):e i=0:=Pi.single_eq_of_ne hi ..
  have he: M.conversion Q e=e := by
    change (∑ i:F.Index,e i • _)=_
    rw [Finset.sum_eq_single_of_mem (0:F.Index) (Finset.mem_univ _) (fun i hi hl=>?_)]
    · rw [show e (0:F.Index)=1 from Pi.single_eq_same ..,one_smul,(Heat.degree_decrease _ _ _ (M.bound _)).1 hR,M.retr]
    rw [hw i hl,zero_smul]
  have he':topBasisComplex S H h p 0=e := by rw [show topBasisComplex S H h p 0=(M.conversion Q).symm e from rfl, ← he,LinearEquiv.symm_apply_apply];exact he.symm
  change (topBasisComplex S H h p 0 j).re= _
  by_cases hj:j=0 <;> simp [he',e,hj]

lemma even_slot (S : SectionData F)(H : Hol G)(h : S.Sound H)(p : Bid.pop S)(i j : F.Index)(ht:Odd ((F.grades i).2+(F.grades j).2)) :topBasis S H h p i j=0:= by
  unfold topBasis topBasisComplex
  rw [(topMatrix S H h p).parityInv i j ht];rfl

section Kernels
variable (S : SectionData F)(H : Hol G)(h : S.Sound H)(p : Bid.pop S)
variable {I : Type*}[Fintype I]
variable (q : ℕ+)(m : ℕ)(v : I→F.Index)(w : I→ℕ)(Ψ : (I→E4)→ℝ)

def diagrams := diagramRead S q m (topBasis S H h p ∘ v) w Ψ
def regulator := physicalRead S q m (topBasis S H h p ∘ v) w Ψ

theorem packet_asymptotics : Aspiration (regulator S H h p q m v w Ψ) (diagrams S H h p q m v w Ψ) :=
  finite S q m (topBasis S H h p ∘ v) w Ψ h p

end Kernels

end YM.PertExtension.LatticePT
