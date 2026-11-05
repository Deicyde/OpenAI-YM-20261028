import YM.RemainderComparison.Passion.Permit
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
-- holder exposes exact physical basis; provide T for actual stencil.Seam with calibration.P.L. cost and Areas
structure SeatD (G:Gauge)(n:Side) where
   origin : Site n
   degree : ℕ
   basis : Labels.Frame G degree
   sectionQ : SectionData basis

namespace SeatD
variable (S:SeatD G n) (X: Hol G)
local notation "F"=> S.basis
local notation "A"=> S.sectionQ
local notation "o" => S.origin
local notation "v" => p.threshold
abbrev suit := S.sectionQ.footprint o
local notation "S₁"=> S.suit
variable (K:Support n)
-- the primary is evaluated with a mask either on its indicated
-- field footprint (canonical), or including donors and retained-test costs too (continuation copy)
inductive MaskType | exactM | expanding
variable (M:MaskType)
def seeing : Support n:= match M with
 | .exactM=> S₁
 | .expanding=> joint A o K
local notation "S₂" => seeing S K M
local notation "Y"=> Local.joint A o K
lemma primary_composes : S₁ ⊆ S₂∧S₂ ⊆ Y:= by cases M; exact ⟨Finset.Subset.rfl,Finset.subset_union_right⟩; exact ⟨Finset.subset_union_right,Finset.Subset.rfl⟩

-- Export in allocated log entries (MASK does NOT require all the sites when in exactM, costs still use X.K). Need record evaluations FULL.C pending registration normalized Asset.Tx
structure PairD (S:SeatD G n) where
   header : S.basis.Coeff
   entry : Config G n→ℝ
variable (x : PairD S) (U:Config G n)

def chord (b: S.basis.Coeff)(V:Config G n):ℂ := Local.presented S.sectionQ S.origin p.threshold (S.basis.core b) V

def sharp (x : PairD S) (U:Config G n) : ℝ := (x.header 0).re + masked v (seeing S K M) (fun V=> (S.chord p x.header V).re) U + masked v (Local.joint A o K) x.entry U -- order p?

def realD (b:S.basis.Coeff):Prop:= b=star b
variable {w : ℝ}
omit [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
-- NO orientation equivariance claimed; owner provided X.T
variable (h : Local.Readable X S.sectionQ p n w)
include h
lemma earthly {x: S.basis.Coeff}(hx:S.realD x)(U:Config G n): Local.presented A o v x U = star (Local.presented A o v x U):=by
    refine Eq.trans (show Local.presented A o v x U = Local.presented A o v (star x) U from congr_arg (fun x:S.basis.Coeff=>Local.presented A o v x U) hx) ?_ -- rw all! change
    unfold Local.presented SectionData.places; dsimp only [LinearMap.coe_mk, AddHom.coe_mk]; rw [Local.scaled_star,h.sound.ordinary_real]
lemma earthlyC {x: S.basis.Coeff}(hx:S.realD x)(U:Config G n): S.chord p x U = star (S.chord p x U):= by -- edit arg
    have ht:S.realD (S.basis.core x):= (congr_arg S.basis.core hx).trans (Local.core_star ..)
    exact earthly p S X h ht _
omit h in
lemma reality (x:ℂ)(h:x=star x): (↑(x.re):ℂ)=x:=by
    apply Complex.ext
    · rfl
    rw [Complex.ofReal_im]; have he:= congr_arg Complex.im h; simp only [Complex.star_def,Complex.conj_im] at he; linarith
lemma rung {x: S.basis.Coeff}(hx:S.realD x):
    ∀ U, (↑(masked p.threshold S₂ (fun V=> (S.chord p x V).re) U):ℂ)= masked v S₂ (S.chord p x) U:=by
    intro V; by_cases he:Healthy v S₂ V
    · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]; exact reality _ (earthlyC p S X h hx V)
    rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he]; rfl
local notation "Y₁"=> Local.joint A o K
lemma plucked (hx:S.realD x.header):
    Complex.ofReal (SeatD.sharp p S K .exactM x U)= Local.primary A o p.threshold x.header U+ masked v Y₁ (Complex.ofRealCLM∘ x.entry) U:=by
   unfold sharp; rw [Complex.ofReal_add,Complex.ofReal_add,rung p S X K _ h hx]
   rw [show Local.primary A o v x.header U=x.header 0 + masked v (seeing S K .exactM) (S.chord p x.header) U from rfl,reality (x.header 0) (show x.header 0= star (x.header 0) from congr_fun hx 0)]
   apply congr_arg
   by_cases h:Healthy (p.threshold) Y₁ U
   · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl
   rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]; rfl

end SeatD
end YM.RemainderComparison.Passion
