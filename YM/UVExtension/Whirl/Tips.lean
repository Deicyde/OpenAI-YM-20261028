import YM.UVExtension.Whirl.Layer
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Whirl
open PhysicalNext PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open PhysicalNext.Repeat
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L: Side} (C: Listing G c)(z w : ℕ)
variable (V:Collection.Source G c) (g t:Trio.Offer G c) (s : Signed) (b : Site c) (h : (C.read V).Moves s b)
local notation "d" => (bison V g t)
local notation "ℒ" => (lodge C z w)
def attire : ((ℒ).pours (bison V g t)).Moves s b := by
  let X:=d; let P:=ℒ; let y:=leanU c; let e:=reel s b h.ep; let q:=congo y e
  have hk i:y (q i)=e (y i):= perch y e i
  let f : Civ c→RegularAddress c:= Sum.elim C.reg (sea z); let u:=Sum.elim V.logRead (Song.choir g)
  have hm i : (f (e i)).support = (f i).support.image (Lattice.affine s b)∧ (f (e i)).site=Lattice.affine s b (f i).site ∧ u (e i)= u i ∘ pull s b:= by
    rcases i with i|i
    · exact ⟨h.reg_support i,h.reg_site i,funext (h.valuesE _)⟩
    obtain ⟨h₁,h₂,h₃⟩:= spirit (leap z) g s b i; exact ⟨h₂,h₁,h₃⟩
  exact ⟨q,h.kp,(fun i=> (hk i).symm ▸ ((hm (y i)).2.1) : ∀ i,(f (y (q i))).site=_), (fun i=> by change (f (y (q i))).support=_; rw [hk]; exact (hm (y i)).1),h.forced_support,h.forced_inventory,h.forced_tests,(fun i V=> by change u (y (q i)) V=_; rw [hk]; exact congr_fun (hm (y i)).2.2 V),h.valuesK⟩

def gales : Takes s b ℒ (bison V g t):= by
  let e:= leanU c; let v:= reel s b h.ep; refine ⟨attire C z w V g t s b h, Refrain.congo e v,fun i=> ?_,fun U i=>?_⟩
  · change (Sum.elim C.reg (sea w) (e _)|>.support)=_; rw [perch]
    suffices hh:∀ i,(Sum.elim C.reg (sea w) (v i)|>.support) = (Sum.elim C.reg (sea w) i|>.support).image (Lattice.affine s b) from hh (e i)
    rintro (i|i); · exact h.reg_support i
    exact (spirit (leap w) g s b i).2.1
  let f : Civ c→ Config G c→ℝ:=Sum.elim (fun _=>0) (choir (-t)); change f (e _) U=_; rw [perch]
  suffices hh : ∀ i,f (v i) U= f i (pull s b U) from hh _
  rintro (j|j); · rfl
  exact congr_fun ((spirit (leap w) (-t) s b j).2.2) U
variable (V':Collection.Source G c) (g' t':Trio.Offer G c)(H:(C.read V').Moves s b)
lemma rotation (hh:Twins h H):(gales C z w V g t s b h).Joint (gales C z w V' g' t' s b H):= by
  have hv:= congr_arg (fun p=>congo (leanU c) (reel s b p)) hh.1
  exact ⟨⟨hv,hh.2⟩,hv⟩
end YM.UVExtension.Whirl
