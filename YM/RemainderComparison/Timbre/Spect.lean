import YM.RemainderComparison.Timbre.Sax
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Timbre
open Seedlings
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
variable {hC he I I' V U}
variable (χ:Chi)
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface
open Harmonics
open BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(y:α)
local notation "X₁"=>brand X y
variable (hC he)
local notation "Z₁" => brand Y₁ y
variable (K':BoxOf C') (D':BoxOf c') (b:Finset ι)(b':Finset δ)
variable (x:Site C) (r n:ℕ)(W' : Warp («S»:= stepped Q H) b b' (S':=stepped Q h))
set_option quotPrecheck false
local notation "uₓ"=> (L).low.cut x

-- lexical elements only, geometry fields to see any mask & enforcers. port.X.No cost expected.
variable (l:ι→ℝ)(l':δ→ℝ)(Gm:Set ι)(Δ:Set δ)(p₁ p₂:ℝ)
local notation "Sg"=> Timbre.trumpets C'
local notation "Sm"=> Timbre.trumpets c'
variable (hc:2*(r+Mint.width J.halo (radiusB p) (radiusB p))<c.val)
lemma incite (sd:Signed)(x y':Site c) : ∃ w:R.activities.Moves sd ((stepped Q h).ratio.embed x), Shifting Y₁ y c' ∅ Sm y' r n Y₁ ∅ Sm w (Equiv.refl _):=by
    obtain ⟨w⟩:= c'.laws.intake.cap.labels.moves sd ((stepped Q h).ratio.embed x)
    exact ⟨w,Timbre.shines ..,fun i=>isEmptyElim i,fun i=>isEmptyElim i⟩
include ht hx hb hc hq
lemma ports (x:Site c) : BoxOf.Port hC he C' c' X Y₁ y Sg Sm ∅ ∅ x r n l l' Gm Δ p₁ p₂ 1:=by
    obtain ⟨w,hP⟩:= Timbre.incite c' Y₁ y r n 1 x 0
    obtain ⟨s,h₁⟩:= Timbre.frigid hC he C' c' ht X Y₁ y 0 r n hc
    exact ⟨hq,⟨ht,hx,hb⟩,Timbre.trumpets c',Y₁,s,w,hP,h₁,by simp⟩
end YM.RemainderComparison.Timbre
