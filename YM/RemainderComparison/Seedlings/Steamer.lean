import YM.RemainderComparison.Seedlings.Sails
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seedlings
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
namespace BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(y:α)
local notation "X₁"=>brand X y
variable (hC he)
local notation "Z₁" => brand Y₁ y
variable (K':BoxOf C') (D':BoxOf c') (b:Finset ι)(b':Finset δ)
variable (x:Site C) (r n:ℕ)(W' : Warp («S»:= stepped Q H) b b' (S':=stepped Q h))
set_option quotPrecheck false
local notation "uₓ"=> (L).low.cut x

variable (hc:2*(2*r+3)<c.val) (hz:Folding hC he C' c' X Y₁ y K' D' b b' x r n W')
local notation "FC"=> frosted hC he C' c' ht X Y₁ y K' D' b b' x r n W' hc hz
variable (l:ι→ℝ)(Gm:Set ι)(b₁:ℝ)(u:α)(l':δ→ℝ)(Δ:Set δ)(b₂:ℝ)(V₀:Config G c) (hv:RG.flags (Pressure.temp p) V₀=∅) (d:ℝ)(hp:(∏ i∈ b,Muse.sits Gm l b₁ i)=d*∏ i∈b',Muse.sits Δ l' b₂ i)
variable (hA:Bloom C' χ)(hE: Bloom c' χ)
include hc hz ht hx hb hq hp hv hA hE
lemma captives :
    pool X y C' b K' x r n χ l Gm b₁ u ((L).low.links V₀)=d*pool Y₁ y c' b' D' (uₓ) r n χ l' Δ b₂ u V₀ ∧
    flagsCollected X y C' b K' r n χ l Gm b₁ u x ((L).low.links V₀)=d* flagsCollected Y₁ y c' b' D' r n χ l' Δ b₂ u (uₓ) V₀:=by
    obtain ⟨j,U,h⟩:= hA.grant; obtain ⟨k,U',hJ⟩:=hE.grant
    let D:=FC; have hx'(s:Sleet.Staff (brand X y) C')(hs:Marvel X y C' b K' (k:=n) (r:=r) x s)(u:α) : (Creek.theater C' χ X y l Gm b₁).solvent u s ((L).low.links V₀) = d* (Creek.theater c' χ Y₁ y l' Δ b₂).solvent u (D.flora s hs) V₀:=by
        have he:= peerTransit hC he C' c' ht X Y₁ y K' D' b b' x r n W' hc hz s hs; have hy:(Creek.theater C' χ X y l Gm b₁).halls s⊆ neighbors r x:= by rw [Creek.point]; exact hs.roam
        exact Harmonics.traversed C' c' hq ht hx hb χ X Y₁ y _ _ _ _ _ _ _ _ he hc hy V₀ hv U' U u d (D.consonant _ _ d s hs hp)
    exact ⟨D.dotted _ _ _ _ _ _ _ _ _ _ hx' u,D.cruise _ _ _ _ _ _ _ _ _ _ hx' u⟩
end BoxOf
end YM.RemainderComparison.Seedlings
