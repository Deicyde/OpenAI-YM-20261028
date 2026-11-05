import YM.RemainderComparison.Seedlings.Steamer
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
variable (x:Site c) (r n':ℕ)
variable (l:ι→ℝ)(l':δ→ℝ)(Gm:Set ι)(Δ:Set δ)(b₁ b₂:ℝ)
structure Port (d:ℝ) : Prop where
    pane : T'= Deck.re T
    inherits : R'.path=R.path ∧ R'.p=R.p ∧ R'.beta=R.beta
    treasury : ∃ (Fo: BoxOf c') (M:δ→ Portrait R α) (W:Warp («S»:=stepped Q H) b b' (S':=stepped Q h))(p:R.activities.Moves 1 ((stepped Q h).ratio.embed x)),
        BoxOf.Shifting M y c' b' Fo 0 r n' Y₁ b' D' p (Equiv.refl _) ∧
         BoxOf.Folding hC he C' c' X M y K' Fo b b' 0 r n' W ∧
         (∏ i∈ b,Muse.sits Gm l b₁ i)=d*∏ i∈b',Muse.sits Δ l' b₂ i
variable (d:ℝ)(hK:BoxOf.Port hC he C' c' X Y₁ y K' D' b b' x r n' l l' Gm Δ b₁ b₂ d)
variable (hA:Bloom C' χ)(hE: Bloom c' χ)(hc:2*(2*r+3)<c.val)
variable (V₀:Config G c)(hv: RG.flags (Pressure.temp p) V₀=∅)(u:α)
local notation "p₀"=> (Lace.project (h:=h) (H:=H) hC he)
include hK hA hE hv hc
lemma barge : let V₁:=(p₀).low.links (Lattice.translate x V₀)
     pool X y C' b K' 0 r n' χ l Gm b₁ u V₁=d*pool Y₁ y c' b' D' x r n' χ l' Δ b₂ u V₀ ∧
     flagsCollected X y C' b K' r n' χ l Gm b₁ u 0 V₁=d*flagsCollected Y₁ y c' b' D' r n' χ l' Δ b₂ u x V₀ :=by
   intro V₁; obtain ⟨h₀,⟨h',hx,hβ⟩,F,M,w,t,hR,hV',hL⟩:=hK
   have hm:= Seedlings.BoxOf.season M y c' b' F 0 r n' b' Y₁ 1 x t D' (Equiv.refl _) hR χ l' Δ b₂ u l' Δ b₂ V₀ (d:=1) hv (by rw [one_mul]) hE
   have hh : RG.flags (Pressure.temp p) (Lattice.translate x V₀)= ∅:= by rw [← Lattice.pull_one]; exact Pane.tranquility _ hv ..
   have hB:=(captives hC he C' c' h₀ h' hx hβ χ X M y K' F b b' 0 r n' w hc hV' l Gm b₁ u l' Δ b₂ _ hh d hL hA hE)
   simp_rw [Lattice.pull_one, show Lattice.affine 1 x 0=x from (by simp [Lattice.affine]), one_mul] at hm
   simp_rw [show (p₀).low.cut 0=0 from map_zero (Macrame.splitter (Deck.divides hC))] at hB
   rw [← hm.1,← hm.2]; exact hB
end BoxOf
end YM.RemainderComparison.Seedlings
