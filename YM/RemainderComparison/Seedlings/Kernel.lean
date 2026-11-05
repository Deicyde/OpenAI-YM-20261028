import YM.RemainderComparison.Seedlings.Mesh
import YM.RemainderComparison.Funk.Drummer
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
variable {Q: KernelChoices}{S : StepData c f} {S': StepData C F}
variable {T : Tube G S} {T':Tube G S'} {p :ℝ} {R:RG.Rep G f} {R': RG.Rep G F}
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R)
variable (χ:Chi)
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface
open Harmonics
namespace BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(y:α)
variable (K':BoxOf C') (D':BoxOf c') (b:Finset ι)(b':Finset δ)
variable (x:Site c) (r n':ℕ)
variable (l:ι→ℝ)(l':δ→ℝ)(Gm:Set ι)(Δ:Set δ)(b₁ b₂:ℝ)
variable (x':Site C)
-- let Ξ choose classic panel leases.O.Cash proof irrelevance.Shadows.Stage
variable (Q P)
def ShapeP (d:ℝ):Prop:=∃ (η:f.val=c.val*P.L.val) (ρ:F.val=C.val*P.L.val) (h:S=stepped Q η)(h':S'=stepped Q ρ)(Tk:Tube G (stepped Q η))(Tp:Tube G (stepped Q ρ))(_he:T=h.symm ▸ Tk) (_he':T'=h'.symm ▸ Tp) (A:Cash W p a L₀ J o K₀ Tp R')(B:Cash W p a L₀ J o v Tk R)(K:BoxOf A)(D:BoxOf B), HEq C' A ∧ HEq c' B ∧ HEq K' K∧ HEq D' D∧ BoxOf.Mesh A B X Y₁ y K D b b' x r n' l l' Gm Δ b₁ b₂ x' d -- note Cash Prop?
variable {d :ℝ}(P':BudgetPoint)
variable (hB : BoxOf.ShapeP P Q C' c' X Y₁ y K' D' b b' x r n' l l' Gm Δ b₁ b₂ x' d)
variable (h : Enlightened Q P K J o p a L₀ χ) (hp:SliceRows.Stamp T)(hp':SliceRows.Stamp T')(hA:P'.threshold=Pressure.temp p)
include h hp hp' hB hA
lemma fuel (V:Config G c) (U:Config G C) (hV:flags P'.threshold V=∅) (hU:flags P'.threshold U=∅) (he:Agrees (Lattice.box r) (expandAt x V) (expandAt x' U)) (u:α): pool X y C' b K' x' r n' χ l Gm b₁ u U=d * pool Y₁ y c' b' D' x r n' χ l' Δ b₂ u V∧ flagsCollected X y C' b K' r n' χ l Gm b₁ u x' U=d* flagsCollected Y₁ y c' b' D' r n' χ l' Δ b₂ u x V:=by
    rcases hB with ⟨η,ρ,e,e',A',B',hf,hf',A,B,I,D,hR,hS,hX,hY,hP⟩
    subst S S'; change T=A' at hf; change T'=B' at hf'; subst T T'; replace hR:=eq_of_heq hR; replace hS:=eq_of_heq hS; subst A B; replace hX:=eq_of_heq hX; replace hY:=eq_of_heq hY; subst I D
    rw [hA] at hV hU
    exact watershed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hP hp hp' _ _ hV hU he u
end BoxOf
end YM.RemainderComparison.Seedlings
