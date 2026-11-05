import YM.RemainderComparison.Serif.Money

/-!
# Directed partial-catalog logs
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Verse Marker Script
variable {β:Type} [DecidableEq β]{Jm:Census β}
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "L₁"=> Muse.song M H χ U.V (∅:Set ℕ) 0
local notation "P₀"=> tax G L x
local notation "Lt"=> sits Z l δ
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)
variable (z:ι→Poly Jm) {fP:β→ℝ} (hZ : Chorus Jm fP Z z k)
open Mallow Ovens Progress.DirectedRecipe

lemma tend {X: Type*}[NormedAddCommGroup X][CompleteSpace X]{P : Filter α}{Z:α→Type*}(σ:(a:α)→ Z a ↪ ι) (f:ι→X)(hp:Summable (fun i=>‖f i‖)) (ht:∀ i, ∀ᶠ x in P,i∈ Set.range (σ x)) : Tendsto (fun i=> ∑' j,f (σ i j)) P (𝓝 (∑' i,f i)) :=by
    let a (p:α)(i):= if i∈ Set.range (σ p) then f i else 0
    have he p: (∑' i,a p i) = ∑' j, f (σ p j):= by
       have hf:(∑' i,a p i)= (∑' j,a p (σ p j)):= ((σ p).injective.tsum_eq (Function.support_subset_iff'.mpr (fun i hi=> if_neg hi))).symm
       rw [hf]; exact tsum_congr fun i=>if_pos ⟨i,rfl⟩
    simp_rw [← he]; apply tendsto_tsum_of_dominated_convergence hp
    · intro i; exact tendsto_const_nhds.congr' ((ht i).mono (fun x hx=> (if_pos hx).symm))
    exact Eventually.of_forall fun i j=> by unfold a; split; exact le_rfl; exact (norm_zero (E:=X)).trans_le (norm_nonneg _)

local notation "E'"=> jewel M H χ

def glyph (j:Staff M H) (Y:Config G c):Poly Jm := (E' j.1 j.2).paint Z (sits Z l δ) z Y

def branch (p:Finset ι)(i:H.fragrances): Config G c→Poly Jm:=let X:= Script.restrict p; poem (M ∘ X) H χ (X ⁻¹' Z) (sits (X ⁻¹' Z) (l ∘ X) δ) (z∘X) i
lemma junction (p:Finset ι)(Y:Config G c)(i: H.fragrances):
    branch M H χ Z l δ z p i Y= ∑ w:Syllable (M ∘ Script.restrict p) H i,glyph M H χ Z l δ z (grid M H p ⟨i,w⟩) Y:=by
   let t:=Script.restrict p; apply Finset.sum_congr rfl; intro w h; symm
   unfold glyph; rw [show grid M H p ⟨i,w⟩=⟨i,Script.label M H t _ w⟩ from rfl,poster,Script.letter,clears] -- infer notation.
variable (Sx : BudgetPoint) (hx:Sx.B=radiusB x)(hv:Sx.threshold=Pressure.temp x)(ht:Sx.order≤j)(hJ:Sx.power≤J)
include h hh hZ hx hv ht hJ
lemma summit (V':Config G c): let t:=fun i=>glyph M H χ Z l δ z i V'
   Summable t ∧ Tendsto (fun s:Finset ι=>∑' i,branch M H χ Z l δ z s i V') atTop (𝓝 (∑' i,t i)):=by
   intro f; obtain ⟨t,hP,hV⟩:= rollbook M H χ Z l δ U h hh z hZ Sx hx hv ht hJ
   obtain ⟨C,hC,hQ⟩:= Poly.equivalent_norm (R:=Jm) hZ.votes
   have hp:Summable (fun i=>‖f i‖):= (hP.mul_right C).of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> (hQ _).trans (mul_le_mul_of_nonneg_right (hV ..) hC))
   have he (p:Finset ι): (∑' i,branch M H χ Z l δ z p i V')=∑' j,f (grid M H p j):=by
      rw [show _= _ from ((hp.comp_injective (grid M H p).injective).of_norm (f:= (fun j=>f ((grid M H p) j)))).tsum_sigma]; -- syntax
      apply tsum_congr; intro i; rw [junction,tsum_fintype]
   refine ⟨hp.of_norm,?_⟩; simp_rw [he]; exact tend (grid M H) f hp (Script.roam M H)
end YM.RemainderComparison.Serif
