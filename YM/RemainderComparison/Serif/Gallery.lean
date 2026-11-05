import YM.RemainderComparison.Serif.Folio

/-!
# Pass also retained force gas
Supports held fixed. Full non-nil reclosure cases with flags U≠0. Assembled on original pipeline (input handles Attempt etc). Joint evaluations including real. Pay convergence locally, no estimate on isolated push denominator substituted into this lemma.
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
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)(P':BudgetPoint) (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)

local notation "VB" => Refrain.read H' D χ E₀ V₀
local notation "f'"=> Refrain.visa H' D

-- Pull entries before pointe

def haven (i:Refrain.Leaf H)(V: Config G c): Poly Jm:=∑' w:Scene M H i.val, (Mosaic.parade M H χ i.val w).paint Z Lt z V

def Lane (U:Config G c):ℕ→ Poly Jm:= stuff (f') (fun i=>haven M H χ Z l δ z i U)

def foible (p:Finset ι)(U:Config G c):ℕ→ Poly Jm:= let X:= Script.restrict p; fun i=> Mosaic.showK (M∘X) H χ (X ⁻¹' Z) (sits (X ⁻¹' Z) (l ∘ X) δ) (z∘X) H' D i U

def tome (p:Finset ι)(U:Config G c) : Finset ℕ→Poly Jm:= Merge.Photo.fronts VB (foible M H χ Z l δ z H' D p U) U P'

def book (U:Config G c): Finset ℕ→Poly Jm:= Merge.Photo.fronts VB (Lane M H χ Z l δ z H' D U) U P'

local notation "FR"=> foible M H χ Z l δ z H' D
local notation "BR"=> book M H χ Z l δ z H' D P' E₀ V₀
local notation "TR"=> tome M H χ Z l δ z H' D P' E₀ V₀
variable (V:Config G c)
local notation "MX" p=> M ∘ Script.restrict p
lemma visits (p:Finset ι)(j:Refrain.Leaf H): FR p V ((f') j)=∑ w:Scene (M ∘ Script.restrict p) H j.val,(Mosaic.parade M H χ j.val (queue M H (Script.restrict p) _ w)).paint Z Lt z V:=by
   unfold foible; unfold Mosaic.showK; rw [stuffed]; refine sum_congr rfl fun i _=>?_ ; rw [Script.parade,Script.letter,clears]
include h hh hZ
lemma station : (∀ i, Tendsto (fun p=> FR p V i) atTop (𝓝 (Lane M H χ Z l δ z H' D V i)))∧
     ∃ u:ℕ→ℝ,Summable u∧ (∀ i,0 ≤ u i)∧
       ∀ i p, Poly.price fP (FR p V i) ≤ u i:=by
    obtain ⟨W_,hw,hW⟩:= Serif.rollK M H χ Z l δ U h hh z hZ
    have hw' i : Summable (fun w:Scene M H (i:Refrain.Leaf H).val=> W_ ⟨i,w⟩):= hw.sigma_factor i
    let u i:= ∑' p:Scene M H (i:Refrain.Leaf H).val,W_ ⟨i,p⟩
    have hz i w:0≤ W_ ⟨i,w⟩:= (Poly.nonnegative hZ.votes _).trans (hW i w V)
    have hp':Summable u:= hw.sigma
    have he (i) (hp:i∉ Set.range f'): Tendsto (fun p=>FR p V i) atTop (𝓝 (Lane M H χ Z l δ z H' D V i)) ∧ ∀ p, FR p V i=0:=by
       have ht (p:Finset ι): FR p V i=0:=by unfold foible; unfold Mosaic.showK; rw [Progress.DirectedRecipe.blank _ _ hp]; rfl
       simp_rw [ht, Lane, Progress.DirectedRecipe.blank _ _ hp]; exact ⟨tendsto_const_nhds,fun _=>trivial⟩
    constructor
    · intro i; by_cases hx:i∈Set.range f'
      swap; · exact (he i hx).1
      obtain ⟨w,rfl⟩:=hx; let f i:= (Mosaic.parade M H χ w.val i).paint Z Lt z V; have hs : Summable (fun i=> ‖f i‖):=(show Summable f from (Poly.budgeted hZ.votes (hw' w) (fun i=>hW w i V)).1).norm -- Summable.norm possibly implicit ℝ Banach FD
      rw [Lane,stuffed]; have hu (p:Finset ι): FR p V ((f') w)=∑' i:Scene (M ∘ Script.restrict p) H w.val,f ((Script.queue M H (Script.restrict p) w.val) i):=by rw [Serif.visits,tsum_fintype]
      simp_rw [hu]; exact Serif.tend (fun i=>Script.queue M H (Script.restrict i) w.val) f hs (fun i=>Script.flags M H w.val i)
    let p:=Refrain.visa H' D; have ht:Summable (stuff p u):= (p.injective.hasSum_iff (fun i hp=>Progress.DirectedRecipe.blank _ _ hp)).1 (show HasSum (stuff p u ∘ p) _ from hp'.hasSum.congr_fun (fun i=>stuffed ..))|>.summable
    refine ⟨stuff p u,ht,fun i=>?_,fun i P=>?_⟩
    · by_cases h:i∈ Set.range p
      · obtain ⟨j,rfl⟩:=h; rw [stuffed]; exact tsum_nonneg fun i=>hz ..
      rw [Progress.DirectedRecipe.blank _ _ h]
    by_cases hv:i∈ Set.range p
    swap; · rw [(he i hv).2 P,Progress.DirectedRecipe.blank _ _ hv,Poly.zero_price]
    obtain ⟨i,rfl⟩:=hv; unfold p; rw [stuffed,visits]; apply le_trans (Poly.batch hZ.votes ..)
    refine le_trans (sum_le_sum (fun j _=> hW i (queue M H (Script.restrict P) _ j) V)) ?_
    let f (w:Scene M H i.val):=W_ ⟨i,w⟩; exact le_trans (show _ ≤ ∑ w∈univ.map (queue M H (Script.restrict P) i.val), f w from by rw [Finset.sum_map]) ((hw' i).sum_le_tsum _ (fun i _=> hz ..))
lemma ledger : Tendsto (fun p=> ∑' i,TR p V i) atTop (𝓝 (∑' i,BR V i)) ∧ Summable (BR V):=by
   obtain ⟨hx,b,hb,he,h⟩:= Serif.station M H χ Z l δ U h hh z hZ H' D V
   obtain ⟨c,hc,hK⟩:= Poly.equivalent_norm (R:=Jm) hZ.votes
   let a (i:Finset ℕ):= (∏ j∈i,b j)*c
   have hp p i : ‖TR p V i‖ ≤ a i:=by
       unfold tome Merge.Photo.fronts; split
       · apply (hK _).trans; exact mul_le_mul_of_nonneg_right ((Poly.multiple hZ.votes ..).trans (prod_le_prod (fun _ _=> Poly.nonnegative hZ.votes _) (fun _ _=> h ..))) hc
       rw [norm_zero]; exact mul_nonneg (prod_nonneg fun i _=>he _) hc
   have ht i:Tendsto (fun p=> TR p V i) atTop (𝓝 (BR V i)):=by
      unfold book tome Merge.Photo.fronts; split_ifs; · exact tendsto_finsetProd _ fun i _=>hx i
      exact tendsto_const_nhds
   have hz:Summable a:=(summable_finsetProd_of_summable_nonneg he hb).mul_right _
   exact ⟨tendsto_tsum_of_dominated_convergence hz ht (Eventually.of_forall hp), (Summable.of_norm (hz.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> le_of_tendsto ((ht i).norm) (Eventually.of_forall (fun j=>hp j i)))))⟩
end YM.RemainderComparison.Serif
