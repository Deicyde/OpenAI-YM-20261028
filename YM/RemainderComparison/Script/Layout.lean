import YM.RemainderComparison.Script.Matrices

/-!
# Restrict assertions supported on diagrams'.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Script
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
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (σ:α ↪ ι)
local notation "M'" => M ∘ σ
local notation "V'"=> drums M σ S
local notation "w'"=> label M H σ

-- Lean handy generalization
lemma join_budget {R ι:Type*}{α:R→Type*}{F:Filter R} [F.NeBot](θ:(r:R)→ (α r ↪ ι))(b : ι→ℝ) (s:ℝ)
    (he:∀ i, ∀ᶠ x in F,i∈ Set.range (θ x))(hp:∀ᶠ x in F, SumBudget (b∘θ x) s) : SumBudget b s:=by
   apply budget_of_sum
   · intro i; obtain ⟨r,⟨p,h⟩,he'⟩:= (he i|>.and hp).exists; rw [← h]; exact he'.1 p
   intro p; obtain ⟨v,hv,he⟩:= ((eventually_all_finset p).2 (fun i hi=> he i)|>.and hp).exists -- pred
   let t:=θ v; let a:= p.preimage t t.injective.injOn
   have h : p=a.map t:=by
      ext i; constructor
      · intro hi; obtain ⟨j,h⟩:=hv i hi; exact mem_map.mpr ⟨j,(show j∈a from mem_preimage.mpr (h.symm ▸ hi)),h⟩
      intro hi; obtain ⟨z,hz,ht⟩:=mem_map.mp hi; subst i; exact mem_preimage.mp (show z∈a from hz)
   rw [h,Finset.sum_map]; exact budget_sum he a

-- natural inclusion

def grid (x:Finset ι): Staff (M ∘ restrict x) H ↪ Staff M H := Embedding.sigmaMap (Embedding.refl _) (fun p=> label M H (restrict x) p)

def prairie (x:Finset ι) : Flak (M ∘ restrict x) H ↪ Flak M H:= Embedding.sigmaMap (Embedding.refl _) (fun p=> queue M H (restrict x) p)
lemma roam (p:Staff M H): ∀ᶠ x in atTop,p∈ Set.range (grid M H x):=by
   filter_upwards [ships M H p.1 p.2] with x hx; obtain ⟨w,hw⟩:=hx; exact ⟨⟨p.1,w⟩, by change Sigma.mk p.1 _=_; exact Sigma.ext rfl (heq_of_eq hw)⟩
lemma explored (p:Muse.Flak M H): ∀ᶠ x in atTop,p∈ Set.range (prairie M H x):=by
   filter_upwards [Script.flags M H p.1 p.2] with x hx; obtain ⟨w,hw⟩:=hx; exact ⟨⟨p.1,w⟩, by change Sigma.mk p.1 _=_; exact Sigma.ext rfl (heq_of_eq hw)⟩

lemma recover (P':BudgetPoint){V:Set (Staff M H)}{f:Staff M H→ℝ}(a b:ℝ)(l:ι→ℝ)
    (h:∀ᶠ x in atTop, Network (M ∘ restrict x) H χ (l ∘ restrict x) P' ((grid M H x) ⁻¹' V) (f∘grid M H x) a b): Network M H χ l P' V f a b:=by
   constructor
   · intro i hi; obtain ⟨x,⟨j,hj⟩,hx⟩:=((roam M H i).and h).exists; rw [←hj] at hi ⊢
     obtain ⟨a',hh⟩:= hx.mark j (show grid M H x j∈ V from hi); refine ⟨a',?_⟩
     change P'.Regular (reachability j.1) (fun U=>_)∧_
     rw [show (etude M H χ ((grid M H x) j).fst ((grid M H x) j).snd).emit l= _ from Eq.trans (congr_arg (fun f:Verse ι (Config G c)=> f.emit l) (resume M H χ (restrict x) j.1 j.2)) (alive (restrict x) l _)]; exact hh
   intro y; apply join_budget (θ:= fun x=>grid M H x) (he:= roam M H)
   filter_upwards [h] with x hx; exact hx.costs y
end YM.RemainderComparison.Script
