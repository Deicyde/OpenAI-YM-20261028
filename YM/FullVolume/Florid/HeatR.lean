import YM.FullVolume.Florid.Wear
import YM.MergeProof.Steps
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
open Extra.Iteration Merge Tickets Merge.Palette Lyre Tune
namespace Crew
-- authentic epochs.affine Camera geometry. φ held input hats all.FULL.Reached.
variable {A:Type}[Fintype A](V:A→Mill U)
open Daisy PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Jams Ovens
variable (p:Tickets (sign (faces V) S))
local notation "V₁"=> Merge.Palette.team (faces V) p
local notation "Λ"=>U.pole
local notation "T₀"=> radiusB x₀
local notation "Q'" => Empire.stella Q
variable {ν α:ℝ} {s:Lyre.Signal 0} (hc:Clear Q L μ ν x₀ v s)(hr: Lyre.Clarity H 0 C δ ν)(hσ:Margin G L x₀ α δ)(hv:2≤v)
variable (X:Coat T F)(he:X.x=x₀)(ht:X.width=o.K)
variable (i:Molecule S)
local notation "f₀"=> U.plainP s ν
local notation "f₁"=> U.totalP s ν
local notation "d" => pleas V p α ν s i
variable (Cy:A→ℝ)(hh:∀ i,0≤Cy i)
local notation "A₀"=>accountK V Cy s
open Merge Switch FullVolume.Ray.Weigh
open Gas Ursell Trees Multiple Letter OmitClusters
set_option quotPrecheck false
open Mill Match Ovens Ovens.Pipes Refrain
open Progress.DirectedRecipe
-- stamp interface independent of actual β. price on FULL input switches.
local notation "X₀"=> staple (H:=H) (J:=H) rfl rfl rfl
variable (χ : Chi)
def archived (K:H.Chainbook→ℝ→ Finset A→ Config G c→ℝ) (i:ℕ) (t:ℝ)(b:Finset A) (U:Config G c):= (Refrain.badge H i).elim (fun p=> K p.val t b U) fun _=>0
variable {w e:ℝ}
def primitive (t:sun) (i:ℕ) (U':Config G c):Ways A:= fun j s=>Palette.shoot (facesT V t) (U.beams _ (U.lay t.property)) χ Cy H (recital U t) j s i U'
local notation "VB"=> Crew.primitive V Cy χ
lemma shootLens {H1 H2: Rep G f}{Y:Cash W x₀ μ L Q o C T R}{J:Cash W x₀ μ L Q o C T H2}{I: Cash W x₀ μ L Q o C T H1}(D:Alliance Y J 1 0) (h:D.units=Equiv.refl _)(Hp:Alliance I J 1 0) (hp:Hp.units= Equiv.refl _) (hx:R.path=H1.path)(he:R.activities.reg=H1.activities.reg)(hk:R.activities.forced=H1.activities.forced)
    (g: Refrain.Leaf J→ Config G c→ℝ) : stuff (Refrain.visa Y D) g=stuff (Refrain.visa I Hp) g:=by
   obtain ⟨q,l,⟨s₁,s₂,Y',v⟩,w,b,q'⟩:=R; obtain ⟨r',l',⟨p₂,s₁',K,k⟩,b',z,s'⟩:=H1; cases hx;cases he; cases hk; obtain ⟨_,_,_⟩:=D;cases h; obtain ⟨_,_,_⟩:=Hp;cases hp;rfl
-- J.shoot when switches J.That prefix equal. Price tuple
lemma bandon {t:sun} {B:Rep G f}{K:Cash W x₀ μ L Q o C T (U.notes t.val)}{P:Cash W x₀ μ L Q o C T B}(hp:Alliance P K 1 0)(he:hp.units=Equiv.refl _)(hx:R.path=B.path)(hr:R.activities.reg=B.activities.reg)(hK:R.activities.forced=B.activities.forced)(u:ℕ)(y:Config G c):primitive V Cy χ t u y=fun i b=>Palette.shoot (facesT V t) K χ Cy P hp i b u y:=by
   let D:=staple (H:=H) (J:=K) (U.seats t (U.lay t.property)).3 (U.seats t (U.lay t.property)).reg (U.seats t (U.lay t.property)).forced
   let A':= U.beams t (U.lay t.property)
   funext i b;unfold primitive Palette.shoot Palette.shootK
   rw [← Crew.shootLens D rfl hp he hx hr hK]; rfl -- proof differs from A'. rfl
include V
lemma peaks (t:sun)(i:ℕ)(z:ℝ)(b:Finset A)(x:Config G c): primitive V Cy χ t i x z b= archived (H:=H) (fun i z b x=> Crew.spine χ V Cy t i x z b) i z b x:=by
   let D:= recital U t; let K:= U.beams t (U.lay t.property); unfold archived
   rcases he:Refrain.badge H i with p|p
   · have hh := Refrain.visited H D ((Refrain.gate H D) p); rw [(Refrain.gate H D).symm_apply_apply, ← he] at hh
     let u:= Refrain.gate H D p; let v := Refrain.visa H D u;have hv:v=i:= (Refrain.badge H).injective hh; subst i; unfold primitive Palette.shoot Palette.shootK; change ((stuff _ _ (Refrain.visa H D u)):Config G c→ℝ) _= _; rw [Progress.DirectedRecipe.stuffed];exact (cabin χ V Cy x K D rfl p.val z b).symm
   have h:i∉Set.range (Refrain.visa H D):=by rintro ⟨q,hp⟩; rw [← hp,Refrain.visited] at he; contradiction
   unfold primitive Palette.shoot Palette.shootK; rw [Progress.DirectedRecipe.blank _ _ h];rfl
local notation "ι"=> fun i=> (Refrain.reserve H (Refrain.badge H i)).support
abbrev Sounding (f:sun→ℝ→Finset A→ Code G c) (i:ℕ): Trail (Config G c) A:= fun t u x s => f t x s i u
abbrev dawn (V:A→Mill U)(Cy:A→ℝ)(χ:Chi)(t:sun)(x:ℝ)(s:Finset A): Code G c:= Palette.shoot (facesT V t) (U.beams _ (U.lay t.property)) χ Cy H (recital U t) x s
def Kit (N:ℕ→ Support c) (v w:ℝ)(f:sun→ℝ→Finset A→ Code G c)(b:ℕ)(e:ℝ):Prop:=∃ z, Ac.Hit N b z e w ∧ ∀ i:ℕ,Strung (Sounding f i) v (z i)
lemma binning (h: Wield χ V Cy e B w)(hv:2≤v) : Kit (fun i=> (Refrain.reserve H (Refrain.badge H i)).support) (v/2) w (dawn V Cy χ) (radiusB x₀) e:= by
    obtain ⟨x,hx,hP⟩:=h.bones; let f(p:Refrain.Annual H):= p.elim (fun p=> x p.val) (fun _=>0)
    refine ⟨f ∘ Refrain.badge H,fun i=> ?_,fun i=>?_⟩
    · let g(p:Refrain.Annual H):= if i ∈ (Refrain.reserve H p).support then f p*Real.exp (e*coverNumber T₀ (Refrain.reserve H p).support) else 0
      apply Cost.equiv (Refrain.badge H) (f:=g); rw [← add_zero w]; exact Cost.sum (budget_pull (fun z:Refrain.Leaf H=>Subtype.val z) Subtype.val_injective (hx i)) (show SumBudget (fun j=>g (.inr j)) 0 from by simp [g,f,SumBudget])
    have he: Sounding (dawn V Cy χ) i=fun t u z b=> archived (H:=H) (fun i z b x=> Crew.spine χ V Cy t i x z b) i z b u:=funext fun t=> funext fun u=> funext fun z=>funext fun b=> peaks V Cy χ t i z b u
    rw [he]; unfold archived; dsimp only [Function.comp_apply]
    rcases Refrain.badge H i with p|p
    · exact hP p.val
    exact Strung.none (by linarith)
end Crew
end YM.ConnectedActivityE6.Empire.Imago
