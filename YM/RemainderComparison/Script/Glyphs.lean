import YM.RemainderComparison.Script.Keys

/-!
# Coverage of all words
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
open Lyric Mosaic Muse
variable (σ:α ↪ ι)
local notation "M'" => M ∘ σ
local notation "V'"=> drums M σ S

def label (p:H.fragrances): Syllable M' H p ↪ Syllable M H p := ⟨fun w i=>drums M σ S (w i),fun _ _ h=>funext fun i=> (drums M σ S).injective (congr_fun h i)⟩
local notation "w'"=> label M H σ

def board : (p:H.Chapter)→ Stone M' H p ↪ Stone M H p
 | .inl _ => drums M σ S
 | .inr p=> label M H σ p

def queue (p:H.Chainbook): Scene M' H p ↪ Scene M H p:= ⟨fun i j k=>board M H σ j.val (i j k), fun _ _ h=>funext fun j=>funext fun i=> (board M H σ j.val).injective (congr_fun (congr_fun h j) i)⟩
lemma ferries {ι A : Type} {P:Filter A} {X:ι→Type} {J:A→ι→Type}[Finite ι](p:(x:A)→(i:ι)→J x i ↪ X i) (f:∀ i,X i)(h:∀ i, ∀ᶠ x in P, f i∈ Set.range (p x i)) : ∀ᶠ x in P, ∃ w:∀ i,J x i, f=fun i=>p x i (w i):=by
   filter_upwards [eventually_all.mpr h] with x hx; choose z hz using hx; exact ⟨z,funext fun i=>(hz i).symm⟩

lemma ships (z:H.fragrances)(f:Syllable M H z) : ∀ᶠ p:Finset ι in atTop, f∈ Set.range (label M H (restrict p) z):=by
   have h : ∀ i:Option (Fin z.1),∀ᶠ p:Finset ι in atTop, f i∈Set.range (drums M (restrict p) S) := fun i=> arrived M (f i)
   filter_upwards [ferries _ _ h] with x hx; obtain ⟨w,h⟩:=hx; exact ⟨w,h.symm⟩
lemma stamps (p:H.Chapter)(s: Stone M H p) : ∀ᶠ z:Finset ι in atTop,s∈ Set.range (board M H (restrict z) p):=by
   rcases p with p|p
   · exact arrived M s
   exact ships M H p s
lemma flags (p:H.Chainbook)(s:Scene M H p): ∀ᶠ z:Finset ι in atTop,s∈Set.range (queue M H (restrict z) p):=by
   have h(i:↥p.1) : ∀ᶠ z:Finset ι in atTop,∀ j:Slots H p i,s i j∈Set.range (board M H (restrict z) i.val):= eventually_all.mpr (fun j=> stamps M H _ _)
   filter_upwards [eventually_all.mpr h] with z hz; choose f hf using hz; exact ⟨f,funext fun i=>funext fun j=> hf i j⟩

lemma bees {τ α β:Type} {f:α→β} (s: Finset τ)(p:τ→Multiset α) : (∑ i∈s,p i).map f=∑ i∈s,(p i).map f:=by
   induction s using Finset.induction_on with
   | empty=>simp
   | @insert i s hi ih=>simp [hi,ih]

lemma joins {ι U:Type}{a b:Verse ι U} (h:a.letters=b.letters)(hp:a.utter=b.utter): a=b:=by cases a;cases b; congr
lemma resume (p:H.fragrances)(w:Syllable M' H p) : etude M H χ p (label M H σ p w)= write σ (etude M' H χ p w):=by
   let z' i:=w i
   apply joins
   · unfold etude write; dsimp only; rw [bees]; exact Finset.sum_congr rfl fun i _=>rfl
   funext U; dsimp only [write,etude,Lyric.string]; apply congr_arg (Lyric.cadence H p *·); refine prod_congr rfl fun i _=>?_; unfold toe; rw [show label M H σ p w i=drums M σ S (w i) from rfl,wage]

lemma poster (p:H.fragrances)(w:Syllable M' H p) : jewel M H χ p (label M H σ p w)= write σ (jewel M' H χ p w):= by
   apply joins
   · have hx:=congr_arg Verse.letters (resume M H χ σ p w); exact hx
   funext U; exact congr_arg (fun f=>masked (Pressure.temp x) (Captain.reachability p) f U) (congr_arg Verse.utter (resume M H χ σ p w))
lemma closet (p:H.Chapter)(w:Stone M' H p): Mosaic.panel M H χ p (board M H σ p w)=write σ (panel M' H χ p w):= by
   rcases p with p|p; exact dockets M H χ σ w _
   have hz:= congr_arg Verse.letters (poster M H χ σ p w)
   exact joins hz <| congr_arg Neg.neg (show Lyric.cut M H χ p _= Lyric.cut M' H χ p _ from congr_arg Verse.utter (poster M H χ σ p w))
lemma parade (p:H.Chainbook)(w:Scene M' H p): Mosaic.parade M H χ p (queue M H σ p w)=write σ (Mosaic.parade M' H χ p w):=by
   apply joins
   · unfold Mosaic.parade write; dsimp only; rw [bees]; refine sum_congr rfl fun i _=>?_ ; rw [bees]; exact sum_congr rfl fun j _=>congr_arg Verse.letters (closet M H χ σ _ (w i j))
   funext U; dsimp only [Mosaic.parade,write]; split; next h=>
      apply Finset.prod_congr rfl; intro i _; exact congr_arg (·/_) (Finset.prod_congr rfl fun j _=>congr_fun (congr_arg Verse.utter (closet M H χ σ _ (w i j))) U) -- if? fix
   next=>rfl
-- orientation

end YM.RemainderComparison.Script
