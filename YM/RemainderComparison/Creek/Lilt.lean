import YM.RemainderComparison.Creek.Ancient
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Creek
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι β : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet Serif Typeface
variable (U:Pad H j χ)
local notation "F'"=> U.S.N
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)(Z:Set ι)(δ:ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l δ H τ K Y I)
local notation "Lt"=> sits Z l δ
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable [DecidableEq β]{Jm:Marker.Census β}
variable (z:ι→Marker.Poly Jm) {gP:β→ℝ} (hZ : Chorus Jm gP Z z k)
open Mallow Ovens Progress.DirectedRecipe
open WickReps
local notation "Tt"=> Sleet.Staff Vx H
local notation "Σ₁" => Mosaic.etude Vx H χ
local notation "Σ₂" => Mosaic.etude Vy H χ
open Mosaic Serif
local notation "A₀" => theater H χ M x' l Z δ
local notation "Rt" => Flues.candle M x' S
variable (P':BudgetPoint)
open Verse
local notation "Ac₀"=> Academy H χ M x' l Z δ k
set_option quotPrecheck false
local notation "mkq" => (A₀).marks
variable {Vb : Set (Staff (brand M x') H)}
lemma prior {w:Staff Vx H→ℝ} {u:ℝ} (hf : ∀ y, Muse.Network (brand M y) H χ Lt P' Vb w a u): Manor.Spinal A₀ Vb Rt P' a u:=by
   have he : (A₀).halls=Sleet.Base Vx H:=funext (point H χ M x' l Z δ)
   let z p:= if p∈ Vb then w p else 0
   have hz p:0 ≤ z p:=by unfold z; split; exact ((hf x').mark p ‹_›).nneg; exact le_rfl
   refine ⟨z,hz,?_,he ▸ (hf x').costs⟩; rintro i hi; rw [he,show z i=w i from if_pos hi]
   have h y:= ((hf y).mark i hi).bound; exact ⟨Creek.symmetry H χ M x' l Z δ P' (fun y=> (h y).1),fun y=> (h y).2⟩

-- dormancy
local notation "virg"=> fun (p:Tt)=> Muse.virgin Vx H χ Z p.1 p.2
local notation "pureV"=> Muse.Pure Vx H χ Z k
local notation "impur" => Muse.impure Vx H χ Z k
def spare : Set Tt:= {i| (A₀).marks i=0}
lemma monastery {i:Tt}(h:i∈ Ac₀) : Muse.Pure Vx H χ Z k i ∨ Muse.impure Vx H χ Z k i:=by
   by_cases he : virg i; exact Or.inl ⟨he,h.1⟩; exact Or.inr ⟨he,h.1⟩
lemma monks {i:Tt}(hx: load Z ((A₀).marks i)=0) (hp: virgin Vx H χ Z i.fst i.snd) : i ∈ spare H χ M x' l Z δ:=by
   have hz:=Muse.harmonic Vx H χ Z i.1 i.2
   apply Multiset.card_eq_zero.mp; rw [show ((A₀).marks i).card= _ from Muse.scores Vx H χ i.fst i.snd, ← hz,show arity _ _ _ _ _ _=0 from hx,show _=0 from hp]
local notation "S*" => spare H χ M x' l Z δ
lemma worn {i:Tt}(hv:i∈ S*) : pureV i ∧ Verse.load Z (mkq i)=0 := by
   change mkq i=0 at hv; have ht : ∀ Z':Set ι, Verse.load Z' (mkq i)=0:=by intro Z'; unfold Verse.load; rw [hv]; simp
   exact ⟨⟨ht _,(ht Z).trans_le (Nat.zero_le _)⟩,ht _⟩
-- anchor E (echo pulled)

def spool : H.fragrances ↪ Tt:= ⟨fun i=> ⟨i,Solo.echo (brand M x') H i⟩,fun _ _ h=>congr_arg Sigma.fst h⟩
local notation "Vt"=> spool H M x'
lemma spiced (i:Tt) (h:i∈ S*) : i∈ Set.range (spool H M x') := by
   let s := Sigma.mk (β:= Syllable Vx H) i.1 (Solo.echo Vx H i.1); refine ⟨i.1,?_⟩ -- edit
   obtain ⟨i,w⟩:=i
   have he : w=Solo.echo Vx H i:=by
      funext j; apply Subtype.ext; refine Finset.eq_empty_iff_forall_notMem.mpr fun k hk=>?_
      have ht:= (leaves H χ M x' l Z δ ⟨i,w⟩ k).2 (Finset.mem_biUnion.mpr ⟨j,mem_univ _,hk⟩)
      rw [show mkq ⟨i,w⟩=0 from h] at ht; exact Multiset.notMem_zero _ ht
   rw [he]; rfl
lemma solitude (i:H.fragrances) : (A₀).solvent y (Vt i)=(fun V=> stream H χ V i):=by
   funext V; change (etude (brand M y) H χ i (Solo.echo Vy H i)).emit Lt V= _
   rw [Verse.emit,Mosaic.pieces]; rw [(Solo.calls Vy H Lt i).2.2,one_mul]; exact congr_fun (Solo.songs Vy H χ i) V
variable {E:Set ℕ}
lemma stocky {d:ℝ}{B:Set Tt}(h: B⊆ S*)(hp : ∀ (i:H.fragrances), spool H M x' i∈B → Solo.Scorched H E i) (he:Solo.Supply H χ E P' a d):
    Manor.Templary A₀ B Rt P' a d:=by
   obtain ⟨w,h',hw,hP⟩:= he.grants; let w':= Progress.DirectedRecipe.stuff Vt w; have hx := Progress.DirectedRecipe.Rack.positive Vt w hw
   have ht i (hi:Vt i∈B) y: P'.Regular ((A₀).halls (Vt i)) ((A₀).solvent y (Vt i))∧ P'.supBounds ((A₀).port (Vt i)) ((A₀).halls (Vt i)) ((A₀).solvent y (Vt i)) (w' (Vt i)):=by
      rw [Creek.solitude, show w' (Vt i)=w i from Progress.DirectedRecipe.stuffed _ _ i]; exact h' i (hp _ hi)
   refine ⟨w',hx,?_,fun x=> Progress.DirectedRecipe.transfer_budget Vt (fun i=>?_) (fun i hi=>?_) (hP x)⟩
   · intro i hi; obtain ⟨p,rfl⟩:= spiced H χ M x' l Z δ i (h hi); exact ⟨Creek.symmetry H χ M x' l Z δ P' (fun i=> (point H χ M x' l Z δ _) ▸ (ht p hi i).1),fun i=>(ht p hi i).2⟩
   · unfold w'; rw [Progress.DirectedRecipe.stuffed]; dsimp only; rw [Creek.point]; rfl
   split; next=> rw [show w' i=0 from Progress.DirectedRecipe.blank _ _ hi,zero_mul]
   next=>exact rfl
-- Pure mass is actually decaying before E.P melancholy. Uses unadorned Armada (canonical O may be picked). Path.
variable {U':BudgetPoint}
lemma stake (N:Captain H j q d v u A b r B e n χ) {y:ℝ} (ht:P'.threshold=Pressure.temp x) (hf:P'.order≤j)(hp:P'.power≤J)(hk:P'.B=radiusB x)(hq:Armada Q L μ a x y B j n):
    Manor.Spinal A₀ S* Rt P' a (collars G y x j J*(Blaze.March.salary Q L μ B x j n*(1/2:ℝ)^0*(1-1/2)⁻¹)):=by
    let w i:= N.markΦ i J; let w':= Progress.DirectedRecipe.stuff Vt w; have hx i:= N.gloryBudget i P' ht hf; have hv i : 0 ≤ w i:= ((hx i|>.2.2 J hp) ((A₀).port (Vt i)) (show _∈reachability i from (Solo.locus H i) ▸ (Beam.dashboard H i).anchor)).1
    have hb i a: P'.Regular ((A₀).halls (Vt i)) ((A₀).solvent a (Vt i))∧∀ x∈(A₀).halls (Vt i), P'.supBounds x ((A₀).halls (Vt i)) ((A₀).solvent a (Vt i)) (w' (Vt i)):=by
        rw [point, Creek.solitude]; unfold w'; rw [Progress.DirectedRecipe.stuffed]; exact ⟨((hx i).2.1),(hx i).2.2 J hp⟩
    have hh:= hq.applies N J 0
    refine ⟨w',Progress.DirectedRecipe.Rack.positive _ _ hv,?_,fun x=> Progress.DirectedRecipe.transfer_budget Vt (fun i=>?_) (fun i hi=> ?_) (hh x)⟩
    · intro i hi; obtain ⟨p,rfl⟩:= spiced H χ M x' l Z δ i hi; exact ⟨Creek.symmetry H χ M x' l Z δ P' (fun i=> (point H χ M x' l Z δ _) ▸ (hb p i).1),fun a=> (hb p a).2⟩
    · unfold w'; rw [Progress.DirectedRecipe.stuffed,point,hk]; dsimp only; rw [if_pos (Nat.zero_le _ )]; rfl
    split; next=> unfold w'; rw [Progress.DirectedRecipe.blank _ _ hi,zero_mul]
    next=>rfl
end YM.RemainderComparison.Creek
