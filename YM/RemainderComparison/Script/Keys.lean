import YM.RemainderComparison.Muse.Digits

/-!
# Restricting the query book; tests and symbolic forests don't become geometry variables

Pass to infinite catalogs countably supported with absolutely summable rents. Prove the exact FULL marked law not merely nets at each fixed volume (caps after switching -- no uniform norm on vacuum exp in circuitry).
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
-- define aliases stable Cast.Finite restrictions also actual tests

def drums (S:StepData c f): Drums (M ∘ σ) S ↪ Drums M S :=
 { toFun:=fun z=> ⟨z.val.map σ,fun i hi k hk eq=>by
                         obtain ⟨r,hr,rfl⟩:=Finset.mem_map.mp hi
                         obtain ⟨k,lT,rfl⟩:=Finset.mem_map.mp hk
                         exact congr_arg σ (z.prop hr lT eq)⟩
   inj':=fun i j hz=>Subtype.ext ((Finset.map_injective σ) (congr_arg Subtype.val hz)) }

variable (z:Drums (M ∘ σ) S)
lemma travels : (drums M σ S z).reach=z.reach:=by change (z.val.map σ).image (sign M S)= z.val.image (sign (M ∘ σ) S); simp_rw [map_eq_image,Finset.image_image]; rfl
lemma wage : team M (drums M σ S z)=team (M ∘ σ) z:=by
   have h: ∀ (M N : Team R),M.own=N.own→M=N:=by rintro ⟨x,y⟩ ⟨t,w⟩ h; congr
   apply h;change (z.val.map σ).image M=z.val.image (M ∘ σ)
   rw [map_eq_image,Finset.image_image]
variable (Z:Set ι)(l:ι→ℝ)(δ:ℝ)
local notation "lt"=> Muse.sits Z l δ

-- equivariant book projections
lemma clears : sits Z l δ∘σ=sits (σ ⁻¹' Z) (l ∘ σ) δ:=by ext; simp [sits, Verse.marked]
lemma earns (p:ℝ): desk Z l δ p ∘ σ=desk (σ ⁻¹' Z) (l ∘ σ) δ p:=by ext;simp [desk,sits,Verse.marked]

def write {U:Type} (u:Verse α U): Verse ι U:=⟨u.letters.map σ,u.utter⟩
lemma alloy {U:Type}(V:Verse α U): (write σ V).stock l= V.stock (l ∘ σ):=by unfold write Verse.stock; rw [Multiset.map_map]
lemma alive {U:Type}(V:Verse α U): (write σ V).emit l= V.emit (l ∘ σ) :=by funext U; unfold Verse.emit; rw [alloy]; rfl
open Marker
lemma liberty {τ:Type}[DecidableEq τ]{Jm:Marker.Census τ} (z:ι→ Poly Jm)(p:Multiset α) : Verse.controls Z z (p.map σ) = Verse.controls (σ ⁻¹' Z) (z ∘ σ) p:=by
   unfold Verse.controls; rw [Multiset.map_map]; apply congr_arg Multiset.prod; exact congr_arg (fun f=>p.map f) (funext fun i=>by simp)
lemma letter {τ:Type}[DecidableEq τ]{Jm:Marker.Census τ} {U:Type}(V: Verse α U) (z:ι→Poly Jm) : (write σ V).paint Z l z= V.paint (σ ⁻¹' Z) (l ∘ σ) (z ∘ σ):=by
   funext U; unfold Verse.paint; rw [alive]; exact congr_arg (_ • · ) (liberty σ Z z _)
lemma sun (p:Multiset α) : Verse.load Z (p.map σ)=Verse.load (σ ⁻¹' Z) p:=by
  induction p using Multiset.induction_on with
  | empty=>simp [Verse.load]
  | cons i s he=>unfold Verse.load at *; by_cases h: (σ i) ∈ Z <;> simp [*] -- beware Set.preimage def simp
lemma docket : (raw M (drums M σ S z))=write σ (raw (M ∘ σ) z):=by unfold raw write; rw [wage]; rfl
lemma dockets (p:Molecule S) : (Mosaic.tile M H χ p (drums M σ S z))=write σ (Mosaic.tile (M ∘ σ) H χ p z):=by unfold Mosaic.tile write act; dsimp only; simp_rw [wage]; rfl

variable {U:Pad H j χ}
lemma scaled (z:Muse.Motto M l δ H b q a j): Muse.Motto (M ∘ σ) (l ∘ σ) δ H b q a j:=by
   refine ⟨?_, z.target,z.positive,z.emit,z.grew⟩; obtain ⟨X,hX,P₀,x,hX⟩:= z.claim
   exact ⟨X,‹_›,P₀,x ∘ σ, ⟨fun j=>hX.currency _,fun i hp=> hX.pin (σ i) hp,fun j=>budget_pull _ σ.injective (hX.crown j),hX.tolerance,hX.sizes⟩⟩
lemma painted (Y:ℕ) (z:Muse.Pale M Z l Y d b a j H): Muse.Pale (M ∘ σ) (σ ⁻¹' Z) (l ∘ σ) Y d b a j H:=by
   obtain ⟨X,h,P'',p',hv⟩:= z; refine ⟨X,h,P'',p'∘σ,?_⟩; rw [show Sleet.pigmentY R Y (M ∘ σ) x d _= Sleet.pigmentY R Y M x d (Muse.sits Z l 0) ∘ σ from ?_]
   · refine ⟨fun i=> hv.currency _,fun i h=> hv.pin (σ i) h,fun i=> ?_,hv.tolerance,hv.sizes⟩
     exact budget_pull _ σ.injective (hv.crown i)
   rw [← Script.clears]; ext; simp [Sleet.pigmentY,Sleet.slump]
-- coverage for restrictions
variable (A:Finset ι)

def restrict : (↥A) ↪ ι:=⟨Subtype.val,Subtype.val_injective⟩
lemma pens (z:Drums M S): z∈Set.range (drums M (restrict A) S)↔ z.val⊆ A:=by
  constructor
  · rintro ⟨i,rfl⟩ j hj; obtain ⟨x,-,rfl⟩:=mem_map.mp hj; exact x.prop
  intro h; let t:=restrict A; let a:= z.val.preimage t t.injective.injOn
  let p:Drums (M ∘ t) S:= ⟨a, fun i hi x hx hn=> t.injective (z.prop (mem_preimage.mp hi) (mem_preimage.mp hx) hn)⟩
  refine ⟨p,Subtype.ext ?_⟩; ext i; constructor
  · intro hi; obtain ⟨j,hj,hk⟩:=mem_map.mp hi; subst i; exact mem_preimage.mp (show j∈ a from hj)
  intro hi
  let p:↥A:= ⟨i,h hi⟩
  change i∈a.map t
  exact mem_map.mpr ⟨p,mem_preimage.mpr hi,rfl⟩

-- Eventual: contains each arbitrary allocation, not just heads with bounded order
lemma arrived (z:Drums M S): ∀ᶠ p:Finset ι in atTop, z∈ Set.range (drums M (restrict p) S):=(eventually_ge_atTop z.val).mono fun j h=> (pens M j z).2 h
end YM.RemainderComparison.Script
