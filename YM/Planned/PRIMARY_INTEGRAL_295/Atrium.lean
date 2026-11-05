import YM.Planned.PRIMARY_INTEGRAL_295.Mirage
import YM.Planned.PRIMARY_INTEGRAL_295.Novas
/-!
# C pore: bank construction on actual centered canonical support

Option E. θ.Stamps. Choose held I even on all inspected X^+, axis also at
adjacent where lying wholly inside X'. Truth wants masks on every Q.F
used in birth. H taller fields beyond literal Boat.M will be errors red.
Single canonical F of one Source. Stencil independent L shapes; cover receipt
only on eventual pre.L Boards where θ Profile.Ω.b δ. doesn't solve Birth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Atrium
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions  Castles    
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations Racks Dials WardBin WardBin.Lies Spurs Vintage
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical NNReal
variable {G:Gauge} {k r n d χ:ℕ} {x:ℝ} {c f:Side} {t θ ξ C M s : ℝ}
variable {F:Labels.Frame G d}

lemma court (X:Support c) (i:Site c) (h:i∈inspected X): ∃ y∈X,separation y i≤4:=by
   rcases mem_union.mp (show i∈inspected X from h) with h|h
   · exact ⟨_,h,by simp⟩
   obtain ⟨j,_,hp⟩:=mem_biUnion.mp h; split at hp <;> rename_i h
   · simp at hp
   obtain ⟨x,hx,hh⟩:=not_disjoint_iff.mp h
   have hu:= Work.E01.sep_touched j x hh; have hl:= Work.E01.sep_touched j i hp; rw [separation_comm] at hu; exact (show _ from ⟨x,hx,(separation_triangle x j.1 _).trans (by omega)⟩)

-- budget from origin. canonical in small.Support with halo T.S.HALL candidates

def size (T:SectionData F):ℕ:= ∑ i∈T.stencil,Laurent.size i

lemma trails (T:SectionData F)(r:Ratio c f)(x:Site f)(h:x∈inspected (T.footprint 0)) : separation 0 (r.parent x) ≤ Atrium.size T +5:=by
    have hx: r.parent 0=0 := (show r.embed 0=0 from r.root.map_zero) ▸ r.embed_parent 0
    obtain ⟨y,hU,hq⟩:=court (T.footprint 0) x h
    obtain ⟨i,hi,rfl⟩:= mem_image.mp hU
    have hh:= spans i f; have hb: Laurent.size i ≤ size T:= Finset.single_le_sum (f:=Laurent.size) (fun i _=>Nat.zero_le _) hi
    have ha:= Work.E04.parent_separation r 0 x; rw [hx] at ha; rw [add_zero] at hq; have he:= separation_triangle (0:Site f) (wrap f i) x; omega

section Season
variable (S:StepData c f) (B:ℕ) (T:SectionData F)(X: Forest S.ratio)
def patchLand : Support f:= inspected (T.footprint 0)
def rooster : Finset X.Free:= Finset.univ.filter fun i:X.Free=> i.val.1 ∈ patchLand (f:=f) T ∧ i.val.1+step i.val.2∈ patchLand (f:=f) T

def door : Finset (Bond f):= Finset.univ.filter fun i=> separation 0 (S.ratio.parent i.1) ≤ 4*B
lemma door_spec (i:Bond f): i∈door S B↔separation 0 (S.ratio.parent i.1)≤4*B:=by simp [door]


variable (ht:300≤B)(he:Atrium.size T+5 ≤ B)
include he ht
lemma within_rooster : ∀ i: rooster S T X, ∀ j, Sparks.alive S B i.val.val j → separation 0 (S.ratio.parent j.1) ≤ 2*B :=by
    intro i j h; have hk := (departures S B i.val.val j ht).1 h
    have hv:= trails T S.ratio _ (mem_filter.mp i.property).2.1; have hr:=separation_triangle (0:Site c) (S.ratio.parent i.val.val.1) (S.ratio.parent j.1)
    omega
def plazas : Bank G S:= ⟨X,B,rooster S T X,door S B,fun i j h=> (door_spec S B j).mpr ((within_rooster S B T X ht he i j h).trans (by omega))⟩
lemma grades : (Fintype.card (rooster S T X) :ℕ) ≤ (door S B).card:=by
    let f : rooster S T X → door S B:=fun i=>⟨i.val.val,(plazas S B T X ht he).seen i _ (by simp [Sparks.alive])⟩
    have hf:Injective f:=by
       intro i j h; have ht:=congr_arg Subtype.val h; exact Subtype.ext (Subtype.ext ht)
    simpa using Fintype.card_le_of_injective f hf
end Season

-- actual x promised, p bound.H. no Spike proof. certificate w.Level.B Pose.
section Echo
variable (S:StepData c f) {x:ℝ}
structure Date (T:SectionData F)(x:ℝ)(L:Patch):Prop where
    count : 300 ≤ radiusB x
    pen : size T + 5 ≤ radiusB x
    admits : 2*Mirage.budget L (cut x) ≤ radiusB x

variable (T:SectionData F)(P : Tube G S)(B: Forest S.ratio) (i:S.Choices)(ε:ℝ)(η: Pulse G) (h : Date T x S.patch)

def lantern (T:SectionData F)(x:ℝ)(P : Tube G S)(B: Forest S.ratio)(i:S.Choices)(ε:ℝ)(η: Pulse G) (h : Date T x S.patch): Torch G S:=
       ⟨plazas S _ T B h.count h.pen, P,i,cut x,ε,η⟩

def priceCard (G : Gauge)(L:Side)(P:ℝ):ℝ:= (8*P+1)^4* ((L.val:ℝ)^4*4)*(1+ (Fintype.card G.ColorIndex:ℝ))

 -- missing def Place
end Echo
end YM.Planned.PrimaryIntegral295.Atrium
