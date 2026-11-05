import YM.RemainderComparison.Lobby.Gas

/-!
# The aligned core portion excised once. Ornament/vessel/earnings may be used again on supported witnesses
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lobby
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open Progress.DirectedRecipe
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {ι β I J:Type} {α:Type*} {c f:Side} [DecidableEq β] {Jm:Marker.Census β} {Y: Stars→Side}
variable (O:Manor G c ι α I) (P:BudgetPoint)(root:ι→Support c) (K : Set I) (k:ℕ)
variable (a:α)(Z:Set ι)(z:ι→Marker.Poly Jm)
open Mosaic Serif Manor Flues
-- generic multilogue.P
variable (s:Finset I){r w D t:ℕ} {E a₀ b₀ e:ℝ} {root}
variable (B : O.Basis s r)(Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (fa:α→∀ i:Stars, Offer G (Y i))

-- k_les support for both types

def ranging (k d:ℕ): Vesuvius G c ι (Site c) α:=
     ⟨fun y=> neighbors d y,fun y=>⟨y,(neighbors_mem ..).2 (by rw [separation_self]; omega)⟩,fun a=>O.currencies a s P B Q (fa a) k,fun _=>0⟩

local notation "Vʼ" => ranging O P s B Q fa k D
local notation "Xʼ" => (mansion Q fa k : Manor G c ι α (Site c))
lemma hearth (he: Expulsion O s P B Q D k fa a₀ b₀) : Vesuvius.Works P root Z Vʼ a₀ b₀ 0 :=by
    obtain ⟨g,hg,h,hV⟩:= he.budget; refine ⟨fun i a=> he.awake a i, ?_,fun i a V=>he.missed a V i, g,fun _=>0,hg,fun _=>le_rfl,h,?_,fun i a V=>?_⟩
    · intro i a j hj; exact False.elim (Multiset.notMem_zero j hj)
    · intro i; apply budget_of_sum; · intro i; split <;> simp
      intro s; simp
    rw [if_pos (show Verse.load Z ((Vʼ).opus i)=0 from by simp [ranging,Verse.load])]; exact hV ..
-- manipulations.Emit all sums
variable (V:Config G c)
local notation "ψ"=> Vesuvius.books a Z z
lemma treeWard (hs:∀ i ∈ s,O.marks i=0) (D:ℕ) : ∑ i∈s,O.paint P Z z a V i= (Complex.ofReal (∑ x:Site c,O.sector a s B x 1)) • (1:Marker.Poly Jm)+∑ i:Site c, (Xʼ).paint P Z z a V i +∑ i: Site c,Vesuvius.books a Z z (ranging O P s B Q fa k D) V i:=by
    simp only [Manor.paint]; have he : Verse.controls Z z 0=1:=by unfold Verse.controls; simp
    have hp : (∑ i∈s,(Complex.ofReal (O.wet P a i V)) • Verse.controls Z z (O.marks i)) = (∑ i∈s,Complex.ofReal (O.wet P a i V)) • (1:Marker.Poly Jm):=by rw [Finset.sum_smul]; exact sum_congr rfl (fun i hi=> by rw [hs i hi,he])
    have hv i: (Xʼ).wet P a i V=masked P.threshold (neighbors k i) (Trio.ornament Q (fa a) i) V:= if_neg (show ¬ (Xʼ).total i from id)
    rw [hp,← Complex.ofReal_sum,O.garnered a s P B Q (fa a) k V,Complex.ofReal_add,Complex.ofReal_add,add_smul,add_smul]; unfold Vesuvius.books; simp_rw [hv, show ∀ i,(Xʼ).marks i=0 from fun _=>rfl, he,show ∀ i,(ranging O P s B Q fa k D).opus i=0 from fun _=>rfl,he]; simp only [Complex.ofReal_sum,sum_smul]; rfl
variable {K}
variable (T: Manor.Quarry O K J root r) (hv:2*w≤f.val)(g:α→J→ Config G f→ℝ)(u:J→ℝ)
local notation "Kʼ"=> vessel O T hv g u D

def blooming (D:ℕ): Vesuvius G c ι J α:=
    ⟨ (vessel O T hv g u D).halls,fun i=>⟨ (vessel O T hv g u D).port i,(vessel O T hv g u D).call i⟩,O.zephyr T P hv g u D,T.sign⟩
local notation "Vˮ" => blooming O P T hv g u D
lemma resonant (hz:∀ i, 0< Verse.load Z (T.sign i))(h:Nimble O T P Kʼ (O.zephyr T P hv g u D) a₀ e): Vesuvius.Works P root Z Vˮ a₀ 0 e:= by
    obtain ⟨f,hf,hB,hX⟩:=h.budget; refine ⟨h.awake,h.letters,h.missed,fun _=>0,f,fun _=>le_rfl,hf,?_,hB,fun i a V=>?_⟩
    · intro i; apply budget_of_sum; · intro i; split<;> simp
      intro s; simp
    rw [if_neg (Nat.ne_of_gt (show 0 < Verse.load Z ((Vˮ).opus i) from hz i))]; exact hX ..

def walls (T:Manor.Quarry O K J root r) : Set I:= {i| ∃ j, i∈T.panel j}
lemma sun_sum (j:J) (D:ℕ): ∑ i∈T.panel j,O.paint P Z z a V i=
     Manor.paint (vessel O T hv g u D) P Z z a V j+ Vesuvius.books a Z z (blooming O P T hv g u D) V j:=by
    unfold Manor.paint Vesuvius.books; let c:= Verse.controls Z z (T.sign j); change _= _ • c+ _ • c
    unfold blooming; dsimp only; rw [← add_smul,← Complex.ofReal_add, Manor.zephyr, add_sub_cancel]; unfold Manor.compass; rw [Complex.ofReal_sum,sum_smul]; refine sum_congr rfl fun i hi=>?_ ; rw [(T.meets j i hi).2.2] -- adjust

section sums
-- arbitrary J T. Partition sum of elections; no colliding h.K.Tag costs. No DecEq required.
variable {fQ:I→Marker.Poly Jm}
lemma adepts (hp:Summable (fun i:walls O T=> fQ i.val)): HasSum (fun i:J=> ∑ j∈T.panel i,fQ j) (∑' i:walls O T,fQ i.val):=by
    let X:=walls O T; have he i (hi:i ∈ X): ∃ j,i∈T.panel j:= hi
    choose d hd using (show ∀ i:X, ∃ j, i.val∈T.panel j from fun i=> he _ i.prop)
    let b (i:J):= T.panel i; let g x:= fQ (x:X).val; have hr i: (i:X).val ∈ b (d i):= hd i
    have hv i j : (i:X).val∈b j↔d i=j:= ⟨fun h=>Classical.byContradiction fun he=> disjoint_left.mp (T.once (d i) j he) (hr _) h,fun h=> h ▸ hr i⟩
    have hh := (show Summable g from hp).hasSum.tsum_fiberwise d
    apply hh.congr_fun; intro i; symm; let u:= b i; let f':={j:X// d j=i}
    let ζ(j:f') : ↥u:= ⟨j.val.val,(hv _ _).mpr j.prop⟩; have hz: Bijective ζ:= ⟨fun i j h=> Subtype.ext (Subtype.ext (show i.val.val=j.val.val from congr_arg (fun x:↥u=>x.val) h)), fun j=> ?_⟩
    · let k:= Equiv.ofBijective ζ hz; calc _ = ∑' i:↥u, fQ i.val := k.tsum_eq (fun i:↥u=> fQ i.val)
                                           _ = ∑ j∈T.panel i,fQ j := by rw [tsum_fintype]; exact Finset.sum_coe_sort ..
    let p : X:=⟨j.val,i,j.prop⟩; exact ⟨⟨p,(hv p i).mp j.prop⟩,rfl⟩
-- rewrite with omitted p domain. supports.Vol.plate
end sums
end YM.RemainderComparison.Lobby
