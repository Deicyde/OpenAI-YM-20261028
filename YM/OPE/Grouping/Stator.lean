import YM.MergeProof.North.Stator
import YM.OPE.Grouping.Fibers
import YM.OPE.Grouping.Stained

/-!
# Simultaneous collapses at a mesh scale

This accounting generalizes the proof for pairs in YM/MergeProof/North/Stator.lean
to a projection along fibers. The Deck prices a nonempty finite number of children
(not necessarily common across grouping regions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {S₀ : Type*} [Fintype S₀][DecidableEq S₀] {Δ : Fibers S₀ V}
open MeasureTheory
structure Salt (V S₀:Type*) [DecidableEq V][Fintype V][DecidableEq S₀][Fintype S₀](Δ:Fibers S₀ V)(G:Gauge)(n:Side) where
   grain : S₀ → Site n
   pepper : S₀→ℂ
   air : Support n → Config G n → Poly (Bud S₀)
   river : Box n → Config G n → Poly (Bud S₀)
namespace Salt
variable (Z:Salt V S₀ Δ G n)(t:ℝ)
structure Breeze (t:ℝ):Prop where
   home s: Burns Z.grain s (Z.air s) t
   permits s : Flow Z.grain s (Z.river s) t
abbrev Turf := {i: Support n × (Bud S₀).Mode // i.2.val.Nonempty ∧ i.2.val.image Z.grain ⊆ i.1}
abbrev Lawn:= S₀⊕ Z.Turf
abbrev Brook:= {i:Box n × (Bud S₀).Mode // Sure i.1 ∧ i.2.val.image Z.grain ⊆ i.1.1}
abbrev Seed:= Z.Lawn×Bool
def focus(i:V):=Z.grain (Δ.twig i)
def marker : Z.Lawn→ (Bud S₀).Mode:= Sum.elim (Bud S₀).fire (fun i=>i.val.2)
def leaf : Z.Lawn→ Support n:= Sum.elim (fun i=> {Z.grain i}) (fun i=>i.val.1)
def syrup : Z.Lawn → Config G n→ℂ := Sum.elim (fun i _=> Z.pepper i) (fun i U=> (Z.air i.val.1 U).part i.val.2)
def kiln (P:Support n)(q:(Bud S₀).Mode):= P∪(Δ.span q).val.image Z.focus

def bud (U : Config G n)(i:Z.Seed):ℂ:= if Healthy t (Z.kiln (Z.leaf i.1) (Z.marker i.1)) U ↔ i.2=true then Z.syrup i.1 U else 0
def vessel : Deck V S₀ Δ Z.Seed Z.Brook G n where
   mode_ := Sum.elim (fun i=> Z.marker i.1) fun i=>i.val.2
   wick i:= Z.leaf i.1
   spill i:= i.val.1
   cover := Sum.elim (fun i=> Z.kiln (Z.leaf i.1) (Z.marker i.1)) (fun i=>Z.kiln i.val.1.1 i.val.2)
   toll := Sum.elim (fun i U=> Z.bud t U i) fun i U=> (Z.river i.val.1 U).part i.val.2
   ash i:=i.2=false
   seat:= Z.focus
local notation "P"=> Z.vessel t
lemma sits (i : Z.Lawn) : (Z.marker i).val.Nonempty∧ (Z.marker i).val.image Z.grain⊆ Z.leaf i:=by
   cases i
   next i=> exact ⟨singleton_nonempty _, fun j h=>by simpa [marker,Census.fire,leaf] using h⟩
   next i=> exact i.property
variable (h:Z.Breeze t)
include h
lemma wet :(P).Wet t:=by
    refine ⟨fun i=>?_,fun i v=>?_,fun i=>(Z.sits _).1,fun i=> i.property.1,fun i U he hx hy=>hx ?_,fun i U hp=>(h.permits i.val.1|>.permits U ?_).1,fun i hi=>?_⟩
    · cases i <;> exact subset_union_left
    · intro h; cases i <;> exact subset_union_right (mem_image_of_mem _ h)
    · exact if_neg (fun hz=> Bool.false_ne_true ((show i.2=false from he).symm.trans (hz.1 hy)))
    · exact fun he=>hp (by change (Z.river i.val.1 U).part _ = _; rw [he,Poly.part_nil])
    change (Δ.span i.val.2).val=∅ at hi; unfold vessel; simp [kiln,Sum.elim,hi] -- roster not
lemma peopled (i:Z.Lawn): UsesFinal t (Z.leaf i) (Z.syrup i) ∧ Measurable (Z.syrup i)∧ GaugeInvariant (Z.syrup i):=by
   cases i
   next i=> exact ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _=>rfl⟩
   next i=> refine ⟨fun x y hx hy=> congr_arg (fun p:Poly (Bud S₀)=> p.part i.val.2) ((h.home i.val.1).home _ _ hx hy), (h.home _).me i.val.2,fun t Q=> ?_⟩; exact congr_arg (fun p:Poly (Bud S₀)=> p.part i.val.2) ((h.home _).turns t Q)
lemma sow (i:Z.Seed):let K:=Z.kiln (Z.leaf i.1) (Z.marker i.1);let v:=fun U=> Z.bud t U i; UsesFinal t K v∧ Measurable v∧ GaugeInvariant v:=by
   intro K v; obtain ⟨hx,hp,hz⟩:= Z.peopled _ h _; have hr:UsesFinal t K (Z.syrup i.1):=Work.H03.reads_larger subset_union_left hx
   refine ⟨fun X Y ha hb=>?_, Measurable.ite ?_ hp measurable_const,fun s U=>?_⟩
   · change (if Healthy t K X ↔ _ then _ else _) = (if Healthy t K Y ↔ _ then _ else _); unfold Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty,hb,hr X Y ha hb]
   · by_cases hh:i.2=true
     · simp only [hh,iff_true,Healthy,disjoint_iff_inter_eq_empty]; exact census_me t K ∅ -- check
     simp only [hh,Bool.false_eq_true,iff_false,Healthy,disjoint_iff_inter_eq_empty]; exact (census_me t K ∅).compl -- Iff false strong
   unfold v bud Healthy; simp only [gauge_flags,hz s U]; congr
lemma turn :(P).Smooth t:=by
    refine ⟨fun j=>?_,fun j=>?_,fun j=>?_,fun i U hi hV=>?_⟩
    · cases j; next i=> exact (Z.sow _ h i).1
      next i=> apply Work.H03.reads_larger (p:=i.val.1.1) subset_union_left (fun X Y hp hv=>?_); exact congr_arg (fun p:Poly (Bud S₀)=>p.part i.val.2) ((h.permits _).home X Y hp hv)
    · cases j; next i=> exact (Z.sow _ h i).2.1
      next i=> exact (h.permits _).me i.val.2
    · cases j; next i=> exact (Z.sow _ h i).2.2
      next i=> exact fun s Q=>congr_arg (fun p:Poly (Bud S₀)=>p.part i.val.2) ((h.permits _).turns s Q)
    change ¬ i.2=false at hi
    change Z.bud .. ≠ 0 at hV; unfold Salt.bud at hV; split at hV
    next he=> exact he.2 (by simpa using hi)
    contradiction
end Salt
end YM.MergeProof.Ribbons.Fibers
