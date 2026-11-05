import YM.TraceExtension.Cask.Stack
import YM.TraceExtension.Cask.Elude
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W:Type}[DecidableEq V][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype L][Fintype W]{G:Gauge}
-- anatomy includes VISUAL calculations. hull only bumps for touched p. Support costs at camera chosen by caller.
structure TourC (R:Rep G n)(V L W:Type)[DecidableEq V] where
    seat : V ↪ Site n
    tie : V → Site n
    cap : V → Support n
    anchor v : seat v ∈ cap v
    centre v : tie v ∈ cap v
    trek : Finset V → (V→G.El) → Config G n → Config G n
    guardP : V→ Config G n→ G.El→ Prop
    adjust : (Site n→G.El) → V→ G.El
    path : L → Support n
    long : L→ Config G n→ℝ
    short : Config G n→ℝ
    marks : V→ Config G n→ G.El→ℂ
    high : V→ Config G n→ G.El→ℂ
    fee : V→ Config G n → Rain V G→ℝ
    who : W→ V
    paint : W→ Config G n→ G.El→ℂ
    size : W→Support n
    lease i : seat (who i)∈size i
variable {R:Rep G n}(C:TourC R V L W)
abbrev bud (S:Finset V)(a:Support n):= a ∪ S.biUnion C.cap
abbrev deer (P:Support n):= univ.filter fun i:V=> C.tie i∈P
abbrev BoxF (n:Side):={i:Box n// Sure i}
abbrev PureC := Σ l:L,{s:Finset V// s⊆deer C (C.path l)∧s.Nonempty}
abbrev Axe := Σ i:BoxF n,{s: Finset V//s⊆deer C i.val.1}
abbrev LandC := Grain (PureC C) (Axe C) W
abbrev actorsC : LandC C→ Finset V:= Sum.elim (fun i=>{C.who i}) (Sum.elim (fun i:PureC C=>i.2.val) (fun i:Axe C=> i.2.val))
def midland (i:Axe C): Box n:=i.1.val
def excerpt : LandC C→Support n:= Sum.elim C.size (Sum.elim (fun i:PureC C=> bud C i.2.val (C.path i.1)) (fun i:Axe C=> bud C i.2.val i.1.val.1))
def agency : Staff V (LandC C) n where
 seat:= C.seat
 cast:= actorsC C
 shop i:= i.isLeft
 foot:= excerpt C
 pole:= Sum.elim (fun _=>∅) (Sum.elim (fun _=>∅) (Prod.fst ∘ midland C))
 flag:= Sum.elim (fun _=>∅) (Sum.elim (fun _=>∅) (Prod.snd ∘ midland C))
 purse i := match i with
    | .inl _ | .inr (.inl _)=> empty_subset _
    | .inr (.inr _)=> subset_union_left
 needs i := match i with
    | .inl _ | .inr (.inl _)=>fun h=>False.elim (not_nonempty_empty h)
    | .inr (.inr i)=>fun _=>i.1.property.1
 miss i := match i with
    | .inl _ | .inr (.inl _)=> empty_subset _
    | .inr (.inr i)=> i.1.property.2
 root i := match i with
    | .inl i => Or.inr (singleton_nonempty _)
    | .inr (.inl i) => Or.inr i.2.property.2
    | .inr (.inr i)=> Or.inl (i.1.property.1.mono i.1.property.2)
 books i x hx := match i with
    | .inl i=> (mem_singleton.mp hx).symm ▸ C.lease i
    | .inr (.inl i)=> mem_union_right _ (mem_biUnion.mpr ⟨x,hx,C.anchor x⟩)
    | .inr (.inr i)=> mem_union_right _ (mem_biUnion.mpr ⟨x,hx,C.anchor x⟩)
lemma ana : Roles (agency C) C.who (midland C):=⟨fun _=>rfl,fun _=>Iff.rfl,fun i=>rfl,fun i=>rfl,fun i=>i.1.property⟩
abbrev patchZ (i:BoxF n): Axe C:=⟨i,⟨∅,empty_subset _⟩⟩
def gazeA (U:Config G n)(p:Rain V G)(s:Finset V) := ∀ i∈s,C.guardP i U (p i)
-- ♥ movement estimates. Compose cubes at treks
structure AirC : Prop where
 gaze i : MeasurableSet {u: Config G n × G.El | C.guardP i u.1 u.2}
 bits i v : UsesFinal R.p.threshold (C.cap i) (fun U=>C.guardP i U v)
 propeller g U i v: C.guardP i (Lattice.gauge g U) (C.adjust g i *v)↔ C.guardP i U v
 start S : Measurable (uncurry (C.trek S))
 tiers S p : MeasurePreserving (C.trek S p) (prior G n) (prior G n)
 base p U : C.trek ∅ p U=U
 eyes S p U g: C.trek S (C.adjust g*p) (Lattice.gauge g U)=Lattice.gauge g (C.trek S p U)
 mask S U p : gazeA C U p S→ flags R.p.threshold (C.trek S p U)=flags R.p.threshold U
 drew S p q: (∀ i∈S,p i=q i) → C.trek S p=C.trek S q
 view S p (P:Support n) U : Agrees P (C.trek S p U) (C.trek (S∩deer C P) p U)
 face S p (P:Support n) (U V) : Agrees P U V→ Agrees P (C.trek S p U) (C.trek S p V)
 stitch i : UsesFinal R.p.threshold (C.path i) (C.long i)
 snow i : Envelope (C.long i)
 hike i : GaugeInvariant (C.long i)
 splits U : R.exponent U=C.short U + ∑ i,C.long i U
 -- combined on S of all picked markers
 sale i : Envelope (uncurry (C.marks i))
 heal i : Envelope (uncurry (C.high i))
 alignmet i : Envelope (uncurry (C.paint i))
 artist (g:Site n→G.El) U i v: C.paint i (Lattice.gauge g U) (C.adjust g (C.who i)*v)=C.paint i U v
 strokes i v : UsesFinal R.p.threshold (C.size i) (fun U=> C.paint i U v)
 pray S p U i : i∈S→ C.high i U (p i)=C.marks i (C.trek S p U) (p i)*(Real.exp (C.fee i U p):ℂ)
 direct S p U i : i∉S→ C.high i (C.trek S p U) (p i) = C.high i U (p i)
 delta S U p : gazeA C U p univ → C.short (C.trek S p U)=C.short U+∑ i∈S,C.fee i U p
 hale i U p : C.high i U p ≠0 → C.guardP i U p
 finishing i U (p:Rain V G) : C.high i U (p i)= cram C.who (fun j=> C.paint j U (p (C.who j))) i
local notation "T"=> Config G n
local notation "Y"=> freq V G
local notation "b!"=> Rain V G
def cortex (i:L)(U:T)(v:b!)(t:Finset V):ℝ:= C.long i (C.trek t v U)-C.long i U
def skin (p:Box n)(U:T)(v:b!)(t:Finset V): ℂ:= flore R p (C.trek t v U)
abbrev tame (i:PureC C)(U:T)(v:b!):= powder (cortex C i.1 U v) i.2.val
def loft (i:PureC C)(U:T)(v:b!):ℂ:= if gazeA C U v i.2.val then ↑(Real.exp (tame C i U v)-1) else 0
def rash (i:Axe C)(U:T)(v:b!):ℂ:= if gazeA C U v i.2.val then powder (skin C (midland C i) U v) i.2.val else 0
def lance : LandC C→ T→ b! →ℂ:= Sum.elim (fun i U v=>C.paint i U (v (C.who i))) (Sum.elim (loft C) (rash C))
end YM.Trace.Cask
