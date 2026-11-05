import YM.UVExtension.Strata.Chain
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Life
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Fluent
-- Syntactic! run the same Berry/Multiple assignment. no opacity quotient within chains.
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain
variable {R R' : Rep G f}{T T': Tube G S} {H:Cash w s q L Q U C T R} {J:Cash w s q L Q U C T' R'}
namespace Badge
abbrev Cold (u : Molecule S→ Support c) := {p: Molecule S// (u p).Nonempty ∧ (roster p).flags=∅}
abbrev Hot (u:Molecule S→ Support c):={p:Molecule S// (u p).Nonempty∧ (roster p).flags.Nonempty}

section Bare
variable (u z:Molecule S→Support c)(h:u=z)
def dahlia : Cold u≃ Cold z:= Equiv.subtypeEquiv (Equiv.refl _) (by intro i; subst_vars; rfl)
def dried : Hot u≃Hot z:= Equiv.subtypeEquiv (Equiv.refl _) (by intro i; subst_vars; rfl)
abbrev grass := batches (dahlia u z h)
def tongs := Equiv.sumCongr (dried u z h) (grass u z h)
def leaf := scrolls (tongs u z h)
lemma dahlia_self (x: Cold u): dahlia u u rfl x=x:= rfl
lemma grass_self (x): grass u u rfl x=x:= rfl
lemma tong_self (x): tongs u u rfl x=x :=by cases x <;> rfl
lemma leaf_self (x): leaf u u rfl x=x:=by
    unfold leaf; rw [show tongs u u rfl=Equiv.refl _ from Equiv.ext (tong_self u)]
    let U:=Equiv.refl (Hot u ⊕ Clusters (Cold u)); change scrolls U x=x; exact (scrolls U).injective (Yearling.scrolls_trans U U x)
abbrev Pool := Reps (Hot u⊕ Clusters (Cold u))
def direct (X: Molecule S→ Support c):Hot X→Support c:= fun i=> X i.val
def indirect (X: Molecule S→ Support c):Cold X→Support c:= fun i=> X i.val
def citizen (x:Pool u):= x.1.toLeft.biUnion fun i=> (roster i.val).flags
def books := OmitClusters.test (indirect u) (direct u)
def chap (x:Pool u):= Letter.staysOne x ∧ Gas.separated (blocked (direct u)) x.1.toLeft ∧ ∀ i∈x.1.toRight, ¬Disjoint (x.1.toLeft.biUnion (direct u)) (books u (.inr i))
lemma floes (x:Pool u): (leaf u z h x).1.biUnion (books z)=x.1.biUnion (books u)∧ citizen z (leaf u z h x)=citizen u x∧ (Ac.Spark (books u) x.1 ↔ Ac.Spark (books z) (leaf u z h x).1)∧ (chap u x ↔ chap z (leaf u z h x)):=by subst z; rw [leaf_self]; exact ⟨rfl,rfl,Iff.rfl,Iff.rfl⟩
lemma indirects (p:Clusters (Cold u)): unionOf (indirect z) (grass u z h p).2=unionOf (indirect u) p.2:=by subst z; rw [grass_self]
lemma honors (p q: Cold u): blocked (indirect u) p q ↔ blocked (indirect z) (dahlia u z h p) (dahlia u z h q):=by subst z; exact Iff.rfl
lemma anchored (p:Clusters (Cold u))(he:(unionOf (indirect z) (grass u z h p).2).Nonempty)(hp:(unionOf (indirect u) p.2).Nonempty) : (⟨Classical.choose hp,unionOf (indirect u) p.2,hp.choose_spec⟩ : RegularAddress c)= ⟨Classical.choose he,unionOf (indirect z) (grass u z h p).2,he.choose_spec⟩:=by subst z; rfl
end Bare
open Song AnalyticBridge VerifiedReset Extra.Iteration
section brand
variable (hp : H.unionP=J.unionP)
def beamv := Equiv.prodCongr (Equiv.refl (Seat c)) (Equiv.sumCongr (grass _ _ hp) (Equiv.refl (Songbook c)))
include hp
-- joins All Bare on H topology
lemma perfed (x:H.fragrances) : perf J (grass _ _ hp x)=perf H x:= indirects _ _ hp x
lemma co (v w:H.ThinP): H.seam v w ↔ J.seam (dahlia _ _ hp v) (dahlia _ _ hp w):=honors _ _ hp v w
lemma costants (x:H.fragrances): coefficient H.seam x.2=coefficient J.seam (grass _ _ hp x).2:= weighs (dahlia _ _ hp) (co hp) x
lemma plateV (p:ℕ)(hr:R.activities.reg=R'.activities.reg): Brim.plate H p=Brim.plate J p:=by unfold Brim.plate; rw [hr] -- Anchor ignored by Dash? no
lemma kings (z:H.fragrances): locate H z=locate J (grass _ _ hp z):= anchored _ _ hp z (crest J _) (crest H z)
omit hp in
private lemma extendsM {ι κ η Y:Type} (E:ι≃κ) (A:η→ι) (B:η→κ)(h:Injective A)(u:Injective B)(hh:∀ i, E (A i)= B i) (f g:η→ Y) (hw:∀ i,f i=g i)(M : ι→Y)(N:κ→ Y)(hp:∀ i,M i=N (E i)) (x:ι): Function.extend A f M x= Function.extend B g N (E x):=by
    by_cases hx:x ∈ Set.range A
    · obtain ⟨i,rfl⟩:=hx; rw [hh,h.extend_apply,u.extend_apply]; exact hw _
    rw [extend_apply' _ _ _ hx,extend_apply']; exact hp _
    rintro ⟨j,hj⟩; exact hx ⟨_,E.injective ((hh j).trans hj)⟩
lemma dashboard (x:H.fragrances)(hr:R.activities.reg=R'.activities.reg): Beam.dashboard H x=Beam.dashboard J (grass _ _ hp x):=by
    have :Nonempty (RegularAddress c):= ⟨locate H x⟩
    exact extendsM (grass H.unionP J.unionP hp) (Brim.icon H) (Brim.icon J) (Beam.icon_inj ..) (Beam.icon_inj J) (fun i=>rfl) _ _ (fun i=> plateV hp i hr) (locate H) (locate J) (kings hp) x
lemma panels (x:H.Chainbook):
      J.library (leaf _ _ hp x)=H.library x ∧ J.inventory (leaf _ _ hp x).1.toLeft=H.inventory x.1.toLeft∧ (Ac.Spark H.bookFoot x.1 ↔ Ac.Spark J.bookFoot (leaf _ _ hp x).1) ∧ (H.Fresh x ↔ J.Fresh (leaf _ _ hp x)) :=floes _ _ hp x

-- enumeration ignores unused cash fields; pack counts Props.
lemma birthday (i:ℕ): Song.pennant J i= beamv hp (Song.pennant H i):=by
    suffices h: ∀ (u z:Molecule S→Support c) (h:u=z) [Countable (Seat c × ((Clusters (Cold u)) ⊕ Songbook c))][Countable (Seat c × (Clusters (Cold z) ⊕ Songbook c))][Infinite (Seat c× (Clusters (Cold u) ⊕ Songbook c))][Infinite (Seat c× (Clusters (Cold z) ⊕ Songbook c))], numbering (Seat c×(Clusters (Cold z) ⊕ Songbook c)) i=(Equiv.prodCongr (Equiv.refl _) (Equiv.sumCongr (grass u z h) (Equiv.refl (Songbook c)))) (numbering _ i) from h H.unionP J.unionP hp
    intro u z h; subst z; intro _ _ _ _; generalize hx: numbering (Seat c × ((Clusters (Cold u)) ⊕ Songbook c)) i=y; rcases y with ⟨_,A|A⟩<;> rfl

def leafO := Equiv.subtypeEquiv (leaf _ _ hp) (p:=fun z: H.Chainbook=> (H.inventory z.1.toLeft).Nonempty) (q:=fun z: J.Chainbook=> (J.inventory z.1.toLeft).Nonempty) (fun i=>by rw [(panels hp i).2.1])
def numa:= Equiv.sumCongr (leafO hp) (Equiv.refl (Blank (c:=c)))
def stocks (u:Molecule S→Support c)(i:Pool u): Prop:= (citizen u i).Nonempty
-- BARE leaf. get support from host; anklet proof abstract carried.
def lect (G:Gauge)(u:Molecule S→Support c)(h:∀ (i:Subtype (stocks u)), citizen u i.val ⊆ i.val.1.biUnion (books u)) : Subtype (stocks u)⊕Blank (c:=c)→ForcedAddress G c:= Sum.elim (fun i=>⟨_,_,show (citizen u i.val).Nonempty from i.2,h i,fun _=>True⟩) (fun i=>⟨{i.2},{i.2},singleton_nonempty _,Finset.Subset.refl _,fun _=>False⟩)
omit hp in
lemma sermon (u z:Molecule S→Support c)(h:u=z)(i)(he:∀ i,stocks u i ↔ stocks z (leaf u z h i))(U V): lect G z U (Equiv.sumCongr (Equiv.subtypeEquiv (leaf u z h) he) (Equiv.refl (Blank (c:=c))) i)=lect G u V i:=by
    subst z; rcases i with i|i
    · refine congr_arg _ (congr_arg Sum.inl (?_ : (Equiv.subtypeEquiv (leaf u u rfl) he i)=i)); exact Subtype.ext (leaf_self u i.val)
    rfl
lemma addrZ (i:Annual H): Refrain.reserve J (numa hp i)= Refrain.reserve H i:= sermon _ _ hp i (fun i=> (show _ from Eq.to_iff (congr_arg Finset.Nonempty ((panels hp i).2.1).symm))) (fun i=> J.shelf i.val) (fun i=> H.shelf i.val)
omit hp in
private lemma stripeJ (u z:Molecule S→Support c)(h:u=z) [Countable (Subtype (stocks u) ⊕ Blank (c:=c))][Countable (Subtype (stocks z) ⊕ Blank (c:=c))][Infinite (Subtype (stocks u)⊕Blank (c:=c))][Infinite (Subtype (stocks z)⊕Blank (c:=c))] (i:ℕ) (he:∀ i,stocks u i ↔ stocks z (leaf u z h i)): numbering (Subtype (stocks z)⊕Blank (c:=c)) i=(Equiv.sumCongr (Equiv.subtypeEquiv (leaf u z h) he) (Equiv.refl (Blank (c:=c)))) (numbering (Subtype (stocks u)⊕Blank (c:=c)) i):= by
    subst z; generalize hx:numbering (Subtype (stocks u)⊕Blank (c:=c)) i=y; rcases y with p|q; change Sum.inl _= Sum.inl _; apply congr_arg Sum.inl; apply Subtype.ext; exact (leaf_self u p.val).symm
    rfl
lemma seats (i:ℕ): Refrain.badge J i=numa hp (Refrain.badge H i):=stripeJ _ _ hp i (fun i=>show (H.inventory i.1.toLeft).Nonempty ↔ (J.inventory (leaf _ _ hp i).1.toLeft).Nonempty from by rw [(panels hp i).2.1]) -- omit hp stripe includes

-- Exact self lanes. Body independence use y. Choose all H=J in soup evaluation, Item currently oracle X ≠ H but shapeP .sameArts argument changes base H to J before comparison. enough.
end brand
end Badge
end YM.UVExtension.Wren
