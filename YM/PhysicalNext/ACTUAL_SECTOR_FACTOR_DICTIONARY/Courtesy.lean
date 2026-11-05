import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Banners
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Episodes

/-! Exact check even on mixed inventories. No forbidden alternatives
simultaneously on a K address whether at root or on two components. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Formal
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace YM.PhysicalNext.Dictionary.Formal
open Wires Geo Notify Voice Voice.Check Voice.Defenses Parcel Shipment Lobbies SectorNext.Reconnect SectorNext.Reconnect.Words
open Finset hiding card
variable {G : Gauge} {c f : Side} {S : StepData c f} {I : Type} [DecidableEq I]
    (D : AnalyticBridge.LocalGaussian.Desk G S) (A : Stores S) (F : Forest S.ratio) (Z : Art I D) (i : Head I) (v : Versions i) (l : Tryouts S)
local notation "T"=>Voice.Check.Test
local notation "Q"=>submit i D A v l
local notation "P"=>shops i v l
local notation "Z₀"=>token D Z

lemma manifest_staged : Shipment.station (Q) = A := by unfold Shipment.station submit; simp
lemma storeworks (a : Bills S I) : suggest a∈(Q) ↔ a∈(P) := by unfold submit; simp only [Fleet.draft,suggest,Finset.inr_mem_disjSum]

omit [DecidableEq I] in
lemma bought (a : Bills S I) : a∈(P)↔match a with
    | .inl j=>j∈l.1
    | .inr (.inl q)=>q∈l.2
    | .inr (.inr (.inl (.inl j)))=>j∈coin i
    | .inr (.inr (.inl (.inr q)))=>q∈curtains i v
    | .inr (.inr (.inr q))=>q∈torn i := by
  rcases a with a|a|(a|a)|a <;> simp only [shops,Finset.inl_mem_disjSum,Finset.inr_mem_disjSum]<;> try rfl

omit [DecidableEq I] in
lemma emissions_at (x : Emit I) : x∈ emissions i ↔ match x with
    | .inl j=> j∈coin i
    | .inr (.inl j)=>j∈menu i
    | .inr (.inr j)=>j∈torn i := by
  rcases x with x|x|x <;> simp only [emissions,Finset.inl_mem_disjSum,Finset.inr_mem_disjSum]<;> try rfl

def registered (x : ↥(emissions i)) : Bill S I := suggest (match h:x.val with
  | .inl j=>Shipment.singleton j
  | .inr (.inl j)=> let hj : j∈menu i := by have hm := (emissions_at i _).mp x.property; rw [h] at hm; exact hm
                     
                     bead j (v ⟨j,hj⟩)
  | .inr (.inr j)=>qualify j.1 j.2)

lemma spent (x : ↥(emissions i)) : registered i v (S:=S) x∈(Q) ∧ burst D Z (registered i v x)=token D Z x.val := by
  rcases x with ⟨x,hx⟩; have h:=(emissions_at i _).mp hx
  rcases x with x|x|⟨j,n⟩ <;> unfold registered <;> dsimp
  all_goals refine ⟨(storeworks D A i v l _).mpr ((bought i v l _).mpr ?_),rfl⟩
  · exact h
  · exact (slides ..).mpr ⟨h,rfl⟩
  exact h

lemma indexed {x : Bill S I} (hx : x∈(Q)) (he : (burst D Z x).Nonempty) : x∈Set.range (registered i v) := by
  rcases x with x|x|x|x|(x|⟨x,b⟩)|⟨j,n⟩
  all_goals try exact (Finset.not_nonempty_empty he).elim
  all_goals have hi:=(bought i v l _).mp ((storeworks D A i v l _).mp hx)
  · exact ⟨⟨.inl x,(emissions_at i _).mpr hi⟩,rfl⟩
  · obtain ⟨hj,rfl⟩:=(slides i v).mp hi
    exact ⟨⟨.inr (.inl x),(emissions_at i _).mpr hj⟩,rfl⟩
  exact ⟨⟨.inr (.inr (j,n)),(emissions_at i _).mpr hi⟩,rfl⟩

omit [DecidableEq I] in
lemma direct : Injective (registered (S:=S) i v) := by
  -- easier cases.
  rintro ⟨x,hx⟩ ⟨y,hy⟩ hm
  rcases x with x|x|⟨j,n⟩ <;> rcases y with x'|x'|⟨j',n'⟩ <;> first| contradiction | skip
  all_goals apply Subtype.ext
  all_goals simp [registered,Shipment.singleton,bead,qualify,suggest] at hm ⊢ <;> first | exact hm | exact hm.1

-- In syntax and on pixel test, no appeals to how two numerically
-- qualifying factors might cancel.
def signal (m : Finset I) : Prop := (emissions i).biUnion (token D Z)=m ∧
    ((emissions i:Set (Emit I)).PairwiseDisjoint (token D Z))
lemma batteries (m : Finset I) : signal D Z i m ↔
    Shipment.signal D Z (Q)=m ∧ ((Q : Finset _):Set (Bill S I)).PairwiseDisjoint (burst D Z) := by
  have hu : Shipment.signal D Z (Q)=(emissions i).biUnion (Z₀) := by
    ext a; rw [Shipment.signal,Finset.mem_biUnion,Finset.mem_biUnion]; constructor
    · rintro ⟨j,hj,ha⟩; obtain ⟨x,rfl⟩:= indexed D A Z i v l hj ⟨a,ha⟩
      rw [(spent D A Z i v l x).2] at ha; exact ⟨x.val,x.property,ha⟩
    rintro ⟨j,hj,ha⟩; let u : ↥(emissions i):=⟨j,hj⟩
    exact ⟨registered i v u,(spent D A Z i v l u).1, (by rw [(spent D A Z i v l u).2]; exact ha)⟩
  rw [signal,hu]; apply and_congr_right
  intro _; constructor
  · intro h₁ a ha j hj hs
    by_contra! hk
    obtain ⟨x,hx,hy⟩:=Finset.not_disjoint_iff.mp hk
    obtain ⟨u,rfl⟩:= indexed D A Z i v l ha ⟨x,hx⟩
    obtain ⟨v', rfl⟩:=indexed D A Z i v l hj ⟨x,hy⟩
    change ¬Disjoint (burst D Z _) (burst D Z _) at hk
    rw [(spent D A Z i v l u).2,(spent D A Z i v l v').2] at hk
    exact hk (h₁ u.property v'.property (fun H=>hs (congr_arg (registered i v) (Subtype.ext H))))
  intro h₁ j hj a ha e
  let u:↥(emissions i):=⟨j,hj⟩; let w:↥(emissions i):=⟨a,ha⟩
  change Disjoint (Z₀ u.val) (Z₀ w.val)
  rw [← (spent D A Z i v l u).2, ←(spent D A Z i v l w).2]
  exact h₁ (show registered i v (S:=S) u∈(↑(Q) : Set (Bill S I)) from (spent D A Z i v l u).1)
    ((spent D A Z i v l w).1) ((direct (S:=S) i v).ne (mt (congr_arg Subtype.val) e))

omit [DecidableEq I] in
lemma choosing : (∀ j∈(P), election D Z F A (team i) j) ↔
    ((∀ j∈ l.1,trying D F A (team i) j) ∧ (∀ j∈l.2, offering D F A j)) ∧
    (∀ j∈menu i,(Z.names j).Nonempty) ∧ (∀ j∈torn i, j.1∈team i ∧ (Z.sig j.1 j.2).Nonempty) := by
  constructor
  · intro h
    refine ⟨⟨fun j hj=> h (supplement j) ((bought i v l _).mpr hj),fun j hj=>?_⟩, fun j hj=>h (bead j (v ⟨j,hj⟩)) ((bought i v l _).mpr
      ((slides i v).mpr ⟨hj,rfl⟩)),?_⟩
    · cases j; exact h (.inr (.inl _)) ((bought ..).mpr hj)
    rintro ⟨j,n⟩ hj; exact h (qualify j n) ((bought ..).mpr hj)
  rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩ j hj
  have he := (bought i v l _).mp hj
  rcases j with j|⟨j,b⟩|(j|⟨j,b⟩)|⟨j,n⟩
  · exact h₁ _ he
  · exact h₂ _ he
  · trivial
  · obtain ⟨ht,_⟩ := (slides i v).mp he; exact h₃ _ ht
  exact h₄ _ he

omit [DecidableEq I] in
lemma authorize : Fleet.pure question (P) ↔ Fleet.pure Prod.fst l.2 ∧ Fleet.pure Prod.fst (torn i) := by
  constructor
  · intro h
    constructor
    · intro j hj x hx ht; have he := h (.inr (.inl j)) ((bought ..).mpr hj) (.inr (.inl x)) ((bought ..).mpr hx) (show _ = _ by simp [question,ht])
      simpa using he
    intro j hj x hx ht; have he := h (.inr (.inr (.inr j))) ((bought ..).mpr hj) (.inr (.inr (.inr x))) ((bought ..).mpr hx)
      (show _=_ by simp [question,ht]); simpa using he
  rintro ⟨h₁,h₂⟩ x hx y hy he
  have ht:=(bought i v l _).mp hx; have hu:=(bought i v l _).mp hy
  rcases x with x|x|(x|x)|x <;> rcases y with y|y|(y|y)|y <;> first | contradiction | skip
  all_goals simp only [question, reduceCtorEq, Sum.inl.injEq,Sum.inr.injEq] at he ⊢
  all_goals first| exact he| exact he.elim | exact h₁ _ ht _ hu he| exact h₂ _ ht _ hu he| exact one_arrow i v _ ht _ hu he

-- exactly the mode/marker requirements on the given K labels.
def welcomes (m : Finset I) : Prop := signal D Z i m ∧ Fleet.origins D.labels A (team i) ∧
    Fleet.pure Prod.fst (torn i) ∧
    (∀ j∈menu i,(Z.names j).Nonempty) ∧ ∀ j∈torn i,j.1∈team i ∧ (Z.sig j.1 j.2).Nonempty

def progress : Prop := Fleet.pure Prod.fst l.2 ∧ (∀ j∈l.1, trying D F A (team i) j) ∧ (∀ j∈l.2,offering D F A j)

theorem listed (m : Finset I) : prints D Z F A m (Q) ↔ welcomes D A Z i m ∧ progress D A F i l := by
  have he := choosing D A F Z i v l
  have hp := authorize i v l
  have ht := Fleet.draft_perm (g:=hump (radiusB D.betaHat)) (A:=A) («T» :=D.labels) (b:=team i) (parent:=question) (t:=P)
  have hx := batteries D A Z i v l m
  have hq := manifest_staged D A i v l
  have hk : Fleet.kSet (Q)=team i := Fleet.draft_k ..
  constructor
  · rintro ⟨_,h0,h⟩
    obtain ⟨h1,h2⟩:=ht.mp (show permits (Fleet.required S D.labels _ question) (Q) from fun j hj=>(h j hj).1)
    have he1 : ∀ j∈(P), election D Z F A (team i) j := by
      intro j hj; rw [← hk] -- A via hq
      have hr:=(show election D Z F (Shipment.station (Q)) (Fleet.kSet (Q)) j from (h (suggest j) ((storeworks D A i v l j).mpr hj)).2.1); rwa [hq] at hr
    obtain ⟨hf,h'⟩:=he.mp he1
    exact ⟨⟨hx.mpr ⟨h0,fun j hj q hh hs =>(h j hj).2.2 q hh hs.symm⟩,h1,(hp.mp h2).2,h'⟩,(hp.mp h2).1,hf⟩
  rintro ⟨⟨h1,H,H0,H1⟩,e0,e1⟩
  obtain ⟨hM,hC⟩:=hx.mp h1
  refine ⟨hq,hM,fun j hj=>⟨(show permits (Fleet.required S D.labels _ question) _ from ht.mpr ⟨H,hp.mpr ⟨e0,H0⟩⟩) _ hj,?_,
    fun q hh hq=> hC (show j∈(↑(Q):Set (Bill S I)) from hj) (show q∈(↑(Q):Set _) from hh) hq.symm⟩⟩
  rcases j with j|j|j
  · trivial
  · trivial
  change election D Z F _ _ _; rw [hk,hq]
  exact he.mpr ⟨e1,H1⟩ j ((storeworks D A i v l j).mp hj)
end YM.PhysicalNext.Dictionary.Formal
