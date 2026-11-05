import YM.EveryPhase.SurjectiveHelpers
import YM.EveryPhase.Hot

/-!
# No missing directions in the boundary isometry
-/
set_option autoImplicit false
noncomputable section

namespace YM.EveryPhase
-- EUCLIDEAN READING OF `shot`. Reuse the argument from C22
-- (`fromRef` through `euclideanRef`; `euclideanShot` and `ample_room`).
section pureShot
open Function Set Filter Complex
open Mink Boundary OS Word
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff

variable {G : Gauge} {L : Register G} {n m : ℕ} {S T : Table L} {V : Chamber T timeAxis}

-- Shot or intermediate train with preceding reference Z,X of padding q
private def fromRef (B : Small S V) (p q : ℝ≥0) :
    ∀ {n}, Times n → SpacePoints n → (Fin n → S.Union) → ℂ → Space3 → V.H
  | 0,_,_,_,_,_ => V.omega
  | n+1,z,x,v,Z,X =>
      Small.rip (z 0-Z) (q+p) (x 0-X) ((B.bar p (v 0)) (B.trainB p n (Fin.tail z)
        (Fin.tail x) (Fin.tail v) (z 0) (x 0)))

private lemma fromTrain (B : Small S V) (p : ℝ≥0) (z : Times n) (x : SpacePoints n)
    (v : Fin n → S.Union) (Z : ℂ) (X : Space3) :
    B.trainB p n z x v Z X = fromRef B p p z x v Z X := by
  cases n <;> simp only [fromRef,Small.trainB]

private lemma fromPoint (B : Small S V) (p : ℝ≥0) (v : Fin n → S.Union) (y : Heights n) (k : Points n) :
    B.shot p n v y k = fromRef B p 0 (shift k y) (trace k) v 0 0 := by
  cases n <;> simp only [Small.shot,fromRef,zero_add,sub_zero]

private lemma nextRef (B : Small S V) (p q : ℝ≥0) (z : Times (n+1)) (x : SpacePoints (n+1))
    (v : Fin (n+1) → S.Union) (Z : ℂ) (X : Space3) :
    fromRef B p q z x v Z X = Small.rip (z 0-Z) (q+p) (x 0-X) ((B.bar p (v 0))
      (fromRef B p p (Fin.tail z) (Fin.tail x) (Fin.tail v) (z 0) (x 0))) := by
  rw [← fromTrain]; rfl

-- Hypotheses actually needed on imaginary coordinates in fromRef.
private def Room (p q : ℝ≥0) (y : Heights n) (Y : ℝ) : Prop :=
    (∀ i, ↑(q+p) < y i - Y) ∧ (∀ i j : Fin n, i < j → ↑(p+p) < y j - y i)

private lemma tailRoom {p q : ℝ≥0} {y : Heights (n+1)} {Y : ℝ} (h : Room p q y Y) :
    Room p p (Fin.tail y) (y 0) := ⟨fun i => h.2 0 i.succ (Fin.succ_pos i),
      fun i j hij => h.2 i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩

private def pinned (e : S.Tag) := S.pin e.1 e.2
private def raw (e : S.Tag) : L.Token := ⟨e.1,S.representative e.1 e.2⟩
private def iz (y : ℝ) : ℂ := ↑y*I

private lemma oneSlab (e : L.Token) {p : ℝ≥0} (hp : 0<p) :
    Slab timeAxis (p+p) [(position 0 p,e)] := by
  have hh : YM.time (position 0 p) = p := by simp
  refine ⟨add_pos hp hp, ⟨locations.mpr (by simp),?_⟩,?_⟩
  · intro i hi; obtain rfl := List.mem_singleton.mp hi
    rw [show (position _ _ : E4) timeAxis = _ from hh]
    exact hp
  intro i hi; obtain rfl := List.mem_singleton.mp hi
  rw [show (position _ _ : E4) timeAxis = _ from hh]; simp [hp]

private lemma euclideanRef {B : Small S V} {A : Spread V}
    (link : B.concretized A) {p : ℝ≥0} (hp : 0<p)
    (q : ℝ≥0) (y : Heights n) (x : SpacePoints n) (v : Fin n → S.Tag) (Y : ℝ) (X : Space3)
    (h : Room p q y Y) :
    ∃ b : Future L timeAxis,
      b.val = List.ofFn (fun i => (position (x i-X) (y i-Y-(q:ℝ)),raw (v i))) ∧
        fromRef B p q (iz ∘ y) x (pinned ∘ v) (iz Y) X = V.GNS.plant b := by
  induction n generalizing q Y X with
  | zero => exact ⟨air timeAxis,List.ofFn_zero.symm,rfl⟩
  | succ n ih =>
    obtain ⟨b,hb,hplant⟩ := ih p (Fin.tail y) (Fin.tail x) (Fin.tail v) _ (x 0) (tailRoom h)
    let r := (y 0 - Y - ↑(q+p)).toNNReal
    have hg : 0 < y 0 - Y - ↑(q+p) := sub_pos.mpr (h.1 0)
    have hr : 0<r := Real.toNNReal_pos.mpr hg
    have hco : (r:ℝ) = y 0 - Y - ↑(q+p) := Real.coe_toNNReal _ hg.le
    let w := entering (oneSlab (raw (v 0)) hp) b
    let s := Small.bufferF (x 0-X)
    refine ⟨travel (over w s) r, ?_, ?_⟩
    · dsimp only [travel,over,w,s,Small.bufferF,entering,linked,raised]
      rw [hb]; simp only [carry,List.singleton_append,List.map_cons,List.map_ofFn]
      rw [List.ofFn_succ]
      congr 1
      · refine Prod.ext (ext_by ?_ ?_) rfl
        · simp
        simp [hco]; ring
      apply congr_arg List.ofFn
      funext i; refine Prod.ext (ext_by ?_ ?_) rfl
      · simp [Fin.tail]
      simp [Fin.tail,hco]; ring
    rw [nextRef]
    have hI : Small.interval (iz (y 0)-iz Y) (q+p) = OS.Semigroup.duration r := by
      apply Complex.ext <;> simp [Small.interval,iz,hco,OS.Semigroup.duration]
    have he : B.bar p (pinned (v 0)) = A.place (p+p) [(position 0 p,raw (v 0))] :=
      link (v 0).1 (v 0).2 p hp
    change V.flow.F (Small.interval (iz (y 0) - iz Y) (q+p)) (V.flow.U s
      ((B.bar p (pinned (v 0))) (fromRef B p p (iz ∘ Fin.tail y) (Fin.tail x) _ (iz (y 0)) (x 0)))) = _
    rw [show Fin.tail (pinned ∘ v) = pinned ∘ Fin.tail v from rfl, hplant,hI,V.flow.roots_heat hr,he]
    rw [A.reads (oneSlab (raw (v 0)) hp) b,← V.across,← V.atBirth]

private lemma euclideanShot {B : Small S V} {A : Spread V}
    (link : B.concretized A) {p : ℝ≥0} (hp : 0<p)
    (y : Heights n) (x : SpacePoints n) (v : Fin n → S.Tag)
    (h : Room p 0 y 0) :
    ∃ b : Future L timeAxis,
      b.val = List.ofFn (fun i => (position (x i) (y i),raw (v i))) ∧
        fromRef B p 0 (iz ∘ y) x (pinned ∘ v) 0 0 = V.GNS.plant b := by
  simpa only [iz,NNReal.coe_zero, Complex.ofReal_zero,zero_mul,sub_zero] using
    euclideanRef link hp 0 y x v 0 0 h

private lemma ample_room {p : ℝ≥0} {y : Heights n} (h : Small.ample p y) : Room p 0 y 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [zero_add,sub_zero]; linarith [h.2 i,p.coe_nonneg]
  rw [NNReal.coe_add]; linarith [h.1.2.2 i j hij,p.coe_nonneg]

lemma bright_shot {B : Boundary.Small S V} {A : Spread V} (he : B.concretized A) {p : ℝ≥0}
    (x : SpacePoints n) (v : Fin n → S.Tag) (y : Heights n) (hp : Boundary.Small.ample p y) :
    ∃ b : Future L timeAxis,
      b.val = Word.realize (fun i => ⟨(v i).1,S.representative _ (v i).2⟩) (place x y) ∧
        V.GNS.plant b=B.shot p n (fun i => S.pin (v i).1 (v i).2) y (place x 0) := by
  obtain ⟨b,hb,H⟩ := euclideanShot he hp.1.1 y x v (ample_room hp)
  refine ⟨b,hb,?_⟩
  rw [fromPoint, show shift (place x 0) y=iz ∘ y by funext; simp [iz,shift,place],
    show Boundary.trace (place x 0)=x by funext; simp [Boundary.trace,place]]
  exact H.symm
end pureShot

open Function Set Filter MeasureTheory Spec Boundary OS Org Word Table.Pairing Next.BOUNDARY
open scoped Topology NNReal ContDiff InnerProductSpace
variable {G : Gauge} {C : Family G} {S T : Table C.book} {V : Chamber T timeAxis}
    {A : Spread V} {Y : Show.Rhythm (C:=C) S V A} {X : Wightman S}
    {J : X.operators.H →L[ℂ] V.H} {R : Algebra S} {W : Surface S}
    {n : ℕ}

private lemma plant_ext {b c : Future C.book timeAxis} (he : ∀ v : Future C.book timeAxis,
    T.gram timeAxis v.val b.val=T.gram timeAxis v.val c.val) : V.GNS.plant b=V.GNS.plant c := by
  apply V.GNS.whole.eq_of_inner_right ℂ
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single i c => simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left,
      V.GNS.measure, he]

private lemma same_plant (ht : T.Symmetric) (hr : T.respects S) (x : Points n) (h : single x timeAxis)
    (v w : Fin n → C.book.Token) (hv : S.classTokens ∘ v=S.classTokens ∘ w) :
    V.GNS.plant ⟨Word.realize v x,living v h⟩=V.GNS.plant ⟨Word.realize w x,living w h⟩ := by
  apply plant_ext; intro u
  obtain ⟨m,d,⟨p,f⟩,rfl⟩ := Work.B14.addresses u
  simp only [Work.B14.mkFuture, Table.Pairing.displacement T ht _ _ p.property h,
    ← S.at_project T ht hr (spans p.property h)]
  apply congrArg (S.useAt T _)
  funext i; refine Fin.addCases ?_ ?_ i
  · intro i; simp [tied]
  intro i; simpa [tied] using congrFun hv i

lemma ordered_covered (H : Attachment X V J) (h : Show.Reveals R X.spin X.J Y W)
    (hs : T.Symmetric) (hr : T.respects S) (ht : Bid.Hull Y.bits Y.lift X.J)
    (hi : Y.lift.NonTangentialFree W) (x : Points n)
    (v : Fin n → C.book.Token) (hp : single x timeAxis) (he : StrictMono (fun i => YM.time (x i))) :
    V.GNS.plant ⟨Word.realize v x,living v hp⟩ ∈ J.range := by
  let y i := YM.time (x i)
  let a := trace x
  have hh : place a y=x := by ext1; simp [place,y,a,trace]
  let w i := S.classTokens (v i)
  let u (i : Fin n) : C.book.Token := ⟨(w i).1,S.representative _ (w i).2⟩
  have hA : S.classTokens ∘ v=S.classTokens ∘ u := by
    funext i; change w i=⟨(w i).1,S.project _ (S.representative _ _)⟩; rw [S.rep]
  obtain ⟨p, hP⟩ := margins_exists (show y∈positiveHeight n from ⟨he,hp.2⟩)
  obtain ⟨b,hb,hB⟩ := bright_shot Y.linked a w y hP.2
  have heq : (⟨Word.realize u x,living u hp⟩ : Future C.book timeAxis)=b := Subtype.ext (by rw [hb,hh])
  rw [same_plant hs hr x hp _ _ hA, heq,hB]
  exact shot_in H h ht hi _ (p,y) hP _

lemma onto (H : Attachment X V J) (h : Show.Reveals R X.spin X.J Y W)
    (hs : T.Symmetric) (hp : T.Smooth) (hr : T.respects S) (ht : Bid.Hull Y.bits Y.lift X.J)
    (hi : Y.lift.NonTangentialFree W) : Surjective J := by
  have covered (b : Future C.book timeAxis) : V.GNS.plant b∈ J.range := by
    obtain ⟨n,d,⟨p,f⟩,rfl⟩ := Work.B14.addresses b
    let y (i : Fin n) := YM.time (p.val i)
    let l : Equiv.Perm (Fin n) := Tuple.sort y
    let k := Points.rearrange l p.val
    let t : Work.B14.Address C.book timeAxis (d ∘ l) :=
      (⟨k,Points.rearrange_in l p.property.1,fun i => p.property.2 _⟩,fun i => f (l i))
    have he : List.Perm (Work.B14.mkFuture _ t).val (Work.B14.mkFuture d (p,f)).val :=
      l.ofFn_comp_perm fun i => ((p.val i), (⟨d i,f i⟩ : C.book.Token))
    have hh : V.GNS.plant (Work.B14.mkFuture d (p,f))=V.GNS.plant (Work.B14.mkFuture _ t) :=
      plant_ext fun q => Table.order T hs (twoSides q.property (Work.B14.mkFuture _ t).property)
        (he.append_left _)
    rw [hh]
    let r i := YM.time (k i)
    have hK : Monotone r := Tuple.monotone_sort y
    let g (e : ℝ≥0) := place (trace k) (r+(e:ℝ) • rate n)
    have hm u i : YM.time (g u i)=(r+(u:ℝ) • rate n) i := by simp only [g,place,points_apply,time_position]
    have hG (u : ℝ≥0) (hx : 0<u) : StrictMono (fun i => YM.time (g u i)) := by
      simp_rw [hm]; exact dawns (show r∈sunrise n from hK) (show 0<(u:ℝ) from hx)
    have hg : g 0=k := by ext1; simp [g,place,trace,r]
    have hl (u : ℝ≥0) : single (g u) timeAxis := by
      rcases u.coe_nonneg.eq_or_lt with hu|hu
      · have he : u=0 := Subtype.ext hu.symm
        rw [he,hg]; exact t.1.2
      refine ⟨fun i j hq => (hG u hu).injective (congrArg YM.time hq), fun i => ?_⟩
      change 0 < YM.time (g u i)
      rw [hm]
      change 0 < r i+(u:ℝ)*(i.val:ℝ)
      exact add_pos_of_pos_of_nonneg (p.property.2 _) (by positivity)
    let F (u : ℝ≥0) : Work.B14.Address C.book timeAxis (d ∘ l) := (⟨g u, hl u⟩,t.2)
    have hx : Continuous F := by
      have he : Continuous g := by unfold g place points position; fun_prop
      exact (he.subtype_mk _).prodMk continuous_const
    have hf : F 0=t := Prod.ext (Subtype.ext hg) rfl
    rw [← hf]
    apply (rangeClosed H).mem_of_tendsto ((((Work.B14.plant_cont V.GNS hs hp (d ∘ l)).comp hx).tendsto (0:ℝ≥0)).mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with i hI
    exact ordered_covered H h hs hr ht hi _ (fun j => ⟨(d ∘ l) j,t.2 j⟩) (hl i) (hG i hI)
  have he : Submodule.span ℂ (Set.range V.GNS.plant) ≤ J.range :=
    Submodule.span_le.mpr (by rintro _ ⟨y,rfl⟩; exact covered y)
  intro v
  have hp : Dense (J.range : Set V.H) := V.GNS.dense.mono he
  exact closure_minimal (Subset.refl (J.range : Set V.H)) (rangeClosed H) (hp v)
end YM.EveryPhase
