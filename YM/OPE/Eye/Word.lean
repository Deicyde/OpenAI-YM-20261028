import YM.Euclid.Words
import YM.Ground.Moments

/-!
# Named finite labelled configurations

We use the same actual table throughout (including the junk off conf;
no estimate cites those unphysical values). On Conf ordering of the
finite naming scheme is irrelevant. This API facilitates re-indexing,
overwriting cluster names etc. at continuum passage and at tree
level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open MeasureTheory Function Filter Set Word Table Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{L:Register G}{V I J:Type*}[Fintype I][Fintype J][Fintype V]
variable (S : Table L)

def runNames (I:Type*) [Fintype I] := (Fintype.equivFin I).symm

def worded (x:I→E4) (v:I→ L.Token) : L.Word := realize (v ∘ runNames I) (points (x ∘ runNames I))
def observe (x:I→E4)(v:I→ L.Token) : ℂ := S.expect (worded x v)
lemma runs_conf {x:I→E4} : points (x ∘ runNames I)∈ conf _ ↔ Injective x:=
    ⟨fun h=>by
      intro i j hij; obtain ⟨a,rfl⟩:=(runNames I).surjective i; obtain ⟨b,rfl⟩:=(runNames I).surjective j; exact congr_arg (runNames I) ((show Injective (x ∘ (runNames I)) from h) hij), fun h=>h.comp (runNames I).injective⟩
lemma worded_distinct {x:I→E4}(v:I→ L.Token) : distinct (worded x v) ↔ Injective x:=(realized ..).trans runs_conf
lemma worded_get (x:I→E4)(v:I→L.Token)(a:L.Plant) : a∈ worded x v ↔ ∃ i,a=(x i,v i):=by
    rw [worded,realize,List.mem_ofFn]; constructor
    · rintro ⟨i,rfl⟩; exact ⟨_,rfl⟩
    rintro ⟨i,rfl⟩; obtain ⟨u,rfl⟩:= (runNames I).surjective i; exact ⟨u,rfl⟩
lemma worded_nodup {x:I→ E4}(v:I→ L.Token)(hx:Injective x) : List.Nodup (worded x v):= List.nodup_iff_injective_get.mpr (plantInj ((worded_distinct v).2 hx))
lemma worded_perm (e:I≃J){x:J→E4}(v:J→L.Token)(h:Injective x): List.Perm (worded (x ∘ e) (v ∘ e)) (worded x v):=
    (List.perm_ext_iff_of_nodup (worded_nodup _ (h.comp e.injective)) (worded_nodup _ h)).2 (by
      intro a; rw [worded_get,worded_get]; constructor
      · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
      rintro ⟨j,hj⟩; obtain ⟨i,rfl⟩:= e.surjective j; exact ⟨i,hj⟩)
lemma perm_observe (h:S.Symmetric) (e:I≃J){x:J→E4}(v:J→L.Token)(hp:Injective x) : observe S (x ∘ e) (v ∘ e)=observe S x v:= S.order h ((worded_distinct ..).2 hp) ((worded_perm e v hp).symm)
lemma observe_carry (h:S.Homogeneous){x:I→E4}(v:I→ L.Token)(hp:Injective x) (a:E4):observe S (fun i=> x i + a) v = observe S x v:=by
    unfold observe worded; rw [S.readAt,S.readAt]; exact h _ _ (runs_conf.mpr hp) a _
lemma card_zero_eq [IsEmpty I] (h:S.Basic) (v:I→L.Token) (x:I→E4) : observe S x v=1:=by
    unfold observe worded; rw [S.readAt]; have hx:Fintype.card I=0:= Fintype.card_eq_zero
    apply (fun (n:ℕ)(hX:n=0)(x:Points n)(v:Fin n→L.Token)=> (show S.read x v=1 by subst n; exact h.trivial ..)) _ hx
lemma named_fin {n : ℕ}(h:S.Symmetric) {x:Points n}(v:Fin n → L.Token)(he:x∈conf n): observe S x.ofLp v=S.read x v:=by
    rw [observe,← S.readAt v]
    refine S.order h ((Word.realized ..).2 he) ((List.perm_ext_iff_of_nodup (List.nodup_iff_injective_get.mpr (plantInj ((Word.realized ..).2 he))) (worded_nodup _ he)).2 ?_)
    intro a; rw [worded_get,realize,List.mem_ofFn]; exact exists_congr fun i=>eq_comm
lemma named_real {w:L.Word}(h:S.Symmetric)(hx:Word.distinct w): observe S (Word.positions w).ofLp (Word.tokens w)=S.expect w:= named_fin S h _ hx

section
variable {Y : Type*}
def beside (x:I→Y) (y:J→Y) : I⊕J → Y := Sum.elim x y
@[simp] lemma beside_left (x:I→Y)(y:J→Y)(i) : beside x y (.inl i)=x i:=rfl
@[simp] lemma beside_right (x:I→Y)(y:J→Y)(i) : beside x y (.inr i)=y i:=rfl
lemma beside_commutes {Z:Type*} (x:I→Y)(y:J→Y)(f:Y→ Z): f ∘ beside x y=beside (f ∘ x) (f ∘ y):= funext fun i=> by cases i<;>rfl
lemma beside_distinct {x:I→Y}{y:J→Y} : Injective (beside x y) ↔ (Injective x ∧ Injective y ∧ ∀ (i:I)(j:J),x i≠y j):=by
    constructor
    · intro h; exact ⟨fun i j H=> Sum.inl.inj (h (show beside x y (.inl i)=beside x y (.inl j) from H)),fun i j H=> Sum.inr.inj (h (show beside x y (.inr i)=beside x y (.inr j) from H)),fun i j he=> Sum.inl_ne_inr (h (show beside x y (.inl i)=beside x y (.inr j) from he))⟩ -- implicit i j?
    rintro ⟨h,hp,ht⟩ (x|x) (y|y) h'
    · exact congr_arg Sum.inl (h h')
    · exact (ht _ _ h').elim
    · exact (ht _ _ h'.symm).elim
    exact congr_arg Sum.inr (hp h')
end
lemma worded_beside (x:I→ E4)(y:J→ E4)(s:I→L.Token)(t:J→L.Token)(hx:Injective (beside x y)) :
    List.Perm (worded (beside x y) (beside s t)) (worded x s ++ worded y t):=by
    refine (List.perm_ext_iff_of_nodup (worded_nodup _ hx) (List.nodup_append.mpr ⟨worded_nodup _ (beside_distinct.mp hx).1, worded_nodup _ (beside_distinct.mp hx).2.1, ?_⟩)).mpr (fun a=> ?_)
    · intro u hu v hv he; obtain ⟨i,rfl⟩:= (worded_get ..).mp hu; obtain ⟨j,rfl⟩:= (worded_get ..).mp hv; exact (beside_distinct.mp hx).2.2 i j (congr_arg Prod.fst he)
    rw [worded_get,List.mem_append,worded_get,worded_get, Sum.exists]; simp
lemma observe_join (h:S.Symmetric)(x:I→E4)(y:J→E4)(s:I→L.Token)(t:J→L.Token)(hx:Injective (beside x y)) : S.expect (worded x s++ worded y t)= observe S (beside x y) (beside s t):= S.order h ((worded_distinct ..).2 hx) (worded_beside x y s t hx)
lemma smooth_observe (h:S.Smooth)(v:I→L.Token) {x:I→E4}(hx:Injective x) : ContinuousAt (fun x:I→E4=>observe S x v) x:= by
    unfold observe worded; simp only [S.readAt]; let z(x:I→ E4):= points (x ∘ runNames I); have he:Continuous z:= by unfold z points; fun_prop -- inspect
    exact (((S.smooth_read h _).continuousOn).continuousAt ((conf_open _).mem_nhds (runs_conf.mpr hx))).comp (f:=z) he.continuousAt
end YM.OPE
