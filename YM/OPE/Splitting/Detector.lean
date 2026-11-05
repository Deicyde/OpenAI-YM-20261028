import YM.OPE.Shape
import YM.OPE.Splitting.Legacy
/-!
# Detector convention and tested values

Exterior readers are read at relative origin with the true Euclidean
hierarchy. We elect to totalize them with **zero** outside their separated
configurations. All estimates use them on pertinent compacts. Each output
needle reads the *raw product*, independently of truncation, layout or depth
in a nested configuration, and has finite clearance data of its own. Every
finite collection can thus be read on a common sufficiently small regime.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter MeasureTheory Word Table Extraction
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{L:Register G}{S:Table L}(T:Table L)
variable {I J : Type}[Fintype I][Fintype J] {P:DiffPlan S}
    {x:I→ E4} {y:J→ E4} {o:E4} (v:I→L.Token)(w:J→L.Token) (d:ℕ) {n:ℕ}

lemma consIn (o:E4)(x:I→E4){e:Fin n≃ I} : (Points.cons o (points (x ∘ e)))∈ conf _ ↔ Injective (beside (sole o) x):=by
    rw [beside_distinct]; constructor
    · intro h; refine ⟨injective_of_subsingleton _,fun i j hi=>?_,fun ⟨⟩ i hi=>?_⟩
      · obtain ⟨i,rfl⟩:=e.surjective i; obtain ⟨j,rfl⟩:= e.surjective j; exact congr_arg e (Fin.succ_injective _ ((show Injective (Points.cons o _).ofLp from h) (show (Points.cons o (points (x ∘ e))) i.succ=(Points.cons o _) j.succ from (by simpa [Points.cons]))))
      obtain ⟨i,rfl⟩ := e.surjective i; exact Fin.succ_ne_zero i ((show Injective _ from h) (show (Points.cons o (points (x ∘ e))) i.succ=(Points.cons o _) 0 from (by unfold sole at hi; simpa [Points.cons] using hi.symm)))
    rintro ⟨hv,h,h'⟩; change Injective (Fin.cons o ((x ∘ e):Fin n→E4)); intro i j; refine Fin.cases ?_ (fun j=>?_) j <;> refine Fin.cases ?_ (fun i=>?_) i
    · intros; rfl
    · intro h; exact (h' () (e _) (by simpa [sole] using h.symm)).elim
    · intro h; exact (h' () (e _) (by simpa [sole] using h)).elim
    simp only [Fin.cons_succ]; intro hi; exact congr_arg Fin.succ (e.injective (h hi))

lemma worded_one (x:E4)(p:L.Token) : worded (sole x) (sole p)=[(x,p)]:=by change List.ofFn (fun _ : Fin (Fintype.card Unit)=> (x,p))=_; rw [Fintype.card_unique, List.ofFn_succ,List.ofFn_zero]
lemma beside_word (o:E4)(v:L.Token)(x:I→E4)(t:I→L.Token)(h:Injective (beside (sole o) x)): List.Perm (worded (beside (sole o) x) (beside (sole v) t)) ((o,v) :: worded x t) := by
    refine (worded_beside (sole o) x (sole v) t h).trans ?_ -- .. misuse
    rw [worded_one]; rfl
lemma head_observe {e:Fin n≃ J}(p:L.Token)(h:T.Symmetric) (he:Injective (beside (sole o) y)) : observe T (beside (sole o) y) (beside (sole p) w) = T.read (Points.cons o (points (y ∘ e))) (Fin.cons p (w ∘ e)):= by
    rw [observe,← T.readAt]
    have he': Injective y:=(beside_distinct.mp he).2.1; symm; apply T.order h ((worded_distinct ..).2 he)
    refine (beside_word o p y w he).trans ?_; rw [realize,List.ofFn_succ]
    have h0:(fun i=> ((Points.cons o (points (y ∘ e))) i,Fin.cons (α:=fun _=>L.Token) p (w ∘ e) i)) 0=(o,p):= by simp [Points.cons]
    dsimp only at h0; rw [h0]; refine List.Perm.cons _ ?_; change List.Perm _ (List.ofFn (fun i=> _ ))
    have ht: (List.ofFn (fun i:Fin n=> ((Points.cons o (points (y ∘ e))) i.succ,Fin.cons (α:=fun _=>L.Token) p (w ∘ e) i.succ))) = realize (w ∘ e) (points (y ∘ e)):= by simp [Points.cons, realize]
    rw [ht]; refine (List.perm_ext_iff_of_nodup (worded_nodup _ he') (List.nodup_iff_injective_get.mpr (plantInj ((realized ..).2 (show (points (y ∘ e))∈ conf n from he'.comp e.injective))))).2 ?_; intro a; rw [worded_get, realize,List.mem_ofFn]; constructor
    · rintro ⟨j,rfl⟩; obtain ⟨i,rfl⟩:=e.surjective j; exact ⟨i,rfl⟩
    rintro ⟨i,rfl⟩; exact ⟨_,rfl⟩

variable (S) in
def observeOne (o:E4)(y:J→E4) (w:J→L.Token) (d:ℕ) : S.Field d→ₗ[ℂ] ℂ :=
    (T.injectFront (w ∘ runNames J) (Points.cons o (points (y ∘ runNames J))) d).comp (S.representative d)
lemma projectedOne (p : L.Ref d)(h:T.Symmetric)(hh:T.respects S) (he:Injective (beside (sole o) y)):
    observeOne S T o y w d (S.project d p) = observe T (beside (sole o) y) (beside (sole (⟨d,p⟩:L.Token)) w):=by -- arg order check
    let q:= Points.cons o (points (y ∘ runNames J)); let z:= (w ∘ runNames J); let U:= T.injectFront z q d
    rw [head_observe (e:=runNames J) T w _ h he]; change U (S.representative _ (S.project d p))= U p
    rw [← sub_eq_zero, ← map_sub]; apply (T.criterion d _).mp (hh d ?_) (Fintype.card J) z q ((consIn (e:=runNames J) o y).2 he) -- unfolding
    apply (Submodule.Quotient.mk_eq_zero _).mp; change S.project _ _ = 0; rw [map_sub, rep,sub_self]
lemma lowerOne {P:DiffPlan S}(p:S.Field d)(hp:P.Inclusions T)(hx:T.Symmetric)(ht:Injective (beside (sole o) y))(he:d≤n)(hh:T.respects S): observeOne S T o y w n (P.rise he p) = observeOne S T o y w d p := by
    let x:= Points.cons o (points (y ∘ runNames J)); let g:= (w ∘ runNames J); have hg:x∈ conf _:= (consIn (e:=runNames J) o y).2 ht; have hr: ∀ t (p:S.Field t), observeOne S T o y w t p=S.useAt T x (Fin.cons ⟨t,p⟩ (S.classTokens ∘ g)):=by
       intro d v; obtain ⟨p,rfl⟩:= S.onto d v; rw [projectedOne T w d p hx hh ht, head_observe (e:=runNames J) T w _ hx ht]; let u:=Fin.cons (α:=fun _=>L.Token) ⟨d,p⟩ g
       have hf : Fin.cons (α:=fun _=> S.Tag) ⟨d,S.project d p⟩ (S.classTokens ∘ g)=S.classTokens ∘ u:= funext (fun i=> by refine Fin.cases ?_ (fun j=>?_) i; rfl; simp only [Function.comp_apply,u,Fin.cons_succ]); rw [hf]; exact (S.at_project T hx hh hg u).symm
    rw [hr,hr,hp.kernels he _ hg]

/-- Frame ext always relative to center, no term read outside separation. -/
def horizonPin (p:Exterior L): E4:=Points.head p.point
def bearing (p:Exterior L) (i:Fin p.n): E4:= p.point i.succ-horizonPin p
lemma bearing_clear (p : Exterior L) : Injective (beside (sole (0:E4)) (bearing p)) :=by
    apply (consIn _ _ (e:= Equiv.refl _)).1; have he : Points.cons (0:E4) (points (bearing p ∘ Equiv.refl _)) = Points.across (-horizonPin p) p.point:= by
       ext1 i; refine Fin.cases ?_ (fun _=>?_) i <;> simp [Points.cons, Points.across,bearing, horizonPin, Points.head,sub_eq_add_neg]
    rw [he]; exact Points.across_in _ p.clear
namespace Prescription
variable (U:Prescription P)

/-- Value may be needed at large distances while formulating the germ;
never use an unseparated test of the law. Asymptotic estimates eventually
fit all the (finite) relevant frames. -/
def reading (S:Table L)(x:I→E4)(v:I→L.Token)(o:E4)(p:Exterior L) :=
    let z:=beside (fun i=> x i-o) (bearing p)
    if Injective z then observe S z (beside v p.letter) else 0

def ope (a: Mode P) (x:I→E4)(v:I→ L.Token)(o:E4):ℂ:= ∑ i∈ (U.sheet a).support, (U.sheet a) i * reading S x v o i

def letter (a: Mode P):L.Token:= ⟨a.fst,S.representative a.fst (U.needle a)⟩

def termRead (x : I→E4) (v : I→ L.Token)(o:E4)(a:Mode P)(y:J→E4)(w:J→L.Token):ℂ:= U.ope a x v o * observe T (beside (sole o) y) (beside (sole (U.letter a)) w)
def truncated (k:ℕ) (x:I→ E4) (v:I→L.Token) (o:E4) (y:J→E4) (w:J→L.Token) :=∑ a∈ bands P k,U.termRead T x v o a y w

lemma one_test (p:Exterior L)(a:L.Ref d) (H:S.Hierarchy): reading S (sole (0:E4)) (sole (⟨d,a⟩:L.Token)) 0 p=S.spectra d (S.project d a) p:=by
    -- inspect
    unfold reading; simp only [sub_zero,if_pos (bearing_clear p)]; rw [head_observe (e:=Equiv.refl _) S p.letter (⟨d,a⟩:L.Token) H.laws.toSymmetric (bearing_clear p)]; change S.read _ _= S.read _ _; have hk:=p.clear; have he : Points.cons (0:E4) (points (bearing p ∘ Equiv.refl _)) = Points.across (-horizonPin p) p.point:= by
       ext1 i; refine Fin.cases ?_ (fun _=>?_) i <;> simp [Points.cons, Points.across,bearing, horizonPin, Points.head,sub_eq_add_neg]
    rw [he]; exact H.translations _ p.point hk _ _
lemma insertOne (x:L.Ref d)(hU: S.Hierarchy)(i:Mode P): U.ope i (sole (0:E4)) (sole ⟨d,x⟩) 0=U.test i d (S.project d x):= by
    unfold ope test; rw [computes]; simp_rw [one_test d _ x hU]
end Prescription
end YM.OPE
