import YM.MultipleContact.Detector
import Mathlib.Algebra.MonoidAlgebra.Basic
/-! Linear syntax to keep alternations and permutation invariance only where applicable (distinct points). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.MultipleContact.Script
open Set Function Filter MeasureTheory Table Extraction Spec Multiset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{L:Register G}
abbrev Alpha (S:Table L):= S.Tag × E4
abbrev Grammar (A:Type*) := AddMonoidAlgebra ℂ (Multiset A)
variable {A P Q ι:Type*}[Fintype ι]
def stamp (x:A) : Grammar A:= AddMonoidAlgebra.single ({x}:Multiset A) 1
def spell (v:ι→A): Grammar A:= ∏ i,stamp (v i)
def letters (v:ι→A): Multiset A:=∑ i:ι, ({v i}:Multiset A)
lemma singleton_mul (g h:Multiset A): AddMonoidAlgebra.single g (1:ℂ) * AddMonoidAlgebra.single h 1=AddMonoidAlgebra.single (g+h) 1:=by rw [AddMonoidAlgebra.single_mul_single,one_mul]
lemma spell_eq (v:ι→A):spell v = AddMonoidAlgebra.single (letters v) 1:=by
    have he(p:Finset ι):p.prod (fun i=>stamp (v i)) = AddMonoidAlgebra.single (∑ i∈p,({v i}:Multiset A)) (1:ℂ):=by
       induction p using Finset.induction with
       | empty=> simpa using (AddMonoidAlgebra.one_def (R:=ℂ) (M:=Multiset A)) -- names
       | @insert i p hi ih=>
         rw [Finset.prod_insert hi,Finset.sum_insert hi, ih,stamp,singleton_mul]

    exact he _
lemma letters_card (v:ι→A):(letters v).card= Fintype.card ι:=by simp [letters,Multiset.card_sum]
lemma letters_image (v:ι→A){x:A}:x∈letters v ↔ ∃i,v i=x:=by
    unfold letters; simp [eq_comm] -- test
lemma frame' (m:Multiset A):∃ n,∃x:Fin n→A,m=letters x:=by
      induction m using Multiset.induction with
      | empty=> exact ⟨0,Fin.elim0,by simp [letters]⟩
      | cons a m ih=> obtain ⟨n,x,hx⟩:=ih; refine ⟨n+1,Fin.cons a x,?_⟩
                      rw [← Multiset.singleton_add,hx]; unfold letters; rw [Fin.sum_univ_succ]; simp
lemma letters_frame (m:Multiset A):∃x:Fin m.card→A,m=letters x:=by
      obtain ⟨n,x,hx⟩:= frame' m
      have he :=letters_card x; rw [← hx] at he; simp only [Fintype.card_fin] at he
      subst n; exact ⟨x,hx⟩
lemma spells_repack {α:Type*}[Fintype α](e:α ≃ ι)(x:ι→A):spell x=spell (x ∘ e):=(Equiv.prod_comp e (fun i=>stamp (x i))).symm
lemma letters_repack {α:Type*}[Fintype α](e:α ≃ ι)(x:ι→A):letters x=letters (x ∘ e):=(Equiv.sum_comp e (fun i=>({x i}:Multiset A))).symm
lemma spell_sigma {j:ι→Type*}[∀ i,Fintype (j i)](f:∀ i,j i→A): (∏ i:ι,spell (f i))= spell (fun x:(Sigma j)=>f x.1 x.2):=by
     unfold spell; exact Eq.symm (Fintype.prod_sigma' (fun i y=>stamp (f i y)))

def mapAdd (f:A→P) : Multiset A →+ Multiset P:=
     ⟨⟨fun m:Multiset A=>m.map f, rfl⟩, Multiset.map_add _⟩
def rewrite (f:A→P) : Grammar A →ₐ[ℂ] Grammar P:= AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (mapAdd f)
lemma rewrite_stamp (f:A→P)(x:A): rewrite f (stamp x)=stamp (f x):=by unfold rewrite stamp; change AddMonoidAlgebra.mapDomain _ _=_; rw [AddMonoidAlgebra.mapDomain_single]; rfl
lemma rewrite_spell (f:A→P)(v:ι→A): rewrite f (spell v)=spell (f ∘ v):=by unfold spell; rw [map_prod]; simp_rw [rewrite_stamp,Function.comp_def]

def Extend (f:Multiset A→ℂ) : Grammar A→ₗ[ℂ]ℂ:=
     ((Finsupp.lsum ℂ) (fun m=> LinearMap.toSpanSingleton ℂ ℂ (f m))).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
lemma extend_word (f:Multiset A→ℂ)(v:ι→A): Extend f (spell v) = f (letters v):= by
     rw [spell_eq]; unfold Extend
     change (Finsupp.single (letters v) (1:ℂ)).sum (fun t=> (LinearMap.toSpanSingleton ℂ ℂ (f t)))=_; rw [Finsupp.sum_single_index (h:=fun t=>(LinearMap.toSpanSingleton ℂ ℂ (f t))) ((LinearMap.toSpanSingleton ℂ ℂ _).map_zero)]; exact one_smul ℂ _

section
variable (S:Table L)
def distinct (y:Multiset (Alpha S)) := (y.map Prod.snd).Nodup
def clear (x:ι→Alpha S) : Prop := Injective (fun i=> (x i).2)
lemma clear_repack {α:Type*}[Fintype α](w:α ≃ ι)(x:ι→Alpha S):clear S (x∘w) ↔ clear S x:=by
       unfold clear; constructor
       · intro h i j ht; exact w.symm.injective (h (by simpa only [comp_apply,w.apply_symm_apply] using ht))
       exact fun h=>h.comp w.injective
private lemma clear_uniq0 {n m:ℕ}{x:Fin n→Alpha S}{y:Fin m→Alpha S}(h:letters x=letters y)(hx:clear S x):∃ e:Fin n≃Fin m,x=y ∘ e:=by
       have he:= (letters_card x).symm.trans ((congr_arg Multiset.card h).trans (letters_card y))
       have hu(i):∃ j,y j=x i:=letters_image y|>.mp (h ▸ (letters_image x).mpr ⟨i,rfl⟩)
       choose f hf using hu
       have hi:Injective f:=fun i j e=> hx (by change (x i).2=(x j).2; rw [← hf i,← hf j,e])
       exact ⟨Equiv.ofBijective f (Fintype.bijective_iff_injective_and_card f|>.mpr ⟨hi,he⟩),funext (fun i=>(hf i).symm)⟩

def readFin {n:ℕ}(x:Fin n→Alpha S):ℂ:=if clear S x then S.useAt S (points (fun i=>(x i).2)) (fun i=>(x i).1) else 0
def pickFrame (x:Multiset (Alpha S)) : Fin x.card→Alpha S:= (letters_frame x).choose
def evaluation:= Extend (A:= Alpha S) (fun x=>readFin S (pickFrame S x))
private lemma at_equiv (hs:S.Symmetric){n m:ℕ}{x:Fin n→Alpha S}(e:Fin n≃Fin m)(y:Fin m→Alpha S)(h:x=y∘e):readFin S x=readFin S y:=by
       subst x; by_cases h':clear S y; swap
       · have hn:= mt (clear_repack S e y).1 h'; exact (if_neg hn).trans (if_neg h').symm
       have he:=Fintype.card_congr e; simp only [Fintype.card_fin] at he; subst m
       rw [readFin,readFin,if_pos ((clear_repack ..).mpr h'),if_pos h']
       let z:=points (fun i=>(y i).2)
       exact S.class_perm S hs e (show z∈conf _ from h') (fun i=>(y i).1)
lemma read_unique (hs:S.Symmetric){n m:ℕ}{x:Fin n→Alpha S}{y:Fin m→Alpha S}(h:letters x=letters y):readFin S x=readFin S y:=by
       by_cases hy:clear S y
       · obtain ⟨e,hg⟩:=clear_uniq0 S h.symm hy; exact (at_equiv S hs e x hg).symm
       by_cases hx:clear S x
       · obtain ⟨e,hg⟩:=clear_uniq0 S h hx; exact at_equiv S hs e y hg
       exact (if_neg hx).trans (if_neg hy).symm
lemma eval_fin (hs:S.Symmetric){n:ℕ}(x:Fin n→Alpha S):evaluation S (spell x)=readFin S x:=
     (extend_word _ x).trans (read_unique S hs ((letters_frame _).choose_spec.symm))
lemma eval_frame (hs:S.Symmetric){n:ℕ}(e:Fin n ≃ ι)(x:ι→Alpha S):evaluation S (spell x)= readFin S (x∘e):=by rw [spells_repack e, eval_fin S hs]

def Truncated {n:ℕ}(x:Points n):=if x∈conf n then (fun y:Fin n → S.Tag=> S.useAt S x y) else fun (_:Fin n → S.Tag)=>0
lemma read_points {n:ℕ}(x:Fin n→ Alpha S):readFin S x=Truncated S (points (fun i=>(x i).2)) (fun i=>(x i).1):=by
      have hiff:clear S x ↔ points (fun i=>(x i).2) ∈ conf n:=Iff.rfl
      unfold readFin Truncated; by_cases h: clear S x <;> simp only [← hiff, h,if_false,if_true]
end
end YM.MultipleContact.Script
