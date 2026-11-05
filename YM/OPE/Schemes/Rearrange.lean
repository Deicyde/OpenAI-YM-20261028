import YM.OPE.Schemes.Corridor
/-!
# Empty-product, reorderings and off-origin transport
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Table Lattice RG Wilson MergeProof Ribbons Accent Source PhysicalNext.Repeat.Legato Next.Extract Next.UVStress Bid Prescription Word
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{L:Register G}{S:Table L}{C:Family G}{I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
variable {P:DiffPlan S}(U:Prescription P) (T:Table L) (y:J→ E4)(v:I→ L.Token)(w:J→ L.Token)(n:ℕ)(x:I→E4)(o s:E4)
-- main tests use root-to-zero displacement

def away (x:I→ E4)(z:E4) : I→ E4:= fun i=> x i-z
lemma away_inject (x:I→E4)(s:E4): Injective (away x s)↔ Injective x:= by
    refine ⟨fun h i j hi=> h (show away x s i= _ from congr_arg (·-s) hi),fun h i j hj=> h (sub_left_inj.mp hj)⟩
lemma beside_away : beside (away x s) (away y s)= away (beside x y) s:= funext fun i=>by cases i <;> rfl
lemma away_sole : sole (o-s)=away (sole o) s:= rfl
lemma observe_away (h:T.Homogeneous) (hp:Injective x): observe T (away x s) v= observe T x v:= by unfold away; simp_rw [sub_eq_add_neg]; exact  observe_carry T h v hp (-s)
lemma ope_away (a:Mode P): U.ope a (away x s) v (o-s)=U.ope a x v o:= by unfold ope reading away; simp
lemma term_away (a:Mode P) (h:T.Hierarchy)(ht:Injective (beside (sole o) y)) : U.termRead T (away x s) v (o-s) a (away y s) w=U.termRead T x v o a y w:=by
    unfold termRead; rw [ope_away,away_sole,beside_away,observe_away]; exacts [h.translations,ht]
lemma trunc_away (h:T.Hierarchy)(ht:Injective (beside (sole o) y)): U.truncated T n (away x s) v (o-s) (away y s) w= U.truncated T n x v o y w:= by unfold truncated; exact Finset.sum_congr rfl fun i _=> term_away U T y v w x o s i h ht

lemma local_one_mem {p:E4} (s:J→ L.Token)(x:J→E4) (H:T.Basic)(h:Injective (beside (sole p) x)): observe T (beside (sole p) x) (beside (sole (L.one n)) s)= observe T x s:=by
    let x':=points (x ∘ runNames J); have hh:= H.unital ((consIn (e:=runNames J) p x).2 h) n (s ∘ runNames J); rw [head_observe (e:=runNames J) T s _ H.toSymmetric h,hh]; unfold observe worded; rw [T.readAt]; congr 1
lemma observe_empty [IsEmpty I](h:T.Hierarchy)(he:Injective y): observe T (beside x y) (beside v w)=observe T y w:=by
    let z:=Equiv.emptySum I J; rw [show beside x y=y ∘ z from funext fun i=> by cases i; exact isEmptyElim ‹I›; rfl, show beside v w=w ∘ z from funext fun i=> by cases i; exact isEmptyElim ‹I›; rfl]; exact perm_observe T h.laws.toSymmetric z _ he
lemma reading_empty [IsEmpty I](h:S.Hierarchy)(p:Exterior L) : reading S x v o p=S.spectra 0 (S.unit 0) p:=by
    have hx: Injective (bearing p):= (beside_distinct.mp (bearing_clear p)).2.1
    have h₁ := (show reading S x v o p=observe S (bearing p) p.letter from by unfold reading; dsimp only; rw [if_pos (show Injective (beside (fun i=>x i-o) (bearing p)) from beside_distinct.mpr ⟨injective_of_subsingleton _,hx,fun i=> isEmptyElim i⟩)]; exact observe_empty S (bearing p) v p.letter (away x o) h hx)
    rw [Table.unit,← one_test 0 _ _ h,h₁]; unfold reading; simp only [sub_zero,if_pos (bearing_clear p)]; exact (local_one_mem S (p:=0) 0 p.letter (bearing p) h.laws (bearing_clear p)).symm
lemma empty_coeff [IsEmpty I](h:S.Hierarchy)(a:Mode P): U.ope a x v o= U.test a 0 (S.unit 0):=by
    unfold ope test; rw [computes]; exact Finset.sum_congr rfl fun i _=> congr_arg _ (reading_empty v x o h i)
-- evaluating the empty product uses physical unit at cap
lemma empty_test [IsEmpty I] (h:S.Hierarchy)(hT:T.Hierarchy)(hr:T.respects S)(hv:P.Inclusions T) (hv':P.Inclusions S)
    (hU:U.Coherent)(ht:Injective (beside (sole o) y)): observe T (beside x y) (beside v w)=U.truncated T n x v o y w:=by
    rw [observe_empty T _ _ _ _ hT (beside_distinct.mp ht).2.1,← local_one_mem T n w y hT.laws ht]
    let p:L.Ref n := L.scalar n; unfold truncated termRead; have hh(a:Mode P): U.test a 0 (S.unit 0)= U.test a n (S.project n p):= (by rw [← U.affinity h.laws.toSymmetric hv' a (S.unit 0) (Nat.zero_le n),P.fixs hv' h.laws (Nat.zero_le n)]; rfl)
    simp_rw [empty_coeff U v x o h,hh]; exact (U.sumAll T w hv hT.laws.toSymmetric hr ht hU p).symm
end YM.OPE
