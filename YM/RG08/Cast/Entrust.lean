import YM.RG08.Cast.Duel

/-! # Matrix kernels and leading pairs, evaluation with NO rank factorial -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function Matrix RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {G:Gauge}{n:ℕ}{P:Side}
variable {D:Kernel (TypeFace n) (TypeFace n)} {M:Matrix (Body n P) (Body n P) ℝ}
local notation "o" => (0:Fin 2)
local notation "u" =>(Fin.succ (0:Fin 1))

def arcade (M:Matrix (Body n P) (Body n P) ℝ)(x:Tape 2 (Cmix P G.ColorIndex n)):ℝ:=Spar.shaded P P G.ColorIndex M (x o) (x u)

lemma spur_matches (h:Matches D M):pour (spur G D) o=arcade M:=by
 funext x
 -- lantern at x o chooses y.1 anchor, other y.1 shift aliases. equiv subtype
 let A:Set Cover:={w|wrap P w=(x u).1}
 let v:lantern o x≃A := {
    toFun y:=⟨(y.val u).1,congrArg Prod.fst (found y.property u)⟩
    invFun w:=⟨Fin.cons (reach (x o)) (fun _=>(w.val,(x u).2)),by
       constructor
       · rfl
       ext i:1
       fin_cases i
       · change port P (reach (x o))=x o;exact Prod.ext (wrap_lift _) rfl
       change (wrap P w.val,(x u).2)=x u;exact Prod.ext w.property rfl⟩
    left_inv y:=by
       apply Subtype.ext;funext i;fin_cases i
       · exact y.property.1.symm
       apply Prod.ext
       · rfl
       exact congrArg (fun t : Cove P (Firm G.ColorIndex n) => t.2) (found y.property u).symm
    right_inv w:=Subtype.ext rfl}
 rw [pour_at,←v.symm.tsum_eq]
 unfold arcade Spar.shaded;rw [Matrix.of_apply]
 have he:=h ((reach (x o)).1,(x o).2.1) ((x u).1,(x u).2.1)
 unfold display reach at he; rw [wrap_lift] at he
 change (∑' c:A, if (x o).2.2=(x u).2.2 then D _ (c.val,_) else 0) = _
 split_ifs with hx
 · dsimp only at he ⊢; rw [←he]
   have hh := _root_.tsum_subtype A (fun v:Cover=>D (lift (x o).1,(x o).2.1) (v,(x u).2.1))
   apply Eq.trans hh;apply tsum_congr;intro i; unfold Set.indicator; by_cases ht:wrap P i=(x u).1 <;> simp [A,ht]
 simp

-- alias under h.Matches resolution: transpose test/cofinal later
lemma picture_arcade {D:Kernel (TypeFace 2) (TypeFace 2)}{M:Matrix (Body 2 P) (Body 2 P) ℝ} (h:Matches D M){τ p:ℝ}(hp:NextTo (beam G D) τ p): pour (P:=P) (Anchor.compress 1 (picture G.ColorIndex 2 (beam G D))) o=arcade (Precision.K M):=by
 rw [descend o hp,show Anchor.compress 2 (beam G D) = spur G D from funext (fun x=>extend_top (k:=2) (spur G D) x),spur_matches h]
 funext x;rw [Spar.query];unfold arcade; simp only [Spar.shaded,Matrix.of_apply]
 -- convert ∑ tape to ∑ Body^2
 let E:Cove P (Kind G.ColorIndex 2) ≃ Body 2 P × G.ColorIndex:=(Equiv.prodAssoc ..).symm
 have he {f:Tape 2 (Cove P (Kind G.ColorIndex 2))→ℝ}: (∑ y,f y)= ∑ a:Cove P (Kind G.ColorIndex 2),∑ b:Cove P (Kind G.ColorIndex 2), f (Fin.cons a (Fin.cons b Fin.elim0)):=by
    rw [← (Fin.consEquiv (fun _:Fin 2=>Cove P (Kind G.ColorIndex 2))).sum_comp f,Fintype.sum_prod_type];apply Finset.sum_congr rfl; intro a _
    rw [← (Equiv.funUnique (Fin 1) (Cove P (Kind G.ColorIndex 2))).symm.sum_comp];apply Finset.sum_congr rfl; intro b _;congr 1;funext i;fin_cases i <;> rfl
 rw [he]
 let w(i:Fin 2):Body 1 P:=((x i).1,(x i).2.1)
 let z(i:Fin 2):=(x i).2.2
 let T:= ((cobound 1).acts P)
 rw [Fintype.sum_prod_type];simp_rw [Fintype.sum_prod_type, Fin.prod_univ_two]
 simp only [Fin.cons_zero,show (1:Fin 2)=(0:Fin 1).succ from rfl,Fin.cons_succ]
 -- innermost picks g=x3 via sum_eq_single
 have coins (x2 x4:Body 2 P)(g:G.ColorIndex):
     (∑ g':G.ColorIndex,(if g=g' then M x2 x4 else 0)* ((if g=z o then T x2 (w o) else 0)*(if g'=z u then T x4 (w u) else 0))) = if g=z o then (if g=z u then M x2 x4*(T x2 (w o)*T x4 (w u)) else 0) else 0:=by
    rw [Finset.sum_eq_single g (by intro i _ ht; simp [Ne.symm ht]) (by simp),if_pos rfl];split_ifs <;> simp
 change (∑ v:Site P,∑ i,∑ g:G.ColorIndex,∑ v':Site P,∑ j,∑ g':G.ColorIndex,(if g=g' then M (v,i) (v',j) else 0)* ((if g=z o then T (v,i) (w o) else 0)*(if g'=z u then T (v',j) (w u) else 0)))=_
 simp_rw [coins, Finset.sum_ite_irrel,Finset.sum_const_zero,sum_ite_eq',if_pos (mem_univ _),Finset.sum_ite_irrel,Finset.sum_const_zero]
 have H : Precision.K M (w o) (w u) = (∑ q:Site P,∑ a,∑ b:Site P,∑ c,M (q,a) (b,c)*(T (q,a) (w o)*T (b,c) (w u))):=by
   rw [Precision.K, Matrix.mul_assoc,Matrix.mul_apply];simp_rw [Matrix.mul_apply,transpose_apply,Fintype.sum_prod_type,Finset.mul_sum]; change (∑ i:Site P,∑ j,∑ l:Site P,∑ m,T (i,j) (w o)*(M (i,j) (l,m)*T (l,m) (w u)))=_
   iterate 4 (apply Finset.sum_congr rfl; intro a b)
   ring
 rw [←H]; unfold z w;split_ifs <;> try rfl
end YM.RG08.Cast
