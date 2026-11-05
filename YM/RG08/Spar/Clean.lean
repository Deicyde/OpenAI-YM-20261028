import YM.RG08.Spar.Grid

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows
open scoped Topology BigOperators Classical ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J V:Type}{c f L:Side}

def clover (L:Side)(T:Kernel I J):Kernel (Co L I) J:= fun x=> T (Cell.column L I x)
lemma river (x:Market (Co L I))(z:Market J):sep x.1 z.1 ≤ 4+Pert.Bulk.delta L (Cell.column L I x).1 z.1:=by
 rw [Cell.column_pos]
 let a:=Lattice.lift x.2.1;let l:ℝ:=L.val
 have he:=sep_triangle (L.val • x.1) (a+L.val • x.1) (L.val • z.1)
 have hz:=Pert.Bulk.length_lift L x.2.1
 rw [scale_sep,sep_comm (L.val • x.1),show sep (a+L.val • x.1) (L.val • x.1)= length a by simp [sep]] at he
 unfold Pert.Bulk.delta; field_simp at * -- maybe overkill
 exact he.trans (add_le_add_left hz _)

variable {T:Kernel I J}{v σ C:ℝ}
lemma clover_prices (hp:0≤v)(he:v≤σ)(hC:0≤C)(hs:RowCost σ L T C)(ht:ColCost σ L T C)(hh:city L T): Priced v (C*Real.exp (4*v)) (clover L T):=by
 let W:=Cell.column L I
 have hf (x:Market (Co L I))(y:Market J): bill (clover L T x y) (v*delta 1 x.1 y.1)≤ bill (T (W x) y) (σ*delta L (W x).1 y.1)* ENNReal.ofReal (Real.exp (4*v)):=by
   rw [←bill_add, delta, show ((1:Side).val)=1 from rfl,one_smul]; simp only [Nat.cast_one,div_one] -- delta_one namespace
   apply bill_mono le_rfl
   have hf:= river x y
   have hm:=mul_le_mul_of_nonneg_left hf hp
   have hh:=mul_le_mul_of_nonneg_right he (delta_nonneg L (Cell.column L I x).1 y.1)
   linarith only [hm,hh]
 let Z:= ENNReal.ofReal (Real.exp (4*v))
 refine ⟨by positivity,fun x y u=>?_,?_,?_⟩
 · rw [show (1:Side).val=1 from rfl,one_smul]; unfold clover;rw [Cell.column_map];exact hh ..
 · intro x j;refine (ENNReal.tsum_le_tsum fun y:Cover=>hf x (y,j)).trans ?_; rw [ENNReal.tsum_mul_right,ENNReal.ofReal_mul hC];exact mul_le_mul_left (hs _ _) _
 intro i z;refine (ENNReal.tsum_le_tsum fun x:Cover=>hf (x,i) z).trans ?_;rw [ENNReal.tsum_mul_right,ENNReal.ofReal_mul hC];apply mul_le_mul_left
 have H:Injective (fun x:Cover=>(W (x,i)).1):=fun x y he=>congr_arg Prod.fst (W.injective (Prod.ext he rfl))
 exact (ENNReal.tsum_comp_le_tsum_of_injective H (fun x=>bill (T (x,i.2) z) (σ*delta L x z.1))).trans (ht _ z)
lemma clover_match (S:StepData c f){A:Matrix (Co f I) (Co c J) ℝ}(h:Matches T A):Matches (clover S.patch.L T) (fun x y=>A ((splitCo S.ratio I).symm x) y):=by
 intro x y;change display T c (Cell.column _ _ x) y=_;rw [h];exact congr_arg (fun q=>A q y) (Cell.convert_origin S x).symm
lemma prism_match (V:Type){A:Matrix (Co f I) (Co c J) ℝ}(h:Matches T A): Matches (prism V T) (fun (x:Co f (I×V)) (y:Co c (J×V))=>if x.2.2=y.2.2 then A (x.1,x.2.1) (y.1,y.2.1) else 0) := by
  intro ⟨x,i,u⟩ ⟨y,j,w⟩; rcases eq_or_ne u w with hu|hu
  · unfold display prism; simp only [if_pos hu];exact h (x,i) (y,j)
  unfold display prism;simp [hu]

lemma ticket_atlas {n:ℕ}(h:Atlas σ L n T C)(hh:city L T)(hv:0≤v)(he:v≤σ)(V:Type): Priced v ((C*(L.val:ℝ)^4/(L.val:ℝ)^n)*Real.exp (4*v)) (clover L (prism V T)):=by
 have ht:=prism_prices T V h
 apply clover_prices hv he (by have:=h.nonneg;positivity) _ ht.col (prism_city _ _ hh)
 intro x u;apply (ht.row x u).trans; apply ENNReal.ofReal_le_ofReal
 gcongr -- div
 exact le_mul_of_one_le_right h.nonneg (one_le_pow₀ (by exact_mod_cast (show 1 ≤ L.val from L.pos)))
end YM.RG08.Spar
