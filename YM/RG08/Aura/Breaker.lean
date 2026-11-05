import YM.RG08.Aura.Dates

/-! # The bridge actually needed to replace A_tr; column-wise gradient on the cover and
 lifted costs in fixed units. -/
noncomputable section
namespace YM.RG08.Aura
open Function Lattice Laurent Pert.Bulk Forms Carrel Steam Rows RG Stationary Bloch Tack Anchor Spar Sedan Precision Finset Exterior Packets Ducat Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {G:Gauge}{I:Type}{σ p:ℝ}{L:Side}

local notation "K"=>Loc G 1

def frost (U:Kernel K I):Kernel G.ColorIndex I:= fun x y=>rim (fun z i=>menu U y z i x.2) (0:Axis) x.1
private lemma harvest (x:Cover)(σ:ℝ)(he:0<σ) : Summable (fun y:Cover=>Real.exp (-σ*sep y x)):=by
 let e:=Equiv.subRight x
 change Summable ((fun y:Cover=>Real.exp (-σ*length y)) ∘ (e:Cover → Cover));rw [e.summable_iff]
 exact (Width.compactPay σ he).2.1
private lemma crisis (x:Cover):delta L x (rent L x)≤4:= by have H:= mixed_sep (L:=L) x (rent L x); simpa [sep_self] using H

def fee (L : Side)(s:ℝ) := (1-Real.exp (-(s/L.val:ℝ)))⁻¹*Real.exp (4*(s/2))*(∑' z:Cover,Real.exp (-(s/2)*sep z 0))
lemma sealife {U:Kernel K I}(hs:0<σ)(hp:0 ≤ p)(h:RowCost σ L U p)(hx:Pert.Bulk.bind (heat G) U=0): RowCost (σ/2) L (frost U) (p * fee L σ) ∧∀ (y:Market I)(x:Cover)(i:Axis)(c:G.ColorIndex), menu U y x i c=frost U (x+step i,c) y-frost U (x,c) y:=by
 have hf: Pert.Bulk.bind (heat G) (0:Kernel K I)=0:=by funext x y; unfold Pert.Bulk.bind Pert.Bulk.tagged;simp [Finset.sum_apply]
 have hh(y c):locked fun z i=>menu U y z i c:=fun x i j=> by have he:=scribe (hx.trans hf.symm) y i j x c; simpa [diff,menu] using he
 let v (x:Cover):=L.val • x;let t:ℝ:=σ/L.val
 have he:0<t:=by unfold t; positivity
 have hd(x y:Cover):σ*delta L x y=t*sep x (v y):=by unfold t v Pert.Bulk.delta;ring
 have hU (y:Market I)(c:G.ColorIndex): fell (fun z i=>menu U y z i c) p t (v y.1):=by
    intro z i;rw [← hd];exact (ENNReal.ofReal_le_ofReal_iff hp).mp ((ENNReal.le_tsum (f:=fun x:Cover=> bill (menu U (x,y.2) z i c) (σ*delta L z x)) y.1).trans (h (z,coord i,c) y.2))
 have hg:0≤(1-Real.exp (-t))⁻¹:=by
                                   have hh:Real.exp (-t)<1:=by rw [Real.exp_lt_one_iff];linarith
                                   exact inv_nonneg.mpr (sub_nonneg.mpr hh.le)
 refine ⟨?_,fun y x i c=> (rim_turn (hh y c) he hp (hU y c) x i).symm⟩
 intro x i
 let u:=σ/2;have hu:0<u:=half_pos hs
 let j:=rent L x.1;let b:=p*(1-Real.exp (-t))⁻¹*Real.exp (4*u)
 have hb:0 ≤ b:=mul_nonneg (mul_nonneg hp hg) (Real.exp_nonneg _)
 have hh0(z:Cover):bill (frost U x (z,i)) (u*delta L x.1 z) ≤ ENNReal.ofReal (b*Real.exp (-u*sep z j)):=by
    unfold bill;apply ENNReal.ofReal_le_ofReal
    have ht : |frost U x (z,i)|≤ p*(1-Real.exp (-t))⁻¹*Real.exp (-t*sep x.1 (v z)):= charged x.1 _ (hU (z,i) x.2) (hh (z,i) x.2) hp he
    apply (mul_le_mul_of_nonneg_right ht (Real.exp_nonneg _)).trans
    unfold b; rw [mul_assoc (p*_ :ℝ),mul_assoc (p*_ :ℝ),←Real.exp_add,←Real.exp_add];gcongr _ * Real.exp ?_
    have hx: sep z j ≤ 4+delta L x.1 z:=by rw [sep_comm z j];apply (inv_scaled L x.1 j x.1 z).trans;rw [sep_self, _root_.zero_div,add_zero];gcongr;exact crisis _
    have H:=hd x.1 z;unfold u at *;nlinarith
 -- convert geom
 refine (ENNReal.tsum_le_tsum hh0).trans_eq ?_
 rw [←ENNReal.ofReal_tsum_of_nonneg (fun _=>mul_nonneg hb (Real.exp_nonneg _)) ((harvest j u hu).mul_left _),tsum_mul_left,show (∑' z:Cover,Real.exp (-u*sep z j))= ∑' z:Cover,Real.exp (-u*sep z 0) from ?_];
 · congr 1;unfold b fee t u;ring
 simp only [sep,sub_zero];exact (Equiv.subRight j).tsum_eq (fun z=> Real.exp (-u*length z))
end YM.RG08.Aura
