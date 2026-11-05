import YM.RG08.Quarry.Looming
import YM.RG08.Gallery.Call
/-! # Normalize currents for first-unmatched -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Glyph
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G : Gauge}

def pend (r:ℝ)(x:Demo (Mix G.ColorIndex 1)):Tray (Market (Loc G 1)):= Demo.pump (Demo.reals r x)
def diver (r:ℝ)(z:Market G.ColorIndex):Tray (Market G.ColorIndex) := Demo.pump (Demo.reals r (Gallery.needle z))

private lemma bolt_price (z:Cover)(p:G.ColorIndex)(x:Mix G.ColorIndex 1): (bolt z p).play x=((if (x.1+step (back x.2.1),x.2.2)=(z,p) then (1:ℝ) else 0)-(if (x.1,x.2.2)=(z,p) then (1:ℝ) else 0)):=by
 rcases x with ⟨x,v,l⟩;obtain ⟨j,rfl⟩:=axisEquiv.surjective v
 dsimp only;rw [coord_map,back_axis];convert! bolt_eval z p x j _
lemma puzzle (d:G.El)(r s:ℝ)(u:Demo (Mix G.ColorIndex 1))(p:Market G.ColorIndex) (i: Mix G.ColorIndex 1):
 let x:=pend r u;let y:=portrait (hot d) (art x (diver (r*s) p))
 ; (Demo.flat y).play i=r* G.adjoint d (heavy G (fun l=>(u.play+s • (bolt p.1 p.2).play) (i.1,i.2.1,l))) i.2.2:=by
 intro x y
 unfold y
 rw [leading,hot_speed];let h:= (Demo.flat (art x (diver (r*s) p))).play ∘ jab (hot d) i
 have he : fbar 0 h - fbar 1 h + fbar 2 h=r • heavy G (fun l=> (u.play+s • (bolt p.1 p.2).play) (i.1,i.2.1,l)):=by
    ext l
    change h (0,l)-h (1,l)+h (2,l)=r*_
    simp only [h,Function.comp_apply,art,Demo.flat,jab,hot,menu,if_neg (by decide:(1:Fin 3)≠0),if_neg (by decide:(2:Fin 3)≠0),if_neg (by decide:(2:Fin 3)≠1),ite_true,Sum.elim_inr,Sum.elim_inl, add_zero,x,pend,diver,Demo.pump];simp only [Demo.reals, Pi.smul_apply,smul_eq_mul,PowerSeries.constantCoeff_C]
    simp [Gallery.needle,Pi.single_apply,heavy,bolt_price]; split_ifs <;> ring
 rw [he,_root_.map_smul];rfl
end YM.RG08.Quarry
