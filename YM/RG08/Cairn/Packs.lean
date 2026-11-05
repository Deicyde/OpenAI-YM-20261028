import YM.RG08.Cairn.Rack
import YM.RG08.Cell.Grid

noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cairn
open Lattice Laurent Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function Stationary Bloch RG Finset Packets
open scoped BigOperators Classical ContDiff Topology ENNReal
variable {I J:Type}{n:ℕ}{c f L:Side}{σ τ W p:ℝ}

def docks (L:Side):Equiv (Tape n (Market (Co L I))) (Tape n (Market I)):= Equiv.arrowCongr (Equiv.refl _) (Cell.column L I)
def coast (L:Side)(F:Flake n (Market I)):Flake n (Market (Co L I)) := F ∘ docks L
lemma coast_y (L:Side){F:Flake n (Market I)}(h:Cohort F): Cohort (coast L F):=by
 intro v x; change F _=F _
 rw [show docks L (sway v x)=sway (L.val • v) (docks L x) by ext i :1; exact Cell.column_map _ _,h]
lemma coast_sym (L:Side){F:Flake n (Market I)}(h:Sym F): Sym (coast L F):=fun e=>funext fun y=>congrFun (h e) (docks L y)
lemma harbor (L:Side)(x:Tape n (Market (Co L I))) : (carpet (Co L I)).radius x ≤ (carpet I).radius (docks L x)+8 := by
 let C:=carpet I
 have hc:0≤C.radius (docks L x):=Ground.radius_nn ..
 apply Ground.radius_le _ x (by change 0≤C.radius _+8; positivity); intro i j
 refine (Cell.separation_to (x i) (x j)).trans ?_
 gcongr
 apply le_trans (div_le_self (sep_nonneg ..) (by exact_mod_cast L.property)) -- approximate
 exact Ground.le_radius C (docks L x) i j
lemma coast_held (L:Side){F:Flake n (Market I)} (h:Held (carpet _) σ p F)(hs:0≤σ): Held (carpet _) σ (Real.exp (8*σ)*p) (coast L F):=ensign.mpr (fun i z=> by
  let B:=mark (carpet I) σ F; let V:=ENNReal.ofReal (Real.exp (8*σ))
  calc
  ∑' x,Forms.row (mark _ _ _) i z x ≤ ∑' x:Tape n (Market (Co L I)),V * Forms.row B i (Cell.column L I z) (docks L x):=ENNReal.tsum_le_tsum (fun x=>by
    unfold Forms.row; by_cases he:x i=z
    · rw [if_pos he,if_pos (show docks L x i=Cell.column L I z by exact congrArg (Cell.column L I) he)]
      have hi:= harbor L x
      unfold B mark V; rw [mul_comm (ENNReal.ofReal _),← bill_add]; apply bill_mono le_rfl; nlinarith
    rw [if_neg he]; exact bot_le)
  _ ≤ _:= by rw [ENNReal.tsum_mul_left,(docks L).tsum_eq,ENNReal.ofReal_mul (Real.exp_pos _).le];gcongr; exact ensign.mp h i _)

-- torus commuting ignoring folded origin (C2.1 pack)

def cov (S:StepData c f):Cove c (Co S.patch.L I) ≃ Cove f I:=(splitCo S.ratio I).symm
lemma pay (S:StepData c f)(u:Tape n (Market (Co S.patch.L I))) : cov S ∘ port c ∘ u=port f ∘ docks S.patch.L u:=by
 ext i :1; exact Cell.convert_origin S (u i)

-- x:D z satisfy rolled match and root i pin at representative (lift z...). compare to D' (cov z); the pin differs by a f.val multiple term computed canonically, so before/after use translated x. composition after wrapping equal. Need inverse.
variable (S:StepData c f)(i:Fin n)(z:Tape n (Cove c (Co S.patch.L I)))
private def drift:Cover:= lift ((cov S (z i)).1)- (Cell.column _ I (reach (z i))).1
private lemma drift_nil: wrap f (drift S i z)=0:=by
 unfold drift cov; rw [map_sub,wrap_lift];erw [Cell.convert_target]; simp [reach]
private lemma prize : pass (drift S i z) (Cell.column _ I (reach (z i)))=reach (cov S (z i)):=by
 apply Prod.ext
 · change (Cell.column _ I (reach (z i))).1 + (lift _ - _)=_;rw [add_sub_cancel];rfl
 · rfl

private theorem wrapped {M:Side}{K:Type}(x:Tape n (Market K)){b:Cover}(hh:wrap M b=0):port M ∘ sway b x=port M ∘ x:=by ext j :1; simp only [sway,pass,comp_apply,port,map_add,hh,add_zero]

private def commuting_pin : (lantern i z) ≃ (lantern i (cov S ∘ z)) where
 toFun x:=⟨sway (drift S i z) (docks _ x.val),⟨by change pass _ (Cell.column _ I (x.val i))=_;rw [show x.val i= reach (z i) from x.property.1,prize];rfl,by rw [wrapped _ (drift_nil ..), ←pay,(x.property.2)]⟩⟩ -- associativity? cov ∘ port ∘ x parsed right-assoc so rw without
 invFun x:=⟨(docks S.patch.L).symm (sway (-drift S i z) x.val),⟨by
    have ht:=prize S i z
    apply (Cell.column S.patch.L I).injective
    change Cell.column _ _ ((Cell.column _ _).symm (pass _ (x.val i))) = _
    rw [Equiv.apply_symm_apply, show x.val i=reach (cov S (z i)) from x.property.1,←ht]; unfold pass;dsimp; rw [add_neg_cancel_right]
   ,by
    apply show Injective (fun x:Tape n (Cove c (Co S.patch.L I))=> cov S ∘ x) from fun x y h=>funext fun j=> (cov S).injective (congrFun h j)
    change (cov S ∘ port c ∘ _)=_
    rw [pay,Equiv.apply_symm_apply,wrapped, (x.property.2)]
    rw [map_neg,drift_nil,neg_zero]⟩⟩
 left_inv x:=by apply Subtype.ext; change (docks S.patch.L).symm (sway _ (sway _ _))=_;rw [sway_sway,neg_add_cancel,sway_zero,Equiv.symm_apply_apply]
 right_inv x:=by apply Subtype.ext;change sway _ (docks S.patch.L ((docks S.patch.L).symm _))=_;rw [Equiv.apply_symm_apply,sway_sway,add_neg_cancel,sway_zero]
-- fill holes via by blocks

lemma coast_pour {F:Flake n (Market I)}(h:Cohort F):pour (coast _ F) i z=pour (P:=f) F i (cov S ∘ z):=by
 rw [pour_at,pour_at, ←(commuting_pin S i z).tsum_eq];apply tsum_congr;intro x; change _ = F (sway _ _);rw [h];rfl
lemma coast_poly [Fintype I]{F:Flake n (Market I)}(h:Cohort F):parley (pour (P:=c) (coast S.patch.L F) i)=MvPolynomial.rename (cov S).symm (parley (pour (P:=f) F i)):=by
 change _= MvPolynomial.rename ((cov S).symm.toEmbedding) _; rw [← Cairn.reindex (e:=(cov S).symm.toEmbedding) (pour (P:=f) F i)];congr 1;funext a
 have he:a=many (cov S).symm.toEmbedding n (cov S ∘ a):=by ext j:1; simp [many]
 rw [coast_pour .., he,(many _ _).injective.extend_apply]
 · rw [←he]
 · exact h
end YM.RG08.Cairn
