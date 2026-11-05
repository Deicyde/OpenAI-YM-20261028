import YM.WilsonBulk.Staves.Furrow

/-!
# Rank extraction & finite volume WT proof delivering kernel identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Lattice Laurent Function Filter Bloch Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset Equiv
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {α β : Type} {G : Gauge} {i j : G.ColorIndex} {p q k n e : ℕ} {c : Side}
open PowerSeries (coeff constantCoeff)
open MvPolynomial (X C homogeneousComponent)
-- shift support at any base

def backed {α : Type} [AddGroup α] [One α] (t : Bool) (a : PotentialForm) (x : Four α) := if t then x-step (axisEquiv.symm a) else x
lemma backed_criterion (x : Site c) (y : Site c×PotentialForm) (t) : x=lastAt y t ↔ backed t y.2 x=y.1 := by cases t <;> simp [lastAt,backed,sub_eq_iff_eq_add]
lemma script_tassel [Fintype α] (v : Legs α q) (V : Page α k) : script (tassel v V)= script V*field v := by
  unfold script; rw [typeset_fin_plus,sum_mul]; refine sum_congr rfl fun i _=>?_ ; simp_rw [tassel_pay,field_append,apply_ite C]; simp [ite_mul,mul_assoc]
lemma planted_shape (x : Site c) (V : Page (Pennant G c) (k+1)) (i : G.ColorIndex) (t b) :
    script (margin (ribbons (q:=q) backed t b i V) (selvedge (x,coord 0) i))=
    ∑ u:G.ColorIndex, script (margin V (selvedge (cameo backed t b x) u))*coeff q (submit (named ∘ selvedge (cameo backed t b x)) (motive t u i)) := by
  simp only [ribbons, plume,margin_grabs,margin_scale,post_mark,selvedge,↓reduceIte,script_sum,script_scale,script_tassel,submit_name,coeff_parallel]; apply sum_congr rfl fun u _=>?_; rw [motive,ink_power]; -- script(P) hull preserve as tag variable!
  -- match outer
  let X:=cameo backed t b x; let T:=script (margin V (selvedge X u))
  change ∑ v:Legs G.ColorIndex q, shaft t u i v • (T*field (selvedge X ∘ v))=T*MvPolynomial.rename (selvedge X) (script (shaft t u i))
  conv_rhs => unfold script field; simp only [map_mul,map_prod,map_sum,MvPolynomial.rename_C,MvPolynomial.rename_X,mul_sum]
  refine sum_congr rfl fun v _=> ?_; unfold field; rw [← MvPolynomial.C_mul']; dsimp only [Function.comp_apply]; ring
lemma pillar (x : Site c× Cloth G) (V : Page (Pennant G c) (k+1)) : script (margin (spiro backed V q) x)= if x.2.1= coord 0 then
    ∑ y:Pennant G c, ∑ t:Bool, if x.1=lastAt (fret y) t then script (margin V y)*coeff q (submit (named ∘ selvedge (fret y)) (motive t y.2.2 x.2.2)) else 0 else 0 := by
  unfold spiro tailBuff; rw [post_mark,script_polish]; rcases x with ⟨x,b,i⟩; split
  next h=>
    change b=coord 0 at h; subst b
    have hs t a u (e:u≠i) : margin (ribbons (q:=q) backed t a u V) (selvedge (x,coord 0) i)=0 := by simp only [ribbons,margin_grabs,margin_scale,plume,post_mark]; simp [Ne.symm e]
    simp_rw [margin_grabs,script_sum];
    rw [sum_comm (s:=univ) (t:= (univ:Finset Bool))]; refine sum_congr rfl fun t _=>?_
    rw [swatch_split, Fintype.sum_prod_type,sum_comm (s:=univ) (t:= (univ:Finset PotentialForm))]; refine sum_congr rfl fun a _=>?_
    rw [sum_eq_single i]; rotate_left
    · intro u _ hu; rw [show margin _ _=_ from hs t a u hu,script_zero]
    · simp
    rw [show script _=_ from planted_shape x V i t a (q:=q)] -- limited? ; sum rhs commute
    rw [sum_comm]; refine sum_congr rfl fun u _=>?_ ; simp_rw [backed_criterion]; simp [fret,selvedge]; rfl
  next h=> simp only [margin_grabs,margin_scale,script_sum,ribbons,plume,post_mark]; simp [h]

lemma reports_with [Fintype α] {I : Record α} (h : Document I) (i : α) (e : ℕ) : coeff e (player i (volumeTape I)) = ∑ k ∈ allowed e, ((k+1:ℕ):ℝ) • script (margin (I e (k+1)) i) := by -- declare I
  rw [player, parallel_D,tape_power, capsule,map_sum]; unfold allowed; rw [sum_range_succ' (fun j=>_)]; simp_rw [script_deriv _ (h.coherent _ _) i]; rw [script_scalar]; simp only [MvPolynomial.pderiv_C,add_zero]; rw [sum_range_succ (n:=e+2), h.cap _ _ (by omega : e+2<e+2+1), margin_zero,script_zero,smul_zero, add_zero] -- syntax sum_range
lemma sock_pure (x : Site c× PotentialForm) (i j : G.ColorIndex) (t : Bool) (q : ℕ) :
    MvPolynomial.IsHomogeneous (coeff q (submit (named ∘ selvedge x) (motive t i j))) q := by
  rw [submit_name, coeff_parallel, motive, ink_power]; exact (field_hom _).rename_isHomogeneous -- check
lemma pure_read [Fintype α] (c' : ℝ) (P : Page α k) (W : Formula α) (he : MvPolynomial.IsHomogeneous W q) :
    homogeneousComponent (σ:=α) n ((c' • script P)*W)= if n=k+q then c' • (script P*W) else 0 := by
  rw [smul_mul_assoc,map_smul,MvPolynomial.homogeneousComponent_of_mem ((field_hom P).mul he),smul_ite,smul_zero]
end Parapet
end YM.WilsonBulk
