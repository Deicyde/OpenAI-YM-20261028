import YM.RG08.Billet.Fable

/-! # Older coefficient direction and full composition expressed as local updates
 preserving coupling. -/
noncomputable section
namespace YM.RG08.Billet
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable (w:ℕ→ℝ)

lemma fees (x y: Essence){z:Essence}(h:budding z):((x*y) ⌾ z)=(x ⌾ z)*(y ⌾ z):=PowerSeries.subst_mul h x y
lemma xrank {z:Essence}(h:budding z): (PowerSeries.X ⌾ z)=z:=PowerSeries.subst_X h -- RHS state template?
/-- Notice chronology: x->f(x), then y=g(input) reads f(g(x)). Ratios have common unit in both cases. -/
def successive (f g:Essence): Essence:= g * (f ⌾ tilt g)
lemma tilted (f g:Essence): (tilt f ⌾ tilt g)=tilt (successive f g):=by rw [tilt,fees _ _ (tassel _),xrank (tassel _),tilt,successive,mul_assoc];rfl -- syntax
lemma sang {f g:Essence}(h:Root f)(he:Root g):Root (successive f g):=by
 unfold successive Root
 rw [coeff_zero_eq_constantCoeff_apply,_root_.map_mul,←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply (φ:=(_⌾tilt g)),rooting,he,h,one_mul]
lemma song (f g h: Essence): (successive f (successive g h))=successive (successive f g) h:=by
 apply tilt_hi
 rw [←tilted,←tilted,←tilted,←tilted];exact (PowerSeries.subst_comp_subst_apply (tassel g) (tassel h) (tilt f)).symm
lemma idle (f:Essence):successive f 1=f:=by apply tilt_hi;rw [←tilted,show tilt (1:Essence) =PowerSeries.X by simp [tilt]];exact PowerSeries.X_subst _
lemma silence (f:Essence):successive 1 f=f:=by rw [successive,show (1:Essence)=(PowerSeries.C (1:ℝ)) by simp,show PowerSeries.C (1:ℝ) ⌾ tilt f =(1:Essence) from ?_,mul_one];simpa using (show PowerSeries.subst (R:=ℝ) (S:=ℝ) (a:=tilt f) (PowerSeries.C 1)=MvPowerSeries.C 1 from PowerSeries.subst_C ..)
lemma stationary: successive (fringe w) (Nacre.ratio w)=1 :=by apply tilt_hi;rw [show tilt (1:Essence) =PowerSeries.X by simp [tilt],←tilted,homebound]
lemma residual: successive (Nacre.ratio w) (fringe w)=1:=by apply tilt_hi;rw [show tilt (1:Essence) =PowerSeries.X by simp [tilt],←tilted,outbound]

-- Ω substitution for kinetic spectrum, for all w (expects w0=1).
def treasury : Essence:=PowerSeries.mk (fun i=>w i)
lemma speak (hw:w 0=1): (Nacre.ratio w)^2=Billet.treasury w ⌾ tilt (Nacre.ratio w):=by
 ext n:1;rw [Nacre.fixed,lo,Billet.treasury]; simp_rw [PowerSeries.coeff_mk];rw [←Finset.sum_erase_add _ _ (show 0∈Nacre.square n by simp),hw,Nat.sub_zero,pow_zero,coeff_one,one_mul,add_comm]
 apply congrArg (· + (if n=0 then 1 else 0):ℝ→ℝ)
 unfold Nacre.boost
 apply Finset.sum_congr rfl; intro i hi; have he:i ≤ n:=by have h := (Finset.mem_erase.mp hi).2;simp [mem_range] at h;omega
 rw [Nacre.factor,coeff_X_pow_mul',if_pos he,coeff_smul];rfl
lemma literal (hw:w 0=1): (fringe w)^2 * Billet.treasury w=1:=by
 let r:=Nacre.ratio w;let s:=fringe w
 have hp:=speak w hw
 have hx:= congrArg (PowerSeries.subst (tilt s)) hp
 change (r^2) ⌾ (tilt s)=(Billet.treasury w ⌾ tilt r) ⌾ tilt s at hx
 rw [show (r^2) ⌾ tilt s=(r ⌾ tilt s)^2 from PowerSeries.subst_pow (tassel s) r 2, show (Billet.treasury w ⌾ tilt r) ⌾ tilt s = Billet.treasury w ⌾ (tilt r ⌾ tilt s) from PowerSeries.subst_comp_subst_apply (tassel r) (tassel s) (Billet.treasury w),show tilt r ⌾ tilt s=PowerSeries.X from outbound w,show Billet.treasury w ⌾ PowerSeries.X = Billet.treasury w from PowerSeries.X_subst _] at hx
 rw [←hx,← mul_pow,show fringe w*(r ⌾ tilt s)=successive r s from rfl,residual,one_pow]
end YM.RG08.Billet
