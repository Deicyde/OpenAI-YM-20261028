import YM.RG08.Orison.Shown
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Composition/inverse direction of adjacent Wilson coupling read
 (mathematical formal coefficients only). -/
noncomputable section
namespace YM.RG08.Billet
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false

infixl:70 " ⌾ " => fun (f g : Essence) => PowerSeries.subst g f
abbrev budding(f: Essence):Prop:= PowerSeries.HasSubst f
def Root (F:Essence):Prop:=coeff 0 F=1
def tilt (f:Essence):=PowerSeries.X *f
lemma tassel (f:Essence): budding (tilt f):= HasSubst.of_constantCoeff_zero' (by unfold tilt; simp)
lemma tilt_low (p:Essence): constantCoeff (tilt p)=0:=by unfold tilt;simp
lemma leftrail (f:Essence)(n:ℕ):coeff (n+1) (tilt f)=coeff n f:=coeff_succ_X_mul ..
lemma tilt_hi {f g: Essence}(h:tilt f=tilt g):f=g:=by ext n:1;rw [←leftrail f,←leftrail g,h]
-- substitutions billing
lemma lo (f g: Essence)(e:ℕ): coeff e (f ⌾ tilt g)=∑ i∈Nacre.square e,coeff i f*coeff (e-i) (g^i):=by
 change coeff e (PowerSeries.subst (tilt g) f)=_
 rw [PowerSeries.coeff_subst' (tassel g), finsum_eq_sum_of_support_subset _ (s:=Nacre.square e) ?_]
 · apply Finset.sum_congr rfl;intro i hi;unfold tilt;rw [mul_pow,coeff_X_pow_mul',if_pos (by simpa using hi),smul_eq_mul]
 intro i hi; by_contra hg;apply hi;unfold tilt;dsimp only;rw [mul_pow,coeff_X_pow_mul',if_neg (by simpa using hg),smul_zero]
lemma rooting {f g: Essence}: coeff 0 (f ⌾ tilt g)=coeff 0 f:=by rw [lo];simp [Nacre.square]
lemma planting {f: Essence}(e:ℕ)(h:Root f): coeff 0 (f^e)=1:=by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow,← PowerSeries.coeff_zero_eq_constantCoeff_apply,h,one_pow]

variable (w:ℕ→ℝ)
def jac := tilt (Nacre.ratio w)
lemma jac_one: coeff 1 (jac w)=1:=(leftrail _ 0).trans (hasHead ..)
lemma jac_oneC:IsUnit (coeff 1 (jac w)):=by rw [jac_one];exact isUnit_one
lemma jac_center:constantCoeff (jac w)=0:= tilt_low _
def going := PowerSeries.substInvOfIsUnit (jac w) (jac_oneC w)
def fringe : Essence:= PowerSeries.mk (fun i=>coeff (i+1) (going w))
lemma fringe_tip : tilt (fringe w)=going w:=by
 ext ( _ | i):1
 · rw [coeff_zero_eq_constantCoeff_apply, tilt_low]; rw [coeff_zero_eq_constantCoeff_apply]; exact (PowerSeries.constantCoeff_substInvOfIsUnit (jac w) (jac_oneC w)).symm
 · rw [leftrail,fringe,PowerSeries.coeff_mk]
lemma fringe_head: Root (fringe w):=by rw [Root,←leftrail,fringe_tip,zero_add,going,PowerSeries.coeff_one_substInvOfIsUnit]; have he:= (jac_oneC w).unit_spec;have hx:=he.trans (jac_one w); rw [show (jac_oneC w).unit =1 from Units.ext hx];rfl
lemma outbound: (tilt (Nacre.ratio w) ⌾ tilt (fringe w))=PowerSeries.X:=by rw [fringe_tip]; exact PowerSeries.subst_substInvOfIsUnit_right (jac w) (jac_center w) (jac_oneC w) -- argument order
lemma homebound : (tilt (fringe w) ⌾ tilt (Nacre.ratio w))=PowerSeries.X:=by rw [fringe_tip]; exact PowerSeries.subst_substInvOfIsUnit_left (jac w) (jac_center w) (jac_oneC w)
end YM.RG08.Billet
