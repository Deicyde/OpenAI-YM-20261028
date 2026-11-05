import YM.RG08.Room.Dance

/-!
# External-coordinate algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Cloud Glyph Finset MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I J : Type}

/-- Characteristic zero. One-derivative detection, including nonhomogeneous inputs -/
lemma notice (x:I){p:Inn I}(h:pderiv x p=0):x∉p.vars:=by
 rw [mem_vars_iff_mem_support x]
 rintro ⟨b,hb,hx⟩
 have hh:b x ≠ 0 := Finsupp.mem_support_iff.mp hx
 let d:=b-Finsupp.single x 1
 have he : d + Finsupp.single x 1 = b :=
   tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hh))
 have hp:=coeff_pderiv (i:=x) p d
 rw [h,coeff_zero,he] at hp
 exact (mul_ne_zero (mem_support_iff.mp hb) (by positivity)) hp.symm

lemma nearby (W:Finset I){p:Inn I}(h:∀ i∈W,pderiv i p=0){R:Type*}[CommRing R][Algebra ℝ R]{x y:I→R}(hh:∀ i∉W,x i=y i): aeval x p=aeval y p:=by
 rw [MvPolynomial.as_sum p,map_sum,map_sum];apply sum_congr rfl;intro i hi;rw [aeval_monomial, aeval_monomial];congr 1
 apply Finsupp.prod_congr;intro j hj;rw [hh j]; intro he; exact (notice j (h j he)) ((mem_vars_iff_mem_support _).mpr ⟨i,hi,hj⟩)

/-- depends on the external alphabet only -/
def Abroad (W:Finset I)(x:Port I):Prop:=∀ i∈W,pin i x=0
lemma abroad_coeff (W:Finset I){p:Port I}: Abroad W p↔∀ i∈W,∀ e,pderiv i (tap e p)=0:=by
 simp only [Abroad]
 constructor
 · intro h i hi e;rw [tap,←flight_apply,h i hi];exact map_zero _
 intro h i hi;ext e :1;rw [flight_apply];exact h i hi e
lemma abroad_belt {W:Finset I}{f:Port I}(h:Abroad W f){x y:I→Port J}(hh:∀ i∉W,x i=y i):belt x f = belt y f:=by
 ext e :1; change tap e (spool (lug x) f)=tap e (spool (lug y) f); rw [ships,ships]
 apply Finset.sum_congr rfl;intro i _
 rw [show (lug x) (tap i f)=(lug y) _ from nearby W (fun j hj=> abroad_coeff _|>.mp h j hj i) hh]
lemma abroad_atom {W:Finset I}{x:I}(hx:x∉W):Abroad W (rod x):=by
 intro i hi;rw [pins,if_neg (by rintro rfl; exact hx hi)]

end YM.RG08.Room
