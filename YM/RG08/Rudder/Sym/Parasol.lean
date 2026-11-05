import YM.RG08.Rudder.Sym.Clash

noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior Laurent AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{j:Fin n}{F:Raw I n}

def groupcard:ℝ:=Fintype.card Signed
lemma card_sun:0<groupcard:=Nat.cast_pos.mpr Fintype.card_pos

def Cardinal (F:Raw I n):Prop:=∀ s,orbit s F=F
def canopy (I:Type)(n:ℕ):Raw I n→ₗ[ℝ] Raw I n:= groupcard⁻¹ • ∑ s:Signed,orbit s
lemma canopy_apply :canopy I n F=groupcard⁻¹ • ∑ s:Signed,orbit s F:=by simp [canopy,LinearMap.sum_apply]
lemma covered :Cardinal (canopy I n F):=by
 intro s
 rw [canopy_apply,map_smul,map_sum];congr 1
 simp_rw [orbit_double]; exact Equiv.sum_comp (Equiv.mulRight s) fun s=>orbit s F
lemma cardinal_fixed (h:Cardinal F):canopy I n F=F:=by
 unfold Cardinal at h;simp_rw [canopy_apply,h,sum_const,card_univ, ←Nat.cast_smul_eq_nsmul ℝ,smul_smul,←show groupcard=(↑(Fintype.card Signed):ℝ) from rfl,inv_mul_cancel₀ card_sun.ne',one_smul]
lemma canopy_field {r:Fin n→ℕ}(h:Graded F r):Graded (canopy I n F) r:=by
 rw [graded_iff] at *;intro k x hx;rw [canopy_apply,Pi.smul_apply,Finset.sum_apply,sum_eq_zero (fun s _=>field_orbit s (h k) x hx),smul_zero]
lemma canopy_cohort (h:Cohort F):Cohort (canopy I n F):=by rw [canopy_apply];exact Cohort.smul (Cohort.sum _ _ (fun s _=>orbit_cohort h s)) _
lemma canopy_held{σ C:ℝ}(h: Held (carpet (Tone I)) σ C F)(hs:0≤σ)(hc:0≤C):Held (carpet (Tone I)) σ (C*Real.exp (8*σ)) (canopy I n F):=by
 rw [canopy_apply]; apply (Held.smul _ (Held.sum (s:=(univ:Finset Signed)) _ _ (fun _ _=>show 0≤C*Real.exp (8*σ) by positivity) (fun s _=>orbit_held h hs s))).mono le_rfl _ (fun _=>le_rfl)
 simp only [abs_of_pos (inv_pos.mpr card_sun),sum_const,card_univ,nsmul_eq_mul,←mul_assoc, ←show groupcard=(↑(Fintype.card Signed):ℝ) from rfl,inv_mul_cancel₀ card_sun.ne',one_mul,le_rfl]

lemma picture_orbit (s:Signed)(h:Graded F 2):picture I n (orbit s F)=orbit s (picture I n F):=by
 have he(l:List (Fin n))(hl:l.Nodup)(F:Raw I n)(h:∀ i∈l,field F i 2):patchL l (orbit s F)=orbit s (patchL l F):=by
   induction l generalizing F with
   | nil=>rfl
   | cons a t ih=>
       rw [List.nodup_cons] at hl
       change patchL t (boundary a (orbit s F))=orbit s (patchL t (boundary a F));rw [commute F s a (h _ (by simp)),ih hl.2 _ (fun i hi=>passive (h i (by simp [hi])) (by rintro rfl;exact hl.1 hi))]
 exact he _ (List.nodup_finRange _) F (fun i _=> graded_iff.mp h i)
lemma picture_canopy (h:Graded F 2): picture I n (canopy I n F)=canopy I n (picture I n F):=by simp_rw [canopy_apply,map_smul,map_sum,picture_orbit _ h]

end YM.RG08.Rudder.Symmetry
