import YM.RG08.Gallery.Dome

/-!
# Signed axis Cabinet on the cover from palette trajectories.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open Carrel Rudder Rudder.Symmetry Anchor
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J:Type}{n k :ℕ}

-- multiple dot price on one occurrence each, absorbing signs/gain
lemma mcolors (F:Flake n I)(a:Tape n (Demo I))(w:Tape n I)(v:Tape n ℝ)(h:∀ i,(a i).play=v i • (needle (w i)).play): multi F a=(∏ i,v i)*F w:=by
 let b:= needle ∘ w;let S:=soft univ b∪soft univ a
 rw [←mlikes F w,multi_in S F a Finset.subset_union_right,multi_in S F _ Finset.subset_union_left]
 unfold appled;simp only [h,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;unfold b; simp_rw [comp_apply]; ring

def rot (s:Signed)(a:Demo (Mix I 1))(i:Mix I 1):ℝ:= supply s i.2*a.play (atlas s i)
def Rotation (V:Script (Mix I 1))(e:ℕ):Prop:=∀ (a:Demo (Mix I 1))(s:Signed)(r:ℝ),∃ v w:Tray (Mix I 1),(Demo.flat v).play=r • a.play ∧ (Demo.flat w).play=r • rot s a ∧tap e (announced V v)=tap e (announced V w)

lemma lifted_adjust [Fintype I]{F: Flake n (Mix I k)} (s:Signed):Anchor.extend k (Carrel.adjust s F)=orbit s (Anchor.extend k F):=by
 apply Cast.compress_inj (k:=k) _ _ Anchor.expand_grade (orbit_graded (s:=s) Anchor.expand_grade)
 have he(V:Flake n (Mix I k)):compress k (Anchor.extend k V)=V:=funext fun i=>extend_top ..
 rw [←adjust_compress,he,he]
variable {V:Script (Mix I 1)} {e:ℕ}

lemma stampede (hV:Rotation V e)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:n≤e+2)(hs:Forms.Sym (V e n))(s:Signed):Carrel.adjust s (V e n)=V e n:=by
 let F:=V e n
 ext x
 let i:=needle ∘ x
 let j (a:Fin n):=Demo.reals (supply s (x a).2) (needle (atlas s (x a)))
 change (∏ i,supply s (x i).2)*F _ =F _
 rw [←mlikes F x,←mcolors F j (atlas s ∘ x) (fun a=>supply s (x a).2) (fun _=>rfl)]
 symm;apply unravel hs hs i j;intro c
 apply sorting V e _ _ ht (fun r=>?_ ) _ hp
 let y:=synth univ c i
 obtain ⟨a,b,he,hu,hB⟩:=hV y s⁻¹ r
 refine ⟨a,b,he,?_,hB⟩;rw [hu];congr 1;ext v
 have hf(a:Fin n): rot s⁻¹ (i a) v=(j a).play v :=by
    have he:x a=atlas s⁻¹ v↔atlas s (x a)=v:=⟨fun H=>H ▸ (lodge s).right_inv v, fun H=>H ▸ ((lodge s).left_inv (x a)).symm⟩
    simp only [rot,i,j,needle,Demo.reals,Pi.single_apply,comp_apply,Pi.smul_apply,smul_eq_mul]
    by_cases h:x a=atlas s⁻¹ v
    · rw [if_pos h.symm,if_pos (he.mp h).symm];rw [← he.mp h]
      dsimp only [Carrel.atlas];rw [mul_one,mul_one]
      have hf: (1:ℝ)=supply s (x a).2 * supply s⁻¹ (cash s (x a).2):=by
         have he: supply 1 (x a).2=1:=by -- recall derive
            have hx:= stand 1 (x a).2
            have ht:=housing 1 1 (x a).2
            rw [one_mul,show cash 1 (x a).2=(x a).2 from congrArg (fun p:Mix I 1=>p.2) (atlas_id (x a))] at ht
            rcases le_total 0 (supply 1 (x a).2) with hh|hh
            · rwa [← abs_of_nonneg hh]
            rw [abs_of_nonpos hh] at hx;nlinarith
         rw [←housing,inv_mul_cancel,he]
      have hx:=stand s (x a).2
      rcases le_total 0 (supply s (x a).2) with hh|hh
      · rw [abs_of_nonneg hh] at hx;rw [hx] at hf ⊢; simpa using hf.symm
      rw [abs_of_nonpos hh] at hx
      rw [show supply s (x a).2=(-1) by linarith] at hf ⊢;linarith
    rw [if_neg (Ne.symm h),if_neg (Ne.symm (mt he.mpr h)),mul_zero,mul_zero]
 change supply s⁻¹ v.2*(∑ a,c a*(i a).play (atlas s⁻¹ v))=∑ a,c a*(j a).play v
 rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;rw [←hf,mul_left_comm];rfl

lemma cardinality [Fintype I](hV:Rotation V e)(ht:∀ k<e,∀ i≠0,V k i=0)(hp:n≤e+2)(hs:Forms.Sym (V e n)):
 Rudder.Symmetry.Cardinal (Anchor.extend 1 (V e n)):=fun s=>by rw [←lifted_adjust,stampede hV ht hp hs]
end YM.RG08.Gallery
