import YM.Frontier6.Normal.Dilate
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-! Radial Taylor jet test map, anchored at relative 0. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Filter Set MeasureTheory Tensor Analysis
open scoped Topology ContDiff BigOperators Classical
variable {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {f:X→Y}
section Vec
variable [NormedSpace ℝ X]
def fragment (j:ℕ)(f:X→Y): X → Y := diagonal (coeff f j 0)
def plan (j:ℕ)(f:X→Y):X → Y := ∑ i:Fin (j+1), fragment i.val f
lemma fragment_smooth (i:ℕ): Smooth (fragment i f):= diag_smooth ..
lemma plan_smooth (i:ℕ): Smooth (plan i f):=by rw [show plan i f=(fun x=> ∑ k:Fin (i+1),fragment k.val f x) from funext fun x=> Finset.sum_apply x _ _]; exact ContDiff.sum (f:=fun k:Fin (i+1)=>fragment k.val f) (s:=Finset.univ) (fun _ _=> fragment_smooth _) -- name

lemma homogeneous_jet (j i:ℕ)(s:ℝ)(x:X)(a:T X Y i):
    s^i • iteratedFDeriv ℝ j (diagonal a) x=s^j • iteratedFDeriv ℝ j (diagonal a) (s • x):=by
  have he:(fun y=> diagonal a (s • y)) = s^i • (diagonal a) := funext fun y=> Tensor.homogeneous a y _
  rw [← blast s (diagonal a) (diag_smooth ..) j x, he, iteratedFDeriv_const_smul_apply (hf:=(diag_smooth a _).contDiffAt)]
lemma zero_fragment (j i:ℕ)(he:j≠i): iteratedFDeriv ℝ j (fragment i f) 0=0:=by
  unfold fragment; let w:= coeff f i 0; let M:=iteratedFDeriv ℝ j (diagonal w) 0
  have ht:= homogeneous_jet j i 2 0 w; rw [smul_zero] at ht
  have hh:(((2:ℝ)^i)-2^j) • M=0:=by rw [sub_smul]; exact sub_eq_zero.mpr ht
  have hi: (2:ℝ)^i ≠ 2^j:= by -- strict mono
     intro hz; exact he (StrictMono.injective (pow_right_strictMono₀ (show (1:ℝ)<2 by norm_num)) hz.symm)
  exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hi)
lemma matches_fragment (i:ℕ)(h:Smooth f): iteratedFDeriv ℝ i (fragment i f) (0:X)=iteratedFDeriv ℝ i f 0:=by
  let v:=iteratedFDeriv ℝ i f 0
  ext1 a
  have he(σ:Equiv.Perm (Fin i)): v (fun j=> a (σ j))=v a:= sym_Jet (charge_smooth h _|>.contDiffAt) a σ
  change iteratedFDeriv ℝ i (fun x=> ((Nat.factorial i:ℝ)⁻¹ • v) (fun _=>x)) (0:X) a=_
  rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  simp_rw [smul_apply,he]; rw [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ, smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
lemma plan_matches (i j:ℕ)(he:i ≤ j)(h: Smooth f): iteratedFDeriv ℝ i (plan j f) (0:X)=iteratedFDeriv ℝ i f 0:=by
  unfold plan; rw [iteratedFDeriv_sum_apply]; rw [Finset.sum_eq_single (⟨i,by omega⟩:Fin (j+1))]; exact matches_fragment _ h; rotate_left
  · simp
  · exact fun k hk=> (charge_smooth (fragment_smooth k.val) _).contDiffAt
  intro k _ hh; exact zero_fragment _ _ (fun h=> hh (Fin.ext h.symm))

lemma fragment_add (f g:X→ ℂ)(h:Smooth f)(hg:Smooth g)(j:ℕ): fragment j (f+g)=fragment j f+fragment j g:=by
   ext1 x; simp only [fragment, Tensor.coeff_add (charge_smooth h j|>.contDiffAt) (charge_smooth hg j|>.contDiffAt),Tensor.diagonal, add_apply, Pi.add_apply]
lemma plan_add (f g:X→ ℂ)(h:Smooth f)(hg:Smooth g)(j:ℕ): plan j (f+g)=plan j f+plan j g:=by unfold plan; simp_rw [fragment_add f g h hg]; exact Finset.sum_add_distrib
lemma plan_smul (f:X→ ℂ)(c:ℂ)(h:Smooth f)(j:ℕ): plan j (c • f)= c • plan j f:=by
   have he(i:ℕ):fragment i (c • f) = c • fragment i f:=by
     unfold fragment coeff Tensor.diagonal; rw [iteratedFDeriv_const_smul_apply (hf:=(charge_smooth h i).contDiffAt),smul_comm]; ext x; rfl -- ext1
   unfold plan; simp_rw [he, Finset.smul_sum]
lemma plan_same {f g:X→ ℂ} (j:ℕ)(h:∀ i≤j, iteratedFDeriv ℝ i f 0 = iteratedFDeriv ℝ i g 0): plan j f=plan j g:=by unfold plan fragment coeff; exact Finset.sum_congr rfl fun i _=>by rw [h i.val (by omega)]
lemma plan_zero {f:X→ ℂ}(j:ℕ)(h:∀ i ≤ j,iteratedFDeriv ℝ i f 0=0):plan j f=0:=by
  unfold plan fragment coeff; exact Finset.sum_eq_zero fun i _=> by rw [h i.val (by omega),smul_zero]; rfl
end Vec
section Inner
variable [InnerProductSpace ℝ X][FiniteDimensional ℝ X]
/-- Total order through m, *fixed across basis changes*. -/
def portion (s:ℝ)(m:ℕ) : Full X →ₗ[ℂ] Full X where
 toFun f:= ⟨fun x=> shrink X s x * plan m (f:X→ℂ) x,(shrink X s).contDiff.mul (plan_smooth m),(shrink X s).hasCompactSupport.mul_right, subset_univ _⟩
 map_add' f g:= by
    change TestFunction.mk _ _ _ _=_; ext1 x
    change shrink X s x * plan m ((f:X→ℂ)+(g:X→ℂ)) x= shrink X s x * plan m (f:X→ℂ) x + shrink X s x * plan m (g:X→ℂ) x; rw [plan_add _ _ f.contDiff g.contDiff,Pi.add_apply,mul_add]
 map_smul' c f:= by
    ext1 x; change shrink X s x * plan m (c • (f:X→ℂ)) x = c* (shrink X s x * plan m (f:X→ℂ) x); rw [plan_smul _ _ f.contDiff]; change _ * (c*plan _ _ _)=_; ring
@[simp] lemma portion_at (s:ℝ)(j:ℕ)(f:Full X)(x:X): portion s j f x=shrink X s x * plan j (f:X→ℂ) x:= rfl
lemma portion_act (s:ℝ)(j:ℕ)(f:Full X) : (portion s j f : X → ℂ)= (shrink X s : X → ℂ)*plan j (f:X→ℂ):=rfl
lemma portion_local {s:ℝ}(h:0<s)(j:ℕ)(f:Full X) : (portion s j f:X→ℂ) =ᶠ[𝓝 0] plan j (f:X→ℂ):=by
   filter_upwards [Metric.closedBall_mem_nhds (0:X) h] with y hy; simp [shrink_home h _ (mem_closedBall_zero_iff.mp hy)]
lemma portion_fits {s:ℝ}(h:0<s)(j:ℕ)(f:Full X): Fits (2*s) (portion s j f):=by unfold Fits; rw [portion_act]; exact tsupport_mul_subset_left.trans (shrink_fits h)
lemma portion_same_jet {s:ℝ}(h:0<s)(j i:ℕ)(f:Full X)(hi:i≤j): iteratedFDeriv ℝ i (portion s j f : X→ℂ) 0=iteratedFDeriv ℝ i (f : X→ℂ) 0:=by rw [((portion_local h j f).iteratedFDeriv ℝ i).eq_of_nhds]; exact plan_matches i j hi f.contDiff
lemma portion_equal (s:ℝ)(j:ℕ){f g:Full X}(h:∀ i≤j, iteratedFDeriv ℝ i (f:X→ℂ) 0=iteratedFDeriv ℝ i (g:X→ℂ) 0): portion s j f=portion s j g:=by ext1 x; simp only [portion_at,plan_same j h]
lemma portion_zero (s:ℝ)(j:ℕ){f:Full X}(h:∀ i≤j,iteratedFDeriv ℝ i (f:X→ℂ) 0=0): portion s j f=0:=by ext1 x; rw [portion_at, plan_zero j h];simp

def leftOut (s:ℝ)(j:ℕ) : Full X →ₗ[ℂ] Full X:= LinearMap.id - portion s j
lemma left_as (s:ℝ)(j:ℕ)(f:Full X): leftOut s j f=f-portion s j f:=rfl
lemma left_fits {s a:ℝ}(he:0<s)(m:ℕ){f:Full X}(h:Fits a f) (hp:2*s ≤ a): Fits a (leftOut s m f):= h.sub ((portion_fits he m f).up hp)
end Inner
end YM.Frontier6.Normal
#print axioms YM.Frontier6.Normal.plan_matches
#print axioms YM.Frontier6.Normal.left_fits
