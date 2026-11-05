import YM.RG08.Rudder.Loop.Signal
import YM.Gauge.Casimir

/-! Joint color-invariance constraints for standalone invariant completions.
Speak also infinitesimal, needed to use exact supplied simplicity criterion; one can
obtain that constraint directly through Ward or by differentiating constant-site identities.
-/
noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal InnerProductSpace
open Forms Packets Finset Function Lattice Laurent Pert.Bulk Exterior AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {G:Gauge}{n:ℕ}

def sing (f:Urn G.ColorIndex n)(X:Tape n G.Color):ℝ:=∑ y,f y * ∏ i,(X i) (y i)

lemma sing_add (f g:Urn G.ColorIndex n)(X:Tape n G.Color) : sing (f+g) X = sing f X+sing g X:=by simp only [sing,Pi.add_apply,add_mul,sum_add_distrib]
lemma sing_smul (f:Urn G.ColorIndex n)(a:ℝ)(X:Tape n G.Color):sing (a • f) X=a*sing f X:=by simp only [sing,Pi.smul_apply,smul_eq_mul,mul_assoc,mul_sum]
lemma sing_zero (X:Tape n G.Color):sing (0:Urn G.ColorIndex n) X=0:=by simp [sing]

lemma sing_perm (f:Urn G.ColorIndex n)(ξ:Equiv.Perm (Fin n))(X:Tape n G.Color): sing (fun x=>f (x ∘ ξ)) X = sing f (X ∘ ξ):=by
 unfold sing; rw [← Equiv.sum_comp (twist ξ) (fun y=>f y*_)];apply sum_congr rfl; intro x _
 change f _*_=f (x ∘ ξ)*_;congr 1
 exact (Equiv.prod_comp ξ fun j=>X j (x j)).symm

/- new structure is a Submodule; verify closed for tsum uses by finite dimension. -/
def dressed (G:Gauge)(n:ℕ):Submodule ℝ (Urn G.ColorIndex n) where
 carrier:={f|(∀ (u:G.El)(X:Tape n G.Color), sing f (fun i=>G.adjoint u (X i))=sing f X) ∧
    ∀ (z:G.Color)(X:Tape n G.Color), ∑ i,sing f (update X i (G.ad z (X i)))=0}
 zero_mem':=⟨fun _ _=> by simp only [sing_zero],fun _ _=>by simp only [sing_zero,sum_const_zero]⟩
 add_mem' {f g} h H:=by obtain ⟨h,hz⟩:=h;obtain ⟨H,Hz⟩:=H;exact ⟨fun u X=>by simp only [sing_add,h,H],fun z X=>by simp only [sing_add,sum_add_distrib,hz,Hz,add_zero]⟩
 smul_mem' a F h:=⟨fun u X=>by rw [sing_smul,sing_smul,(Set.mem_setOf.mp h).1], fun z X=>by simp only [sing_smul,←Finset.mul_sum,(Set.mem_setOf.mp h).2 z X,mul_zero]⟩

lemma respects (G:Gauge)(n:ℕ):adjGrade (dressed G n):=by
 intro ξ f hf
 obtain ⟨he,hr⟩:=(show (∀ u X,sing f (fun i=>G.adjoint u (X i))=sing f X)∧ ∀ z X,(∑ i,sing f (update X i (G.ad z (X i))))=0 from hf)
 refine ⟨fun u X=>?_, fun z X=>?_⟩
 · simp_rw [sing_perm]; exact he ..
 rw [← Equiv.sum_comp ξ];simp_rw [sing_perm]
 rw [show (∑ i,sing f (update X (ξ i) (G.ad z (X (ξ i))) ∘ ξ))=∑ i,sing f (update (X ∘ ⇑ξ) i (G.ad z ((X ∘ ⇑ξ) i))) from ?_, hr]
 apply sum_congr rfl;intro i _; congr 1; ext j:1;rcases eq_or_ne j i with he|he<;>simp [he,ξ.injective.eq_iff]

lemma pin_single (f:Urn G.ColorIndex 2)(y:Tape 2 G.ColorIndex):
 sing f ((EuclideanSpace.basisFun G.ColorIndex ℝ) ∘ y)=f y:=by
 unfold sing
 have he(x:Tape 2 G.ColorIndex):(∏ i:Fin 2,EuclideanSpace.basisFun G.ColorIndex ℝ (y i) (x i))=(if x=y then (1:ℝ) else 0):=by
   by_cases hh:x=y
   · simp [hh,EuclideanSpace.basisFun_apply]
   rw [if_neg hh];obtain ⟨i,hi⟩:=Function.ne_iff.mp hh
   exact prod_eq_zero (mem_univ i) (by simp [EuclideanSpace.basisFun_apply,hi])
 simp_rw [comp_apply,he,mul_ite,mul_one,mul_zero]; simp
end YM.RG08.Rudder.Symmetry
