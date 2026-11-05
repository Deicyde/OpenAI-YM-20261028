import YM.RG08.Rudder.Trials
import YM.AnalyticNext.QUARTIC_MATCH.Cells.Resolve

/-!
# Position lift interfaces, preserving colors/components and dealing with canonical
quasi-local kernels. Take the recent (same supplied snapshot) position-space multi lift
proof. Further files choose one common lift at every demand with Lipschitz change.
-/
noncomputable section
namespace YM.RG08.Rudder
open scoped Topology BigOperators Classical
open Forms Finset Function Exterior AnalyticNext.QuarticMatch.BoxChain Pert.Bulk Lattice Laurent
set_option autoImplicit false
variable {I:Type}{n:ℕ}{σ C:ℝ}{s:List (Fin n)}

abbrev Tone (I:Type):=Finset Axis × I
abbrev Raw (I:Type)(n:ℕ):=Flake n (Market (Tone I))

variable {F T:Raw I n}

def lyre (x:Tape n (YM.AnalyticNext.QuarticMatch.BoxChain.Cell ℤ))(y:Tape n I):Tape n (Market (Tone I)):=fun i=>( (x i).1,(x i).2,y i)

def hum (F:Raw I n)(y:Tape n I):ArrayC (Fin n) ℤ ℝ:=fun x=> F (lyre x y)

def joinC (f:Tape n I→ArrayC (Fin n) ℤ ℝ):Raw I n:=fun x=> f (fun i=>(x i).2.2) (fun i=>((x i).1,(x i).2.1))
lemma hum_back (F:Raw I n):joinC (hum F)=F:=rfl
lemma hum_fore (f:Tape n I→ArrayC (Fin n) ℤ ℝ):hum (joinC f)=f:=rfl

/- linear gradient adjoint per slot -/
def boundary (j:Fin n): Raw I n→ₗ[ℝ] Raw I n where
 toFun F:= joinC (fun y=>lower j (hum F y))
 map_add' F T:=by ext x;let u (i:Fin n):=(x i).2.2;let v(i:Fin n):=((x i).1,(x i).2.1);change (lower j (hum F u+hum T u)) v=_;rw [map_add];rfl
 map_smul' a F:=by ext x;let u (i:Fin n):=(x i).2.2;let v(i:Fin n):=((x i).1,(x i).2.1);change (lower j (a • hum F u)) v=_;rw [map_smul];rfl

/- pointwise finite dependence -/
lemma local_boundary (j:Fin n):Continuous (@boundary I n j):=by
 apply continuous_pi;intro x
 let c(i:Fin n):=((x i).1,(x i).2.1)
 let z(i:Fin n):=(x i).2.2
 change Continuous fun F:Raw I n=>lower j (hum F z) c
 simp_rw [lower_at]; apply continuous_finsetSum;intro i _;unfold sect;dsimp only [LinearMap.coe_mk,AddHom.coe_mk];split_ifs
 · exact continuous_const
 change Continuous (fun F:Raw I n=>sign _ _ • (F _-F _))
 have H (x:Tape n (Market (Tone I))):Continuous fun F:Raw I n=>F x:=continuous_apply _
 exact (continuous_const (Y:=ℝ)).smul ((H _).sub (H _))

def patchL (s:List (Fin n)):Raw I n→L[ℝ] Raw I n:=match s with
 | []=>ContinuousLinearMap.id ℝ _
 | j::l=> (patchL l).comp (⟨boundary j,local_boundary j⟩ : Raw I n→L[ℝ] Raw I n)

def picture (I:Type)(n:ℕ): Raw I n→L[ℝ] Raw I n:=patchL (List.finRange n)
lemma patch_eval (s:List (Fin n))(F:Raw I n)(y:Tape n I):hum (patchL s F) y = YM.AnalyticNext.QuarticMatch.BoxChain.solve s (hum F y):=by
 induction s generalizing F with
 | nil=> rfl
 | cons j l ih=>change hum (patchL l (boundary j F)) y = YM.AnalyticNext.QuarticMatch.BoxChain.solve l (lower j (hum F y));rw [ih];rfl

def Graded (F:Raw I n)(r:Fin n→ℕ):Prop:=∀ y j, Rank (hum F y) j (r j)
def Closing (F:Raw I n):Prop:=∀ y j,ClosedSlot (hum F y) j
def NextTo (F:Raw I n)(σ C:ℝ):Prop:=∀ y,Pricing (hum F y) σ C
lemma Closing.sub (h:Closing F)(g:Closing T):Closing (F-T):=by intro y j;exact (h y j).sub (g y j)
lemma Graded.sub {r:Fin n→ℕ}(h:Graded F r)(g:Graded T r):Graded (F-T) r:=fun y j=>(h y j).sub (g y j)
lemma NextTo.sub {D:ℝ}(h:NextTo F σ C)(g:NextTo T σ D): NextTo (F-T) σ (C+D):=fun y=>(h y).sub (g y)

lemma NextTo.unit (hh:0<σ)(hc:0≤C)(h: Cohort F)(H:Held (carpet (Tone I)) σ C F)(hn:0<n):NextTo F σ C:=by
 intro y; refine ⟨fun b x=>?_,hh,hc,?_⟩
 · exact h b (lyre x y)
 intro x i j
 unfold cost hum
 let V:=carpet (Tone I); let a:=V.radius (lyre x y)
 have he:=H.check hc hn (lyre x y)
 have hb:=V.le_radius (lyre x y) i j
 change (↑(size ((x i).1-(x j).1)):ℝ) ≤a at hb
 rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
 rw [Real.norm_eq_abs]; apply le_trans _ he;gcongr

lemma NextTo.cohort (h:NextTo F σ C):Cohort F:=by
 intro b x
 let c(i:Fin n):=((x i).1,(x i).2.1);let z(i:Fin n):=(x i).2.2
 exact (h z).same b c

theorem Ferry (I:Type)(n:ℕ)(hn:2≤n)(σ:ℝ)(hσ:0<σ):∃ θ K:ℝ,0<θ∧θ≤σ∧0≤K∧
 ∀ C:ℝ,∀ T:Raw I (n+1), NextTo T σ C →Graded T 1→Closing T→
    ∃ U:Raw I (n+1), NextTo U θ (K*C) ∧ Graded U 2 ∧ picture I (n+1) U=T:=by
 obtain ⟨θ,K,Ht,Hk,H,Hf⟩:=multi (V:=ℝ) n hn σ hσ
 refine ⟨θ,K,Ht,Hk,H,fun C T hP hG hC=>?_⟩
 choose f hp he hF using (fun y=> Hf C (hum T y) (hP y) (fun i=>⟨hG y i,hC y i⟩))
 use joinC f
 refine ⟨hp,fun y j=>hF y j,?_⟩
 rw [← hum_back (picture I (n+1) (joinC f)),←hum_back T];congr 1
 funext y;rw [picture,patch_eval,he y];rfl
end YM.RG08.Rudder
