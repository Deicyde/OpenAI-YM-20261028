import YM.AnalyticNext.CUBIC_MATCH.Motions
import YM.AnalyticNext.CUBIC_MATCH.Rays
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Differences
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post

set_option warningAsError false

/-!
# Ward identities at the first unmatched order

Real derivatives. Here symmetries that may not keep the actual Forest or a
particular stationary representative fixed are not a problem; move arbitrary
full-log curves and then invoke the priced horizontal comparison. Gauge,
orbit and slot assertions are on the *total translated action*, not on an
untransported density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function RG Precision Wilson Lattice Exterior Bid Tree Work.F03 Work.F05
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {c f n : Side} {S : StepData c f}

section maps

def rotate (s : Signed) : Dir G n →L[ℝ] Dir G n :=
    LinearMap.toContinuousLinearMap
      { toFun := fun v => pulled v s
        map_add' := fun x y => by
          funext i; simp only [pulled,Pi.add_apply]; split <;> abel
        map_smul' := fun t x => by
          funext i; change pulled (t • x) s i = t • pulled x s i; simp only [pulled,Pi.smul_apply]; split <;> simp only [smul_neg] }

lemma rotates (s : Signed) (x : Dir G n) : represent (rotate s x) = pull s 0 (represent x) := by
  simpa only [one_smul] using! (represent_pulled s x 1).symm



def recolor (u : G.El) (r : ℕ) : fieldDir G n r →L[ℝ] fieldDir G n r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => G.adjoint u (x i)
      map_add' := fun x y => by ext1 i; simp only [Pi.add_apply,map_add]
      map_smul' := fun t x => by ext1 i; simp [map_smul] }

lemma recolor_one (u : G.El) (x : Dir G n) :
    represent (recolor u 1 x) = gauge (fun _ => u) (represent x) := by
  funext i
  apply G.mat_injective
  simp only [Lattice.gauge,G.mat_mul,G.mat_inv,represent_link]
  change G.mat (G.lieExp (G.adjoint u _))=_
  rw [G.mat_lieExp,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl









lemma root_identity (n : Side) (G : Gauge) :
    Lattice.gauge (fun _ => 1) (1:Config G n)=1 := gauge_trivial _











end maps

abbrev value (B : Forest S.ratio) (t : S.Choices) (p : Clip) (P : PathData G)
    (ρ : Dir G c → AxisChart G B) (u : Dir G c) := tested B t p P u (ρ u)

/-- Ward check for functions in external log coordinates. `shifted` is a
third-order condition along genuine curved trajectories in the group. -/
structure Checks (p : Side) (A : Dir G p → ℝ) : Prop where
  analytic : ContDiffAt ℝ ω A 0
  shifted (u : fieldDir G p 0) (x : Dir G p) :
    term 3 (fun t : ℝ => A (logged (gauge (rootTurn u t) (represent (t • x))))) =
      term 3 (fun t : ℝ => A (t • x))
  color (u : G.El) (x : Dir G p) :
    term 3 (fun t : ℝ => A (recolor u 1 (t • x)))= term 3 (fun t : ℝ => A (t • x))
  rotated (u : Signed) (x : Dir G p) :
    term 3 (fun t : ℝ => A (rotate u (t • x)))= term 3 (fun t : ℝ => A (t • x))

lemma checksRead (A : Config G n → ℝ) (ha : ContDiffAt ℝ ω (fun x : Dir G n => A (represent x)) 0)
    (hg : ∀ u U, A (gauge u U)=A U) (hs : ∀ s U, A (pull s 0 U)=A U) :
    Checks n (fun x : Dir G n => A (represent x)) := by
  constructor
  · exact ha
  · intro u x
    let F := fun t : ℝ => gauge (rootTurn u t) (represent (t • x))
    have he : F 0=1 := by
      unfold F; rw [turn_zero,zero_smul,Precision.link_one]; exact root_identity _ _
    have hh := read_logged he (fun i => gauged_smooth (u:=fun t : ℝ => t • x) (by fun_prop) (turn_smooth u (v:=id) contDiffAt_id) i)
    apply term_congr; filter_upwards [hh] with t ht
    exact (congr_arg A ht).trans (hg _ _)
  · intro u x; simp_rw [recolor_one,hg]
  intro u x; simp_rw [rotates,hs]

section motion
variable {t : S.Choices} {p : Clip} {σ C Λ η} {P : PathData G} {B : Forest S.ratio} {D : Bed}
  {ρ : Dir G c → AxisChart G B} (h : S.patch.Branches S.kernel G) (hb : P.Bounds p σ C Λ)
  (hc : Critical B p P ρ) (hp : Comptroller B D p P)

include h hb hc hp







/-- Log curve from stationary tangent, never uses independence from choices. -/
def sline (B : Forest S.ratio) (ρ : Dir G c → AxisChart G B) (x : Dir G c) (s : ℝ) :=
    s • fderiv ℝ (inclusion B (G:=G)) 0 (x,fderiv ℝ ρ 0 x)

omit h hb hc hp in
lemma sline_fst (x : Dir G c) (s : ℝ) : (sline B ρ x s).1=s • x := by
  unfold sline; rw [inclusion_deriv]; rfl


variable (hη : 0 < η) (hg : PriceGap B p P η)
include hη hg








end motion

/-- Turn orbit invariance into a multilinear assertion ready to read on
coordinate-delta probes. -/
lemma rotate_tensor {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} (k : ℕ)
    (L : E →L[ℝ] E) (h : ContDiffAt ℝ k f 0) (he : ∀ x, term k (fun t : ℝ => f (L (t • x))) =
      term k (fun t : ℝ => f (t • x))) (x : Fin k → E) :
    Tensor.coeff f k 0 (fun i => L (x i)) = Tensor.coeff f k 0 x := by
  have ht : ContDiffAt ℝ k f (L 0) := (map_zero L).symm ▸ h
  have hg := ht.comp (f:=L) _ L.contDiff.contDiffAt
  have hh : Tensor.coeff (f ∘ L) k 0 = Tensor.coeff f k 0 :=
    Tensor.ext_diag _ _ (Tensor.coeff_symm hg) (Tensor.coeff_symm h)
      (funext fun i => (term_ray hg _).symm.trans ((he i).trans (term_ray h i)))
  conv_rhs => rw [← hh]
  simp only [Tensor.coeff, smul_apply, jet_comp_linear L ht, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

lemma killed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Tensor.T E ℝ 3}
    {v : E} (h : Tensor.Sym A) (hv : ∀ x (t : ℝ), Tensor.diagonal A (x+t • v)=Tensor.diagonal A x) :
    A.curryLeft v = 0 := by
  have hs : Tensor.Sym (A.curryLeft v) := Tensor.freeze_sym _ h v
  apply Tensor.ext_diag _ _ hs (show Tensor.Sym _ from fun x s => rfl)
  funext y
  have hx : HasDerivAt (Tensor.diagonal A ∘ fun t : ℝ => y+t • v) 0 0 := by
    rw [show (Tensor.diagonal A ∘ fun t : ℝ => y+t • v)=(fun _ => Tensor.diagonal A y) from funext (hv y)]
    exact hasDerivAt_const _ _
  have he : HasDerivAt (fun t : ℝ => y+t • v) v 0 := by
    simpa using! (((hasDerivAt_id' (0:ℝ)).smul_const v).const_add y)
  have hz : ContDiffAt ℝ ω (Tensor.diagonal A) (y+(0:ℝ)•v) := (Tensor.diag_smooth ..).contDiffAt
  have hh := ((hz.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 he).unique hx
  rw [zero_smul,add_zero,Tensor.differential_diagonal _ h] at hh
  change A.curryLeft v (fun _ => y)=0; simpa [nsmul_eq_mul] using hh

namespace Checks
variable {A R : Dir G n → ℝ}
lemma inherited (h : Checks n A) (hr : Checks n R) : Checks n (A-R) := by
  have hx (x : Dir G n) : ContDiffAt ℝ ω (fun i : ℝ => i • x) 0 := by fun_prop
  have hh (x : Dir G n) {L : ℝ → Dir G n} (H : L 0=0) (hL : ContDiffAt ℝ ω L 0)
      (Ha : term 3 (fun i => A (L i)) = term 3 (fun i : ℝ => A (i • x)))
      (Hr : term 3 (fun i => R (L i)) = term 3 (fun i : ℝ => R (i • x))) :
      term 3 (fun i => (A-R) (L i))=term 3 (fun i : ℝ => (A-R) (i • x)) := by
    have he (f : ℝ → Dir G n) (hp : ContDiffAt ℝ ω f 0) (Hf : f 0=0) :
        term 3 (fun i => (A-R) (f i))=term 3 (fun i => A (f i))-term 3 (fun i => R (f i)) := by
      simp only [Pi.sub_apply]
      exact term_sub ((((show ContDiffAt ℝ ω A (f 0) from Hf.symm ▸ h.analytic).comp _ hp)).of_le le_top)
        ((((show ContDiffAt ℝ ω R (f 0) from Hf.symm ▸ hr.analytic).comp _ hp)).of_le le_top)
    exact (he L hL H).trans ((congr_arg₂ (·-·) Ha Hr).trans (he _ (hx x) (zero_smul _ _)).symm)
  constructor
  · exact h.analytic.sub hr.analytic
  · intro u x
    let V := fun t : ℝ => Lattice.gauge (rootTurn u t) (represent (t • x))
    have h0 : V 0=1 := by unfold V; rw [turn_zero,zero_smul,Precision.link_one]; exact root_identity _ _
    exact hh x (L:=fun t => logged (V t)) (by simp only [h0,logged_zero])
      (logged_smooth h0 (fun i => gauged_smooth (hx x) (turn_smooth u (v:=id) contDiffAt_id) i))
      (h.shifted u x) (hr.shifted u x)
  · intro t x
    exact hh x (by simp) ((recolor (n:=n) t 1).contDiff.contDiffAt.comp _ (hx x)) (h.color t x) (hr.color t x)
  intro s x
  exact hh x (by simp) ((rotate (n:=n) (G:=G) s).contDiff.contDiffAt.comp _ (hx x)) (h.rotated s x) (hr.rotated s x)

open Matrix in
lemma horizontal_tensor (h : Checks n A) (h₁ : fderiv ℝ A 0=0) (h₂ : iteratedFDeriv ℝ 2 A 0=0)
    (u : fieldDir G n 0) : (Tensor.coeff A 3 0).curryLeft (dColor G n 0 u)=0 := by
  refine killed (Tensor.coeff_symm (h.analytic.of_le le_top)) (fun x t => ?_)
  let g (s : ℝ) := gauge (rootTurn (t • u) s) (represent (s • x))
  have hp : g 0=1 := by unfold g; rw [turn_zero,zero_smul,Precision.link_one]; exact root_identity _ _
  have hv : ContDiffAt ℝ ω (logged ∘ g) 0 := logged_smooth hp
    (fun i => gauged_smooth (u:=fun s : ℝ => s • x) (by fun_prop) (turn_smooth (t • u) (v:=id) contDiffAt_id) i)
  have hh := term_three_of_lowNull (f:=A) (a:=logged ∘ g) (by simp only [Function.comp_apply,hp,logged_zero])
    (h.analytic.of_le le_top) (hv.of_le le_top) h₁ h₂
  have hx : dColor G n 0 (t • u) = t • dColor G n 0 u := by
    funext i
    ext j
    change (d _ n *ᵥ parts G 0 (t • u) j) i=t*(d _ n *ᵥ parts G 0 u j) i
    rw [show parts G 0 (t • u) j=t • parts G 0 u j from rfl, Matrix.mulVec_smul]; rfl
  rw [show deriv (logged ∘ g) 0 = x+dColor G n 0 (t • u) from (turns_through x (t • u)).deriv,hx] at hh
  exact hh.symm.trans ((h.shifted (t • u) x).trans (term_ray (h.analytic.of_le le_top) x))

lemma colored_tensor (h : Checks n A) (u : G.El) (x : Fin 3 → Dir G n) :
    Tensor.coeff A 3 0 (fun i => recolor u 1 (x i)) = Tensor.coeff A 3 0 x :=
  rotate_tensor _ _ (h.analytic.of_le le_top) (h.color u) _

end Checks
end YM.CubicMatch
