import YM.UVExtension.Lamppost.Parade

/-!
# Four real probes, the dense complex structure, and bounded-spread continuation

Finite charts only! The normed test holder needs the completion. Real input
is concrete linear data with a linear read. Null space allowed. Don't assume
functions on concrete real data are well-defined on its completed holder. Get
agreement from the probes. In particular derivative terms defined patchwise
on configurations need not themselves extend in the configuration variable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Oriel
open Function Filter Set Metric Lamppost
open scoped BigOperators Topology ContDiff Classical
variable {X Y R : Type} [AddCommGroup R] [Module ℝ R]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
variable (L:R→ₗ[ℝ] X)
-- joint real coords incl normalized tuning along radii. Costs small.
abbrev radiusU : ℝ:=1/128
abbrev shieldB := Courtyard (ι:=Fin 4) (fun _=> ball 0 3)
abbrev pocket : ℝ:= 1/256
abbrev traceB : ℝ:= 1/16384
abbrev rim : ℝ :=1/131072
abbrev Plot₀ := Plot (Fin 4)
def tick (v:Fin 4→ R) (x:Fin 4→ℝ):= ∑ i,x i • v i
def tock (v:Fin 4→ R) (z:Plot₀) := ∑ i,z i • L (v i)
def paint (L:R→ₗ[ℝ] X) (x:X) : Prop:= ∃ a b,x=L a + Complex.I • L b
-- simple actual complexification; not asking bounds on extension outside closure of complex span
structure Firm : Prop where
    ink (x y : R) : let z:= L x+ Complex.I • L y; ‖L x‖ ≤ ‖z‖∧ ‖L y‖ ≤ ‖z‖
    runs : Dense {x|paint L x}

lemma rsmul (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X] (k:ℝ)(x:X): (k:ℂ) • x=k • x:= by rw [show (k:ℂ)=k • (1:ℂ) by simp, smul_assoc,one_smul]
lemma tone (c:ℂ)(x:X) : c • x=c.re • x+Complex.I • (c.im • x) :=by
  rw [← rsmul X, ← rsmul X,_root_.smul_smul, mul_comm Complex.I, ← add_smul, Complex.re_add_im]
lemma characters (v:Fin 4→R)(z:Plot₀) :tock L v z=L (tick v fun i=> (z i).re) + Complex.I • L (tick v fun i=> (z i).im):= by
  unfold tock tick
  simp only [map_sum,map_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; exact tone _ _
lemma splits (h:Firm L)(v w: Fin 4→ R)(z z':Plot₀)(hx:tock L v z=tock L w z') :
    L (tick v fun i=> (z i).re)=L (tick w fun i=> (z' i).re) ∧ L (tick v fun i=> (z i).im)=L (tick w fun i=> (z' i).im):= by
  rw [characters,characters] at hx
  generalize Lx : tick v (fun i=>(z i).re)=x, Gx:tick w (fun i=>(z' i).re)=u, Ly:tick v (fun i=>(z i).im)=y, Gy:tick w (fun i=>(z' i).im)=p at hx ⊢
  have hp : L (x-u)+Complex.I • L (y-p)=0:=by rw [map_sub,map_sub,smul_sub]; rw [show L x-L u+(Complex.I • L y-Complex.I • L p)=L x+Complex.I • L y -(L u+Complex.I • L p) by abel,hx,sub_self]
  obtain ⟨ht,he⟩:= h.ink (x-u) (y-p); rw [hp,norm_zero,map_sub] at ht he; exact ⟨sub_eq_zero.mp (norm_le_zero_iff.mp ht),sub_eq_zero.mp (norm_le_zero_iff.mp he)⟩

structure Reel (f:R→Y) (M : ℝ) (v:Fin 4→R) where
    F : Plot₀ → Y
    score : Bumps shieldB F
    bound z (h:z∈shieldB) : ‖F z‖ ≤ M
    ear (x:Fin 4→ℝ)(h:∀ i, |x i| < radiusU): F (Lamppost.hoist x)=f (tick v x)
structure Charted (f:R→Y) (M:ℝ): Prop where
    spins (v:Fin 4→ R) : (∀ i,‖L (v i)‖≤1) → Nonempty (Reel f M v)

open Complex
variable {f : R→Y} {M : ℝ}
lemma diary (f:ℂ→Y)(h:DifferentiableOn ℂ f (ball 0 3))(hp:∀ z∈ ball (0:ℂ) 3, ‖f z‖≤M) {x:ℂ}(hx : ‖x‖<1) : ‖f x-f 0‖≤ M*‖x‖:=by
  rw [show M*‖x‖=M*‖x-(0:ℂ)‖ by simp]; let s:= ball (0:ℂ) 1
  have ht:s⊆ball 0 3:= ball_subset_ball (by norm_num)
  apply (convex_ball (0:ℂ) 1).norm_image_sub_le_of_norm_deriv_le (fun z hz=> h.differentiableAt (isOpen_ball.mem_nhds (ht hz))) _ (mem_ball_self one_pos) (mem_ball_zero_iff.mpr hx)
  intro z hz; have hh :closedBall z 1 ⊆ ball 0 3:= fun w hw=> mem_ball.mpr (by linarith only [mem_ball.mp hz,mem_closedBall.mp hw, dist_triangle w z 0])
  rw [← cderiv_eq_deriv isOpen_ball h one_pos hh]
  simpa only [div_one] using norm_cderiv_le one_pos (fun x hx=>hp x (hh (sphere_subset_closedBall hx)))

variable (h:Charted L f M)
include h
omit [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X] in
lemma blank (x y:R)(ht:‖L x‖ ≤ pocket)(he:L x=L y): f x=f y:=by
  suffices hv: ∀ t:ℝ,0<t → t<radiusU → ‖f y-f x‖≤M*t by
    apply Eq.symm; apply sub_eq_zero.mp
    apply norm_le_zero_iff.mp; refine le_of_tendsto_of_tendsto (f:=fun _:ℝ=>‖f y-f x‖) (b:=𝓝[>]0) tendsto_const_nhds (g:=fun t:ℝ=>M*t) ?_ ?_ -- arguments verify
    · exact (show Continuous (fun t:ℝ=>M*t) by fun_prop).continuousWithinAt (x:=0) |>.tendsto.congr' (EventuallyEq.rfl) |>.mono_right (le_of_eq (by simp))
    filter_upwards [self_mem_nhdsWithin,(nhdsWithin_le_nhds (s:=Ioi 0) (a:=(0:ℝ))) (gt_mem_nhds (show (0:ℝ)<radiusU from (by norm_num [radiusU])))] with t ht hs; exact hv t ht hs
  intro t hT hp; let v:= ![pocket⁻¹ • x,t⁻¹ • (y-x), (0:R), 0]
  have hh:0<pocket:=by norm_num [pocket]
  obtain ⟨F⟩:= h.spins v (fun i => by fin_cases i <;> simp [v,← he,norm_smul]; unfold pocket at ht; linarith)
  let g (z:ℂ):Plot₀:= ![(pocket:ℂ),z,0,0]; have hF:MapsTo g (ball 0 3) shieldB:=by intro z hz; apply within.mpr; intro i; fin_cases i <;> norm_num [g,pocket, mem_ball_zero_iff,Complex.norm_real] at hz ⊢ ; assumption
  have hz:= F.score _ g isOpen_ball hF (differentiable_pi.mpr (fun i=>by fin_cases i <;> simp [g])|>.differentiableOn)
  let r:=![pocket,t,(0:ℝ),0]; let r':=![pocket,0,(0:ℝ),0]
  have hg: F.F (g ↑t)=f y:= by
    rw [show g ↑t=hoist r by ext i; fin_cases i <;> simp [r,g,hoist], F.ear r (by intro i; fin_cases i <;> norm_num [r,abs_of_pos hT,pocket,radiusU] at hp ⊢; assumption)]
    unfold tick; simp [Fin.sum_univ_succ,r,v,hT.ne']

  have hg':F.F (g 0)=f x:= by
    rw [show g 0=hoist r' by ext i; fin_cases i <;> simp [r',g,hoist],F.ear r' (by intro i; fin_cases i <;> norm_num [r',pocket,radiusU])]; unfold tick; simp [Fin.sum_univ_succ,r',v]
  have he' : ‖(t:ℂ)‖=t:= (norm_real t).trans (Real.norm_of_nonneg hT.le)
  have hh := diary _ hz (fun z hz=> F.bound _ (hF hz)) (x:=↑t) (he'.trans_lt (hp.trans (by norm_num [radiusU]))); rw [he',hg,hg'] at hh; exact hh
end YM.UVExtension.Oriel
