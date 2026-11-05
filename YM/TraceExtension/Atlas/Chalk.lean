import YM.Work.A13
import YM.Work.A14
import YM.TraceExtension.Centered
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Set Filter Analysis Table
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
section
variable {E E' : Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
end
variable {E E' : Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
variable {G : Gauge}{L:Register G}{S:Table L}{d:ℕ}
private lemma parameter_add (K : Ortho.Skew) (s t : ℝ) :
    Ortho.oneParameter K (s+t) = Ortho.oneParameter K s * Ortho.oneParameter K t := by
  apply Subtype.ext
  haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  change NormedSpace.exp ((s+t) • K.val) =
    NormedSpace.exp (s • K.val) * NormedSpace.exp (t • K.val)
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl K.val).smul_left s).smul_right t)

def circle {R : Rotation S} {H:S.RealSpin} (h: Spin.Port R H) (U:E≃ₗ[ℂ] S.Field d) : Ortho →* (E →L[ℂ] E) where
   toFun s := LinearMap.toContinuousLinearMap (U.symm.toLinearMap.comp ((R.act _ s).comp U.toLinearMap))
   map_one' := ContinuousLinearMap.ext fun v=> by change U.symm (R.act _ _ _)=v; rw[h.fixes]; exact U.symm_apply_apply v
   map_mul' := fun s t=> ContinuousLinearMap.ext fun v=>by change U.symm (R.act _ (s*t) _)=U.symm (R.act _ s (U (U.symm _))); rw[h.sends,U.apply_symm_apply]; rfl

def cog {R : Rotation S} {H:S.RealSpin} (_h: Spin.Port R H) (U:E≃ₗ[ℂ] S.Field d) : Ortho.Skew → (E →L[ℂ] E) := fun s=> LinearMap.toContinuousLinearMap (U.symm.toLinearMap.comp ((R.lie _ s).comp U.toLinearMap))

-- vector derivation on transport for ℝ action. use restrict scalars: normedℂ not Automatically std
variable [NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
lemma passing [CompleteSpace E] {R : Rotation S} {H : S.RealSpin} (h: Spin.Port R H)(U:E≃ₗ[ℂ] S.Field d) (p: Ortho.Skew)(t:ℝ): (circle h U (Ortho.oneParameter p t)).restrictScalars ℝ=NormedSpace.exp (t • (cog h U p).restrictScalars ℝ):=by
    let f:=circle h U;let g:=Ortho.oneParameter p;let c:= cog h U p
    ext1 x
    have he:g 0=1:=Work.A13.oneParameter_zero p
    let A(t:ℝ):= f (g t) x
    have hA(s): HasDerivAt A (c (A s)) s:=by
       let v:= f (g s) x;let W(t:ℝ):= f (g t) v
       have hW:HasDerivAt W (c v) 0:= ((LinearMap.toContinuousLinearMap U.symm.toLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (h.spinAt _ p (U v))
       have hh : HasDerivAt (fun r : ℝ=> r-s) 1 s:= (hasDerivAt_id s).sub_const s; have hx:= hW.scomp_of_eq s hh (by simp)
       rw[one_smul,show W ∘ (fun r:ℝ=>r-s)=A from ?_] at hx; exact hx
       ext1 i; unfold W; change (f (g (i-s))*f (g s)) x= _;rw [← f.map_mul,← parameter_add, sub_add_cancel]
    let V(t:ℝ):= NormedSpace.exp (t • (c.restrictScalars ℝ)) x
    have ht(u): HasDerivAt V (c (V u)) u:= (ContinuousLinearMap.apply ℝ E x).hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_exp_smul_const' (c.restrictScalars ℝ) u)
    have hp:A=V:= ODE_solution_unique_univ (f:=A) (g:=V) (s:=fun _=>univ) (fun (_:ℝ)=> c.lipschitz.lipschitzOnWith) (fun t=> ⟨hA t, mem_univ _⟩) (fun t=> ⟨ht t,mem_univ _⟩) (show A 0=V 0 from by simp[A,V,he])
    exact congr_fun hp t
lemma raygo [CompleteSpace E]{R:Rotation S}{H:S.RealSpin}(h:Spin.Port R H) {L':Register G}{S':Table L'}{R':Rotation S'}{H':S'.RealSpin}(hr:Spin.Port R' H')(M:ℕ→ (E≃ₗ[ℂ] S.Field d))(U:E≃ₗ[ℂ] S'.Field d)(u:Ortho.Skew)(t:ℝ)(v:E)
    (hx:Tendsto (fun i=> cog h (M i) u) atTop (𝓝 (cog hr U u))): Tendsto (fun i=> circle h (M i) (Ortho.oneParameter u t) v) atTop (𝓝 (circle hr U (Ortho.oneParameter u t) v)):=by
    let C:E→L[ℝ] E := (cog hr U u).restrictScalars ℝ; let a(i):= (cog h (M i) u).restrictScalars ℝ;let k:= Ortho.oneParameter u t
    have hu:Tendsto a atTop (𝓝 C):= (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).continuous.continuousAt.tendsto.comp hx
    letI : NormedAlgebra ℚ (E→L[ℝ] E):= NormedAlgebra.restrictScalars ℚ ℝ _
    have hh := (NormedSpace.exp_continuous (𝔸:=E→L[ℝ] E)).continuousAt.tendsto.comp (Tendsto.const_smul hu t)
    change Tendsto _ _ (𝓝 (circle hr U k v)); rw [show circle hr U k v=NormedSpace.exp (t • C) v from congr_arg (fun x:E→L[ℝ] E=> x v) (passing hr U u t)]
    exact (((ContinuousLinearMap.apply ℝ E v).continuous.continuousAt.tendsto).comp hh).congr (fun i=> (congr_arg (fun x:E→L[ℝ] E=> x v) (passing h (M i) u t)).symm)
-- note comparators register different L! add L'.
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma inv_way [CompleteSpace E](f:ℕ→ Ortho →* (E→L[ℂ] E))(w:Ortho→* (E→L[ℂ] E))(u:Ortho)(h:Tendsto (fun i=>f i u) atTop (𝓝 (w u))): Tendsto (fun i=>f i u⁻¹) atTop (𝓝 (w u⁻¹)):=by
    have he(g:Ortho)(P:Ortho→* (E→L[ℂ] E)): IsUnit (P g):=⟨⟨P g,P g⁻¹,by rw [← map_mul,mul_inv_cancel,map_one],by rw [← map_mul,inv_mul_cancel,map_one]⟩,rfl⟩
    have ht(g:Ortho)(P:Ortho→* (E→L[ℂ] E)): Ring.inverse (P g) = P g⁻¹:=by
        apply (he g P).mul_right_inj.mp
        rw [Ring.mul_inverse_cancel,← map_mul,mul_inv_cancel,map_one]; exact he g P
    simp_rw [← ht]; obtain ⟨x,hx⟩:= he u w; exact ((show ContinuousAt Ring.inverse (w u) from hx ▸ NormedRing.inverse_continuousAt x).tendsto).comp h
end YM.Trace.Pilot
