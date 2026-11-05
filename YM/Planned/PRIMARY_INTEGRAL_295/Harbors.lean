import YM.Planned.PRIMARY_INTEGRAL_295.Moulin

/-!
# D-costs for one actual rooted v.Bond all orientations

Use branch authority with kept-root input log in `Hollow G c f`.
Neighborhood for v *unscaled* as supplied by Honey.binning.
Log right trivial derivative independent of transports elsewhere. Burn
assertion exact support.Q anchor. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Harbors
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform Honey Drupes Density Mowing Festoons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {k n : ℕ} {c f : Side} {S:StepData c f}

section
variable (G:Gauge) (n:ℕ) (P:Patch)(Q:KernelChoices)

private lemma single_log :∃ C:ℝ,1≤C ∧ Allows n G.plog 1 C:=by
   let C:= 1+∑ i∈ Finset.range (n+1), ‖iteratedFDeriv ℝ i G.plog 1‖
   have hp:1≤C:=le_add_of_nonneg_right (by positivity)
   refine ⟨C,hp,G.plog_diff,fun i hi=>?_⟩
   apply le_trans (Finset.single_le_sum (fun i (_:i∈Finset.range (n+1))=> norm_nonneg (iteratedFDeriv ℝ i G.plog 1))
     (show i∈Finset.range (n+1) from Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
   unfold C; linarith

lemma servants (σ:ℝ) (hσ:0<σ):∃ r D:ℝ, 0<r ∧ 1≤D ∧ ∀ c f(S:StepData c f) (K:Core G S), S.kernel=Q→S.patch=P→P.Branches Q G →
   ∀ s:Signed, ∀ (i:Bond c)(j:G.ColorIndex)(e:Acres f G)(x: Dir G c), ‖x‖ ≤ r → let p:=Mowing.dropQ s i j (G:=G) (f:=f); Allows n
      (fun v=>K.D v p e) x (D*Decay σ (origin S p) (chair S e)):=by
  obtain ⟨r,C,hr,hC,hR,h⟩:= binning G (n+1) Q P
  obtain ⟨B,hB,hP⟩:=single_log G (n+1)
  let D:= |-Real.sqrt Q.penalty| * Push.Uniform.composeCost (n+1) B (2^(n+1)*C*C)
  have hD:0≤D:=by unfold D Push.Uniform.composeCost; positivity
  let H:=|ballast| * D
  have hH:0≤H:=by unfold H; positivity
  let L:= Real.exp (σ* ((Next.Fluctuations.predReach P+1:ℕ):ℝ))*H
  refine ⟨r,1+L,hr,le_add_of_nonneg_right (by unfold L; positivity),fun c f S K hk hv hp s i j e x hx=>?_⟩
  intro p
  obtain ⟨rfl⟩:=hk; obtain ⟨rfl⟩:=hv
  let A:=Hollow G c f; let U(y:A):=K.target s y.1 y.2 i; let z:A:=(x,0); let q:=K.jump p.1
  have hc : ‖z‖ ≤ r:= by unfold z; rw [Prod.norm_def]; apply max_le hx; rw [norm_zero]; exact hr.le
  have he: Allows (n+1) (fun y:A=>G.mat (U y)) z C:= h c f S rfl rfl K s i z hc -- explicit
  let V:A→L[ℝ] A:= ContinuousLinearMap.inl ℝ (Dir G c) (Temps G f) ∘L ContinuousLinearMap.fst ..
  have ht : ‖V‖≤1:=by apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one; intro x hx; change max ‖x.1‖ ‖(0:Temps G f)‖≤ _; rw [norm_zero]; exact max_le ((norm_fst_le _).trans hx.le) zero_le_one
  let f(y:A):= G.mat (U y*(U (V y))⁻¹)
  have hm: V z=z:=rfl
  have hf: Allows (n+1) f z (2^(n+1)*C*C):= he.times ((pulse_left V (f:=fun y=>G.mat (U y)) (show Allows _ _ (V z) _ from hm.symm ▸ he) ht).inverse (f:=U ∘ V))
  have hq: Allows (n+1) (Function.uncurry q) z D:= by
     have he:f z=1:=by unfold f; rw [hm,mul_inv_cancel,G.mat_one]
     exact ((show Allows (n+1) G.plog (f z) B from he.symm ▸ hP).comp hf).smul (-Real.sqrt S.kernel.penalty)
  let g:=Mowing.shot q e j
  have hh: Allows n g x H:= Moulin.stinted (Function.uncurry q) _ (Pi.single e (1:ℝ)) (by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; by_cases h:i=e <;> simp [h]) j hq
  set t:=Decay σ (origin S p) (chair S e)
  refine (show Allows n _ x (L*t) from Moulin.catapult x hH hσ hh (r:=Next.Fluctuations.predReach S.patch+1) (fun hi=> funext (fun v=>Mowing.focus s K v e i j hp hi))).mono ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (decay_pos ..).le
end
end YM.Planned.PrimaryIntegral295.Harbors
