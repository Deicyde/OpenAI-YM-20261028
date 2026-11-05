import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Aperture
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Taps

/-!
# Through n dry line meters

Normalize up front. E and signal comparison while direction in true coords
(not suppress outputs of long sign rotation). `feed` purchases below. No
θ schedules changed. Keep monotone toward post-L payments. In absence of
Drills D jets one cannot reapply sector-affine Polar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}

section spring
variable {ι κ : Type} [Fintype ι] [Fintype κ] {b : Directions G c} {a : ι → Site c} {e : κ → Site c} {d v : ℝ}
open FreeResolvent (native Mark)
lemma rayD {K : PriceCoords G c→ Matrix ι κ ℝ} {n : ℕ} (i : ι) (j : κ) (h : Polar (reader G c b) a e K n d v) (hd : 0<d) (hv : 0 ≤ v) :
    Brush n (activation G n 0 d *v) 1 (fun x=>K (reader G c x) i j) b := by
  have he:= Polar.weighted 0 h hd hv; let z:= activation G n 0 d*v
  let E := FreeResolvent.TestD.evaluate i j
  have hp : tape (reader G c b)= b := rfl
  have hk := he.smooth; rw [hp] at hk
  have hx := E.contDiff.contDiffAt.comp (f:=cart K) b hk
  refine ⟨hx,zero_le_one,fun l hl=> Planned.AtomRegular.op_le_of_unit ?_ (fun w hw=> ?_)⟩
  · exact mul_nonneg (mul_nonneg (zero_le_one.trans (activation_one G n 0 hd)) hv) (by positivity)
  rw [one_pow,mul_one]
  let l':= List.ofFn w
  have hh: Afford 1 0 (0:Site c) l' := by
    unfold Afford l'; rw [List.forall_mem_ofFn_iff]; intro i j; simp [Mark.hill]; exact (norm_le_pi_norm ..).trans (hw _)
  have hs:= (he.each (0:Site c) zero_le_one l' (List.length_ofFn.trans_le hl) hh).row.rows i
  rw [hp,Mark.payment] at hs
  simp only [Mark.hill,pow_zero,one_pow,inv_one,mul_one,one_mul, l',FreeResolvent.Stars.list_result,id_comp] at hs
  change ‖(iteratedFDeriv ℝ l (E ∘ cart K) b) w‖ ≤ z
  have hy : iteratedFDeriv ℝ l (E ∘ cart K) b w = (iteratedFDeriv ℝ l (cart K) b w) i j := by
    exact congr_arg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin l=> Directions G c) ℝ=> T w) (E.iteratedFDeriv_comp_left (i:=l) hk (Nat.cast_le.mpr hl))
  rw [hy]
  let m:= iteratedFDeriv ℝ l (cart K) b w
  change ‖m i j‖≤z; change (∑ j,(native c).weight d (a i) (e j)*|m i j|) ≤ z at hs
  have hr : 1≤(native c).weight d (a i) (e j) := Real.one_le_exp (show 0 ≤ d*separation (a i) (e j) by positivity)
  rw [Real.norm_eq_abs]
  exact (le_mul_of_one_le_left (abs_nonneg _) hr).trans ((Finset.single_le_sum (s:=Finset.univ) (a:=j)
    (fun j _=>mul_nonneg ((native c).weight_nn d (a i) (e j)) (abs_nonneg (m i j))) (Finset.mem_univ j)).trans hs)
end spring
section issuance
variable {L : Side} {η r Q V Y M d v K s l t : ℝ} {m j : ℕ}
  (X : Coat T F) (h : P.Funds S T)
variable (hb : Allow X.blank.plate (along S) m η r Q) (hK : KernelJets j d v s l M (bareStores S) F T X.x 1 X.k 0)
    (hk : 1 ≤ j) (hd : 0<d) (hM : 0 ≤ M)

abbrev Polish := fderiv ℝ (forecast T X.x F X.k-study X) 0
include h hb hK hk hd hM
lemma tilt0 (hW : Click (drills X)) (hD : Click (mine X)) (hZ : DifferentiableAt ℝ (receipt X) 0)
    (hp : ‖fderiv ℝ (ore X) 0‖≤K) :
    ‖Polish X‖ ≤ missPay η r Q v M m X.B * K := by
  have ho : KernelJets j d v s l M (bareStores S) F T X.x 1 X.k (reader G c 0) := by rw [map_zero]; exact hK
  have ht:= (ho.windowJets 0 le_rfl).polar hM le_rfl; simp only [FreeResolvent.TestD.drain,add_zero,inv_one,mul_one] at ht
  have hr : Click (looks X) := fun i l=> ((rayD i l ht hd hM).smaller hk).smooth.differentiableAt (by simp)
  have hv : Click (rake X) := fun i l=> ((rayD i l ho.moves hd hM).smaller hk).smooth.differentiableAt (by simp)
  have hl : DifferentiableAt ℝ (paint X) 0 := by
    refine differentiableAt_pi.mpr fun i=> ?_; simp_rw [receive X h]
    split
    next hz => exact differentiableAt_pi.mp hZ i
    exact differentiableAt_const _
  let μ := missPay η r Q v M m X.B; have he : 0 ≤ μ := add_nonneg (mul_nonneg hb.disc (hb.heap _)) (mul_nonneg hM (Real.exp_pos _).le)
  have hx := (darkness X h hb hK hd).2
  let J := ((drills X 0).submatrix (tube X) (tube X)-looks X 0)ᵀ; have ha:= (norm_nonneg _).trans hp
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg he ha) ?_
  intro u; simp only [Polish]; change ‖meter (forecast T X.x F X.k-study X) u‖ ≤ _
  have hd := angle X h hW hD hZ hr hv hl u
  rw [hd,← matchesP X h hD hZ u hv hl, mul_assoc]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg he (mul_nonneg ha (norm_nonneg u)))).mpr
  intro i; rw [Real.norm_eq_abs]; refine ticket_local J i (pure_pay hx le_rfl i) _ (fun j _=> ?_) (mul_nonneg ha (norm_nonneg _))
  exact ((norm_le_pi_norm (meter (ore X) u) (tube X j)).trans (le_trans (ContinuousLinearMap.le_opNorm ..) (mul_le_mul_of_nonneg_right hp (norm_nonneg _))))
end issuance
end YM.PhysicalNext.Repeat.Malachite
