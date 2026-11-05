import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Largo

/-! # All through total order k extra profile/rank costs of Ξ and Γ

First-entry upgrade of the parent h ticket; the latter is still earned
ELSEWHERE. Spend at the tilted motion currency of the REAL field even
when W projects to several syllables iterating over the same slot, of Gaussian-held
or poured. The tiny physical normalization at these *post*-L guards pays
for converting even the highest derivative (takes a (1/k)-power in each
radius before summing at this rank). No enlargement of `motionBill` or
`M.royalty` needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure ProjectorNext.Equivariance Heir AnalyticBridge.LocalGaussian Extra.Iteration
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {d : Desk G S}
    {I : Type} [Fintype I] {X : Support f} {Y : Support c} {n : ℕ} {D : Record} {Q M r t : ℝ}
    {V : Config G c} {h : Config G c → G.Color} {test : Directions G c → Prop}

abbrev toHue (G : Gauge) := (WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap
private lemma scaled_charge (hM : 1≤M) (hQ : 0≤Q) (ht : 0 < t) (hc : ‖toHue G‖ ≤ Q) (hv : M^n * Q ≤ t)
    (hr : 0 ≤ r) (h : Config G c → G.Color) (he : ∀ i, Charge test n V r (fun W => h W i)) : Charge test n V (r/M) (fun W => t⁻¹ • h W) := by
  let y (V : Config G c) (i : G.ColorIndex) := h V i; let L := t⁻¹ • toHue G
  have hh : HasOrderAt y V n := contDiffAt_pi.mpr fun i => (he i).smooth
  change Charge test n V (r/M) (L ∘ y)
  refine ⟨L.contDiff.contDiffAt.comp _ hh,by positivity, fun l hl hl' hA => ?_⟩
  have hq : ‖leftDerivs y l V‖ ≤ r^l.length := by
    apply (pi_norm_le_iff_of_nonneg (pow_nonneg hr _)).mpr; intro i
    rw [show (leftDerivs y l V) i=leftDerivs (fun W => y W i) l V from (linear_parts (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:G.ColorIndex=>ℝ) i) hh hl').symm]; exact (he i).price l hl hl' hA
  change ‖leftDerivs (fun W => L (y W)) l V‖ ≤ _; rw [linear_parts L hh hl']; apply (L.le_opNorm _).trans
  have he : ‖L‖ ≤ Q/t := by unfold L; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le,div_eq_inv_mul]; gcongr
  calc
    _ ≤ (Q/t) * r^l.length := mul_le_mul he hq (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      rw [div_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ ht]; linarith only [mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM hl') hQ).trans hv) (show 0≤r^l.length by positivity)]

def QuietPrice (χ : Chi) (G : Gauge) (n : ℕ) (t : ℝ) := ∀ {c : Side} (V : Config G c) (r : ℝ) (test : Directions G c → Prop)
    (h : Config G c → G.Color), 0 ≤ r → (∀ i, Charge test n V r (fun W => h W i)) →
      Ticket test n V 1 r (broad χ t ∘ h) ∧ Ticket test n V 1 r (1-(broad χ t ∘ h))

private lemma quiet_price (χ : Chi) (G : Gauge) (n : ℕ) (hM : 1 ≤ M) (hQ : 0≤Q) (ht : 0 < t) (hc : ‖toHue G‖ ≤ Q) (hv : ((2+M)*(1+n))^n * Q ≤ t)
    (hh : ∀ x : G.Color, Farewell (broad χ 1) x n M) : QuietPrice χ G n t := by
  intro c V r test f hr he
  let v : ℝ := (2+M)*(1+n); have hv' : 1≤v := by unfold v; nlinarith only [hM,Nat.cast_nonneg (α:=ℝ) n]
  let p := broad χ t ∘ f
  have h := (scaled_charge hv' hQ ht hc (show v^n*Q ≤ t from hv) hr f he).inspect (hh _) (((broad_smooth χ 1).of_le (budgetThrough n)).contDiffAt)
  rw [show (broad χ 1) ∘ (fun W => t⁻¹ • f W)=p by funext W; simpa only [p,Function.comp_apply,smul_inv_smul₀ ht.ne',mul_one] using (broad_scale χ ht 1 (t⁻¹ • f W)).symm] at h
  obtain ⟨hp,hp'⟩ := broad_range χ (f V) t; change 0≤p V at hp; change p V ≤ 1 at hp'
  have hw : (1+(‖(1:ℝ)‖+M))*climbing n (r/v) = r := by unfold climbing v; rw [norm_one]; field_simp; ring
  have hw' : (1+M)*climbing n (r/v) ≤ r := (mul_le_mul_of_nonneg_right (by rw [norm_one]; linarith : 1+M ≤ 1+(‖(1:ℝ)‖+M)) h.radius_nonneg).trans hw.le
  exact ⟨((h.tip.with_one (show ‖p V‖ ≤ 1 from by rw [Real.norm_eq_abs,abs_of_nonneg hp]; exact hp') le_rfl).mono le_rfl hw'), hw ▸ (((Ticket.pure h.radius_nonneg (1:ℝ)).sub h).tip.with_one (show ‖1-p V‖ ≤ 1 from by rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]; linarith) le_rfl)⟩

def Gliss (D : Record) (d : Desk G S) (n : ℕ) := ∀ t, Pitch.height D d ≤ t → QuietPrice d.profile G n t

theorem gliss (G : Gauge) (H : Patch) (D : Record) (n : ℕ) (q : Chi) : ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} {S : StepData c f} (d : Desk G S),
    S.patch=H → x=d.betaHat → betaF G x H.L/2 ≤ d.input.beta → q=d.profile → d.input.p.threshold= fiery G x H.L → Gliss D d n := by
  obtain ⟨M,hM,h⟩ := broad_grade (G:=G) q n 1 zero_lt_one
  let K : ℝ := ((2+M)*(1+n))^n * ‖toHue G‖; have hε := D.guards; have hK : 0≤K := by unfold K; positivity
  filter_upwards [(meter_grows.comp (Work.E09.betaF_growth G H.L)).eventually_ge_atTop (64*K/D.ε), (Work.E09.betaF_growth G H.L).eventually_gt_atTop 0] with x hi hx c f S d _ _ he hq hT t ht
  let y := betaF G x H.L; change 0<y at hx; change y/2 ≤ _ at he; have hY := coupling_pos hx
  have hβ : 0<d.input.beta := by linarith
  have hp : 0<d.g := coupling_pos hβ
  have hg : d.g ≤ 2*coupling y := by
    unfold Desk.g coupling; rw [← div_eq_mul_inv, inv_le_comm₀ (Real.sqrt_pos.mpr hβ) (by positivity), inv_div, div_le_iff₀ (zero_lt_two' ℝ)]; nlinarith [Real.sq_sqrt hβ.le, Real.sq_sqrt hx.le, Real.sqrt_nonneg y, Real.sqrt_pos.mpr hβ]
  have hL : K ≤ Pitch.height D d := by
    unfold Pitch.height Psalm.cap; rw [hT, le_div_iff₀ (by norm_num),le_div_iff₀ hp]; change _ ≤ D.ε*(coupling y*meter y)
    have he := mul_le_mul_of_nonneg_right (show 64*K ≤ meter y * D.ε from (div_le_iff₀ hε).mp hi) hY.le
    nlinarith only [mul_le_mul_of_nonneg_right hg hK,he]
  intro c; exact quiet_price d.profile G n hM (norm_nonneg _) (lt_of_lt_of_le (by have := d.input.p.threshold_pos; unfold Pitch.height Psalm.cap; positivity) ht) le_rfl (hL.trans ht) (hq ▸ h)
end YM.PhysicalNext.JointLoad.Psalm
