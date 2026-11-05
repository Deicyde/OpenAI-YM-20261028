import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Dolphin
/-!
 # Rev up. After-L threshold feasibility. ppm stamp on Y small and forecast factors all.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Extra.Iteration Extra.Iteration.Scales Next
open Next.Free Next.SectorChange Next.SectorChange.Rows Exterior Bloch Planned.AtomRegular SelectedOrderedKernels.Sector MeasureTheory MultiNext.SignedSource JointLoad JointLoad.Heir Lute
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n r p:ℕ}{ε τ:ℝ}
-- payment table imported coupling requests. given τ.

lemma abates (k r:ℕ)(G:Gauge) (L : Side)(hv:0<ε):∀ᶠ x : ℝ in atTop,∀ (B : BudgetPoint), B.threshold=fiery G x L→∀ β, betaF G x L/2≤ β → 0< coupling β ∧ Lute.ζ B (coupling β)*bulk 1 r x^k≤ε:=by
   let a := G.slopeConstant*Real.log L.val
   let H:=(2*(r+48:ℝ)); have hH(k':ℝ): bulk 1 r k'=H*(1+(radiusB k':ℝ)):=by unfold bulk H; push_cast; ring
   let F(x:ℝ):=H*(1+(radiusB x:ℝ)); have ht: H≥0:=by unfold H; positivity
   have hp : Tiny (fun x => meter (x+a)) (fun x=> F x ^ k):= ((Tiny.const (Tiny.grow a) H ht).mul (Tiny.cover a) (Tiny.grow a)).pow (Tiny.grow a) k
   have hT := ((flowering a k).const_mul (H^k)); rw [mul_zero] at hT
   filter_upwards [eventually_gt_atTop (-a), hp (1/2) (by norm_num),hT.eventually (ge_mem_nhds (half_pos hv)),((tendsto_rpow_atTop (y:=(1/2:ℝ)) (by norm_num)).comp (Tiny.grow a)).eventually_ge_atTop (4/ε)] with x hx he hf hh B hB β hβ
   let y:=x+a; have hy:0<y:=by unfold y; linarith; -- cast
   have hβ : y≤2*β:=by change y/2 ≤ _ at hβ; linarith
   have hβ':0<β:=by linarith
   refine ⟨coupling_pos hβ',?_⟩
   have hL : coupling β ≤ 2*coupling y := by
     unfold coupling; rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hβ'),div_mul_eq_mul_div,le_div_iff₀ (Real.sqrt_pos.mpr hy),one_mul]; nlinarith [Real.sq_sqrt hy.le, Real.sq_sqrt hβ'.le, Real.sqrt_nonneg β]
   have h : B.threshold* F x^k ≤ ε/2:=by rw [hB]; unfold F; rw [mul_pow]; linarith only [show H^k * ((1+(radiusB x:ℝ))^k * fiery G x L) ≤ ε/2 from hf]
   rw [Lute.ζ,hH,add_mul]; change _ * F x^ k+ _ *F x^k ≤ _
   have hvv : coupling β / B.threshold *F x^k ≤ ε/2 := by
     rw [div_mul_eq_mul_div,div_le_iff₀ B.threshold_pos,hB]
     have hY:= coupling_pos hy
     apply (mul_le_mul hL he.2 he.1 (by positivity)).trans
     have hsq : meter y^(1/2:ℝ)*meter y^(1/2:ℝ)=meter y := by rw [← Real.rpow_add (meter_pos y)]; norm_num
     have h' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hv).mp hh) (show 0 ≤ meter y^(1/2:ℝ) from Real.rpow_nonneg (meter_pos y).le _)
     change _ ≤ meter y^_*ε*(meter y^_) at h'; rw [mul_right_comm _ ε,hsq] at h'
     change _ ≤ ε/2*(coupling y*meter y)
     nlinarith only [mul_le_mul_of_nonneg_right h' hY.le]
   linarith only [hvv,h]

lemma garnets (C:Libretto G n)(D:Record)(L: Side)(r p:ℕ) (ht:0≤τ)(he:0<ε):∀ᶠ x:ℝ in atTop,∀ P B: BudgetPoint,P.power=p→B.threshold=fiery G x L→ B.B ≤2*radiusB x→P.threshold ≤ 2*B.threshold → ∀ β:ℝ,betaF G x L/2 ≤ β→ ∀ (f:Side)(X:Support f),coverNumber B.B X ≤ 1→ opal C D P B L X r x (coupling β) ≤ 1 ∧clocks C τ*opal C D P B L X r x (coupling β)* AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*((n+1)+(n+1))) ≤ ε := by
    let Z := boost C D L + (16 / D.ε)
    let s:=fuse n p; let v:=visitors (n+1)
    let f:=clocks C τ; let Q:=guests G D.K (n+1) L
    have hf:f≥0:=clocks_pos C ht; have hQ:0≤Q:= guest_nn G L _ D
    have h':0≤ boost C D L:= boost_nn ..
    have hZ : 0<Z:=add_pos_of_nonneg_of_pos h' (by have := D.guards; positivity)
    let A:= min (1 / Z) (ε /((f+1)*Z*(Q+1)))
    have hA:0<A:=lt_min (by positivity) (by positivity)
    filter_upwards [abates (s+v) r G L hA] with x hx P B hp hB h hb β hβ f' X hX
    let U:= bulk 1 r x; let V:=Lute.ζ B (coupling β)
    obtain ⟨hy,hκ⟩:=hx B hB β hβ
    have hu:1≤U:=bulk_one ..
    have hv:0≤V:= add_nonneg B.threshold_pos.le (by have := B.threshold_pos; positivity)
    have hX':bulk (coverNumber B.B X) r x≤ U:=by unfold U bulk; gcongr
    have he : V*U^(s+v) ≤1/Z∧V*U^(s+v) ≤ ε/((f+1)*Z*(Q+1)):=le_min_iff.mp hκ
    have hs: opal C D P B L X r x (coupling β) ≤ Z*V*U^s:=by
       unfold opal; have hf : 0 ≤ 16/D.ε:=by have h:= D.guards; positivity
       unfold Z; rw [add_mul,add_mul]; refine add_le_add ((booster h hb hy.le).trans ?_) (le_mul_of_one_le_right (mul_nonneg hf hv) (one_le_pow₀ hu))
       have hp':= bulk_one (coverNumber B.B X) r x; rw [hp]; gcongr
    refine ⟨hs.trans ?_,?_⟩ -- bad
    · rw [mul_assoc,mul_comm]; exact (le_div_iff₀ hZ).mp ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu (Nat.le_add_right s v)) hv).trans he.1) -- incorrect
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hs hf) (le_trans (fares h) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (bulk_one ..)) hX' v) hQ)) (by have := D.peak; unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; positivity) (by positivity)).trans
    change f*(Z*V*U^s)*(Q*U^v) ≤ _
    calc
      _ ≤ (f+1)*(Z*V*U^s)*((Q+1)*U^v):=by gcongr<;> linarith
      _ = V*U^(s+v)* ((f+1)*Z*(Q+1)):=by rw [pow_add]; ring
      _ ≤ _:= (le_div_iff₀ (by positivity :0<(f+1)*Z*(Q+1))).mp he.2
end YM.PhysicalNext.Repeat.Cub
