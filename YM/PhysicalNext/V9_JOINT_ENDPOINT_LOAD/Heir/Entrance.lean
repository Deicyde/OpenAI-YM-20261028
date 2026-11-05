import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Cooling
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Fusion

/-! # Withdrawing actual epoch receipts at fixed adjacent-stage prices -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Filter Function Lattice Wilson Pressure RG Tree Precision Next Next.Free Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory Extra.Iteration Extra.Iteration.Scales SelectedOrderedKernels.Sector
    AnalyticBridge.LocalGaussianLaws
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {L : Side} {P B : BudgetPoint} {x u a t K : ℝ} {n r : ℕ} {C : Libretto G n} {D : Record}

lemma plents (C : Libretto G n) (D : Record) (L : Side) (r p : ℕ) (hn : 0 < n) : ∀ᶠ x : ℝ in atTop, ∀ β, betaF G x L/2 ≤ β →
    0<coupling β ∧ ∀ P B : BudgetPoint, B.threshold=fiery G x L → P.power=p → Lute.Plented C D P B L r x (coupling β) := by
  let a := G.slopeConstant*Real.log (L.val:ℝ)
  let d := Lute.debited n p; let H := Lute.boost C D L; let K := Lute.guests G D.K n L
  have hH : 0≤H := Lute.boost_nn ..; have hK : 0≤K := Lute.guest_nn ..
  obtain ⟨v,hv,hv'⟩ : ∃ v > (0:ℝ), (H*v)^(n+n)*K ≤ 1 := by
    have h : Continuous (fun y : ℝ => (H*y)^(n+n)*K) := by fun_prop
    obtain ⟨z,h1,h2⟩ := Metric.mem_nhds_iff.mp ((h.tendsto 0).eventually (ge_mem_nhds (by simp [zero_pow (by omega : n+n≠0)] : (H*0)^(n+n)*K<1)))
    exact ⟨z/2,half_pos h1,h2 (Metric.mem_ball.mpr (by simpa [abs_of_pos h1] using half_lt_self h1))⟩
  let Z (x : ℝ) := ((r+48:ℝ)*(1+(radiusB x:ℝ)))^d
  have hu : Tiny (fun x => meter (x+a)) Z := ((Tiny.const (Tiny.grow a) (r+48:ℝ) (by positivity)).mul (Tiny.cover a) (Tiny.grow a)).pow (Tiny.grow a) d
  have hT := ((flowering a d).const_mul ((r+48:ℝ)^d)); rw [mul_zero] at hT
  filter_upwards [eventually_gt_atTop (-a),((tendsto_rpow_atTop (y:=(1/2:ℝ)) (by norm_num)).comp (Tiny.grow a)).eventually_ge_atTop (4/v),hu (1/2) (by norm_num),hT.eventually (ge_mem_nhds (half_pos hv))] with x hx hy hq hf β hβ
  let y := x+a; have hz : 0<y := by unfold y; linarith
  have hβ : y ≤ 2*β := by change y/2 ≤ _ at hβ; linarith
  have hβ' : 0 < β := by linarith
  refine ⟨coupling_pos hβ',fun P B hB hp => ?_⟩
  let w := coupling β
  have hw : 0 ≤ Lute.ζ B w := add_nonneg B.threshold_pos.le (by have := coupling_pos hβ'; have := B.threshold_pos; unfold w; positivity)
  have hZ : 1≤ Z x := one_le_pow₀ ((show 1 ≤ _ by linarith [Nat.cast_nonneg (α:=ℝ) r] : (1:ℝ)≤r+48).trans (le_mul_of_one_le_right (by positivity) (by simp)))
  have he : coupling β ≤ 2*coupling y := by
    unfold coupling; rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hβ'),div_mul_eq_mul_div,le_div_iff₀ (Real.sqrt_pos.mpr hz),one_mul]; nlinarith [Real.sq_sqrt hz.le, Real.sq_sqrt hβ'.le, Real.sqrt_nonneg β]
  have hV : coupling β / B.threshold * Z x ≤ v/2 := by
    have hh : B.threshold = coupling y * meter y := hB
    have hY := coupling_pos hz
    rw [div_mul_eq_mul_div,div_le_iff₀ B.threshold_pos,hh]; apply (mul_le_mul he hq.2 hq.1 (by positivity)).trans
    have hsq : meter y^(1/2:ℝ)*meter y^(1/2:ℝ)=meter y := by rw [← Real.rpow_add (meter_pos y)]; norm_num
    have h' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hv).mp hy) (show 0 ≤ meter y^(1/2:ℝ) from Real.rpow_nonneg (meter_pos y).le _)
    change _ ≤ meter y^_*v*(meter y^_) at h'; rw [mul_right_comm _ v,hsq] at h'
    nlinarith only [mul_le_mul_of_nonneg_right h' hY.le]
  have hf : B.threshold * Z x ≤ v/2 := by unfold Z; rw [hB,mul_pow]; linarith only [show (r+48:ℝ)^d*((1+(radiusB x:ℝ))^d * fiery G x L) ≤ v/2 from hf]
  unfold Lute.Plented; rw [hp]; change ((H*_)^(n+n)*K)*Z x≤1
  have hQ : Lute.ζ B w * Z x ≤ v := by unfold Lute.ζ; rw [add_mul]; linarith
  calc
    _ ≤ ((H*Lute.ζ B w)^(n+n)*K)*(Z x)^(n+n) := mul_le_mul_of_nonneg_left (le_self_pow₀ hZ (by omega)) (by positivity)
    _ = (H*(Lute.ζ B w*Z x))^(n+n)*K := by rw [mul_right_comm,←mul_pow,mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hH (mul_nonneg hw (zero_le_one.trans hZ))) (mul_le_mul_of_nonneg_left hQ hH) _) hK).trans hv'

-- pre-L matins calls etc are at a given Pt (across its adjacency);
-- tower axis custodians still have to meet the chosen δ and N.
lemma leads (Pt : Teller G) (δ K : ℝ) (hd : 0<δ) (hK : 0≤K) : ∃ C : Libretto G Pt.below.order, C.δ=δ ∧ C.N=K ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → ∀ F, Matins T F Pt.top.power (2*C.C) C.M := by
  obtain ⟨Z⟩ := Foliage.collarSupply G Pt.below.order; obtain ⟨Q⟩ := authority G Pt.below.order; obtain ⟨W⟩ := webExists G
  have h := Foliage.Cube.fee_one Z
  obtain ⟨M,hM,H⟩ := coaches Pt Pt.top.power (2*Foliage.Cube.fee Z) Pt.top.power_ge (by positivity)
  exact ⟨⟨Z,Q,W,δ,hd,K,hK,M,hM⟩,rfl,rfl,H⟩

lemma songs (H : Patch) (Pt : Teller G) (C : Libretto G Pt.below.order) (hp : H.Branches Pt.bind G) (hL : licensed C.δ C.N H.L)
    (hk : Pt.below.order ≤ Pt.top.order) (he : Pt.below.power ≤ Pt.top.power)
    (hm : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), Pt.Funds S T → ∀ F, Matins T F Pt.top.power (2*C.C) C.M) (r : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ D : Record, D.ε ≤ R ∧ Tight C D ∧ ∀ᶠ x : ℝ in atTop, ∀ P B : BudgetPoint,
      P.threshold=temp x → B.threshold=fiery G x H.L → B.B=radiusB (betaF G x H.L) → P.order=Pt.below.order → B.order=Pt.top.order →
      P.power=Pt.below.power → B.power=Pt.top.power → (∀ β, betaF G x H.L / 2 ≤ β → 0 < coupling β ∧ Lute.Plented C D P B H.L r x (coupling β)) ∧
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=H → Seam T C.δ C.N → Lift.Booth Pt S T → 100*(1+radiusB x)≤c.val → Plays C D P B Pt T x := by
  let n := Pt.below.order; have hn : 6≤n := Pt.below.order_ge
  have h₀ := C.web.cost
  obtain ⟨b,Q,hb,hQ,hh⟩ := Psalm.harmony G H Pt hp n (by omega)
  obtain ⟨w,g,d,M,Y,s,Y',hw,hg,hd,hs,hM,hY,hY',h⟩ := haar_operators G H Pt hp n
  let ε := min R ((128*C.web.scale)⁻¹); have hε : 0 < ε := lt_min hR (by positivity)
  let Z := 1+peal G n Pt.below.power d s M w Y g Y'
  let D : Record := ⟨b,hb,Q,hQ,ε,hε,peakCost G n M w Y,le_add_of_nonneg_right (abs_nonneg _),Z,le_add_of_nonneg_right (by unfold peal; positivity)⟩
  have hε' := min_le_right R ((128*C.web.scale)⁻¹)
  have ht : Tight C D := ⟨le_trans hε' (inv_le_comm₀ (by positivity) (by norm_num) |>.mpr (by linarith)),by
    have h := mul_le_mul_of_nonneg_left hε' (zero_le_one.trans h₀); field_simp at h; change C.web.scale * min R _ ≤ 1/128; rw [mul_comm (128:ℝ),← one_div]; linarith⟩
  refine ⟨D,min_le_left ..,ht,?_⟩
  filter_upwards [hh,h,rehearses hL ht _ _ he,Folio.subscribe Pt H,plents C D H.L r Pt.below.power (by omega), Rebuild.geometry (G.slopeConstant * Real.log H.L.val)] with x hx h hR hB hP hE P B hv hb' hBB h₁ h₂ h₃ h₄
  refine ⟨fun β hl => let hb := hP β hl; ⟨hb.1,hb.2 P B hb' h₃⟩,fun S T hH hT hh hc => ⟨hB S T hh.1 hH, h₄.symm ▸ hm S T hh.1,hT, fun F k => (hx S T hH hh hc F k).1,fun F k => (hx S T hH hh hc F k).2,fun A F k {ι} _ _ e o R V hR hv' => ?_,hc,hH.symm ▸ hR P B hv hb' (hBB.symm ▸ hE.1.1) h₃ h₁ (h₂.symm ▸ hk) h₄⟩⟩
  rw [hv] at hv'; have hr := ringing (h S T hH hc hh.1 A F k V hv') hg hv e hR
  rw [hb',← hH]; convert hr using 1; unfold D Z; simp only [h₃]
end YM.PhysicalNext.JointLoad.Heir
