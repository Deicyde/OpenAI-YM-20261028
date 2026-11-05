import YM.Next.ROTATIONS.Sources
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Awning
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Epoch
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pose
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Arc.Wire
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Cut.Wind
import YM.UVNext.PRICED_KERNELS.Gaps

/-!
# Earned Ψ bias of the *literal* transported output colors

Realized path from Binding, after ψ stencil cutting and putting the
orbit at fingers V. Critical L^-2 price with PRE-Patch constants, not
per period. Actual restarted threshold. `pointing`: compare low's curl
at the fine field site with short Ψ-row onto the real Rank arguments
on V (including non-linear error by face_chart_cost etc.), paying also
for coupling conversion. Need aperture charge separately from Focusing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle WeightedGaussianMarginal45C.Issue.Cut UVNext.PricedKernels
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

def priceCore (G : Gauge) := (face_chart_cost G).choose
def areaCore (G : Gauge) := (face_chart_cost G).choose_spec.choose

def ticketPsi (z : ℝ) (L : Side) := ticket (TypeFace 2) (psiBudget z / (L.val:ℝ)^2)
def retractPsi (G : Gauge) (L : Side) (z x s : ℝ) :=
    cheque (TypeFace 2) s (psiBudget z / (L.val:ℝ)^2) x * (priceCore G*linkRoom x)+ ticketPsi z L*(priceCore G*linkRoom x^2)

-- ensure from Sizing before the proposed L assignments
def Sizing (G : Gauge) (L : Side) (z : ℝ) := (Fintype.card G.ColorIndex:ℝ) * ticketPsi z L * 2 ≤ 1/4096
lemma sizing_gap (z : ℝ) (G : Gauge) : ∃ k : ℕ,∀ (L : Side), k ≤ L.val → Sizing G L z := by
  let C := psiBudget z; let N := Fintype.card G.ColorIndex * (Fintype.card (TypeFace 2):ℝ); let t := 8192*N*C
  obtain ⟨i,h⟩ := exists_nat_gt t; refine ⟨i,fun L hL=> ?_⟩
  unfold Sizing ticketPsi ticket
  let l:=(L.val:ℝ); have hl : 1≤l := Nat.one_le_cast.mpr L.property
  have h1 : N*C*2/l^2 ≤ 1/4096 := (div_le_iff₀ (by positivity)).mpr (by
    have he := h.trans_le (show (i:ℝ) ≤ l from Nat.cast_le.mpr hL); unfold t at he; nlinarith only [he,hl])
  unfold N C l at h1
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h1

structure Steady (G : Gauge) (L : Side) (z x s β β' : ℝ) : Prop where
  visible : 0<x
  doors : clearanceFare (retime x) ≤ linkRoom x
  base : linkRoom x ≤ areaCore G
  slide : relativePay β β' x
  sparks : 0 < β
  checks : 0 < β'
  extent : Sizing G L z
  torch : Fintype.card G.ColorIndex * (retractPsi G L z x s + ticketPsi z L*phase x) ≤ phase (betaF G x L)/2048
  bill : (retractPsi G L z x s + ticketPsi z L*phase x * coupler x) / coupling β ≤ x^(-(1/16):ℝ)

lemma threshold_allows (G : Gauge) (L : Side) (C : ℝ) (hc : 0≤C) : ∀ᶠ x in atTop, C*linkRoom x^2 ≤ phase (betaF G x L) := by
  filter_upwards [const_allow hc (show (-(3/4):ℝ)< -(1/2) by norm_num),
    across_heat G L,(Work.E01.betaF_tendsto G L).eventually (surge.eventually_ge_atTop 2),eventually_gt_atTop (0:ℝ)] with x hv he hs hx
  let y:=betaF G x L
  rw [linkRoom_sq hx]; refine hv.trans ?_
  rw [phase,Real.rpow_neg hx.le,← Real.sqrt_eq_rpow]; exact he.2.trans
    ((mul_comm ..).trans_le (mul_le_mul_of_nonneg_left hs (by unfold Vac.Numbers.Hat; positivity)))

lemma ret_power_scopes (c : ℝ) (h : 0≤c) : ∀ᶠ x in atTop,c*clearanceFare (retime x) ≤ linkRoom x:= by
  filter_upwards [tall_limit.eventually (extension_small c h),burst_limit,eventually_gt_atTop 0] with x hv he hx
  exact hv.trans (Real.rpow_le_rpow_of_nonpos hx he.1 (by norm_num))

lemma steady_pass (G : Gauge) (L : Side) (z : ℝ) (s γ : ℝ) (hZ : Sizing G L z)
    (hz : 0≤z) (hs : 0<s) :
    ∀ᶠ x : ℝ in atTop,∀ β β', x/2 ≤ β → β ≤ 3*x → x/2 ≤ β' → |β'-β| ≤ γ → Steady G L z x s β β' := by
  let M := psiBudget z / (L.val:ℝ)^2
  let C:=priceCore G; let P:=ticketPsi z L; let N:=(Fintype.card G.ColorIndex:ℝ); let K:=C+P*C
  have hm : 0≤ M := div_nonneg (psiBudget_nn _ hz) (sq_nonneg _)
  obtain ⟨hC,hr,_⟩ := (face_chart_cost G).choose_spec.choose_spec
  change 0<C at hC; change 0<areaCore G at hr
  have hP : 0≤P:=ticket_nonneg _ hm
  have hN : 0≤N:= Nat.cast_nonneg _
  have hK : 0≤K := by unfold K; positivity
  filter_upwards [currency (TypeFace 2) s M (3/8) hs hm, (tendsto_rpow_atTop (by norm_num : 0 < (3/4:ℝ))).eventually_ge_atTop γ,
    earns,across_heat G L, linkRoom_tends.eventually (ge_mem_nhds hr),ret_power_scopes 1 zero_le_one,
    threshold_allows G L (4096*N*K) (by positivity), phase_fit, Work.E09.temp_cost (1/32) (by norm_num),
    const_allow (show 0≤ 2*K+2*P by positivity) (show -(3/32:ℝ)< -(1/16) by norm_num),eventually_gt_atTop (1:ℝ),
    PhysicalGuard7f546.Curved.band G L] with x ht he hv hu h hj hp hW hY hk hh hc
  intro β β' hc0 hc1 hc2 hc3; let b:=linkRoom x
  have hz : 0<x:=zero_lt_one.trans hh; obtain ⟨hb,hg,_,hG,_⟩ := hc _ hc0 hc1
  let t:=phase x; let t':=phase (betaF G x L); let a:=retractPsi G L z x s
  have hf : a≤K*b^2 := by
    have hb : 0≤b := (linkRoom_pos hz).le
    have h : a ≤ b*(C*b)+P*(C*b^2) := add_le_add (mul_le_mul_of_nonneg_right ht (mul_nonneg hC.le hb)) le_rfl
    exact h.trans_eq (by unfold K; ring)
  refine ⟨hz,by simpa using hj,h,hv _ _ hc0 hc2 (hc3.trans he),hb,by linarith,hZ,?_,?_⟩
  · have hV : t ≤ 2*t' := hu.1
    change 4096*N*K*b^2 ≤ t' at hp
    have hh : 0 ≤ t' := by unfold t'; exact (alpha_phase _ (add_pos_of_pos_of_nonneg hz (Work.E04.shift_nonneg G L))).le
    change N*P*2 ≤ _ at hZ
    change N*(a+P*t) ≤ t'/2048
    linarith only [mul_le_mul_of_nonneg_left hf hN,mul_le_mul_of_nonneg_left hV (mul_nonneg hN hP),hp,mul_le_mul_of_nonneg_right hZ hh]
  · have hs : t ≤ x^(-(1/2:ℝ)+1/32) := hW.trans hY
    let g := coupling β; let Y := coupler x; have hY : 0≤Y:= by unfold Y coupler; positivity
    let W := x^(-(3/32):ℝ)
    have h2 : t*Y*Real.sqrt x≤ W := by
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hY) (Real.sqrt_nonneg x)).trans_eq ?_
      unfold Y coupler W; rw [Real.sqrt_eq_rpow,← Real.rpow_add hz,← Real.rpow_add hz]; norm_num
    have h3 : b^2*Real.sqrt x≤ W := by
      unfold b W; rw [linkRoom_sq hz,Real.sqrt_eq_rpow,← Real.rpow_add hz]; apply Real.rpow_le_rpow_of_exponent_le hh.le; norm_num
    change (a+P*t*Y)/g ≤ _
    rw [div_eq_mul_inv]
    apply le_trans _ hk
    have ht : 0≤ t:=(alpha_phase x hz).le
    apply le_trans (mul_le_mul_of_nonneg_right (add_le_add_left hf _) (show 0≤g⁻¹ from (inv_pos.mpr hg).le))
    apply (mul_le_mul_of_nonneg_left hG (show 0 ≤ K*b^2+P*t*Y by positivity)).trans; change _ ≤ (2*K+2*P)*W
    linarith only [mul_le_mul_of_nonneg_left h3 hK, mul_le_mul_of_nonneg_left h2 hP]

section use
variable {C : Family G} (B : Binding C) {N i p : ℕ}
local notation "S" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i
local notation "X" => stamp C.path.levels N p
local notation "y" => betaF G (C.path.levels.clock.hatBeta i) (C.S.block i)
variable (hi : i<N) (hh : C.path.levels.clock.J (i+1)=C.path.levels.clock.J i)
local notation "J" => C.path.levels.clock.J i
local notation "z" => B.prices.Ω (C.path.levels.clock.J i)
local notation "s" => B.prices.α (C.path.levels.clock.J i)
variable {o : Site (C.side i p)} {W : ℕ} {β β' : ℝ}
    {A : Stores (C.path.levels.clock.op i p)} {V : Config G (C.side i p)} {v : Dir G (C.side i p)}

def purseMean (o : Site (C.side i p)) (V : Config G (C.side i p)) (g : ℝ) :=
    Normal.reads (short B N p i).H (fun j => (rigid (kiosk g o V) j : ℂ))
lemma readInvoice (q : Incidence G (C.side (i+1) p)) (V : Config G (C.side i p)) (o) (g : ℝ) :
    (purseMean B o V g (N:=N) q).re = (∑ j, panePsi G S (shorter B N i) (toPAC q) (toPAC j)* flatten (look (spine V o)) (toPAC j))/g := by
  unfold purseMean; rw [linear_write]
  simp_rw [H_at,← Complex.ofReal_mul,← Complex.ofReal_sum,Complex.ofReal_re]; rw [sum_div]; refine sum_congr rfl ?_; intro a _
  let p := fromBead G a
  rw [show flatten (look (spine V o)) (toPAC a)= (look (spine V o) (p.1,plaquette p.2)) a.2.2 from rfl,looking]
  unfold rigid Tapes.kiosk; dsimp only
  rw [PiLp.smul_apply,smul_eq_mul]; unfold p; ring

private lemma adjust_rows {I : Type} [Fintype I] (A B v u : I→ℝ) (C L γ δ : ℝ) (hC : 0 ≤ C) (hd : 0≤δ) (hr : ∑ i, |A i-B i| ≤ γ) (hA : ∑ i, |B i|≤L) (hv : ∀ i,|v i|≤ C) (hB : ∀ i, B i≠0 → |v i-u i|≤ δ) :
    |∑ i,A i*v i-∑ i,B i*u i| ≤ γ*C+L*δ := by
  rw [show ∑ i,A i*v i-∑ i,B i*u i = ∑ i, (A i - B i)*v i + ∑ i, B i * (v i-u i) from ?_]
  swap; simp_rw [sub_mul,mul_sub,sum_sub_distrib]; abel
  refine (abs_add_le ..).trans (add_le_add ((abs_sum_le_sum_abs ..).trans ?_) ((abs_sum_le_sum_abs ..).trans ?_))
  · calc
      _ ≤ ∑ i, |A i-B i| *C := sum_le_sum fun i _=> by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
      _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hr hC
  calc
    _ ≤ ∑ i, |B i| *δ := sum_le_sum fun i _=> by
      rw [abs_mul]; by_cases h : B i = 0
      · rw [h,abs_zero,zero_mul,zero_mul]
      exact mul_le_mul_of_nonneg_left (hB i h) (abs_nonneg _)
    _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hA hd

include hi hh
-- Main bias estimate, V orbit in Rank coordinates.
lemma pointing (hA : Pose A o W x V v) (h : Steady G (C.S.block i) z x s β β')
    (F : Forest (C.path.levels.clock.op i p).ratio) (u : Cell (C.side (i+1) p)) (hu : separation o ((C.path.levels.clock.op i p).ratio.parent u.1)+walls x+2≤ W) :
    let T:= tunnel B N i p; let f:= Work.F03.faceCurl u (low T F v)
    ‖f‖ ≤ phase y/2048 ∧ ∀ k,
      |((coupling β)⁻¹ • f) (k:G.ColorIndex) - (purseMean B (i:=i) o V (coupling β') (N:=N) (u.1,u.2,k)).re| ≤ x^(-(1/16):ℝ) := by
  intro T f; let g:=coupling β; let g':=coupling β'
  let W0:=spine V o; let t:=phase x; let D := ticketPsi z (C.S.block i)
  let Z:=retractPsi G (C.S.block i) z x s; let H:=B.world.H N (i+1); let H':=B.world.H N i
  let Y:=look W0; let b:=linkRoom x; let L := priceCore G
  obtain ⟨hL,hR,hk⟩:= (face_chart_cost G).choose_spec.choose_spec; change 0<L at hL
  have ht : 0<t := alpha_phase x h.visible; have he := B.prices.alpha_pos J; have hg : 0<g:=coupling_pos h.sparks
  have hP := sufficient_rows B hi hh; have hQ := psiBudget_nn _ (minimum_price B N i hi.le); have hb : 0≤ b := (linkRoom_pos h.visible).le
  have h0 : 0 ≤ psiBudget z / ((C.S.block i).val:ℝ)^2:=div_nonneg hQ (sq_nonneg _); have hD : 0≤D:=ticket_nonneg _ h0
  have hZ : 0 ≤ Z := add_nonneg (mul_nonneg (cheque_sign _ h0) (mul_nonneg hL.le hb)) (mul_nonneg hD (mul_nonneg hL.le (sq_nonneg _)))
  have hv : ‖v‖ ≤ b := le_trans hA.worth (by linarith only [h.doors,hb])
  let η k : Incidence G (C.side (i+1) p):=(u.1,u.2,k)
  let L' (k) j:=panePsi G S (shorter B N i) (toPAC (η k)) (toPAC j)
  let Q (k) := ∑ j, L' k j * flatten Y (toPAC j)
  have hx (k) : |Q k|≤ D*t ∧ |f k - Q k|≤ Z := by
    have hg : ∑ j, |L' k j|≤ D := by
      have he:= exact_short_price B he hP (η k)
      simp_rw [H_at,Complex.norm_real,Real.norm_eq_abs] at he; exact he
    have H1 (j) (hj : L' k j ≠ 0) : separation o j.1 + 2 ≤ W := by
      let sh:=(short B N p i).H (η k)
      have he' : j∈sh.support := Finsupp.mem_support_iff.mpr (by unfold sh; rw [H_at]; exact_mod_cast hj)
      have ht' : separation ((C.path.levels.clock.op i p).ratio.parent u.1) j.1 ≤ walls x := (support_rows B he hP).pole (η k) _ he'
      refine le_trans (add_le_add_left (separation_triangle o ((C.path.levels.clock.op i p).ratio.parent u.1) j.1) _) ?_; omega
    constructor
    · apply (abs_sum_le_sum_abs ..).trans
      calc
        _ ≤ ∑ j, |L' k j| *t := Finset.sum_le_sum fun j _=> by
          by_cases hr : L' k j=0
          · simp [hr]
          have hk' : separation o (fromBead G j).1 + 2 ≤ W := H1 j hr
          have hx := dotSize 1 (by norm_num) V hA.glisten hA.border hk'
          rw [div_one] at hx
          unfold Tapes.kiosk at hx; rw [inv_one,one_smul] at hx
          rw [abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          change |look _ ((fromBead G j).1,plaquette (fromBead G j).2) j.2.2| ≤ _
          rw [looking]; exact (color_component ..).trans hx
        _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right hg ht.le
    let m j:= flatten (dColor G _ 1 v) (toPAC j); let P k j:=panePsi G S (curves B N i) (toPAC (η k)) (toPAC j)
    have hw' : ∑ j, |P k j-L' k j|≤cheque (TypeFace 2) s (psiBudget z / ((C.S.block i).val:ℝ)^2) x := by
      have ht' := (high_rows B hi hh (η k)).2
      simp_rw [H_at, rich_path B hi hh,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm (panePsi G S (shorter B N i) (toPAC (η k)) _)] at ht'; exact ht'
    rw [show f k=∑ j,P k j*m j from ?_]
    swap
    · have hT := WeightedGaussianMarginal45C.Arc.phase_eq T F (H:=H) (B:=H') (B.pays.crossings N i p hi) (B.pays.all N (i+1) hi _) v
      change flatten (dColor G _ 1 (low T F v)) (toPAC (η k))=_; rw [hT,mulVec,dotProduct]
      trans ∑ j, tensor G (psi S H H' T.R) (toPAC (η k)) (toPAC j)*m j
      · exact (Equiv.sum_comp toPAC (fun j=>tensor G (psi S H H' T.R) (toPAC (η k)) j *flatten (dColor G (C.side i p) 1 v) j)).symm
      refine sum_congr rfl fun j _=>?_ ; congr 1; apply Complex.ofReal_injective; exact (planner_at B N i p hi _ _).symm.trans (rich_path B hi hh _ _)
    apply adjust_rows _ (L' k) m _ (L*b) D _ (L*b^2) (mul_nonneg hL.le hb) (mul_nonneg hL.le (sq_nonneg _)) hw' hg
    · intro j; exact (color_component ..).trans (((hk v (fromBead G j)).1).trans (mul_le_mul_of_nonneg_left hv hL.le))
    intro j hj
    let p:=fromBead G j; obtain ⟨h1,h2,h3,h4⟩:= therm W o p (H1 j hj)
    change |(Work.F03.faceCurl p v-look W0 (p.1,plaquette p.2)) j.2.2|≤_
    rw [looking]; apply (color_component ..).trans
    change ‖Work.F03.faceCurl p v-G.curvature (faceValue (spine V o) p)‖≤L*b^2
    rw [corners, hA.wires _ h1,hA.wires _ h2,hA.wires _ h4,hA.wires _ h3, ← corners,norm_sub_rev]
    exact (((hk v p).2 (hv.trans h.base)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv _) hL.le))
  refine ⟨le_trans (color_count (add_nonneg hZ (mul_nonneg hD ht.le)) f (fun i'=> ?_)) h.torch,fun k => ?_⟩
  · obtain ⟨h1,h2⟩:=hx i'
    exact (norm_le_norm_sub_add (f i') (Q i')).trans (add_le_add h2 h1)
  let M:=Q k
  rw [readInvoice]; change |(g⁻¹ • f) k - M/g'| ≤ _; simp only [PiLp.smul_apply,smul_eq_mul]
  apply le_trans _ h.bill
  change _ ≤ (Z+D*t*coupler x)/g
  rw [show g⁻¹*f k - M/g' = ((f k-M)+ -(g'⁻¹*g-1)*M)/g from by field_simp; try ring]
  rw [abs_div,abs_of_nonneg hg.le]; apply div_le_div_of_nonneg_right _ hg.le
  refine (abs_add_le ..).trans (add_le_add (hx k).2 ?_)
  rw [abs_mul,abs_neg,mul_comm |(_)-1|]; exact (mul_le_mul (hx k).1 h.slide (abs_nonneg _) (mul_nonneg hD ht.le))
end use
end YM.PhysicalNext.InteractingRank
