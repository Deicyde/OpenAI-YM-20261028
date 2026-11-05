import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.CoreBudget
import YM.TraceExtension.Prom.Port.Leading
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.CoreBudget for dynamic stops. Pulse extension.
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

-- ensure from Sizing before the proposed L assignments

section use
variable {C : Family G} (B : Binding C) {N i p : ℕ}
local notation "S" => C.path.levels.clock.op i p
local notation "x" => C.path.levels.clock.hatBeta i

local notation "y" => betaF G (C.path.levels.clock.hatBeta i) (C.S.block i)
local notation "K" => C.path.levels.clock.J (i+1)
variable (hi : i<N)
local notation "J" => C.path.levels.clock.J i
local notation "z" => max (B.prices.Ω K) (B.prices.Ω J)
local notation "s" => min (B.prices.α K) (B.prices.α J)
variable {o : Site (C.side i p)} {W : ℕ} {β β' : ℝ}
    {A : Stores (C.path.levels.clock.op i p)} {V : Config G (C.side i p)} {v : Dir G (C.side i p)}

private lemma adjust_rowsSky {I : Type} [Fintype I] (A B v u : I→ℝ) (C L γ δ : ℝ) (hC : 0 ≤ C) (hd : 0≤δ) (hr : ∑ i, |A i-B i| ≤ γ) (hA : ∑ i, |B i|≤L) (hv : ∀ i,|v i|≤ C) (hB : ∀ i, B i≠0 → |v i-u i|≤ δ) :
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

include hi
-- Main bias estimate, V orbit in Rank coordinates.
lemma pointingSky (hA : Pose A o W x V v) (h : Steady G (C.S.block i) z x s β β')
    (F : Forest (C.path.levels.clock.op i p).ratio) (u : Cell (C.side (i+1) p)) (hu : separation o ((C.path.levels.clock.op i p).ratio.parent u.1)+walls x+2≤ W) :
    let T:= tunnel B N i p; let f:= Work.F03.faceCurl u (low T F v)
    ‖f‖ ≤ phase y/2048 ∧ ∀ k,
      |((coupling β)⁻¹ • f) (k:G.ColorIndex) - (purseMean B (i:=i) o V (coupling β') (N:=N) (u.1,u.2,k)).re| ≤ x^(-(1/16):ℝ) := by
  intro T f; let g:=coupling β; let g':=coupling β'
  let W0:=spine V o; let t:=phase x; let D := ticketPsi z (C.S.block i)
  let Z:=retractPsi G (C.S.block i) z x s; let H:=B.world.H N (i+1); let H':=B.world.H N i
  let Y:=look W0; let b:=linkRoom x; let L := priceCore G
  obtain ⟨hL,hR,hk⟩:= (face_chart_cost G).choose_spec.choose_spec; change 0<L at hL
  have ht : 0<t := alpha_phase x h.visible; have he := lt_min (B.prices.alpha_pos K) (B.prices.alpha_pos J); have hg : 0<g:=coupling_pos h.sparks
  have hP := sufficient_rowsSky B hi; have hQ := psiBudget_nn z ((minimum_price B N i hi.le).trans (le_max_right ..)); have hb : 0≤ b := (linkRoom_pos h.visible).le
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
      have ht' := (high_rowsSky B hi (η k)).2
      simp_rw [H_at, rich_pathSky B hi,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm (panePsi G S (shorter B N i) (toPAC (η k)) _)] at ht'; exact ht'
    rw [show f k=∑ j,P k j*m j from ?_]
    swap
    · have hT := WeightedGaussianMarginal45C.Arc.phase_eq T F (H:=H) (B:=H') (B.pays.crossings N i p hi) (B.pays.all N (i+1) hi _) v
      change flatten (dColor G _ 1 (low T F v)) (toPAC (η k))=_; rw [hT,mulVec,dotProduct]
      trans ∑ j, tensor G (psi S H H' T.R) (toPAC (η k)) (toPAC j)*m j
      · exact (Equiv.sum_comp toPAC (fun j=>tensor G (psi S H H' T.R) (toPAC (η k)) j *flatten (dColor G (C.side i p) 1 v) j)).symm
      refine sum_congr rfl fun j _=>?_ ; congr 1; apply Complex.ofReal_injective; exact (planner_at B N i p hi _ _).symm.trans (rich_pathSky B hi _ _)
    apply adjust_rowsSky _ (L' k) m _ (L*b) D _ (L*b^2) (mul_nonneg hL.le hb) (mul_nonneg hL.le (sq_nonneg _)) hw' hg
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
