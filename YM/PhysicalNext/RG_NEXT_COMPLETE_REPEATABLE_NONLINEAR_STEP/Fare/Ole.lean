import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Sum
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Caverns

/-!
# Outside core chart. Physical real kernel geometry on poly volume
 From healthy and no wire crossing (fixed δ). All of SliceSet but
 never infer tag outside likelihood. `Cops` sufficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    {u σ C Λ : ℝ} {n : ℕ}
local notation "X" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "Y" => Poll.Body K
variable (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3))
variable (ρ : Bid.Dir G c→ AxisChart G F)
local notation "R" => A.tables T.high S.patch
local notation "φ" => Lapis.table F k T.up T.high
local notation "r" => Lapis.orbit F ρ
section LA
variable (hr : A.Service F T.high T.up ρ) (he : Larger (G:=G) S) (h : T.up.Bounds T.high σ C Λ)
include hr he h
lemma climbs (x:X) (hx: ‖x‖<(R).horizon) (b D : ℝ) (hb : 0<b) (hd : 0 ≤ D) (z:Y) (hz : combineH (G:=G) F (x,z)∈closedBall 0 (R).safety) (ht : D*b ≤ ‖z-r x‖) :
    (R).gap/4*D^2*b^2 ≤ φ (x,z)-φ (x,r x):= by
  let d:= b⁻¹ • (z-r x); let p t:=visit r d t (b,x)
  have hp: b • d=z-r x:= smul_inv_smul₀ hb.ne' _
  have hD : D ≤ ‖d‖ := by rw [← hp,norm_smul, Real.norm_of_nonneg hb.le,mul_comm D] at ht; exact (mul_le_mul_iff_right₀ hb).1 ht
  let L:=combineH (G:=G) F; let M:= (R).gap/2
  have hu := (A.receipt F k h he rfl rfl).1
  have hq:0<M:=half_pos hu.pos_m
  have hl (t:ℝ) (ht:t∈Set.Icc 0 1) : L (p t)∈ closedBall 0 (R).safety:= by
    have hv : p t=(1-t) • (x,r x) + t • (x,z):= by
      change (x,_)=_; ext : 1
      · change x=(1-t) • x + t • x; rw [← add_smul]; simp
      change r x + t • b • d=(1-t) • r x + t • z; rw [hp,smul_sub,sub_smul,one_smul]; abel
    rw [hv,map_add,map_smul,map_smul]; exact convex_closedBall (0:Positions (Joint F G)) _ (hr.pricing (mem_ball_zero_iff.mpr hx)) hz (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let m : ℝ := M*D^2
  let f (t:ℝ):=Lantern.offer φ r d (b,x) t
  have hc t (ht:t∈Set.Icc (0:ℝ) 1): (1-t)*m ≤ f t:= by
    obtain ⟨-,hK,hx⟩:= pulse F k T.up T.high σ C Λ A he h (p t).1 (p t).2 (hl t ht)
    have he := hK d.ofLp; rw [hx] at he; apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht.2); apply le_trans _ he; apply mul_le_mul_of_nonneg_left _ hq.le; exact (pow_le_pow_left₀ hd hD _).trans_eq (EuclideanSpace.real_norm_sq_eq d)
  have hv (t:ℝ) (ht:t∈Set.Icc 0 1):ContDiffAt ℝ 2 φ (p t):=
    ((hu.born _ (closedBall_subset_ball hu.reserveH_lt (hl t ht))).1.of_le (by simp)).comp (p t) L.contDiff.contDiffAt
  have hj:ContinuousOn f (Set.Icc 0 1):= by
    intro t ht; apply ContinuousAt.continuousWithinAt; apply ContinuousAt.mul (continuousAt_const.sub continuousAt_id)
    have hb:= ((hv t ht).fderiv_right (by norm_num : (1:ℕ∞ω)+1≤ (2:ℕ∞ω))).fderiv_right (by norm_num : (0:ℕ∞ω)+1 ≤ (1:ℕ∞ω))
    apply ContinuousAt.clm_apply _ continuousAt_const; exact ContinuousAt.clm_apply (hb.continuousAt.comp (f:=fun t:ℝ=> p t) (by unfold p Lantern.visit; fun_prop)) continuousAt_const
  let C₀ (t:ℝ):=(1-t)*m; have hl: Continuous C₀ := by unfold C₀; fun_prop
  have hX:= intervalIntegral.integral_mono_on zero_le_one (hl.intervalIntegrable 0 1 (μ:=volume)) (hj.intervalIntegrable_of_Icc zero_le_one) hc
  have h₀ : (∫ t in (0:ℝ)..1,C₀ t)=m/2:= by unfold C₀; rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub]<;> first| fun_prop| (norm_num; first | ring| done)
  rw [h₀] at hX; have hs:= Lantern.funds φ r d b x (heart F k T.up T.high ρ σ C Λ A he h hr x hx d) hv; rw [hp,add_sub_cancel] at hs
  rw [hs]; convert! mul_le_mul_of_nonneg_left hX (sq_nonneg b) using 1; unfold m M; ring
end LA

lemma wall (G : Gauge) (P : Patch) (Q : KernelChoices) (rX : ℝ) (hp : 0 < rX) : ∃ δ : ℝ, 0<δ ∧
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=Q → Larger (G:=G) S → ∀ F : Forest S.ratio, ∀ V : Config G c, ∀ U : F.Slice G, ∀ k:S.Choices, SectorMeasure.Alive S (F.drape U) k →
      (∀ i: Pressure.Cell f, toll (F.drape U) i ≤ δ) →
      (∀ i, wire (S.prediction (F.drape U) k) V i ≤ δ) →
        ∃ z:Poll.Body (Precision.Key F G), ‖weld _ z‖ ≤ rX ∧ U = draw F V z := by
  obtain ⟨C,hC,H⟩ := Work.E02.answer G P.L P.J Q
  obtain ⟨RX,M,hR,hM,H'⟩ := log_chart_cost G
  let s: ℝ := (box (macroR P)).card* (Fintype.card PlaqAxes:ℝ)
  let D:= C*s+1; have hD : 0 < D:= add_pos_of_nonneg_of_pos (by unfold s; positivity) zero_lt_one
  let δ:= min (M/D) (rX/(RX*D)); have h:0<δ:=lt_min (by positivity) (by positivity)
  refine ⟨δ,h,?_⟩
  intro c f S hP hQ hS F V U k hh hu hv
  let u (i : F.Free):= U i*(floorG F V i)⁻¹
  have hl (p: F.Free) : G.chord (u p)≤D*δ:= by
    let i:= p.val; let x:=S.ratio.parent i.1
    have hp := Work.E01.port_le S (F.drape U) x δ h.le fun _ _=> hu _
    have he:Bid.Cops (S:=S) (F.drape U) V (S.prediction (F.drape U) k) i C:=
      H c f S hQ (hP ▸ rfl) (hP ▸ rfl) hS.2.1 hS.2.2 F (F.drape U) (fun i hi=> F.on_tree _ ⟨i,hi⟩) V i k (Pressure.wraps S k hh _)
    calc
      _ = G.chord (F.drape U p * (replica S.ratio V p)⁻¹):= congr_arg (fun x=> G.chord (x*(replica S.ratio V p)⁻¹)) (F.off_tree U p).symm
      _ ≤ _ := he
      _ ≤ C*(s*δ)+δ := add_le_add (mul_le_mul_of_nonneg_left (by rwa [hP] at hp) hC.le) (by split; exact h.le; exact hv _)
      _ = _ := by unfold D; ring
  let v i:= G.plog (G.mat (u i))
  have hm : D*δ ≤ M:= by rw [mul_comm]; exact (le_div_iff₀ hD).mp (min_le_left ..)
  refine ⟨(weld _).symm ((tint G _).symm v),le_trans (tint_inv_le v) ?_,?_⟩
  · apply (pi_norm_le_iff_of_nonneg hp.le).mpr; intro i
    apply ((H' (u i) ((hl i).trans hm)).2.trans ((mul_le_mul_of_nonneg_left (hl i) hR.le).trans ?_)); rw [← mul_assoc, mul_comm _ δ]; exact (le_div_iff₀ (mul_pos hR hD)).mp (min_le_right ..)
  funext i; change _=G.lieExp (v i)*floorG F V i; rw [(show G.lieExp (v i)=u i from H' _ ((hl i).trans hm)|>.1), show u i=_ from rfl]; exact (inv_mul_cancel_right _ _).symm

lemma crashed {U : Config G f} {V: Config G c} (k:S.Choices) {δ:ℝ} (h:0≤δ) (he : ¬∀ i, wire (S.prediction U k) V i ≤ δ) : S.kernel.penalty*δ^2/2 ≤ noiseTaylor S V U k := by
  push Not at he; obtain ⟨i,hi⟩:=he
  have hu := pow_le_pow_left₀ h hi.le 2
  unfold wire at hu; rw [G.chord_price] at hu
  apply le_trans _ (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j (_: j∈(univ:Finset (Bond c))) => (G.price_range (V j*(S.prediction U k j)⁻¹)).1) (mem_univ i)) S.kernel.penalty_pos.le)
  rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (by linarith only [hu]) S.kernel.penalty_pos.le
end YM.PhysicalNext.Repeat.Fare
