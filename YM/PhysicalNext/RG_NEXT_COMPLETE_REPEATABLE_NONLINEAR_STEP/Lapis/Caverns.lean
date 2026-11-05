import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Port
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Jas
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Lapses
import YM.Push.RELAY_DIFFERENCE.Dictionary

/-!
# Caverns on unmasked aux step
 Evaluate _b Exact_ and Brush on continuous r.
 δgap from billetery, not Payment Theta. Later appeal x post kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lapis
open Filter Function Metric Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Gauge Matrix Finset Set Push Push.Uniform Bid
open ConnectedActivityE6 Blaze Brush Lantern Planned.JetPort WithLp
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (k : S.Choices) (p : PathData G) (b : Clip)
variable {n j : ℕ}
local notation "P" => Primary c G
local notation "K" => Precision.Key F G
local notation "X" => Positions P
local notation "Y" => Poll.Body K

variable (ρ : Dir G c→AxisChart G F) (σ C Λ : ℝ)
    (A : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3)) (hg : Larger (G:=G) S)
    (hp : p.Bounds b σ C Λ) (hr : A.Service F b p ρ)
local notation "T" => A.tables b S.patch
include k hg hp
lemma zeroF : priced F k b p 0=0 := (price_identity F k hp hg.1).2.1 -- which arg?
include hr
omit k hg hp in
lemma zeroO : orbit F ρ 0=0 := by unfold orbit Uniform.station; simp [hr.critical.1]
lemma heart (x:X) (hx : ‖x‖ < (T).horizon) (z : Y) : fderiv ℝ (table F k p b) (x,orbit F ρ x) (0,z)=0 := by
  let u:= curve (Uniform.station ρ) x; let M:=priced F k b p
  let L:= combineH (G:=G) F
  have hu : u= L (x,orbit F ρ x):= rfl
  replace hx:=mem_ball_zero_iff.mpr hx
  have hg := (hr.entered hp hg rfl rfl hx k).self_of_nhds
  have ht := hr.pricing hx; have hv := (A.receipt F k hp (by assumption) rfl rfl).1
  have he: ContDiffAt ℝ ω M u:= (hv.born _ (closedBall_subset_ball hv.reserveH_lt ht)).1
  have hz : Slope M u=0:= hg
  have hh : (fderiv ℝ M u).comp (lowerCol (ι:=P) (τ:=K))=0 := ((show HasFDerivAt M (fderiv ℝ M u) (meetVar x (Uniform.station (S:=S) ρ x)) from (he.differentiableAt (by simp)).hasFDerivAt).comp (Uniform.station (S:=S) ρ x) (meet_derivative x (Uniform.station (S:=S) ρ x))).unique ((slope_zero_test he).1 hz)
  change fderiv ℝ (M ∘ L) _ _=_
  rw [fderiv_comp _ (((hu ▸ he) : ContDiffAt ℝ ω M _).differentiableAt (by simp)) L.differentiableAt,L.fderiv]
  exact congr_arg (fun L : Positions K→L[ℝ] ℝ=> L z.ofLp) hh
omit hr in
lemma pulse (x:X) (y : Y) (hy: combineH (G:=G) F (x,y)∈Metric.closedBall 0 (T).safety) :
    let M:= glow F p b k (tint G _ x) (tint G _ y.ofLp)
    M.PosDef ∧ Charge M ((T).gap/2) ∧
      ∀ z:Y, dotProduct z.ofLp (M *ᵥ z.ofLp)=scratch (0,z) (table F k p b) (x,y) := by
  intro M; have hv:= A.receipt F k hp hg rfl rfl |>.1; have hh:= A.full_pack F k hp hg rfl rfl |>.2.2.2.2.2.2.2.2 x y.ofLp hy
  have ht:0<(T).gap:=hv.pos_m
  refine ⟨Charge.positive hh.2.2.1 hh.1 (half_pos ht),hh.2.2.1,fun z=> ?_⟩; exact power F k p b x y z (hv.born _ (closedBall_subset_ball hv.reserveH_lt hy)).1
lemma wakes (x:X) (hx : ‖x‖ < (T).horizon) : let M:= gram F p b ρ k x
    M.PosDef ∧ Charge M ((T).gap/2) ∧ (∀ z, dotProduct z (M⁻¹ *ᵥ z) ≤ ((T).gap/2)⁻¹ * dotProduct z z) ∧
      ∀ z:Y, dotProduct z.ofLp (M *ᵥ z.ofLp)=scratch (0,z) (table F k p b) (x,orbit F ρ x) := by
  intro M
  obtain ⟨h,hq,hx⟩:= pulse F k p b σ C Λ A hg hp x (orbit F ρ x) (hr.pricing (mem_ball_zero_iff.mpr hx))
  refine ⟨h,hq,?_,hx⟩; intro z
  have ht:0<(T).gap:=(A.receipt F k hp hg rfl rfl).1.pos_m
  have hp := Charge.energy_inverse (S:=M) hq (half_pos ht) (isUnit_iff_ne_zero.mpr h.det_pos.ne') z
  let y:=M⁻¹ *ᵥ z
  have he : (z ⬝ᵥ y)^2 ≤ (z ⬝ᵥ z)* (∑ i,y i^2) := by unfold dotProduct; simpa [pow_two] using sum_mul_sq_le_sq_mul_sq Finset.univ z y
  let D:= ((T).gap/2)⁻¹; have hD : 0<D:=inv_pos.mpr (half_pos ht)
  have hh: z ⬝ᵥ z = ∑ i,z i^2 := by simp [dotProduct,pow_two]
  have hv : 0≤ z ⬝ᵥ z:= hh ▸ sum_nonneg (fun _ _=> sq_nonneg _)
  rw [← hh] at hp -- noise
  nlinarith only [mul_le_mul_of_nonneg_left hp hv,he,mul_nonneg hD.le hv] -- z hp syntactic
section brush
-- radii polynomial bookkeeping
variable (D : ℝ) (he : 1 ≤ D) (hC : (Fintype.card (Joint F G):ℝ) ≤ D)
include he hC

def mineshaft (j:ℕ) (V : ChartPrices) (D:ℝ) := tollS D (j+3) V.value * (1+V.initial)

omit hr in
lemma trench (x : X×Y) (hx: combineH (G:=G) F x∈ball 0 (T).initial) : Brush (n+3) (mineshaft n T D) 1 (table F k p b) x := by
  have hv:= (A.receipt F k hp hg rfl rfl).1
  have hh:= horizon0 he hC (show 0 ≤ (T).value from hv.pos_C.le) hv.pos_a hv.pos_r (zeroF F k p b σ C Λ hg hp) (by omega) hx (fun i hi=> ⟨(hv.born _ hi).2,(hv.born _ hi).1⟩)
  have ht:= Brush.reading (combineH (G:=G) F|>.toContinuousLinearMap) hh (feesComb (G:=G) F); rw [one_mul] at ht; exact ht

omit he k hg hp hr in
lemma countsK : (Fintype.card K:ℝ) ≤ D := le_trans (by exact_mod_cast Fintype.card_le_of_injective (f:=Sum.inr (α:=P) (β:=K)) Sum.inr_injective) hC
omit he k hg hp hr in
lemma countsP : (Fintype.card P:ℝ) ≤ D := le_trans (by exact_mod_cast Fintype.card_le_of_injective (f:=Sum.inl (α:=P) (β:=K)) Sum.inl_injective) hC

def lensT (n:ℕ) (V : ChartPrices) (D : ℝ) := V.zone + tollS D (n+2) (pathCost V (n+2))
lemma luminous (x : X) (hx : x∈ ball 0 (T).horizon) : Brush (n+2) (D*lensT n T D) 1 (orbit F ρ) x := by
  have hu:= Counter.service hr hp hg rfl rfl k
  obtain ⟨h,hD,hQ,hH⟩:= (hu.carrier hx).2 (n+2) le_rfl
  have hb:= byline he (countsP F D hC) hD.le (hr.series hx) (mem_closedBall_zero_iff.mp (hr.landed hx)) h hH
  exact Brush.report hb _ (transit1 K he (countsK F D hC))

def Mvolume (V : ChartPrices) (n : ℕ) := logging V.coords n (transit V n) (V.gap/2) (chargeBill V n)
def thickness (V : ChartPrices) (n : ℕ) (D : ℝ) := tollS D (n+1) (Mvolume V n)*(1+V.horizon)
lemma patented (x : X) (hx : ‖x‖ < (T).horizon) : Brush (n+1) (thickness T n D) 1 (fun x=> Lantern.shade (gram F p b ρ k) x-Lantern.shade (gram F p b ρ k) 0) x := by
  let t:= Mvolume T n; replace hx:=mem_ball_zero_iff.mpr hx
  have hu y hy:= Counter.service hr hp hg rfl rfl k|>.alongShell (x:=y) hy
  have hh :0<t:=logging_pos (hu x hx).rate_pos (hu x hx).mass_pos (hu x hx).cost_pos
  have hv := logRate_pos («K»:=(T).coords) (N:=n) (hu x hx).rate_pos (hu x hx).mass_pos (hu x hx).cost_pos
  let f x:= Real.log (gram F p b ρ k x).det
  have he := horizonB (u:=f) he (countsP F D hC) hh.le hv hr.x_pos (Nat.succ_pos _) hx (fun i hi=> ⟨((hu i hi).whole_log).2,((hu i hi).whole_log).1⟩)|>.2
  refine ((he.smul (1/2)).climb (mul_le_of_le_one_left he.nonneg (by norm_num)) le_rfl).shimmy (Eventually.of_forall fun i=>?_)
  change f i/2-f 0/2=1/2*(f i-f 0); ring
end brush
end YM.PhysicalNext.Repeat.Lapis
