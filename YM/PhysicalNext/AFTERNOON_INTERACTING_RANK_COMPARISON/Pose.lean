import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cues
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Further.FREE_COVARIANCE_KP.KP.Episode
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Reheat
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Reads
import YM.Push.FREE_RESOLVENT.Fees
import YM.Push.GRID_APPROXIMATION.Roll
import YM.Push.PRICE_COMPILER.Compiler
import YM.UVNext.PRICED_KERNELS.Echo


/-!
# One pose of the coarse field V

Rank wants comparisons over masks that can grow faster even than radiusB
(can't take a fixed tier). Earn instead from the Rank threshold and the
specific `spine` gauge (used in Rank) directly. Then get 45C-type viewing
permits on this very gauge at every readable address sufficiently interior.
And don't take kernels at differently tuned clipping/exponents or unpadded
m-cuts. Clearance of A from the mask is critical here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     Next.Rank Tapes Perch Paint Spindle 
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma phase_fit : ∀ᶠ x in atTop, phase x ≤ temp x := by
  filter_upwards [phaseFit,eventually_gt_atTop 0] with x h hx
  have hh : regular x=temp x := by simp [regular,temp,bill,Perch.boil,Perch.y,Vac.Numbers.Hat]
  rw [← hh]; linarith only [h, alpha_phase x hx]

def poseRules (G : Gauge) := Classical.choice (charts G)

-- budget after q
structure Enclosed (q : ℕ) (G : Gauge) (x : ℝ) : Prop where
  starts : 200 ≤ radiusB x
  brims : radiusB (retime x)≤ 4*radiusB x
  lower : 0<phase x
  upper : phase x = temp (retime x)
  spun : 4*((q*walls x:ℕ):ℝ)*phase x ≤ (poseRules G).c
  cuff : 2*(4*((q*walls x:ℕ):ℝ)*phase x) ≤ clearanceFare (retime x)/2
  fares : clearanceFare (retime x) ≤ (poseRules G).c

lemma encloses (q : ℕ) (G : Gauge) : ∀ᶠ x in atTop, Enclosed q G x := by
  have hχ := poseRules G|>.radius
  have hv : ∀ᶠ x in atTop, clearanceFare x≤(poseRules G).c := by
    filter_upwards [(boundary_limited 1 zero_le_one).eventually (ge_mem_nhds hχ)] with x hx; exact (one_mul _).symm.trans_le hx
  filter_upwards [burst_limit,tall_limit.eventually hv,eventually_gt_atTop 0,Work.E01.radiusB_tendsto.eventually_ge_atTop q,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 200,brims] with x hP₀ hc hx he h hi
  let m:=(radiusB x:ℝ); let P:=(q:ℝ)*m^2
  have hm : 1 ≤ m := by unfold m; exact_mod_cast (show 1≤radiusB x by omega)
  have hP : P=((q*walls x:ℕ):ℝ) := by unfold P m walls; push_cast; rfl
  have hZ : 2*(4*((q*walls x:ℕ):ℝ)*phase x) ≤ clearanceFare (retime x)/2 := by
    rw [←hP]; unfold clearanceFare; push_cast
    have hf : 1 ≤ (Fintype.card PlaqAxes : ℝ) := by norm_cast
    have hz : 0≤ m := zero_le_one.trans hm
    have ht : 0 ≤ temp (retime x):=(alpha_phase x hx).le.trans hP₀.2.2.symm.le
    let p:=(radiusB (retime x):ℝ); have hm' : m ≤ p:=Nat.cast_le.mpr hi.1; have hv : 1≤p:= hm.trans hm'
    have hp : P ≤ m^3 := (mul_le_mul_of_nonneg_right (show (q:ℝ) ≤ m from Nat.cast_le.mpr he) (sq_nonneg m)).trans_eq (by ring)
    have hs : m^3 ≤ (2*(p+1)+1)^5 := le_trans (pow_le_pow_right₀ hm (by norm_num : 3 ≤ 5)) (pow_le_pow_left₀ hz (by linarith : m≤2*(p+1)+1) _)
    change 2*(4*P*phase x) ≤ 16*(2*(p+1)+1)^5*(Fintype.card PlaqAxes:ℝ)*temp (retime x)/2
    have ht : P*phase x ≤ (2*(p+1)+1)^5*Fintype.card PlaqAxes*temp (retime x) := mul_le_mul ((hp.trans hs).trans
      (le_mul_of_one_le_right (by positivity) hf)) hP₀.2.2.symm.le (alpha_phase x hx).le (by positivity)
    linarith only [ht]
  exact ⟨h,hi.2,alpha_phase x hx,hP₀.2.2.symm,by linarith only [hZ,hc,hχ],hZ,hc⟩

section paid
variable {W q : ℕ} {o u : Site c} {x : ℝ} {V : Config G c}
    {A : Stores S}
def clearMargin (A : Stores S) (o : Site c) (W : ℕ) := Disjoint (Spindle.patch W o) A.place

/-- Fix z at `fingers V`. Thus exactly in the output frame of the
leading moments, not an approximate path or rotating at wave estimates. -/
structure Pose (A : Stores S) (o : Site c) (W : ℕ) (x : ℝ) (V : Config G c) (v : Dir G c) : Prop where
  glisten : Healthy (phase x) (Spindle.patch W o) V
  border : 2*(W+1)<c.val
  tolls : A.flags= RG.flags (temp (retime x)) V
  worth : ‖v‖≤ clearanceFare (retime x) / 2
  wires (i : Bond c) : i∈Room o W → spine V o i = represent v i
  center (i : Site c) : separation o i+walls x ≤ W → Clears A (retime x) i (radiusB (retime x)) ∧
    AgreeNear id i (radiusB (retime x)) (spine V o) (represent v) ∧ paid S (replica S.ratio (spine V o)) i (radiusB (retime x)) (clearanceFare (retime x))

lemma inland (h : 200 ≤ radiusB x) (hb : radiusB (retime x) ≤ 4*radiusB x) : 11*radiusB (retime x)+1 ≤ walls x := by
  let a:= radiusB x
  have he : 200 ≤ a:=h
  change 11*radiusB (retime x)+1 ≤ a^2
  change radiusB (retime x) ≤ 4*a at hb
  have ht : 200*a ≤ a^2 := (Nat.mul_le_mul_right a he).trans_eq (pow_two a).symm
  omega

lemma posing (he : Enclosed q G x) (hW : W ≤ q*walls x) (h : clearMargin A o W)
    (hp : 2*(W+1)<c.val) (hA : A.flags= RG.flags (temp (retime x)) V) (hv : Healthy (phase x) (Spindle.patch W o) V) : ∃ v, Pose A o W x V v := by
  let I:= poseRules G
  have hc : clearanceFare (retime x) ≤ I.c := he.fares
  let t:=phase x
  have ht:=he.lower; change 0<t at ht
  have hs : 4*W*t ≤ 4*((q*walls x:ℕ):ℝ)*t := by gcongr
  obtain ⟨hP,Hk,-⟩ := closer I hp V hv 1 zero_lt_one he.lower (hs.trans he.spun)
  let a := wired 1 o W V
  have hx : ‖a‖ ≤ clearanceFare (retime x) / 2 := by
    change ‖a‖ ≤ _ / 1 at hP; rw [div_one] at hP; exact hP.trans ((mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 2)).trans he.cuff)
  have hh : 0 ≤ clearanceFare (retime x) := by linarith only [hx,norm_nonneg a]
  let C i := if h':i∈Room o W then a ⟨i,h'⟩ else 0
  let v : Dir G c := fun i => C (i.1,axisEquiv.symm i.2)
  have hz i (hl : i∈Room o W) : spine V o i=represent v i := by
    rw [← show G.lieExp ((1:ℝ) • a ⟨i,hl⟩)= _ from Hk ⟨i,hl⟩,represent,increment,one_smul,Pi.one_apply,mul_one, collect]
    unfold v; dsimp only; rw [← coord_map,axisEquiv.symm_apply_apply, Prod.mk.eta]; simp [C,hl]
  have hY : ‖v‖ ≤ clearanceFare (retime x) / 2 := by
    refine le_trans ((pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr ?_) hx
    intro i; unfold v C; split
    · exact norm_le_pi_norm ..
    rw [norm_zero]; exact norm_nonneg _
  refine ⟨v,hv,hp,hA,hY,hz,fun i hi =>?_⟩
  let T := replica S.ratio (spine V o)
  have hK := inland he.starts he.brims
  have hB : AgreeNear id i (radiusB (retime x)) (spine V o) (represent v) := by
    intro z hu
    change separation i z.1 ≤ _ at hu
    apply hz; apply mem_filter.mpr; refine ⟨mem_univ _,(Spindle.doors z.1).mpr ?_, (Spindle.doors _).mpr ?_⟩
    · apply (separation_triangle _ i _).trans; omega
    refine (separation_triangle o z.1 _).trans (le_trans (add_le_add (separation_triangle _ i _) (Work.E01.sep_step_le ..)) ?_); omega
  refine ⟨?_,hB,fun j hj =>?_⟩
  · intro hL; obtain ⟨z,hz,he⟩:= halo_spec.mp hL; apply Finset.disjoint_left.mp h (Spindle.doors z|>.mpr ?_) hz; rw [separation_comm] at he; apply (separation_triangle _ i _).trans; omega
  have hz : T j=G.lieExp (collect G (blueprint S v) j) := by
    rw [show T j=replica S.ratio (represent v) j from copyAgree _ _ _ _ hB j hj,replica_rep v]
    simp [represent,increment]
  let a:=collect G (blueprint S v) j
  change G.chord (T j) ≤ _
  rw [hz]
  have he' : ‖a‖ ≤ clearanceFare (retime x) / 2 := (norm_le_pi_norm (blueprint S v) (j.1,coord j.2)).trans ((blueprint_bill v).trans hY)
  exact (I.light a (le_trans he' (by linarith only [hh,hc]))).trans (by linarith only [he'])
end paid
end YM.PhysicalNext.InteractingRank
