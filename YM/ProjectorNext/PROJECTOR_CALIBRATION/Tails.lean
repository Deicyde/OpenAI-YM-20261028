import YM.Next.BOUNDARY.Synchronize
import YM.Next.EXTRACTION.Basis
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Model

/-! # Tails on the physical fits. No assumption on growth beyond the actual makes & Simple.

Schedule receipts used only for the finite accuracy, no implicit RRequirements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Function Filter Labels Work Tensor Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge}
open Next.Scheduling

/-- The two parameters used in the approximation. hatted threshold,
*actual* coupling (include deficit/running and regulator p convention). -/
def pair (C : Family G) (N p : ℕ) : ℝ × ℝ :=
    let θ:= C.path.levels.clock.threshold N
    (θ,(C.beta N p)⁻¹ / θ^2)

theorem withering {C : Family G} (he : C.Makes) (hG : G.Simple) (per : ℕ → ℕ) :
    Tendsto (fun N => pair C N (per N)) atTop (𝓝 0) := by
  let A:=C.path.levels
  let c:=A.clock
  let f:= c.hatBeta
  let M:= c.monitor
  have hf : Tendsto f atTop atTop := tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have hw (N : ℕ) : Clock.watch 2 (f N)=M N := Clock.watch_two _
  have hg : Tendsto M atTop atTop := by
    convert (Clock.growing (by norm_num : (0:ℝ)<2)).comp hf using 1
    exact (funext hw).symm
  have ht : Tendsto c.threshold atTop (𝓝 0) := by
    convert (Clock.light 2 1 1 (by norm_num)).comp hf using 1; funext N; dsimp only [comp_apply]
    rw [Real.rpow_one,Real.rpow_one,hw,mul_comm]; rfl
  refine ht.prodMk_nhds ?_
  let g (N : ℕ) := (C.beta N (per N))⁻¹ / c.threshold N^2
  show Tendsto g atTop (𝓝 0)
  have hy (N) : 0 < f N := lt_trans zero_lt_one (A.fits.delayed N)
  have hz (N) : f N / 2 ≤ C.beta N (per N) := (he.wilson.represents N _ N le_rfl).band.1
  have hv (N) : 0 < C.beta N (per N) := (half_pos (hy N)).trans_le (hz N)
  have hM (N) : 0<M N := Real.exp_pos _
  have hU : Tendsto (fun N => 2*((M N)⁻¹)^2) atTop (𝓝 0) := by
    simpa using (hg.inv_tendsto_atTop.pow 2).const_mul 2
  refine squeeze_zero (g:=fun N => 2*((M N)⁻¹)^2) (fun N => ?_) (fun N => ?_) hU
  · unfold g; have h := hv N; positivity
  let x:= C.beta N (per N)
  let u:= f N
  let y:= M N
  let r := Real.sqrt u
  have e : 0 < r := Real.sqrt_pos.2 (hy N)
  have H : r^2=u := Real.sq_sqrt (hy N).le
  have i : 0 < y := hM N
  have a : 0 < x := hv N
  change x⁻¹ / (r⁻¹*y)^2 ≤ 2*y⁻¹^2
  field_simp
  linarith [hz N]

private lemma uniformly (p : ℕ → ℕ → Prop) (h : ∀ u : ℕ → ℕ, ∀ᶠ N : ℕ in atTop,p N (u N)) :
    ∀ᶠ N : ℕ in atTop, ∀ v, p N v := by
  classical
  let u (N : ℕ) : ℕ := if h : ∃ i, ¬p N i then h.choose else 0
  filter_upwards [h u] with N hN v
  by_contra hv
  have hh : ∃ i, ¬p N i := ⟨v,hv⟩
  exact hh.choose_spec (by simpa [u,hh] using hN)

variable {d : ℕ}

lemma paid (S : Schedule) (s : Finset Cover) :
    ∀ᶠ N : ℕ in atTop, ∀ p, ∀ x∈s, ∀ i : Axis,20*((x i).natAbs+1)≤(S.side N p).val := by
  have h (x : s) (i : Axis) : ∀ᶠ N : ℕ in atTop,20*((x.val i).natAbs+1)≤(S.denominator N).val :=
    S.den_strict.tendsto_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_all.mpr (fun x => eventually_all.mpr (h x))] with N hN p x hx i
  exact (hN ⟨x,hx⟩ i).trans (Nat.le_mul_of_pos_left _ (S.period p).property)

namespace Machine
variable {C : Family G} (M : Machine C.params d)

theorem funded (hG : G.Simple) (he : C.Makes) (I : Finset (Lens G d)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ) (E : Packet C d N p), M.lined E →
      ∀ i k, k ∈ I → let F := C.labels.level d; let x := parameters F i
        ‖E.amount x k-probe F k (M.trophy F x)‖ ≤ ε := by
  let F := C.labels.level d
  let f (i) (k : Lens G d) (w : ℝ×ℝ) := ∑ l : F.Index, ((parameters F i).val l)*M.calendar F l k w.1 w.2
  have hf (i) (k : Lens G d) : Continuous (f i k) := continuous_finsetSum _ fun l _ =>
    continuous_const.mul (M.smooth_calendar F l k).continuous
  have hz i (k : Lens G d) : ∀ᶠ N : ℕ in atTop,∀ p, ‖f i k (pair C N p)-f i k 0‖ ≤ ε := by
    refine uniformly _ fun u => ?_
    refine ((hf i k).tendsto 0 |>.comp (withering he hG u)).eventually (p:=fun y => ‖y-f i k 0‖ ≤ ε) ?_
    filter_upwards [Metric.closedBall_mem_nhds (f i k 0) hε] with x hx
    simpa [dist_eq_norm] using hx
  filter_upwards [paid C.S M.curtain,eventually_all.mpr fun i => eventually_all.mpr (fun k : I => hz i k)] with N hN hh p E h i k hk
  dsimp only
  rw [M.calendar_eq E M.served (hN p) h, M.spends]
  exact hh i ⟨k,hk⟩ p

end Machine
end YM.ProjectorNext.Calibration
