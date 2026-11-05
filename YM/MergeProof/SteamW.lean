import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.MergeProof.KeyWest
import YM.MergeProof.Stove
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Proceed
import YM.Progress.CLASSICAL_KIN_RECURSION.Delta
import YM.Push.LOOP_COEFFICIENT.Resolution

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion Spindle Atlas Cells PhysicalNext.InteractingRank
open RG.Supply PhysicalNext.Repeat.Legato.Bandage Next.Rank.Perch Tapes Peak Flux Ac 
    Station Spec Vac.Numbers
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}(C:Family G)(d:ℕ) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
-- eventually financial:
def generator (G:Gauge)(d:ℕ):ℝ:=2*(winter G d+1:ℕ)
lemma tremor {d:ℕ} (b : ℝ) {r:ℝ}(he : generator G d≤r) : ∀ᶠ x in atTop,∀ (s:ℝ),0 ≤ s→ bill b x*s ≤ bill (-8) x→ Hat x ^ r*s≤ fog G d x:=by
   let w:= winter G d; let c:= -(8+b)
   -- s ≤ exp(c*(loglog x)^2)< x
   have hp : ∀ᶠ x:ℝ in atTop,c*boil x ≤ Real.log x := by
      have hz := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp y_rate).const_mul c
      rw [mul_zero] at hz
      filter_upwards [hz.eventually (ge_mem_nhds zero_lt_one), Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hx ht
      change c*(y x^2*Real.exp (-(y x))) ≤ 1 at hx
      have ht':Real.exp (y x)=Real.log x:=Real.exp_log ht
      rw [Real.exp_neg,ht', ← mul_assoc, ← div_eq_mul_inv] at hx
      exact (div_le_one ht).mp hx
   filter_upwards [hp,eventually_gt_atTop (1:ℝ)] with x hz hx s hs hv
   have hX:=zero_lt_one.trans hx
   have hT:0 < Hat x:=inv_pos.mpr (Real.sqrt_pos.mpr hX)
   rw [mul_comm] at hv
   have hξ : s ≤ x:=by
      apply (le_div_iff₀ (show 0<bill b x from Real.exp_pos _)|>.mpr hv).trans
      unfold Next.Rank.Perch.bill; rw [← Real.exp_sub]; exact (Real.exp_monotone (by linarith only [show -(8+b)*boil x ≤ Real.log x from hz])).trans_eq (Real.exp_log hX)
   have h : Hat x≤1:= (inv_le_one₀ (Real.sqrt_pos.mpr hX)).mpr (Real.one_le_sqrt.mpr hx.le)
   apply (mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hT h he) hξ hs (Real.rpow_nonneg hT.le _)).trans
   unfold generator; rw [show (2:ℝ)*((winter G d+1:ℕ):ℝ)=(↑(2*(w+1)):ℝ) by push_cast;rfl]
   rw [Real.rpow_natCast,pow_mul]; have hp: Hat x^2=x⁻¹:=by unfold Hat; rw [inv_pow,Real.sq_sqrt hX.le]
   rw [hp,pow_succ]; unfold fog; rw [inv_pow, mul_assoc, inv_mul_cancel₀ hX.ne',mul_one]
-- one arity, general probes. trade towards mark - ultimately can pass.
variable (H:C.Makes) (hG:G.Simple) (h:Geyser C W u ψ φ δ ζ r D) (ht:∀ i,1 ≤ r i)
include H hG h ht
lemma quaking {b a c:ℝ}(hb:0<b) {m:ℕ}{Y:Points (m+1)} (he:Y∈generic _)(hz: (ζ d)= fly C.path.levels d)(hv:generator G d ≤ c): ∀ᶠ k in atTop, Fit C.path.levels b k Y→Allowed C.path.levels b k→ ∀ (hk:C.ref d ≤ k),∀ N,∀ (hN:k<N),∀ p,∀ τ: Course C N p k,∀ v: Fin (m+1)→ C.label d,
       (∀ j,bill a (clim C.path.levels k)* moneys C d k N p (v j) ≤ bill (-8) (clim C.path.levels k)) → Stake m Y b hN.le v H hk τ (Hat (clim C.path.levels k)^c):=by
   filter_upwards [Edition.raise C Y hG he hb, (hat_rate C.path.levels hG).eventually (tremor a hv)] with k hk hv hy hA hK N hN p τ v hW
   let Q:= C.path.rep N p k; have ht': Q.p=C.path.levels.budget k:=(H.wilson.represents N p k hN.le).vac; let x:=clim C.path.levels k
   let z:= seats C b Y hN.le p; have hx:0<x:= zero_lt_one.trans (C.path.levels.fits.delayed _); have hz':0< Hat x^c:= Real.rpow_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hx)) _
   have hV : Edition.Spaced Q.p.B z:=by rw [ht']; exact hk hy hA _ _ _
   refine caught C N k p d m v b Y hN H hK τ h ⟨fun _ _ i hi j hj hh=> hV i j hh⟩ (fun x=> (Extra.Multi.Occupancy.of_injective (injected _ z Q.p.B_pos hV) x).trans (ht k)) hz' (fun i=> ?_)
   rw [hz]; exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (paid_pos ..) (C.path.levels.params k).columns_ge) hz'.le).trans (hv _ (money_nn ..) (hW i))
variable {e:ℝ}
lemma bursts {S:Table C.book} (X:Columns C S d) (F:Cohesion C d) (hz: (ζ d)= fly C.path.levels d)(hv:generator G d ≤ F.mark) {O:HaarBudget G} : ∀ᶠ k in atTop,Metering F O k e→ LanternMarks H F X k:= by
   filter_upwards [eventually_all.mpr (fun i=> quaking C d H hG h ht (a:=F.pan) F.hr (X.row i).probes hz hv)] with k hk hp
   intro hi he; let t:= (F.current k).band; have hE: t= F.fixed:= F.sameB _
   have hx: Allowed C.path.levels t k:= hp.cost.coup.heft
   filter_upwards [eventually_gt_atTop k] with N hN ht p i v hV
   rw [show (F.current k).band=F.fixed from hE]; apply hk i (hE ▸ he i) (hE ▸ hx) hi N hN p _ v hV
end YM.MergeProof.Accent
