import YM.RG05Readout.Grants.Volume
import YM.RG05Readout.Address.Ribbon
/-!
# Wrap under ratio powers repaid once per step
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Copper
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native Address
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}
-- exponent ≤- (d+1) sufficient for advance.
def thin (P:Side)(d:ℕ):ℝ:= ((P.val:ℝ)^(d+1))⁻¹
lemma wraps (S:Family G)(h:G.Simple)(d:ℕ):∀ᶠ m in atTop,∀ p:ℕ,
        let q (k):= wrap_price d S*Trace.Physical.Germ.wraps (S.path.levels.budget k) (S.side k p);
        q m ≤ thin (S.S.block m) d ∧ q (m+1)≤ thin (S.S.block m) d:=by
    let A:=S.path.levels; let L:=S.S; let t:=L.scale
    have ht:= L.divergent; have hw:Height L atTop t id 1:= level_height tendsto_id; have hu:= hw.step A.fits.mesh
    let F i:=((L.block i).val:ℝ); have hp(i):0<F i:=by unfold F; positivity
    have he : RateIs atTop t F 0:=by
       have hf:RateIs atTop t (fun i=> L.a i / L.a (i+1)) (-1- -1):= hw.mesh.div hu.mesh
       have h' (i):F i= L.a i/L.a (i+1):= by rw [L.a_step]; unfold F; field_simp [(L.a_pos i).ne']
       simp_rw [← h',sub_self] at hf; exact hf
    have hv := oversized A h 2
    have hz:= tendsto_atTop_mono (f:=id) (g:=Nat.succ) (fun i=>(Nat.le_succ i)) tendsto_id
    let c:= wrap_price d S
    have hq: RateLE atTop t (fun i=> c*(F i)^(d+1) *Real.exp (-2*t i)) (-2):=by
        have h₁:= ((RateLE.const c ht).mul ((he.power (d+1)).pays ht)).mul (RateLE.exp (-2) ht)
        simpa only [mul_zero,add_zero,zero_add] using h₁
    filter_upwards [hv,hz.eventually hv,hq 0 (by norm_num)] with i hi hk hl p
    have hN: c*(F i)^(d+1)*Real.exp (-2*t i)≤ 1:= (le_abs_self _).trans (by simpa using hl)
    have hp': t i ≤ t (i+1):=(scale_mono _).monotone i.le_succ
    have hF : c*Real.exp (-2*t i)≤thin (L.block i) d:=by
        rw [thin,← one_div]; exact (le_div_iff₀ (pow_pos (hp i) _)).mpr (le_trans (le_of_eq (mul_right_comm c _ _)) hN)
    intro q; have hc:0 ≤ c:=zero_le_one.trans (price_nn ..)
    exact ⟨le_trans (mul_le_mul_of_nonneg_left (hi p) hc) hF,le_trans (mul_le_mul_of_nonneg_left ((hk p).trans (Real.exp_monotone (mul_le_mul_of_nonpos_left hp' (by norm_num)))) hc) hF⟩
end YM.RG05Readout.Copper
