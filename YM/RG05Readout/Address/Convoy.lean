import YM.RG05Readout.Address.Upwind
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{N m p d:ℕ} {s K α β γ A c t u:ℝ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p)
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "δ"=> displacement C p m
local notation "L"=> C.path.S.block m
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "∂"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K
local notation "U"=> Palette C d
local notation "J"=> Mark C d
local notation "N₀"=> (Fintype.card (Mark C d):ℝ)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))}
def above (k:ℕ)(x:Palette C d): Palette C d:=x-(Address.clear C d k) x
lemma clear_above (k:ℕ)(x:Palette C d): size (above k x) ≤ size x:=by
    unfold size; apply Finset.sum_le_sum; intro i _; unfold val above Address.clear; simp only [Pi.sub_apply]; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; split <;> simp

-- retain actual on all higher lifts on a given horizon. charge on exact map itself preL.*
lemma sails_now {Q:Mark C d→ Palette C d} {ξ:ℝ} (hw:Plot D s K c α β T)
    (hy:∀ i,size (Q i) ≤ ξ* chargeN L i)(hg:∀ i,size (Address.clear C d (weights i) (Q i - leadScale C L i (T i.1))) ≤ γ):
    Contour C m d (ξ+c) c γ (IsLinearMap.mk' (fun x=>Slide x Q) (slide_linear _)):=by
    let H(i:J):= Address.clear C d (weights i) (leadLean (T:=T) i)
    let V(i:J):= ((chargeN L i:ℂ)⁻¹) • above (weights i) (Q i)
    let W(i:J):= V i+H i; have hl(i:J):0 < chargeN L i:=lt_of_lt_of_le zero_lt_one (charge_one ..)
    have hy'(i:J): size (V i) ≤ ξ:=by
       unfold V; rw [size_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hl i).le]; exact (mul_le_mul_of_nonneg_left ((clear_above ..).trans (hy i)) ((inv_pos.mpr (hl i)).le)).trans_eq (by rw [mul_left_comm,inv_mul_cancel₀ (hl i).ne',mul_one])
    have hc(i j:J)(he:weights j ≤ weights i): val (W i) j= val (leadLean (T:=T) i) j:=by
       change val (V i) j+ val (H i) j=_
       unfold V H val Address.clear above; simp only [Pi.smul_apply, Pi.sub_apply]
       change _ • (_-(if weights j ≤ weights i then _ else _))+(if weights j ≤ weights i then _ else _)=_
       rw [if_pos he, if_pos he,sub_self,smul_zero,zero_add]
    have ht:BeamLine C d W (ξ+c) c:=⟨fun i=>(size_add ..).trans (add_le_add (hy' i) ((size_cap ..).trans (leans i hw|>.1))),fun i=> hc i i le_rfl ▸ (leans i hw|>.2.1),fun i j he hj=> (hc i j he).trans ((leans i hw).2.2 j hj he)⟩
    refine ⟨W,ht,fun x=>?_⟩
    let f:=fun i:Mark C d=> (↑(chargeN L i):ℂ)
    have hB (i:J) : size (Q i-f i • W i)≤ γ:=by
       rw [show Q i-f i • W i= Address.clear C d (weights i) (Q i-leadScale C L i (T i.1)) from ?_]
       · exact hg i
       unfold W V H; rw [smul_add,smul_smul, show (f i)*(chargeN L i:ℂ)⁻¹=1 from mul_inv_cancel₀ (by unfold f; exact_mod_cast (hl i).ne'),one_smul]; unfold above; rw [map_sub, lead_pay, map_smul]; unfold f; abel
    change size (Slide x Q-Slide (amplify d C L x) W) ≤ _
    unfold Slide; rw [← Finset.sum_sub_distrib]; apply (size_sum ..).trans; rw [size,Finset.mul_sum]
    refine Finset.sum_le_sum fun i _=>?_; rw [amplifies, mul_comm (γ), mul_comm ((↑(chargeN L i):ℂ)),mul_smul, ← smul_sub,size_smul]
    exact mul_le_mul_of_nonneg_left (hB i) (norm_nonneg (val x i))
end YM.RG05Readout.Address
