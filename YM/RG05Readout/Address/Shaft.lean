import YM.RG05Readout.Address.Ribbon
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{N m p d:ℕ} {s K α β γ A c t e:ℝ}
    {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "Z"=> (C.path.levels.clock.op m p)
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "Kc"=> kappa C.path
local notation "O"=> Bud C p m
local notation "ψ"=> child C p m
local notation "L"=> C.path.S.block m
local notation "λ₀"=>(((L).val:ℝ)^d)
local notation "I"=> Palette C d
local notation "J"=> Mark C d
local notation "tilt"=> amplify d C L
local notation "N₀"=> Fintype.card J
local notation "η'"=> decay d L K c α* shiftFee (M).p
local notation "ϑ"=> tollP d K c β
local notation "π"=> tollV d L K c α β*shiftFee (M).p
local notation "Ω"=> margin d c K
local notation "v₀"=> wrap_price d C* Trace.Physical.Germ.wraps (M).p (C.side (m+1) p)
local notation "v₁"=> wrap_price d C* Trace.Physical.Germ.wraps (R).p (C.side m p)
variable {T:∀ i:Letter d,Heading (C.labels.level (kept i))} (hw:Plot D s K c α β T)
variable {u:∀ i:Bud C p m,(C.path.rep N p (m+1)).activities.Moves (1:Signed) (child C p m i)}
-- Step defect exact.
variable {T':Tape G (C.side (m+1) p)} {B B' e Q e':ℝ}
variable (W:Palette C d→ₗ[ℂ]Tape G (C.side m p)) (hb: Group C N m p d W B')
-- same Train.Stop at chosen graph. Contract no approximation reset.
include hb hw
lemma nil_step (h:C.Makes)(hm:m<N) (u:∀ i:Bud C p m,(C.path.rep N p (m+1)).activities.Moves (1:Signed) (child C p m i))
    (P: Tape G (C.side (m+1) p))(X:Palette C d)(s₀:ℝ)(hc: Printed C d M 0 (Kc (m+1)) P X 0 s₀) (hs:Turns (K:=K) (β:=β) (c:=c) (α:=α) (γ:=γ) C N m p d B) :
        let P':= Ω*(λ₀*v₀)+η'; let V':=(1+v₁)*P'; let δ':=ϑ*(λ₀*v₀)+π
        ∃ U: Tape G (C.side m p), ∃ x : Palette C d,size x ≤ V'*s₀∧ Train (d:=d) D u P U (δ'*s₀)∧ ∃ y:Palette C d, Printed C d R 0 (Kc m) (U-W x) y 0 ((P'+B'*V')*s₀):=by
     intro P' V' δ'; obtain ⟨l,hS,hF⟩:= yield_now D hw u h hm; obtain ⟨U,x,z,hT,hK,hO⟩:= hF P X _ _ hc
     have h0s:=hc.nonneg
     have he:= wraps_paid d C hc hs.bound hs.bill
     rw [zero_sub,size_neg] at he
     let v:=tilt X; have hp:size v≤ (λ₀*v₀)*s₀:=((size_tuned ..).trans ((mul_le_mul_of_nonneg_left he (pow_nonneg (by positivity) _)).trans_eq (mul_assoc ..).symm))
     have hΩ:0 ≤ Ω:= mul_nonneg (add_nonneg (sCpos (zero_le_one.trans hw.cursor.fits)) (aCpos (zero_le_one.trans hw.cursor.fits))) (zero_le_one.trans hw.posp)
     have hv:0 ≤ v₁:= mul_nonneg (zero_le_one.trans (price_nn ..)) ((Real.exp_pos _).le)
     have hw' : Ω*size v+η'*s₀ ≤ P'*s₀:= le_trans (add_le_add_left (mul_le_mul_of_nonneg_left hp hΩ) _) (by unfold P'; ring_nf; exact le_rfl)
     have hx:=hT.grow hw'
     have he: size z ≤ P'*s₀:= le_trans (size_compare z _) (le_trans (add_le_add (echo_bill L l hS.paid X) hO) hw')
     let p':=hw.cursor.sense d le_rfl; obtain hc':=wraps_paid d C hx p'.order p'.power
     have hX : size x ≤ V'*s₀:= le_trans (size_compare x z) ((add_le_add he hc').trans_eq (by unfold V';ring))
     refine ⟨U,x,hX,hK.easier ?_,?_⟩
     · unfold δ'; rw [add_mul]; apply add_le_add_left
       rw [mul_assoc (ϑ)]; exact mul_le_mul_of_nonneg_left hp (mul_nonneg (aCpos (zero_le_one.trans hw.cursor.fits)) (by have hs:=hw.posp; have ht:=hw.cursor.fits; have hδ:=hw.b_pos; positivity))
     obtain ⟨q,hq⟩:= hb.capacity0 (-x); rw [size_neg] at hq; have hQ := hx.addP hq (h.wilson.represents N p m hm.le).good p'.order p'.power; rw [map_neg,add_neg_cancel] at hQ; rw [sub_eq_add_neg]; exact ⟨_, hQ.grow (le_trans (add_le_add_right (mul_le_mul_of_nonneg_left hX (zero_le_one.trans hb.pos)) _) (by ring_nf; exact le_rfl))⟩
end YM.RG05Readout.Address
