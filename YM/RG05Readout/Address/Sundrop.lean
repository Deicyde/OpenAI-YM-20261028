import YM.RG05Readout.Address.Convoy
/-!
# Supplies and graph step

Parent coordinates and true arc. Separate epsilon bills for wrap. Use real,
not label, `X`, so must repay those both in forward geometry and in looking
back to the pivot. No derivative analyticity asserted.
-/
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

structure Group (C:Family G)(N m p d:ℕ)(V:Palette C d→ₗ[ℂ]Tape G (C.side m p)) (B:ℝ):Prop where
    capacity0(x):∃ z:Palette C d,Printed C d (C.path.rep N p m) 0 (kappa C.path m) (V x) z x (B*size x)
    pos : 1 ≤ B
variable (C d m N p)
-- orientation slack. choose τ
structure Turns (B:ℝ): Prop where
    -- epsilon absorption, incl K preL profile prices. C chooses B after observing levels, substantial
    bound : d ≤ (M).p.order
    bill  : d ≤ (M).p.power
    rear : λ₀*(v₀*B)≤1
    grasp:η'*B ≤ 1
    loop:0 ≤ π -- problematic β var
    shave: v₁*((2*Ω+1)*λ₀)+η'*B+Ω*(λ₀*(v₀*B))≤ γ
    cap : γ ≤ 1
variable {C d m N p}

variable (h:C.Makes)(hm:m<N)
def ahead (K c:ℝ)(d:ℕ):= 2*margin d c K+1
section curve
variable {V:Palette C d→ₗ[ℂ]Tape G (C.side (m+1) p)} {B:ℝ} (H: Group C N (m+1) p d V B) {l:Mark C d→Palette C d}(ht:South (c:=c) (K:=K) (α:=α) (T:=T) (m:=m) l)
-- rates purchases; future wrench argument.
local notation "c₀"=> ahead K c d
include hw hm h H ht u
omit h hm in
lemma angle (hc:Turns (K:=K) (β:=β) (c:=c) (α:=α) (γ:=γ) C N m p d B) -- order edit
    (hP:∀ (x y : Palette C d)(r:ℝ)(F : Tape G (C.side (m+1) p)),Printed C d M 0 (Kc (m+1)) F x y r → ∃ U z, Made (d:=d) (c:=c) (K:=K) (α:=α) (β:=β) D u l F x r U z) :
      ∀ i: J,∃ (U:Tape G (C.side m p))(w z:Palette C d), size z ≤ (Ω+1)*chargeN L i ∧ Printed C d R 0 (Kc m) U w z (c₀*chargeN L i) ∧ Train (d:=d) D u (V (ticket i)) U ((2*ϑ+π*B)*chargeN L i) ∧
         size (Address.clear C d (weights i) (z-leadScale C L i (T i.1)))≤ γ+oldCost d K*α:=by
     intro i; obtain ⟨pα,hR⟩:= H.capacity0 (ticket i); rw [size_ticket, mul_one] at hR
     obtain ⟨U,k,w,hF,hV,hx⟩:= hP _ _ _ _ hR -- Made with implicit fields
     let mu:=chargeN L i; have hi : 1 ≤ mu:=charge_one L i  
     let f:=v₀*B
     have hf:size (pα-ticket i) ≤ f:=by rw [size_turn]; exact wraps_paid d C hR hc.bound hc.bill
     let y:=size (tilt pα); have hT: size (tilt (ticket i))=mu:=by rw [ticket_charge,size_smul,size_ticket,mul_one,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hi)]
     have ht' : size (tilt (pα-ticket i)) ≤ λ₀*f:= (size_tuned ..).trans (mul_le_mul_of_nonneg_left hf (by positivity)); let V':=Slide pα l
     have hx' : y ≤ 2*mu:=by
          apply (size_compare _ (tilt (ticket i))).trans
          rw [hT,← map_sub]; have hκ:=ht'.trans hc.rear -- fix
          linarith only [hκ,hi]
     have hΦ : size (V'-l i) ≤ Ω*(λ₀*f):=by
          let p:Palette C d→ₗ[ℂ]I:= (slide_linear l).mk' _; rw [←ticket_self i l]
          change size (p _-p _) ≤ _; rw [← map_sub]
          exact (echo_bill L l ht.paid _).trans (mul_le_mul_of_nonneg_left ht' (mul_nonneg (add_nonneg (sCpos (zero_le_one.trans hw.cursor.fits)) (aCpos (zero_le_one.trans hw.cursor.fits))) (zero_le_one.trans hw.posp)))
     have hΩ:0 ≤ Ω:= mul_nonneg (add_nonneg (sCpos (zero_le_one.trans hw.cursor.fits)) (aCpos (zero_le_one.trans hw.cursor.fits))) (zero_le_one.trans hw.posp)
     have hp : Printed C d R 0 (Kc m) U w k (c₀*mu):=by
          apply hF.grow; change Ω*y+η'*B≤ _
          apply (add_le_add (mul_le_mul_of_nonneg_left hx' hΩ) hc.grasp).trans; unfold ahead; linarith only [hi]
     have ha:=hw.cursor.sense d le_rfl
     have hc₁ : 0 ≤ v₁ := mul_nonneg (zero_le_one.trans (price_nn ..)) ((Real.exp_pos _).le)
     have hv:size (k - w)≤ v₁*(c₀*λ₀):= le_trans (wraps_paid d C hp ha.order ha.power) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (charge_global ..) (by unfold ahead; positivity)) hc₁)
     have hj:size (k-l i) ≤ γ:=le_trans ((le_of_eq (congr_arg size (show k-l i=(k-w)+(w-Slide pα l)+(Slide pα l - l i) from by abel))).trans ((size_add ..).trans (add_le_add ((size_add ..).trans (add_le_add hv hx)) hΦ))) hc.shave
     refine ⟨U,w,k, (size_compare k (l i)).trans ((add_le_add (ht.paid i) (hj.trans (hc.cap.trans hi))).trans_eq (by ring)), hp,?_,?_⟩
     · refine hV.easier ?_; have ht0 : 0≤ ϑ:=by unfold tollP; have hpp:= aCpos (d:=d) (zero_le_one.trans hw.cursor.fits); have hK:=zero_le_one.trans hw.cursor.fits; have hb:=hw.b_pos; have hc:=hw.posp; positivity
       have hs := mul_le_mul_of_nonneg_left hx' ht0; have hk:= H.pos
       have he : π*B ≤ π*B*mu:= le_mul_of_one_le_right (mul_nonneg hc.loop (zero_le_one.trans hk)) hi
       change ϑ*y+_ ≤ _ * mu; linarith only [he,hs]
     exact (le_of_eq (congr_arg (fun z:Palette C d=> size (Address.clear C d (weights i) z)) (show k-leadScale C L i _=(k-l i)+(l i-leadScale C L i (T i.1)) from by abel))).trans (by rw [map_add]; exact (size_add ..).trans (add_le_add ((size_cap ..).trans hj) (ht.grants i)))
end curve
end YM.RG05Readout.Address
