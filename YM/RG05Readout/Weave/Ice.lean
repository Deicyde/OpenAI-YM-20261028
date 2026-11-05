import YM.RG05Readout.Weave.Bare
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
/-!
# Reprice through registered gates
-/
open Copper
variable {B B' :ℝ}{V:Palette C d→ₗ[ℂ]Tape G (C.side (m+1) p)}
local notation "ℓ"=> C.path.levels.clock.J (m+1)
local notation "n₁"=> C.path.levels
-- expose actual parameters used to derive cone; future transverse needs more quantitative shape gates
structure Wager (P:Palette C d→ₗ[ℂ]Tape G (C.side (m+1) p))(W: Palette C d →ₗ[ℂ]Tape G (C.side m p)) (z:Palette C d ≃ₗ[ℂ]Palette C d):Prop where
   goes : ∀ x:Palette C d, Train (d:=d) D u (P x) (W (z x)) (ld C.path.levels m*size (tilt x))
   strength x : size (tilt x) ≤ ld C.path.levels m*size (z x) ∧ size (z x)≤ ld C.path.levels m * size (tilt x)
   shape : ∃ s K c β T γ, Plot D s K c (Doors.rate L) β (T:∀ i:Native.Letter d,Heading (C.labels.level (kept i))) ∧
          γ=trim L+ oldCost d K*Doors.rate L ∧ Contour C m d (beamCost d c K) c γ z.toLinearMap ∧
          beamCost d c K + γ ≤ ld C.path.levels m
lemma lit_step (h: C.Makes)(hm:m<N)(hc:SignedPrice C m p d N D B B')(hy: Group C N (m+1) p d V B) :
    ∃ W z, Group C N m p d W B' ∧ Wager (D:=D) (u:=u) V W z:=by
   obtain ⟨s,K,c,β,T,Q,H,Hs⟩:= hc.author
   obtain ⟨hT,hX,hu,hW,hxz,hf,hδ,hV,hζ⟩:=Hs
   obtain ⟨W,z,hG⟩:=Onward.can H u h hm hT hy (lit _).le hδ hf hV hc.pos.2 hζ
   let γ:= trim (L)+oldCost d K*Doors.rate (L)
   have hi :beamCost d c K+γ≤ ld C.path.levels m:=by
       have hK:= zero_le_one.trans H.cursor.fits; have hj:=light (L)
       have hL:Doors.rate L≤1:=Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (L).property) (by norm_num)
       apply le_trans _ (show 2*Q+beamCost d c K + (1+ oldCost d K) ≤ _ from hxz); exact add_le_add (le_add_of_nonneg_left (by positivity)) (add_le_add hj (mul_le_of_le_one_right (by unfold oldCost; positivity) hL))
   refine ⟨W,z,hG.back,⟨fun x=>(hG.aligned x).easier ?_,fun x=>⟨(hG.pays x|>.1).trans ?_,(hG.pays x|>.2).trans (mul_le_mul_of_nonneg_right hi (size_ge _))⟩,s,K,c,β,T,γ,H,rfl,hG.shape,hi⟩⟩
   · exact mul_le_mul_of_nonneg_right hW (size_ge _)
   apply mul_le_mul_of_nonneg_right _ (size_ge _); let Ω':=margin d c K; have he:= H.posp; have hv:= zero_le_one.trans H.cursor.fits; have hc:(0:ℝ)≤Ω':= mul_nonneg (add_nonneg (sCpos hv) (aCpos hv)) (zero_le_one.trans he); have h : 0 ≤ oldCost d K:=by unfold oldCost; positivity
   exact le_trans ((le_add_of_nonneg_right (show 0≤ beamCost d c K by change 0 ≤ Ω'+1+c; linarith)).trans (le_add_of_nonneg_right (by linarith))) hxz
local notation "O0" => Trace.Physical.Germ.wraps (M).p (C.side (m+1) p)
local notation "O1" => Trace.Physical.Germ.wraps (R).p (C.side m p)
local notation "P0" => wrap_price d C
lemma dark_step (h: C.Makes)(hm:m<N)(hc:SignedPrice C m p d N D B B') (V:Palette C d →ₗ[ℂ]Tape G (C.side m p)) (hy : Group C N m p d V B') (T:Tape G (C.side (m+1) p))(x:Palette C d)(e:ℝ) (hp:Printed C d M 0 (Kc (m+1)) T x 0 e) :
     let q:= trim L
     ∃ (U:Tape G (C.side m p))(y:Palette C d),
        Train (d:=d) D u T U (ld C.path.levels m*e)∧size y ≤ q * e ∧ ∃ f:Palette C d,Printed C d R 0 (Kc m) (U - V y) f 0 (q*e):=by
   intro q; obtain ⟨s,K,c,β,X,Q,H,Hs⟩:= hc.author
   obtain ⟨hT,hX,hu,hW,hxz,hf,hδ,hV,hζ⟩:=Hs
   obtain ⟨hPp,hQ⟩:=max_le_iff.mp hu
   obtain ⟨U,y,hY,hp',w,ht⟩:= nil_step H V hy h hm u T x e hp hT
   let α:= Doors.rate L
   let hkg:= margin d c K
   let η:= decay d L K c α*shiftFee (M).p
   let b:=hkg*((L).val:ℝ)⁻¹+η
   let p':=hkg*(λ₀ * (P0*O0)) + η
   let v':= (1+P0*O1) * p'
   have hi:= hp.nonneg; have hj:=zero_le_one.trans H.cursor.fits; have hz:=zero_le_one.trans H.posp
   have hc₁:B ≥ 1:= hc.pos.1; have hc₂:B' ≥ 1:=hc.pos.2
   have hξ:=Doors.rate_pos (L)
   have hη:0 ≤ η:= mul_nonneg (decays L hj hz hξ.le) (zero_le_one.trans shift_pays)
   have hhkg:0 ≤ hkg:=mul_nonneg (add_nonneg (sCpos hj) (aCpos hj)) hz
   have hz':0 ≤ p':=by unfold p'; have hw := mul_nonneg (a:=P0) (b:=O0) (zero_le_one.trans (price_nn ..)) ((Real.exp_pos _).le); positivity
   let X0:= L
   have hb:P0*O0≤thin L d:=by rw [(h.wilson.represents N p _ hm).vac];exact hQ
   have hb':P0*O1≤thin L d:=by rw [(h.wilson.represents N p m hm.le).vac];exact hPp
   have hu :λ₀*(P0*O0) ≤ ((X0.val:ℝ)⁻¹):=(mul_le_mul_of_nonneg_left hb (pow_nonneg (by positivity) _)).trans_eq ((mul_comm ..).trans (small_power ..))
   have he':p' ≤ b:= add_le_add_left (mul_le_mul_of_nonneg_left hu hhkg) _
   have hv':v' ≤ 2*b:= mul_le_mul (le_trans (add_le_add_right (hb'.trans (thin_one ..)) _) (le_of_eq (one_add_one_eq_two))) he' hz' zero_le_two
   refine ⟨U,y,hp'.easier (mul_le_mul_of_nonneg_right ?_ hi), (hY.trans (mul_le_mul_of_nonneg_right (hv'.trans ?_) hi)), w,ht.grow (mul_le_mul_of_nonneg_right ?_ hi)⟩ -- ?_ order
   · let v:= tollV d L K c α β*shiftFee (M).p; let M':=tollP d K c β; have hp₀ := H.b_pos; have hx : 0≤ M':=mul_nonneg (aCpos hj) (by positivity)
     have he:= mul_le_mul_of_nonneg_left hu hx; have hv:= hT.loop; 
     apply le_trans ?_ hW
     have ht : ((X0.val:ℝ)⁻¹) ≤ 1:= inv_le_one_of_one_le₀ (by exact_mod_cast X0.property)
     have h' := (he.trans (mul_le_of_le_one_right hx ht)); exact add_le_add (h'.trans (by linarith only [hx])) (le_mul_of_one_le_right hv hc₁)
   · apply le_trans ?_ hX
     have h : 0 ≤ b:=hz'.trans he'
     change _ ≤ b+B'*(2*b); exact (le_mul_of_one_le_left (by positivity) hc₂).trans (le_add_of_nonneg_left h)
   exact (add_le_add he' (mul_le_mul_of_nonneg_left hv' (zero_le_one.trans hc₂))).trans hX
end YM.RG05Readout.Address
