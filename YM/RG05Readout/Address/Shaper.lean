import YM.RG05Readout.Address.Groove
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}
variable {C:Family G} {N m p d:ℕ}{δ:E4}
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level
local notation "Y"=> C.params
local notation "S"=> C.localSection
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
local notation "ℓ"=> (((L).val:ℝ)⁻¹)
variable {s t K u τ α c β a:ℝ}{D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} (hp:Cursor C N m p d s K) (h:C.Makes)(hm:m<N)(hx:SoundDoor (C.path.levels.clock.op m p) D)(hδ: δ∈Native.box)
variable (k:Letter d)(o:Site (C.side (m+1) p)) (j:(C.labels.level (kept k)).Index) {T:Heading (C.labels.level (kept k))}
local notation "W"=> F (kept k)
variable (ho:(C.path.levels.clock.op m p).ratio.parent o=0) (hw: Pricing (C.localSection (kept k)) C.path N p m C.params D T a c α β)
local notation "Ct"=> (Fintype.card (Letter d):ℝ)
def regain (d:ℕ)(K:ℝ):= (stCost d K+aCost d K)
include hp h hm hδ ho hw
lemma regular_curve (P:Coefficient W (C.side (m+1) p))(hP:P.Format o Y M)(h₁:P.remBound o M (κ (m+1)) t)(h₂:P.x=0)(hα:0 ≤ α)(hκ:κ (m+1) ≤ 1) :
      let X:= (glyph (readJ k 0) (invoice P o (S (kept k)) M)).comp (Native.pull δ ℓ)
      ∃ F':Tape G (C.side m p),∃ x z:Palette C d, Course (D:=D) o X F' x z (stCost d K*(α*t)) (aCost d K*((2+α)*t+K*(α*t))) ∧ size x ≤ aCost d K*(α*t):=by
   intro X; let y:= invoice P o (S (kept k)) M
   obtain ⟨Q,hp',hh,hR,hg⟩:= regular_grant C N m p (kept k) o D h hm ho hw P hα hκ hP h₁ h₂; have hK:=zero_le_one.trans hp.fits; have ht:= rem_nonneg h₁
   obtain ⟨V,x,z,hA,hV,hF⟩:= primitive hp h hm hw.soundD hδ k 0 Q y o hp' hh hR (fun i hi=> False.elim (Nat.not_lt_zero _ hi)) hα
   refine ⟨V,x,z,⟨hA.paid.grow ?_,hA.ready.extend ?_⟩,?_⟩
   · let a:= (W).coeffSize Q.x; let e:=α*t; refine le_trans (b:=K*(K*e+(2*K*e+e))+Ct*K^2*(2*K*e+e)) ?_ (le_of_eq ?_)
     · change K*(K*a+(2*K*a+e))+Ct*K^2*(2*K*a+e) ≤ _; gcongr
     · unfold stCost e;ring
   · unfold aCost; gcongr
   exact (hV.trans (mul_le_mul_of_nonneg_left hg (by positivity))).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) (mul_nonneg hα ht))

-- Tail atoms migrate at d stage as further suppressed L^{-1}; no reproject. scalar stamps. Non-leading all the way.
section
omit hp ho hδ hw k T
variable {b:ℝ} {g:Heading (C.labels.level 0)} (he:Pricing (C.localSection 0) C.path N p m C.params D g a c α β)
    (h₀:MapsTo (fun x=>δ+(((C.path.S.block m).val:ℝ)⁻¹) • x) Native.box Native.box)
-- per unit (ScalarCoord norm+t). v weighted. keep separate arcs for branch charges.
include he h₀ ho
lemma high_curve (f:PulseC) (hz:Tail d f)(hv:Priced d f b)(P:Coefficient (C.labels.level 0) (C.side (m+1) p))(hP: P.Format o Y M)(hT:P.remBound o M (κ (m+1)) t)(hc:1 ≤ c)(hα:0≤α)(hβ:0 ≤ β)(hκ:κ (m+1)≤1):
     let W':=(F 0).coeffSize P.x
     let Y':= c*W'+α*t
     let V:= (glyph f (invoice P o (S 0) M)).comp (Native.pull δ ℓ)
     ∃ (Q:Tape G (C.side m p)), Course (d:=d) (D:=D) o V Q 0 0 (b*ℓ*(Y'+Y')) (b*ℓ*((1+c+β)*W'+ (2+α)*t)):=by
    intro W' Y' V; obtain ⟨Q,hQ,hX,hW,hF⟩:= rough C N m p 0 o D h hm ho he hα P hc hβ hκ hP hT
    have hℓ:0 < ℓ:= inv_pos.mpr (by positivity); have hL:1 ≤ ((L).val:ℝ):=by exact_mod_cast (L).property
    let s:= f.comp (Native.pull δ ℓ)
    have hv' : Tail d s ∧ Priced d s (b*ℓ^(d+1)):=tail_aff d f hℓ.le ((inv_le_one₀ (by positivity)).mpr hL) δ h₀ hz hv
    let H':=(v) • (glyph s (invoice Q 0 (S 0) R))
    simp only [pow_zero,one_mul] at hX hW hF -- also step? hW twice
    have ht : H'=glyph s (invoice (stretch (v) Q) 0 (S 0) R):=by rw [invoice_stretch]; exact (glyph_stretch ..).symm
    have hu : ‖(v)‖ * ℓ^(d+1) = ℓ:=by
       simp only [Complex.norm_pow,Complex.norm_natCast]
       rw [pow_succ,inv_pow,←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
    have hv'' : Necklace (F 0) (S 0) Y R 0 (κ m) d 0 0:= Necklace.empty
    have hg : ‖v‖* (F 0).coeffSize Q.x ≤ ‖v‖*Y':= mul_le_mul_of_nonneg_left hF (norm_nonneg _)
    have hh: (F 0).coeffSize (stretch (v) Q).x ≤ ‖v‖*Y':= (Size.smul ..).trans_le hg
    have ha := Printed.grow (printed_high s hv'.1 hv'.2 (stretch (v) Q) (stretch_format _ hQ) (stretch_rem _ hX)) (le_refl _)
    rw [←ht] at ha
    refine ⟨H',⟨ha.grow ?_,?_⟩⟩
    · have hx := add_le_add_left hh (‖v‖*Y') -- incorrect
      let y:= b*ℓ^(d+1); have hy : 0 ≤ y:= Priced.nonneg d hv'.2
      apply (mul_le_mul_of_nonneg_left hx hy).trans_eq ?_; unfold y; nth_rw 2 [← hu]; ring
    intro φ x hg; let Φ:=s φ; rw [show V φ=Φ • invoice P o (S 0) M from rfl,show H' φ = (v*Φ) • (invoice Q 0 (S 0) R) from (smul_smul (v) Φ _)]
    apply (hW.matchPay Φ (v*Φ) v (mul_one _)).cost
    have hl:1≤ ‖v‖:= by simp only [Complex.norm_pow,Complex.norm_natCast]; exact one_le_pow₀ hL
    rw [max_eq_right (a:=‖Φ‖) (b:=‖v * Φ‖) (by rw [norm_mul]; exact le_mul_of_one_le_left (norm_nonneg _) hl), norm_mul]
    have hφ : ‖v‖ * ‖Φ‖ ≤ b*ℓ*x:= (mul_le_mul_of_nonneg_left (hv'.2 _ x hg) (norm_nonneg _)).trans_eq (by rw [←mul_assoc, mul_left_comm,hu])
    exact (mul_le_mul_of_nonneg_right hφ hW.nonneg).trans_eq (mul_right_comm ..)
end
end YM.RG05Readout.Address
