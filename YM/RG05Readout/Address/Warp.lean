import YM.RG05Readout.Address.Fiber
/-!
# Prices required for shortening horizon

Assigned in actual calendar before steps. Bounds uniform in orientation and
horizons through announced horizon; large shrinkage price multiplies only the
converted primary cut. Real full-output guarantees in addition.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}
section low
variable (C:Family G)(N m p d:ℕ) (D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
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

structure Cursor (s K:ℝ):Prop where
   sense z:z≤d→ Readable Y (S z) (R).p (C.path.S.side m p) s
   short g h:h≤ g → g ≤ d →  upgradeCost Y (S g) (S h) s s (R).p.supportExponent ≤ K
   age g h:h≤g → g≤d →  (horizon_cost_price (F h) (F g)).choose ≤ K
   card (i:Letter d):Cap (d+2) (line i) K
   fits : 1≤ K
   earns : pulseFee d ≤ K
   keeper : Nonempty (Keeper ((R).p) ((R).activities))
   stalls : hitWidth (R).p * κ m ≤ 1
variable {C N p m d D}{s t u K:ℝ}{h g:ℕ}
variable (hz:C.Makes) (hm:m<N) (P:Cursor C N m p d s K)
section
variable {b:Site (C.path.S.side (m+1) p)} {V:Three G (C.path.S.side (m+1) p)}
include P hm hz
lemma Cursor.reshape (U:Coefficient (C.labels.level g) (C.side m p))(hw:h ≤ g)(hl:g≤d)(hQ: SoundDoor Z D)
    {χ:ℂ} (hf:U.Format 0 Y R)(hp: U.remBound 0 R (κ m) u) (hB : Ride Z b 0 D χ V (invoice U 0 (S g) R) t):
      let W:= K*(F g).coeffSize U.x
      ∃ Q: Coefficient (C.labels.level h) (C.side m p), Q.Format 0 Y R∧Q.remBound 0 R (κ m) (W+(0+W)+u) ∧ Ride Z b 0 D χ V (invoice Q 0 (S h) R) (t+W) ∧ (F h).coeffSize Q.x ≤ W ∧ ∀ k:ℕ,(F h).coeffSize (basisCut (F h) k Q.x)≤ K*(F g).coeffSize (basisCut (F g) k U.x):=by
       intro Wt; obtain ⟨L'⟩:= P.keeper
       obtain ⟨Q,hF,hD,hK,⟨p',htt,hV⟩,hX⟩:=rewrite_down (S g) (S h) hw U L' hf hp (P.sense g hl) (P.sense _ (hw.trans hl)) (hz.wilson.represents N p m hm.le).good (forcedPos ..) P.stalls; let δ:=horizon_cost_price (F h) (F g)
       have ht:= P.short g h hw hl -- implicit
       have ht':= mul_le_mul_of_nonneg_right ht (Work.G08.size_nonneg (F g) U.x)
       have h0 (k): (F h).coeffSize (basisCut (F h) k Q.x)≤ K*(F g).coeffSize (basisCut (F g) k U.x):=le_trans (δ.choose_spec.2 hw Q.x U.x hX) (mul_le_mul_of_nonneg_right (P.age g h hw hl) (Work.G08.size_nonneg ..))
       refine ⟨Q,hF,rem_mono hK (add_le_add_left (add_le_add ht' (add_le_add_right ht' _)) _),(hB.change (q':=invoice Q 0 (S h) R) hD hQ (Useful.invoice _ _ _ R (hz.wilson.represents N p m hm.le).good hK hF) htt hV).cost (add_le_add_right ht' _),?_,h0⟩ -- hr1 edit
       have he : basisCut (F h) h Q.x=Q.x:= funext fun i=> if_pos ((F h).bound i)
       have ht₀:=(h0 h); rw [he] at ht₀
       exact ht₀.trans (mul_le_mul_of_nonneg_left (cap_rows ..) (zero_le_one.trans P.fits))
end
end low
end YM.RG05Readout.Address
