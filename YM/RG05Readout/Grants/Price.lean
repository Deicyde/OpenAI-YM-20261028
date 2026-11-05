import YM.RG05Readout.Grants.Pinned
/-!
# After thresholds. Clearance for winding receipts on ANY period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Copper
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native Address
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{m N p d:ℕ} {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "L"=> C.path.S.block m
local notation "Λ"=> (((L).val):ℝ)
local notation "A"=> C.path.levels
-- supply graph geometric prices Tail. Using budgets in common C, not Hessian forms.
def ld (P:Levels G)(m):= lamp (P.S.block m) (P.clock.J (m+1))
variable {s K B B' Q c t β :ℝ}
local notation "Z!"=> C.path.rep N p m
local notation "Z'"=> C.path.rep N p (m+1)
local notation "ξ"=> Doors.rate L
local notation "q"=> trim L
local notation "π"=> margin d c K
local notation "j"=> (A).clock.J (m+1)
local notation "F₁"=> (Trace.Physical.Germ.wraps (Z!).p (C.side m p))
local notation "F₂"=> (Trace.Physical.Germ.wraps (Z').p (C.side (m+1) p))
local notation "scale!"=> wrap_price d C
local notation "O"=> Bud C p m
-- precisely matched bounds through terminal-normalized Demand history
structure SignedPrice (C:Family G) (m p d N:ℕ) (D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))(B B':ℝ):Prop where
   author : ∃ s K c β:ℝ, ∃ (T:∀ i:Native.Letter d,Heading (C.labels.level (kept i))) (Q:ℝ), Plot (C:=C) (d:=d) D s K c (Doors.rate (C.path.S.block m)) β T ∧
            let L':= C.path.S.block m; let X:= margin d c K*((L'.val:ℝ)⁻¹) + decay d L' K c (Doors.rate L') *shiftFee (C.path.rep N p (m+1)).p; let w (k):= wrap_price d C * Trace.Physical.Germ.wraps (C.path.levels.budget k) (C.side k p)
            Turns (K:=K) (β:=β) (c:=c) (α:=Doors.rate L') (γ:=trim L') C N m p d B ∧
            X+ B'*(2*X)≤ trim L' ∧
            max (w m) (w (m+1))≤ thin L' d ∧
            2*tollP d K c β+tollV d L' K c (Doors.rate L') β*shiftFee (C.path.rep N p (m+1)).p*B ≤ ld C.path.levels m ∧
            2*Q+beamCost d c K+(1+ oldCost d K) ≤ ld C.path.levels m ∧
            0 ≤ Q∧clipPrice (Fintype.card (Mark C d)) d (beamCost d c K) c ≤ Q∧ Q*(trim L'+oldCost d K*Doors.rate L') ≤ 1/2∧
            ahead K c d*(2*Q)≤ B'
   pos : 1≤ B ∧ 1 ≤ B'
   caps : B+B' ≤ ld C.path.levels m
-- numeric assembly any true family with delivered budget
lemma light (L₀:Side):trim L₀ ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast L₀.property) (by norm_num)
lemma lit (L₀:Side):0 < trim L₀:= Real.rpow_pos_of_pos (by positivity) _
lemma small_power (d : ℕ)(P:Side) : thin P d * (P.val:ℝ)^d=(P.val:ℝ)⁻¹:=by
    have hp : (P.val:ℝ) ≠ 0:= by positivity
    unfold thin; field_simp; ring
lemma thin_one (d : ℕ)(P:Side): thin P d ≤ 1:= (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by exact_mod_cast P.property))
variable {T:∀ i:Native.Letter d,Heading (C.labels.level (kept i))}
variable (h:C.Makes)(hm:m<N)
include h hm
lemma enamel (hw:Plot D s K c (Doors.rate L) β T)(hC:Crossed d (j) L ((A).params (m+1)) c K B B' Q β)(hz : 0≤ Q)
  (hp: clipPrice (Fintype.card (Mark C d)) d (beamCost d c K) c ≤ Q)(h_t : ahead K c d*(2*Q) ≤ B')
  (ha : 1 ≤ B) (ha' :1 ≤ B')
  (hh : max (scale!*F₁) (scale!*F₂) ≤ thin L d) :
    SignedPrice C m p d N D B B':=by
    have hH := h.wilson; let X' := (A).params (m+1); have hf : (Z').p=(A).budget (m+1):= (hH.represents N p _ hm).vac
    have hR : (Z!).p=(A).budget m:= (hH.represents N p m hm.le).vac
    have hw' := (hw.cursor.sense d le_rfl); have hk := zero_le_one.trans hw.cursor.fits; have hc := zero_le_one.trans hw.posp; have hξ:0 < ξ:=Doors.rate_pos _
    have hs₀:= hw.b_pos; have hx : shiftFee (Z').p = roughT X':=by rw [hf];rfl
    obtain ⟨h10,h11⟩:=max_le_iff.mp hh
    have he : ((Λ)^d)*(scale!*F₂*B)≤ (Λ)⁻¹*B:=by
       rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans ha)
       exact (mul_le_mul_of_nonneg_left h11 (pow_nonneg (by positivity) _)).trans_eq ((mul_comm ..).trans (small_power ..))
    have hB:0 ≤ π:=mul_nonneg (add_nonneg (sCpos hk) (aCpos hk)) hc
    refine ⟨⟨s,K,c,β,T,Q,hw,?_⟩,⟨ha,ha'⟩,hC.supp⟩
    intro L' X w; dsimp only[L']; unfold X
    rw [hx]; refine ⟨?_,?_,?_,hC.tickets,hC.modest,hz,hp,hC.fares,h_t⟩
    · refine ⟨?_,?_,he.trans hC.warm,(by rw [hx]; exact hC.lapse),?_,?_,light (L)⟩
      · rw [hf]; rw [hR] at hw'; -- danger rewriting dep binder proof
        exact hw'.order.trans ((A).fits.deepOrder m.le_succ)
      · rw [hf]; rw [hR] at hw'; exact hw'.power.trans ((A).fits.deepPower m.le_succ)
      · have ht := aCpos (d:=d) hk
        exact mul_nonneg (add_nonneg (mul_nonneg ht (by positivity)) (by positivity)) (zero_le_one.trans shift_pays)
      rw [hx]; apply le_trans _ hC.small; refine add_le_add (add_le_add_left ?_ _) (mul_le_mul_of_nonneg_left he hB); apply (mul_le_mul_of_nonneg_right h10 (by positivity:0 ≤ (2*π+1)*Λ^d)).trans_eq
      rw [mul_left_comm,small_power,mul_comm]
    · have ht:=hC.sink
      let X0:= grant d L K c X'; change (1+B'*2)*X0 ≤ trim L at ht; change X0+B'*(2*X0)≤trim L; linarith
    unfold w; rw [hR,hf] at hh; exact hh
end YM.RG05Readout.Copper
