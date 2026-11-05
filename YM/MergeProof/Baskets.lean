import YM.MergeProof.Balloon
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(v:C.label d)(a:ℝ)(ha:0<a)(B:Stock.Tabs C.path.levels)
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Geyser C W u ψ φ δ (fly C.path.levels) r D) (hx:∀ i:ℕ, 1≤r i)
set_option quotPrecheck false
local notation "b!"=> Cells.center C.S p
local notation "T"=> C.path.levels
local notation "A"=> Site (C.side m p)
local notation "P"=> C.path.levels.budget
local notation "F"=> C.labels.level d
-- centered at site zero only. Root N large after m. Works when opens L.T. 
include ha
-- reserve Micro metering: Use known proof of log telescoping on SAME profiles.Hat β
lemma cheap (hG:G.Simple)(hK:Mix.paidL C) {u:ℝ}(hu:0<u) : ∀ᶠ k in atTop, 6-Real.log (plumR C d a k) ≤ (d+u)*C.S.scale k:=by
   let n:= 2*winter G d; let f:=Mix.width C a n
   obtain ⟨hz,he⟩:= Work.I04.answer G hG a C n ha hK
   have ht : Tendsto (fun i=>u/2*C.S.scale i) atTop atTop:= C.S.divergent.const_mul_atTop (half_pos hu)
   filter_upwards [ht.eventually_ge_atTop 1, he _ (half_pos hu)] with i hi hx'
   unfold plumR -- invalid
   rw [Real.log_mul (pow_pos (C.S.a_pos _) _).ne' (hz i).ne', Real.log_pow,Stock.a_log _ i,Real.log_exp]
   have hK: (1:ℝ) ≤ Nat.factorial ((C.path.levels.params i).order):= by exact_mod_cast Nat.factorial_pos _
   have hg0 := div_le_self (hz i|>.le) hK
   have hg : Real.log (Mix.last C i (f i)) ≤ Real.log (f i):=Real.log_le_log (div_pos (hz i) (zero_lt_one.trans_le hK)) hg0
   change 5 - Real.log (Mix.last C i (f i)) ≤ _ at hx'; change 6 - (_* -(C.S.scale i) + Real.log (f i)) ≤ _
   linarith only [hi,hx',hg]

local notation "T!"=> Stock.Tabs.chosen C.path.levels 1 B
include B
lemma coastwise (hG:G.Simple)(hK:Mix.paidL C) {u:ℝ}(hu:0<u): ∀ᶠ m in atTop, expense C a m (T! m) d ≤ ((d:ℝ)+u)* C.S.scale m:=by
  let p:= T!; let z := min (u/4) (u/(4*((d:ℝ)+u)))
  have h0:0<z:=by unfold z; positivity
  have hz := B.pay (T) 1 le_rfl _ h0
  have hp:∀ i,i ≤ p i:=fun i=>(Stock.Tabs.opened (T) 1 B i).1
  have hP:Tendsto p atTop atTop:=tendsto_atTop_mono hp tendsto_id
  filter_upwards [hz,hP.eventually (Vac.treasury_stage _ hG),hP.eventually (cheap C d a ha hG hK h0)] with i hi hT hE
  let r:= p i; let b:=T; let w:= C.S.a i/C.S.a r; let q:=Vac.fiat G (b.params r) (b.clock.hatBeta r); let t:= C.S.scale r; let v:= C.S.scale i
  change w^4*q ≤ z*t at hi; change Vac.treasury b r ≤ q at hT
  have hs:1 ≤ w:= (one_le_div (C.S.a_pos r)).2 (C.S.strictAnti.antitone (hp i))
  have hB:1 ≤ q:=by
    unfold q Vac.fiat
    have he := (b.params r).paths_pos
    have ha := (b.params r).clip.quadratic_pos
    have hp : 0≤ (Fintype.card PlaqAxes:ℝ)*((b.params r).clip.direct + (b.params r).paths^2) + 4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log (b.clock.hatBeta r)/2) := by
      have hu := Real.log_pos (b.fits.delayed r)
      positivity
    linarith only [hp,he]
  have hW : t-v≤ z*t:=by
    have hf : t - v = Real.log w:= by
       unfold t v Schedule.scale w; rw [Real.log_div (C.S.a_pos _).ne' (C.S.a_pos _).ne',Real.log_inv, Real.log_inv]; ring
    rw [hf]; exact (Real.log_le_self (zero_le_one.trans hs)).trans (le_trans ((pow_one w).symm.trans_le (pow_le_pow_right₀ hs (show 1 ≤ 4 by norm_num))) ((le_mul_of_one_le_right (by positivity) hB).trans hi)) -- log_le_self positive require
  let d':ℝ:= d
  have hw : 0 < d'+u:= by unfold d'; positivity
  have hZ:z≤u/(4*(d'+u)):= min_le_right ..
  have hh : z*(4*(d'+u))≤u:= (le_div_iff₀ (by positivity)).mp hZ
  have ht':0≤ t:= Shoot.scale_nn b r
  have hq := mul_le_mul_of_nonneg_right (le_of_lt hu) ht'
  have hx:= (mul_le_mul_of_nonneg_left hT  (by positivity : 0≤w^4)).trans hi
  change w^4 * Vac.treasury b r +6-Real.log (plumR C d a r) ≤ (d'+u)*v
  change 6-Real.log (plumR C d a r) ≤ (d'+z)*t at hE
  linarith only [hE,hq,hx,mul_le_mul_of_nonneg_left hW hw.le,mul_le_mul_of_nonneg_right hh ht',mul_le_mul_of_nonneg_right (show z ≤ u/4 from min_le_left _ _) ht']
end YM.MergeProof.Accent
