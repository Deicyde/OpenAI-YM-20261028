import YM.MergeProof.North.Wicker
import YM.Progress.CLASSICAL_KIN_RECURSION.Weir
import YM.Push.LOOP_COEFFICIENT.Block.Explain
import YM.Push.LOOP_COEFFICIENT.Fine.Budgets
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d h:ℕ){x:ℝ} {j : ℕ→ℕ}
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "J"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
variable (hG:G.Simple)(t:ℝ) (hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hj:Tendsto j atTop atTop) -- notation binder
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hV:Velour C (renal C.path.levels) r D')
variable {b a:ℝ}(hb:0<b)(ha:0<a)(hp:D+h=d+4)
local notation "F"=> fun i=> fuga C.path.levels (i+1)
local notation "A"=> fun (i:ℕ)=> whims C (j i) i d h b a
local notation "Z'"=> fun (i:ℕ)=> ventola C.path.levels (j i) (i+1) δ η (δ (i+1)) ((A) i)
local notation "N"=>Note C.S
local notation "M"=> (((d:ℝ)+4+8)*(1-t))
open Accent
include hj hT hV hG
lemma pica {w:ℕ→Bool→ℝ}(v:Bool)(hw:N (fun i=>w i v) x): N (fun i=> picket C.path.levels (j i) (i+1) δ η (δ (i+1)) (w i) v) (x+4*(1-t)):=by
   have hh:C.S.Gentle:=C.path.levels.fits.mesh; obtain ⟨hs,he⟩:= mintN C hG
   have hF:=Note.note_a C.S; have hx:= ((hs.relay j hj hT).mills ((he.relay j hj hT).mills hw)).splits (Note.notes C.S 16 (by norm_num)); have hb := ((hF.relay j hj hT).splits ((hF.scales hh).scales hh)).powerN 4 -- ratio
   exact (((hs.scales hh|>.mills ((hs.scales hh).mills (hx.mills hb))).splits ((billed C hG hV).scales hh)).swapP (by push_cast; ring))
include D hp ha hb
lemma quilled : Note C.S Z' (-D + M) :=by
   have hg:= plumN C d hG a ha|>.relay j hj hT; have he:= ((plumN C 4 hG b hb).relay j hj hT).splits (((fuchsia C hG hV).scales C.path.levels.fits.mesh).powerN h); unfold ventola
   apply ((pica _ hG _ hT hj hV (w:=A) false (by exact hg)).mills (pica _ hG _ hT hj hV (w:=A) true (by exact he))).swapP
   have hi:(d:ℝ)+4-h=D:=by exact sub_eq_of_eq_add (by exact_mod_cast hp.symm)
   push_cast; rw [←hi]; ring
omit hG hV hj hT ha hb hp D
variable {u ψ:ℕ→ℝ}{W:Worth}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
local notation "μ"=> fly C.path.levels d
include hW
lemma seeing {b:ℝ}(hb:0<b)(i k:ℕ)(hk:C.ref d ≤ k)(hi:k ≤ i) : march (fun _:Unit=>b) η k i () ≤ b*((C.S.a i/C.S.a k)^(d+1))* (μ i/μ k):=by
   have hξ: 0< μ k:= hW.grows _ k hk
   induction i,hi using Nat.le_induction with
   | base=> rw [marines k η _ (fun _=>hb),div_self (C.S.a_pos k|>.ne'),div_self hξ.ne',one_pow,mul_one,mul_one]
   | succ i hi ih=>
      simp only [march,if_pos hi]
      let L:ℝ:= (C.S.block i).val; have hp:0<L:=by unfold L; positivity
      let q:= L^(d+1); have hx:0<q:=pow_pos hp _
      have hh':0<η i:= hW.costs.stay.water _ (Nat.zero_le i)|>.1
      let t:= (C.S.a (i+1)/C.S.a k)^(d+1)
      have ht : 0<t:= pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _
      have ht' : t * q=(C.S.a i/C.S.a k)^(d+1):=by unfold t q; rw [←mul_pow, C.S.a_step]; unfold L; field_simp
      have he : b*t*((η i*q*μ i)/μ k)≤ b*t*(μ (i+1)/μ k):= mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hW.jump d i (hk.trans hi)) hξ.le) (by positivity)
      exact (mul_le_mul_of_nonneg_left ih hh'.le).trans ((by rw [← ht']; ring:η i*_ = b*t*((η i*q*μ i)/μ k)).le.trans he)
end YM.MergeProof.Ribbons
