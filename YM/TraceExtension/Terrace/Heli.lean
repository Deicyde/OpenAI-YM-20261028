import YM.TraceExtension.Terrace.BackWind
import YM.TraceExtension.Shepherd.Folly
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Climb Analysis Work Weir
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Relay Shepherd Menu
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
def coast (x:ℝ)(m:ℕ):= (m+wheelQ x)*(4*radiusB x+2)+10*radiusB x
lemma coasts(m:ℕ): ConstMass 0 (fun x:ℝ=>(coast x m:ℝ)):=by unfold coast;push_cast; exact ((((mass (Nat.cast_nonneg _)).gather (bankH 60)).cop ((upperB.times _ (by norm_num)).gather (mass (by norm_num)))).gather (upperB.times _ (by norm_num)))
-- use booking practice around.B Temporal.H
abbrev auraQ (A:Levels G)(l:ℕ) :Prop:= ∀ᶠ k in atTop,let P:=A.params k; let x:=A.clock.hatBeta k; ∀ (w:ℝ),1 ≤ w → w ≤ Real.exp ((prism x:ℝ)/32) →∀ (n:Side)(R:Rep G n)(Λ:ℝ), Age P x Λ R→∀ z:ℝ, Shepherd.tariff R (wingC R z P.width P.paths Λ) (2*hue x) ≤ 1 → ExpenseH P.paths Λ (Weir.smoke x) (Weir.hue x) 1 P.width x z w R l (wheelQ x) (prism x)
variable (C)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> C.path
local notation "H!"=> (A).clock.hatBeta
local notation "S"=> C.S
variable (P:C.Makes)(h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
include P h θ
private def bench (x:ℝ)(m:ℕ):= 10*coast x m+2+100*high x+64*radiusB x *prism x+2*radiusB x+5
omit P in
lemma pegged (m:ℕ):∀ᶠ i:ℕ in atTop,let k:=summit A i; room A i k (2*coast (H! k) m) ∧ ∀ p:ℕ, bench (H! k) m < (C.S.toDepth (Terrace.stellar A i|>.le) p).count.val:=by
   have he: ConstMass 0 (fun x=>(bench x m:ℝ)):=by
       unfold bench; push_cast; exact (((((((coasts m|>.times _ (by norm_num)).gather (mass (by norm_num))).gather (expansion.times _ (by norm_num))).gather ((upperB.times _ (by norm_num)).cop (bankH 40))).gather (upperB.times _ (by norm_num))).gather (mass (by norm_num))))
   have hh :∀ᶠ x:ℝ in atTop, (((2*coast x m):ℕ):ℝ) ≤ x∧ (bench x m:ℝ)+1 ≤ x:=by
       have hx:= ((coasts m).times 2 zero_le_two); filter_upwards[(ferry hx) 1 zero_lt_one,(ferry (he.gather (mass zero_le_one))) 1 zero_lt_one] with x hi he; push_cast; exact ⟨hi.2.trans (Real.rpow_one _).le, he.2.trans (Real.rpow_one _).le⟩
   let κ:= summit (A)
   filter_upwards [(Sstar _).eventually ((hrate (A) h).eventually hh), (Kagura (d:=1) A h θ), toll_small (x:=1) one_pos (stickK _ h θ)] with i hi hp hh k
   refine ⟨hp _ ((hi.1).trans_eq (pow_one _).symm),fun p=>?_⟩
   let Y:= (S).toDepth (Terrace.stellar (A) i|>.le) p; have ht: (Y.count.val:ℝ)=C.S.a i/C.S.a k:=by rw[eq_div_iff (C.S.a_pos k).ne',mul_comm]; exact C.S.embeds_scale Y
   let v:= bench (H! k) m; apply (Nat.cast_lt (α:=ℝ)).mp; rw [show _ =_ from ht,z_scale]; exact (lt_of_lt_of_le (by linarith: (v:ℝ)< (v:ℝ)+1) (hi.2.trans (hh.trans (Real.exp_monotone (by change _ ≤ gap (A) i k; exact (mul_le_of_le_one_left (gate_le _ ((A).fits.delayed _)|>.le) (by norm_num)).trans (gstar ..))))))
variable {r:ℕ→ℕ}{δ u:ℕ→ℝ}{W:∀ N p k:ℕ,k<N→GaugeDoor (C.path.rep N p (k+1)) (C.path.rep N p k)}
variable (hp:Moonlit C.path r (renal C.path.levels) u W)(hr:∀ᶠ i in atTop,2 ≤ r i)
include hp hr K
lemma trod (l:ℕ)(hX:auraQ C.path.levels l) : ∀ᶠ i:ℕ in atTop,let k:=summit (A) i;let t:=(H! k); let P:=(A).params k; let d:=wheelQ t; let e:= ((A).clock.loopCap k)
    ∀ p N:ℕ,∀ hk:k≤N,let R:=C.path.rep N p k; let n:= C.side k p; Age P t e R→∀ (x:Site n)(j:Axis)(ν:G.El→ G.El)(f:Config G n→ G.El →ℂ)(Y:Support n)(D:ℝ), ProofC R x f ν Y D→ coverNumber R.p.B Y ≤ l → x∈Y → 0 ∈Y → separation 0 x ≤ high t+1→ (∀ U v, ‖f U v‖ ≤ t)→ tariff R (wingC R D P.width P.paths e) (2*hue t) ≤ 1 →
        (tilesAt C.S p ((stellar A i).le.trans hk)).rootTest (C.beta N p) (backTo C.path N p hk (lensF R x j ν f d)) ≤ Tau (A) i (-1900000) :=by
    let Q:= A; let k':= summit A; obtain ⟨J,hJ⟩:=eventually_atTop.mp hr
    filter_upwards [ pegged C h θ l,(Sstar Q).eventually hX,rateD Q h θ K, ((growthP.comp (hrate Q h|>.comp (Sstar Q))).eventually_ge_atTop 1),open_budget Q h θ K,eventually_ge_atTop J] with i hi he hz hT ht hj k t M d e p N hk R n hR x j ν f Y D hD hU hf hP hx hF hV
    let m:= basin A K i; have ht:m<k:=ht; let y:=prism t; let w:=bountyW A i; have hs:= (hR.hM.2.1)
    have hη:pierSize R.p d l=coast t l:=by unfold pierSize coast; rw [hs]
    apply le_trans (b:=Real.exp ((C.S.a i/C.S.a m)^4 * Vac.treasury (A) m+4)/(w m)^2) _ hz.2.2
    apply garnet P hp x j ν f hD hk ht (unwinds ..) hR.coverage hR.dialect hR.high (fun j hi hK=> hJ _ (hj.trans ((unwinds ..).trans hi))) l d y hT hU hf hP _ _ _ (bell Q k|>.le) hF w (fun i hi he=> zero_lt_one.trans_le (stipend ..)) (fun j hi he=> hz.2.1 j ((unwinds ..).trans hi) he)
    · have h:= he (w k) (stipend ..) hz.1 n R e hR D hV; rw [Harmony Q k] at h; exact h
    · intro hk'; rw[show (T!).rep N p k=R from rfl]
      have ht:bench t l < ((C.S.toDepth hk' p).count.val):= hi.2 p; unfold bench at ht; rw[hη,hs]; unfold y;omega
    rw [hη]; exact hi.1
end YM.Trace.Terrace
