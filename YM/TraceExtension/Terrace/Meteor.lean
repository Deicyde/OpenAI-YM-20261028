import YM.TraceExtension.Terrace.HomePort
import YM.MergeProof.Dollars
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Next.UVStress
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Next.Rank.Station
open UVNext.FreeStress (camera)
open MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
set_option quotPrecheck false
local notation "A"=>C.path.levels
local notation "T!"=> tilesAt C.S
lemma anti_test {S:Schedule}{G:Gauge}{i j p:ℕ}(h:i≤ j)(U V:Config G (S.side j p)→ℂ)(β:ℝ): (tilesAt S p h).rootTest β (U-V)= (tilesAt S p h).rootTest β (V-U):=by
    rw [← neg_sub V U,← neg_one_smul ℂ (V-U), root_smul];norm_num
variable (h:G.Simple)(θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W)
-- normalized marker representation at *measurement* engineering units a_j. Probe arity-two in the history.
structure Probe (C:Family G)(m j p N:ℕ)(hn:(summit C.path.levels j)<N)(y:C.label 5) :Prop where
     cost : (C.labels.level 5).coeffSize (columns C 5 (summit C.path.levels j) N p y) ≤ (C.S.a j)^5*(C.path.levels.clock.hatBeta (summit C.path.levels j))^m
     hue : night (C.labels.level 5) y
     toll : let V:= C.O N p y 0; let β:=C.beta N p; let B:=(tilesAt C.S p ((stellar C.path.levels j).le.trans hn.le));let v:= Tau C.path.levels j
         ∃ u: Config G (C.side (summit C.path.levels j) p)→ℂ, let A0:= backTo C.path N p hn.le u
             Interior (B.chamber 0) A0 ∧ B.rootTest β (A0-V) ≤ v (-200) ∧ ∀ x z,x≠z→∀ g:Config G (C.side (summit C.path.levels j) p)→ℂ,(∀ U, ‖g U‖ ≤ v 150000) → Interior (Push.GridApprox.window 0 (lensScope C 4)) g →
             room (C.path.levels) j (summit C.path.levels j) (lensScope C 4)→‖pew C.S ((stellar C.path.levels j).le.trans hn.le) β x z A0 (backTo C.path N p hn.le g)‖ ≤ v (-200)
include H h ht θ K hM
lemma mileage (m:ℕ)(v:C.label 4) : ∀ᶠ i in atTop,let k:=summit C.path.levels i; ∀ᶠ p:ℕ in atTop,∀ (N:ℕ) (hn:k < N)(T0:Module.End ℂ (C.label 4)),Tested C 4 i N p T0 →∀ (b:ℝ),1 ≤ b → b ≤ tilt_cap (A) i → let h: i ≤ N:= (stellar C.path.levels i).le.trans hn.le; let T:= tilesAt C.S p h
       (∀ d:ℕ,d ≤ 5 → ∀ v:C.label d,Interior (T.chamber 0) (C.O N p v 0)) → ∀ y, Probe C m i p N hn y→∀ x z:Site (C.side i p),x≠z→ ‖pew C.S h (C.beta N p) x z (C.O N p y 0) (C.O N p (ladd C b i N p 4 T0 v) 0)‖ ≤ Tau (A) i (-100):=by
    filter_upwards [concert h θ K H ht hM m,outside h θ K H ht 4 (by decide) v, toll_small (x:=1) one_pos (sapTree h (A) 4 (by positivity))] with i hi hg hw k
    filter_upwards [hi] with p hp N hn T0 hT b hz he h₀ T hF y hY x z hx
    let t:= Tau (A) i; let β:=C.beta N p; let P:= C.O N p y 0; let Q:= C.O N p (ladd C b i N p 4 T0 v) 0
    have hS:= seamless H N p
    obtain ⟨hQ,g,hG,hC,hR,hB,hz₁⟩:= hg N p hn T0 hT b hz he (hF _ (by decide)); obtain ⟨f,hα,hχ,hD⟩:=hY.toll; let V:= backTo C.path N p hn.le g; let U:= backTo C.path N p hn.le f; have hp': Interior (T.chamber 0) P:= hF 5 le_rfl y; have hq': Interior (T.chamber 0) Q:= hF 4 (by decide) _; let F0:= T.rootTest (G:=G) β
    have hP : F0 P ≤ t 5:= hp _ hn _ hY.hue hY.cost _
    have hb : F0 V ≤ t (-300)+t 5:=by
        nth_rw 1[← sub_add_cancel V Q]; exact (hS.semi _ _ _ (Next.UVStress.minus hB hq') hq').trans (add_le_add hz₁ hQ)
    let L (Z B': Config G (C.side N p)→ℂ):= pew C.S h₀ β x z Z B'
    have h₁ : ‖L U V‖ ≤ t (-200):=hD _ _ hx _ hG hC hR
    have h₂ : ‖L P (Q-V)‖ ≤ t 5*t (-300):= by
       refine (pulpit _ _ _ _ _ hx hp' (Next.UVStress.minus hq' hB) hS).trans (mul_le_mul hP ?_ (T.root_nonneg β (Q-V)) (Tau_pos ..|>.le)); rw [anti_test]; exact hz₁
    have h₃ : ‖L (P-U) V‖ ≤ t (-200)*(t (-300)+t 5):=by
       refine (pulpit _ _ _ _ _ hx (Next.UVStress.minus hp' hα) hB hS).trans (mul_le_mul ?_ hb (T.root_nonneg β V) (Tau_pos ..|>.le)); rw[anti_test]; exact hχ
    have hz(A' B':ℝ): t A'*t B'=t (A'+B') :=(Tau_add ..).symm
    change ‖L P Q‖≤ t (-100); rw [show L P Q=L U V+L P (Q-V)+L (P-U) V from slides C.S h₀ β x z hα hB hp' hq']; apply le_trans ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h₁ h₂)) h₃)); rw [mul_add,hz,hz,hz]
    have hp : 4*t (-195) ≤ t (-100):= calc
      _ ≤ t 1*t (-195):= mul_le_mul_of_nonneg_right hw (Tau_pos ..|>.le)
      _ ≤ _:= (hz ..).le.trans (tau_mono (A) i (by norm_num))
    apply le_trans _ hp; have hw (x:ℝ)(he:x ≤ -195):t x ≤ t (-195):= tau_mono (A) i he
    linarith only [hw _ (by norm_num : (-(200:ℝ)) ≤ -195),hw _ (by norm_num : (5:ℝ)+ -300 ≤ -195),hw _ (by norm_num : (-(200:ℝ))+ -300 ≤ -195),hw _ (by norm_num : (-(200:ℝ))+ 5 ≤ -195)]
end YM.Trace.Terrace
