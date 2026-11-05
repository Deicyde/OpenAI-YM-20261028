import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Calls
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Laud
/-!
# Any Alloy at admissible waits, SAME generation expenses on auxiliaries
 Output f support width additional.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {X : Metals G} (D : Rolls X.p) {c f : Side} {L : Side} {i j m n N : ℕ}
variable {C : Targets X.p X.K} {Z : Expenses C} {p : Return.Wages} {v : ℕ→ℝ}
    (R : Register D Z p v) (A : Alloy X D)
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "t" => A.B.a.clock.hatBeta m
variable {Y : ℕ→ℕ→ℝ→ℝ} {M : ℕ→ℕ→ℕ} {β : ℝ} (ht : Planks D R A.post Y A.delay M) (h : AsDivisors A.B.a.S) (hm : m<N) (H : f.val=c.val*(A.B.a.S.block m).val)
    (F : Forest (panel A m H).ratio)
local notation "T" => orchestra A N H
lemma curryP {P P': Patch} {K K': KernelChoices} {R R': RG.Stage} (A : Paintings.Supply G P K R) (h:P=P') (he:K=K') (hr:R=R') : ∃ B : Paintings.Supply G P' K' R',(B.sights,B.allowance)=(A.sights,A.allowance):=by subst P' K' R'; exact ⟨A,rfl⟩
include h
include hm
lemma presents (hc:Quilt T F (Y J I t)) : ∃ ρ, 
      Critical F (T).high (T).up ρ ∧ ClassicalMatch F (T).high (T).low (T).up (T).down ρ ∧
      FiniteBound F (T).up (T).down (T).high (T).low (A.B.kin.alpha N m) X.O ρ (pref D J+A.post.Γ J) (min (knot D J) (A.post.c J)) (A.B.a.clock.loopCap (m+1)) := by
  have hJ:= A.B.a.clock.adm (m+1); let P := Mural.sheet X.p D hJ; let z:= A.B.a.params (m+1); let Q:= atlas X.p P (X.p.profile J); let P':= (A.B.a.clock.op m 0).patch; let V := A.B.valid
  have hS : P'=P:= by
    cases h : P' with
    | mk k j hm hf ho =>
      have hh : j= J:= by rw [← show (Patch.mk k j hm hf ho).J=j from rfl,← h]; rfl
      have hK : k=D.L J:= by rw [← show (Patch.mk k j hm hf ho).L=k from rfl,← h]; exact PriceCompiler.block_eq V m
      subst k j; rfl
  have hr : A.B.a.clock.kernel = X.p.kernel:= V.kernel
  have hz := params_eq V (m+1)
  obtain ⟨Q',he⟩:=curryP Q hS.symm hr.symm (show X.p.profile (J)=z from hz.symm)
  obtain ⟨ρ,hρ,hΘ,hs,hK⟩:= ligatures A.B.kin A.B.support X.oga h Q' hm H F hc.large.2.2 hc.large
  refine ⟨ρ,hρ.critical,hΘ,fatten (R:=T) hK (add_le_add ?_ le_rfl) (show 0 ≤ pref D J+A.post.Γ J from add_nonneg (zero_le_one.trans (above_one _ _)) (A.post.pos _).le) (coverBill ..|>.1) ?_⟩
  · unfold pref; rw [dif_pos hJ]; exact (congr_arg Prod.snd he).trans_le (le_max_right ..)
  have hv : knot D J≤ Q'.sights:= by rw [show Q'.sights=Q.sights from congr_arg Prod.fst he]; exact knot_low hJ (show 0 < Q.sights from hs.trans_eq (congr_arg Prod.fst he))
  exact min_le_min hv le_rfl
include ht
lemma burst (hq : (C J I).table=X.O)
    (hc: Stores.till t ≤ c.val) (hf : Quilt T F (Y J I t)) {a β:ℝ} (P': Cash (p J I) t (R.μ J I) (D.L J) (C J I) (R.o J I) a T (virgin T (A.B.a.budget (m+1)) β)) (X':Coat T F) (hW:X'.x=t) (hw:X'.width=(R.o J I).K) (hM : X'.manifest) (hY : flags (Pressure.temp t) X'.V=∅) (x:Positions (Uniform.Primary c G)) (he:X'.V=represent (tint G _ x)) (hx:‖x‖+2*furl G (D.L J) t < eaves G (D.L J) t) : 0<tramp T (A.B.a.budget (m+1)) β x ∧ Blaze.Brush (M J I) ((betaF G t (D.L J))^( -(23/20:ℝ))) ((eaves G (D.L J) t)⁻¹) (off (harmony T (A.B.a.budget (m+1)) β (A.B.kin.alpha N m))) x:= by
  obtain ⟨ρ,hρ,hΘ,hK⟩:=presents D A h hm H F hf
  obtain ⟨hκ,h₀⟩:= ht J I (step_paid A.B.a m) t (A.B.valid.pays m); have hV:= P'.laws.data; have hA:= A.B.support; let V:= A.B.a.clock
  have hw : V.hatBeta (m+1)=betaF G t (D.L J):= (Application.clock_next A.B.a m 0).trans (congr_arg (betaF G t) (PriceCompiler.block_eq A.B.valid m)) -- parser
  have hB' : V.loopCap (m+1) ≤ ConnectedActivityE6.loopBill G (D.L J) t:= by
    have hp:= coverBill A.B.a (m+1)|>.2; apply hp.trans_eq; change 2*V.monitor (m+1)=2*Delay.fineMonitor G (D.L J) _; unfold Calendar.monitor Delay.fineMonitor; rw [hw]; rfl
  have hB : V.loopCap m ≤ ConnectedActivityE6.loopBill G (D.L J) t:= (coverBill A.B.a m).2.trans (brace _ hκ)
  have hj := V.adm (m+1); let Z:= T
  have he' := hV.funds
  have hi : A.B.a.params (m+1) = X.p.profile (J) := params_eq A.B.valid (m+1); have hQ : A.B.a.params m = X.p.profile (I):=params_eq A.B.valid m
  have hx' : |A.B.kin.alpha N m|≤ cloak D J := by
    have ht:=hA.kinetic N m hm; rw [hi,(PriceCompiler.block_eq A.B.valid m)] at ht; unfold cloak
    let u:= G.slopeConstant * Real.log (D.L J).val; have hh:|A.B.kin.alpha N m|≤ |A.B.kin.alpha N m+u|+|u|:= by
      have he:=abs_sub (A.B.kin.alpha N m+u) u
      simpa only [add_sub_cancel_right] using he
    linarith only [ht,hh]
  have ha :=h₀ c f _ T F X' (A.B.a.budget (m+1)) (A.B.a.budget m) hj (he'.patch rfl rfl) (show (panel A m H).kernel=X.p.kernel from A.B.valid.kernel) hc hf
  have hz : Z.down.Bounds Z.low (X.p.profile I).width (X.p.profile I).paths (ConnectedActivityE6.loopBill G (D.L J) t):= by
    rw [← hQ]; have hv:= hA.cap N m hm.le; exact {hv with two:=budget_loosen hv.two hB}
  have hz' : Z.up.Bounds Z.high (X.p.profile J).width (X.p.profile J).paths (ConnectedActivityE6.loopBill G (D.L J) t):= by
    rw [← hi]; have hv:= hA.cap N (m+1) hm; exact {hv with two:=budget_loosen hv.two hB'}
  exact ha (congr_arg RG.Stage.clip hi) (congr_arg RG.Stage.clip hQ) hz' hz _ _ ρ (coverBill A.B.a (m+1)|>.1) hB' hx' hρ hΘ (by rw [hq]; exact hK) rfl _ _ P' hW (by assumption) hM hY x he hx
end YM.PhysicalNext.Repeat.Pane
