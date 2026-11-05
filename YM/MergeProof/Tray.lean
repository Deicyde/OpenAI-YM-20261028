import YM.MergeProof.Heat
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Eco
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Ninety

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
lemma offerSp (L:Side)(p:RG.Stage)(h:ℝ) : ∀ᶠ x in atTop, ∀ V: BudgetPoint,V.threshold=Pressure.temp x→V.B=radiusB x → Time.Same p V →∀ α:ℝ,|α|≤h →
      YM.Merge.Spicy.opens G V p.clip p.width p.paths α (Time.credit G p * δE x) ≤ betaF G x L ^(-(1/4):ℝ):= by
  let a:=G.slopeConstant*Real.log L.val
  filter_upwards [Time.small_expenses (YM.Merge.Spicy.endcap G p h) a, plain.pitched, Delay.shift_pos G L,eventually_gt_atTop (1:ℝ)] with x hx hz hF hv V he hV hp α hi
  have ht : plain.t x=V.threshold:=by rw [he, (Time.threshold_aligned x (by linarith)).1]; rfl
  have hh:V.B=cover x:=hV
  have hg : 0 < gap x := gp (by linarith); have he := mul_nonneg (Time.credit_pos G p).le (Real.rpow_nonneg hg.le (11/5:ℝ))
  have hS : gap x ≤ 1:= inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hv.le)
  have hf : credit G p * δE x ≤ V.threshold^2:=by
    have hd : δE x ≤ gap x ^ (2:ℕ) := (Real.rpow_le_rpow_of_exponent_ge hg hS (by norm_num : (2:ℝ)≤(11:ℝ)/5)).trans_eq (Real.rpow_two _)
    have hy := mul_le_of_le_one_left (b:=δE x) (Real.rpow_nonneg hg.le _) ((Time.authorized G p).1.trans (by norm_num))
    exact hy.trans (hd.trans (pow_le_pow_left₀ hg.le (ht ▸ le_mul_of_one_le_right hg.le hz.2.2.1) 2))
  refine (YM.Merge.Spicy.opens_table G p hp hi he hf).trans ((show YM.Merge.Spicy.endcap G p h*(1+(V.B:ℝ))^4 * V.threshold ≤ gap (betaF G x L)^ ((1:ℝ)/2) from by rw [hh,← ht]; exact hx).trans_eq ?_); unfold gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hF.le,← Real.rpow_mul hF.le]; ring_nf

variable (R : Register D p u l)
def Pungent (Z: Delays Θ) : Prop:= ∀ j x,Z.betaEntry j≤ x →∀ i,StepStages j i→
    let p':= s.profile i; let B:=radiusB x; let L:=D.L j; let a:=betaF G x L; let μ:=R.μ j i
    (∀ c k:ℝ, 0 ≤ c → 0 ≤ k → k ≤ Real.exp (Trio.coverTicket (X j i).halo)*a^ (-(1/8):ℝ) → c ≤ Real.exp (-(X j i).mark L μ x) → ∃ κ, Payments.Rates B (stems μ L G x) c k κ) ∧
    ∀ V:BudgetPoint,V.threshold=Pressure.temp x→V.B=B→Time.Same p' V→∀ α:ℝ,|α|≤UVNext.CouplingReset.alphaBound D j→ let f:= YM.Merge.Spicy.opens G V p'.clip p'.width p'.paths α (Time.credit G p'* δE x);0≤f→∃ κ,Payments.Rates B (straw μ L G x) (stems μ L G x) f κ
lemma bravo (V : Delays Θ) : ∃ W : Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ, DelayLe W Y → Pungent R Y := by
  let N i:= s.profile i
  let U j i x:=
    (∀ c k:ℝ, 0 ≤ c → 0 ≤ k → k ≤ Real.exp (Trio.coverTicket (X j i).halo)*(betaF G x (D.L j))^ (-(1/8):ℝ) → c ≤ Real.exp (-(X j i).mark (D.L j) (R.μ j i) x) → ∃ κ, Payments.Rates (radiusB x) (stems (R.μ j i) (D.L j) G x) c k κ) ∧
    (∀ V:BudgetPoint,V.threshold=Pressure.temp x→V.B=radiusB x→Time.Same (N i) V→∀ α:ℝ,|α|≤ UVNext.CouplingReset.alphaBound D j → let f:= YM.Merge.Spicy.opens G V (N i).clip (N i).width (N i).paths α (Time.credit G (N i)*δE x);0≤f→∃ κ,Payments.Rates (radiusB x) (straw (R.μ j i) (D.L j) G x) (stems (R.μ j i) (D.L j) G x) f κ)
  have hP j i (hi:StepStages j i):∀ᶠ x in atTop,U j i x:= by
    let μ:= R.μ j i; let L:=D.L j
    have hf:= R.consumes _ _ hi; have hp: 0<μ:= hf.2.1
    filter_upwards [mingle (G:=G) L _ (show 0<μ/4 by positivity) (he:=zero_lt_one) (by norm_num : -(1/8:ℝ)<0) (Rate.power.mul_left (Real.exp (Trio.coverTicket (X j i).halo))), 
      mingle (G:=G) L _ (show 0<μ/8 by positivity) zero_lt_two (by norm_num : -(1/4:ℝ)<0) Rate.power, offerSp L (N i) (UVNext.CouplingReset.alphaBound D j)] with x hz hv hB
    refine ⟨fun c k hu hk h hh=>hz _ _ hu hk h (by rwa [one_mul,← syrup (μ:=μ) L (X j i)]),?_⟩
    intro V hK hf hR α hα f hΩ
    have hs : stems μ L G x= 2*lauge L (μ/8) x 1 G:=by unfold stems lauge; ring_nf
    have hC:0≤ stems μ L G x:=by unfold stems lauge; positivity
    obtain ⟨p,hp⟩:= hv _ f hC hΩ (hB _ hK hf hR α hα) hs.le
    exact ⟨p,show Payments.Rates _ (straw μ L G x) _ _ _ from by rw [show straw μ L G x=2*lauge L (μ/8) x (1/2) G from by unfold straw lauge; ring_nf]; exact hp⟩
  obtain ⟨x,-,hx,H⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> hP j i hi)
  exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩, fun Y hy j x hx i hi=>H j x ((hy.beta j).trans hx) i hi⟩
end YM.PhysicalNext.Repeat.Mallow
