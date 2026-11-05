import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Market
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Blazing
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Fees
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Scrutiny
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Fund
import YM.Progress.JOINT_CALENDAR.Period
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Backwards
import YM.Push.LOCAL_SPLITTING.Delay




/-!
# Before rank-density expansion

Expose the exponent for group-invariant transport. At *chosen*
protocol height x, not yet specialized to β range of Epoch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet Push.Local MeasureTheory
   Next.Fluctuations.Sector Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian Milk AnalyticNext.ConnectedActivity Cab Aff
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} {A : Stores S} {H : Forest S.ratio}
   {P : Teller G} {T : Tube G S} {R : Rep G f} {B : BudgetPoint}
   {q : Chi} {J : ChartRatio G} {d : ℝ} {ρ : Pilot G S x}

-- persist ALL actual receptive chart data before varying U or H
structure Dyed (G : Gauge) (S : StepData c f) where
  source : Rep G f
  things : Tube G S
  chi : Chi
  ratio : ChartRatio G
  arc : ℝ
  bp : BudgetPoint
  mode : Forest S.ratio
  token : S.Choices
namespace Dyed
variable (v : Dyed G S)

def top (ρ : Pilot G S x):= gazed v.things ρ.tag v.chi ρ.view x v.source.beta v.arc ρ.y
-- volume-constant and banker already use kinetic at the SAME forest mode and token
def loading (x : ℝ) (V : Config G c) :=
    banker v.things v.bp V v.source.beta * prefactor S G v.source.beta * Real.exp (v.source.v*(Fintype.card (Site f):ℝ))*
    spare v.ratio v.source.beta ^ Fintype.card v.mode.Free * (Real.sqrt (Native.kinetic v.things v.mode v.token x).det)⁻¹

def keptEarly (ρ : Pilot G S x) :=
    let V:=ρ.view; let F:=ρ.park; let A:=ρ.key; let k:=ρ.tag
    let Q:=fog A F v.things x V k; let W:=Rows.gram v.things x V k (shots S x) A F;
    -(Fintype.card (Frozen A x F):ℝ)*Real.log (spare v.ratio v.source.beta)-(1/2)*(Real.log W.det-Real.log (Native.kinetic v.things F k x).det)+
      (1/2)*Real.log (1+(W*Q-1)).det

def spoolLift (ρ : Pilot G S x) :=
    let A:=ρ.key; let F:=ρ.park; let k:=ρ.tag; let Y:=ρ.y.1; let z:=ρ.y.2
    let U:=top v ρ; let V:=ρ.view; let W:=Rows.gram v.things x V k (shots S x) A F;
    let p:=meanLog A F v.things x V k v.chi v.arc Y; let a:= p+coupling v.source.beta • z; let Q:=fog A F v.things x V k;
    -v.source.beta * (Aff.weight*∑ i, Milk.levy v.things x V Y k v.chi v.arc v.source.p.threshold a i) +
      ((Rows.eta v.things x V k (shots S x) A F v.chi v.arc Y p (coupling v.source.beta)) ⬝ᵥ z) +
      (z ⬝ᵥ ((Q⁻¹-W) *ᵥ z))/2 + keptEarly v ρ + (∑ i, logGuard v.chi v.ratio v.arc (Next.SectorChange.tape a i)) +
      (apart v.source U x + coarseTail v.things x v.bp V v.source.beta)

-- core truth emitted BEFORE marker K. All positive for this branch.
def freight (ρ : Pilot G S x):=
    let A:=ρ.key; let F:=ρ.park; let k:=ρ.tag; let V:=ρ.view; let z:=ρ.y; let U:=top v ρ
    let Q:=fog A F v.things x V k; let m:= meanLog A F v.things x V k v.chi v.arc z.1
    v.ratio.scale ^ Fintype.card (Active A x F) * chartCost Q (coupling v.source.beta) * Real.exp (force Q z.2/2) *
      reserve v.chi v.ratio v.arc (displaced m (coupling v.source.beta) z.2) * S.noise v.source.beta (S.prediction U k) V * Real.exp (v.source.exponent U)

lemma charge_eq (h : P.Funds S v.things) (hr : v.things.up=v.source.path) (hc : v.things.high=v.source.clip) (ρ : Pilot G S x) :
    let Y:=ρ.y.1; let k:= ρ.tag; let F:=ρ.park; let A:=ρ.key; let V:=ρ.view; let T:=v.things; let m:=meanLog A F T x V k v.chi v.arc Y; let a:=m+coupling v.source.beta • ρ.y.2
    let U:=v.top ρ; let e₀:= Wax.theta T.down T.low S.patch.L.val x (temp x) V; let mon:=∑ i,monetary S (S.prediction U k) V i
    Aff.weight*(∑ i, Milk.levy T x V Y k v.chi v.arc v.source.p.threshold a i)=mon+(cutR v.source (till x) U-e₀)-Rows.guide T x V k (shots S x) A F v.chi v.arc Y a + Rows.guide T x V k (shots S x) A F v.chi v.arc Y m:= by
  dsimp only
  have hU:= funds_branch h
  obtain ⟨u,f₁,hF,hL'⟩:=h.feeds
  obtain ⟨A,F,k,V,y⟩:=ρ; let ρ:Pilot G S x :=⟨A,F,k,V,y⟩; let U:=v.top ρ
  set g := coupling v.source.beta; let W:= shots S x; let m:= meanLog A F v.things x V k v.chi v.arc y.1; let a:=m+g • y.2
  let f' := fun z:Prices G (Active A x F)=> Aff.weight*∑ i,coinMeter v.things x V y.1 k v.chi v.arc z (i:Grain S)
  let E:= Aff.weight*∑ i:Grain S, outer v.things x V k v.source.p.threshold U i
  have hc₁ : Aff.weight*(∑ i, Milk.levy v.things x V y.1 k v.chi v.arc v.source.p.threshold a i)= E-f' a+f' m:= by
    unfold levy; rw [sum_add_distrib, sum_sub_distrib,mul_add,mul_sub]; unfold E U top gazed; simp_rw [← mean_endpoint]; rfl
  have he z : f' z = Rows.guide v.things x V k W A F v.chi v.arc y.1 z := by
    unfold f'; rw [Rows.guide_rows v.things x V k W A F v.chi v.arc y.1 hF _,Fintype.sum_prod_type]; unfold averaged; apply congr_arg (Aff.weight*·)
    refine sum_congr rfl fun s _ => ?_; simp_rw [Fintype.sum_sum_type, coinMeter]; simp [W]
  let mon:=∑ i, monetary S (S.prediction U k) V i
  let e₀ := Wax.theta v.things.down v.things.low S.patch.L.val x (temp x) V
  have hD: E=mon+(cutR v.source (till x) U-e₀):= by
    unfold E e₀ Wax.theta cutR; rw [← hr,← hc, ← av_const mon,←av_sub,←av_add]
    rw [Fintype.sum_prod_type]; apply congr_arg (Aff.weight*·); apply sum_congr rfl; intro i _
    let W' :=pull i 0 V; let U':=pull i 0 U; let Z:= S.prediction U' (choice i k)
    have hm: mon=∑ j,monetary S Z W' j:=by
      unfold Z W'; rw [show S.prediction U' _=pull i 0 _ from (carry i hU k U).2]; unfold monetary; simp_rw [wire_pulled]
      exact (_root_.Equiv.sum_comp (StepData.sendBonds i 0) _).symm
    simp_rw [Fintype.sum_sum_type]; rw [hm]
    have ht:= v.things.locates (till x) U' Z W' v.source.p.threshold (temp x)
    dsimp only [Milk.outer,Sum.elim_inl,Sum.elim_inr]; rw [sum_add_distrib,sum_add_distrib]; linarith only [ht]
  exact hc₁.trans (congr_arg₂ HAdd.hAdd (congr_arg₂ HSub.hSub hD (he a)) (he m))

theorem cardinal_spin {b₀ a C η : ℝ} (h : P.Funds S v.things) (hp : Physical.Certified S v.things x a C η b₀) (hr : v.things.up=v.source.path) (hc : v.things.high=v.source.clip) (hJ : LocalRatio v.ratio) (hb : 0<v.source.beta) (hΘ : v.bp.threshold=temp x) (ρ : Pilot G S x) (hd : Matched ρ) :
    0<v.loading x ρ.view ∧ v.freight ρ = v.loading x ρ.view * Real.exp (v.spoolLift ρ) := by
  have hU:= funds_branch h
  obtain ⟨u,f₁,hF,hL'⟩:=h.feeds
  obtain ⟨A,F,k,V,y⟩:=ρ; let ρ:Pilot G S x :=⟨A,F,k,V,y⟩; let U:=v.top ρ
  let S0:= (Native.kinetic v.things F k x).det; let K:=Native.kinetic v.things v.mode v.token x; let H:= K.det
  have hK: K.PosDef:= (Export.normal hp _ _ hU).1
  let Q:= fog A F v.things x V k; let L:=Rows.gram v.things x V k (shots S x) A F
  have hΨ:= Work.F05.free_card F v.mode
  have hPos:0<v.loading x V:= by
    unfold loading banker; have hf:= prefactor_pos (G:=G) (S:=S) v.source.beta; have hx:= hK.det_pos; have hs:= spare_pos v.ratio hJ hb; change 0<_*_*(Real.sqrt K.det)⁻¹; positivity
  refine ⟨hPos,?_⟩
  obtain ⟨-,hg,hQ,-⟩:=hp.text A F k V hd
  have hE:v.ratio.scale ^ Fintype.card (Active A x F) * chartCost Q (coupling v.source.beta)=spare v.ratio v.source.beta^ Fintype.card v.mode.Free*(Real.sqrt H)⁻¹*Real.exp (keptEarly v ρ):= by
    have he:= solvent_ledger x A v.source F v.ratio v.bp L Q K hK hg hQ hJ hb
    have ht:S0=H:= shared v.things F v.mode k x hF hU v.token
    unfold keptEarly; dsimp only [ρ]; rw [show (Native.kinetic v.things F k x).det= H from ht,← hΨ, scalars_align x A v.source F v.ratio Q]; exact he
  set g := coupling v.source.beta; let W:= shots S x; let m:= meanLog A F v.things x V k v.chi v.arc y.1; let a:=m+g • y.2
  have hR : (∑ i, logGuard v.chi v.ratio v.arc (Next.SectorChange.tape a i))=Real.log (reserve v.chi v.ratio v.arc (displaced m g y.2)):= by
    unfold reserve displaced; rw [Real.log_prod (fun i _=> (extended_pos v.chi v.ratio v.arc _).ne')]; exact sum_congr rfl (fun _ _=> (Real.log_exp _).symm)
  have hY := charge_eq v h hr hc ρ; dsimp only [ρ] at hY
  let mon:=∑ i, monetary S (S.prediction U k) V i
  let e₀ := Wax.theta v.things.down v.things.low S.patch.L.val x (temp x) V
  have hphys : S.noise v.source.beta (S.prediction U k) V=prefactor S G v.source.beta*Real.exp (-v.source.beta*mon):= by
    unfold StepData.noise mon prefactor; rw [prod_mul_distrib, Finset.prod_const,card_univ,mul_sum,Real.exp_sum]; congr 1; refine prod_congr rfl fun i _=> ?_
    unfold StepData.penaltyWeight monetary wire; rw [G.chord_price]; ring_nf
  let c' := Rows.guide v.things x V k W A F v.chi v.arc y.1
  have ht' := Rows.adjusted v.things x V k W A F v.chi v.arc y.1 Q m y.2 (coupling_pos hb)

  let iD := Real.exp (force Q y.2/2); let w' := reserve v.chi v.ratio v.arc (displaced m g y.2)
  have hEd: v.source.v*Fintype.card (Site f) + apart v.source U x = v.source.exponent U + v.source.beta * cutR v.source (till x) U:= by
    rw [add_comm (Rep.exponent ..), Cab.reacts]; unfold apart; ring_nf
  have hh := convert_full v.things x V v.bp v.source.beta hΘ
  let β:=v.source.beta; let L':= Real.log w'; let t:= v.source.v* Fintype.card (Site f); let c:= coarseTail v.things x v.bp V v.source.beta
  have hU : v.spoolLift ρ = v.keptEarly ρ+c + force Q y.2/2 + L' + β*e₀ - β*mon + v.source.exponent U - t := by
    -- no slicing assumptions so far.
    unfold spoolLift; dsimp only [ρ];
    change -β * _ + _ + _ + _ + (∑ i, logGuard v.chi v.ratio v.arc (Next.SectorChange.tape a i)) +(apart v.source U x+c)= _
    rw [hR,hY]
    let Z:= Rows.eta v.things x V k W A F v.chi v.arc y.1 m (coupling β) ⬝ᵥ y.2
    let G0 : ℝ:= (y.2 ⬝ᵥ ((Q⁻¹-L)*ᵥ y.2))/2
    change -(c' m)/g^2 + Z + G0=force Q y.2/2-c' a/g^2 at ht'
    rw [show ∀ z:ℝ, z/g^2=z*β from fun z=> by rw [div_eq_mul_inv,show (g^2)⁻¹=β from by_coupling hb], show ∀ z:ℝ,z/g^2=z*β from fun z=> by rw [div_eq_mul_inv,show (g^2)⁻¹=β from by_coupling hb]] at ht'
    change t + _ = _+β* _ at hEd
    change -β*(mon+(cutR _ _ _-e₀) - c' a+c' m)+Z+G0+v.keptEarly ρ+ L'+ (apart _ _ _ + c) =_
    -- Bank includes - β e₀
    linarith only [ht',hEd]
  -- λ.fullBank removes exp(-β*e₀)
  change Real.exp (-β*e₀)= banker v.things v.bp V β * Real.exp c at hh
  have hl : Real.exp L' = w':= Real.exp_log (reserve_pos ..)
  change v.ratio.scale ^ Fintype.card (Active A x F)*chartCost Q g*Real.exp (force Q y.2/2)*w'*S.noise β (S.prediction U k) V*Real.exp (v.source.exponent U)= _*_ -- f's
  let Ω:=spare v.ratio v.source.beta ^ Fintype.card v.mode.Free * (Real.sqrt H)⁻¹
  calc
    _ = Ω*Real.exp (v.keptEarly ρ) * Real.exp (force Q y.2/2) * Real.exp L' *
       (prefactor S G β * Real.exp (-β*mon))* Real.exp (v.source.exponent U):= by rw [hE,hphys,hl]
    _ = prefactor S G β * Ω * Real.exp (v.keptEarly ρ+ force Q y.2/2+ L' -β*mon + v.source.exponent U):= by simp only [sub_eq_add_neg, Real.exp_add, neg_mul]; ring
    _ = banker v.things v.bp V β * Real.exp c * prefactor S G β * Ω * Real.exp (β*e₀+(v.keptEarly ρ+ force Q y.2/2+ L' -β*mon + v.source.exponent U)):= by
       rw [← hh,Real.exp_add (β*e₀)];
       have he:Real.exp (-β*e₀)*Real.exp (β*e₀)=1:= by rw [← Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero]
       linear_combination -(prefactor S G β*Ω*Real.exp (v.keptEarly ρ+ force Q y.2/2+ L' -β*mon + v.source.exponent U))*he
    _ = _ := by
       change _= banker v.things v.bp V β*prefactor S G β*Real.exp t * _ * _ * Real.exp (v.spoolLift ρ)
       rw [show β*e₀+(v.keptEarly ρ+force Q y.2/2+L'-β*mon+ v.source.exponent U)= v.spoolLift ρ + t - c by linarith only [hU]]
       have he:Real.exp c*Real.exp (v.spoolLift ρ + t - c)=Real.exp t*Real.exp (v.spoolLift ρ):= by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
       -- cash at shared plan
       unfold Ω H K
       linear_combination banker v.things v.bp V β * prefactor S G β * (spare v.ratio v.source.beta ^ Fintype.card v.mode.Free) * ((Real.sqrt (Native.kinetic v.things v.mode v.token x).det)⁻¹) * he
end Dyed
end YM.PhysicalNext.InteractingRank.Pump
