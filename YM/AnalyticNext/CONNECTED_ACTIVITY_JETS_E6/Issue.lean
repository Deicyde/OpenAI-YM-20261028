import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Guards
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.OptionCost
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Quotation
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Revenue
import YM.Progress.STATIONARY_SCENES.Classical

/-!
# Produce bills for every word in one vacuum step

Keep coherent path p ordering. Supply from old `R` at the actual x, via
Intake. No per-vertex estimate input. Calls Buy.sectors open-wallet API
(`Grant.order`, `Buy.quoted`) to allow *same μ* as physical allocation (Y
vs optional h's are NOT separable single-oriented packets). Optional hit
pricing includes hail AFTER normalized probability purchase. No global
phase or devicing assumptions beyond Stamps. Increase epsilon etc once in
`Target`, then n qualifies H and W on all sectors. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n L : Side} {P : Teller G} {S : StepData c f} {T : Tube G S}

namespace Target
variable (R : YM.ConnectedActivityE6.Target G P)

/-- Post W, L, Θ, BEFORE delay; retain covariance price powers for ALL
S at measure pay. No clocks rerolled. -/
structure Order (G : Gauge) (W : ℝ) where
  eta : ℝ
  gap : ℝ
  ample : ℝ
  indexPay : ℝ
  K : ℝ -- width shell
  γ : ℝ
  cap : ℝ
  a : ℝ -- broad gamma plateau
  ξ : ℝ -- threshold touch
  f : Torch eta gap ample
  large : 0<a
  gamma : γ*K≤a
  rare : 0<ξ

/-- In the orientation and baked virtual constants this is measured in
normalization relative to actual probability, not assuming Polymer exp log.
Working Gate `Components` after this. -/
structure GrantBodies (W x μ : ℝ) (L : Side) (R : ConnectedActivityE6.Target G P) (o : Order G W) (C : ℝ) (T : Tube G S) : Prop where
  funds : Works P L x S T
  room : Room P S T x
  grant : PointCharge T x W μ
  μ_pos : 0<μ
  W_pos : 0<W
  covers : 4*o.a*Pressure.fiery G x L < R.table.radius
  access : ShellAccess S G x W o.K o.γ
  localP (F : Forest S.ratio) (X : Coat T F) (ht : X.x=x) (hp : X.width=o.K) : X.manifest →
    Port P L o.eta o.gap o.ample o.indexPay X
  -- Plateau margin for differentiating at HELD-U. Use smaller ξ later to recover
  -- a strict slack on Gamma too. Regardless of whether χ has other symms.
  safety : 0<o.cap ∧ o.cap+1 ≤ o.a ∧ (Fintype.card G.ColorIndex:ℝ)*o.ξ ≤ 1 ∧
    (∀ (F : Forest S.ratio) (X : Coat T F), X.x=x→ X.width=o.K → X.manifest →
       (∀ i, ‖X.μ i‖≤o.cap*X.t) ∧ (Stamp T →
       ∀ i : Site c, ¬Inside i X.seeds (30*X.B) → ∀ β>0, ∀ z : Air f G, X.watch i o.ξ β X.B z →
          let U:= X.input (X.liftA β z)
          Tags.siteMass U X.k i=1 ∧ (∀ p : Cell f,S.ratio.parent p.1=i→ toll U p < X.t/4) ∧
          ∀ j : Axis, Tags.pinMass U X.k (i,j)=1 ∧ wire (S.prediction U X.k) X.V (i,j) < W*X.t))
  glides : let m := Census.tubularPrice G L; let B := radiusB x
           scraps o.eta o.gap o.ample m B<1 ∧ o.ample*distPay o.eta o.gap o.ample m B < 1

structure Invoices (W x μ : ℝ) (L : Side) (R : YM.ConnectedActivityE6.Target G P) (o : Order G W)
    (C : ℝ) (T : Tube G S) (K : Rep G f) : Prop where
  intake : Intake P T x K
  data : GrantBodies W x μ L R o C T
  acquired : (R.costs L μ K.beta x C).Buy S.patch.L R.halo (radiusB x)
  vapors : ∃ (k : ℕ→ℝ) (y : LogIndex c f→ℝ) (E : ℝ),
    let X := (fun _ : WarningAt c f=>E*topStorm S.patch)
    0≤E ∧ Sales (radiusB x) R.relative R.ε (footprints T K R.halo (radiusB x))
      (Sum.elim k (Sum.elim y X)) (Sum.elim (Raw.forcedExtra K) (Sum.elim (exCharge T K) (fun _=>0)))
        (R.goal L x) ∧ ∀ (F : Forest S.ratio) (Y : Coat T F), Y.x=x → Y.width=o.K → Y.manifest →
      (∀ i U, |Y.bag K o.a U i| ≤ k i) ∧ (∀ i z, |Y.farLog K o.a R.table z i| ≤ y i ∧
        |Y.raiseAir K o.a R.table z i| ≤ y i) ∧
      (∀ u l A, |Y.Pack K R.table l W o.a A u| ≤ Packets.income 1 (C*Delay.bill G L x^5)
          (R.costs L μ K.beta x C).gain A.shares) ∧
        ∀ v : Finset (WarningAt c f), Y.dice.real (Y.catastrophe o.ξ K.beta v) ≤ E^v.card ∧
          ∀ l z, (∀ i∈v,Y.detect (Y.liftA K.beta z) W o.a K l i≠0) → z∈Y.catastrophe o.ξ K.beta v

/-- Pre-L order and width requests. The `D` and coefficients
must also be bought when performing the scheduling of all β_ˆ.
Uniform actual quantitative parameters. Stamp still physical linear
input on those same `T`; not an RStage from these hypotheses alone. -/
theorem issue :
    ∃ n : ℕ,∀ L : Side,n ≤ L.val → ∀ᶠ W in atTop, 0<W ∧ ∃ μ : ℝ, 0<μ ∧ ∀ (D : Patch), D.Branches P.bind G →
      ∃ (o : Order G W) (C : ℝ), 0 ≤ C ∧
        ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T →
        GrantBodies W x μ L R o C T ∧
        ∀ K : Rep G f, Intake P T x K → Stamp T → Invoices W x μ L R o C T K := by
  obtain ⟨N,hN⟩ := Grant.order P
  obtain ⟨A,U,hA,hU,hV⟩ := max_prices P
  obtain ⟨τ,hτ,n,h⟩ := Coat.scopes P A hA
  have he : 0≤ R.relative := by unfold Target.relative; nlinarith [R.bound,R.usable,R.pos]
  obtain ⟨M,H⟩ := recommends P R.table_exists R.grants.1 R.grants.2.1 R.grants.2.2 he R.usable
    R.halo (le_trans (by norm_num) R.buys) hA
  refine ⟨N+n+M,fun L hL => ?_⟩
  filter_upwards [hN L (by omega), h L (by omega)] with W H₁ H₂
  obtain ⟨hw,μ,hμ,hM⟩ := H₁
  refine ⟨hw,μ,hμ,fun D hd =>?_⟩
  obtain ⟨K,γ,hK,hγ,hS⟩ := shell_access G P D L hw
  obtain ⟨η,r,Q,Y,hF,hG⟩ := shoots P L D hd
  obtain ⟨C,hC,E,hE,hU⟩ := tends_val P L D hd η r Q Y W γ K (-1) hF
  let a := max (C+1) (γ*K)
  have h1 : C+1≤a := le_max_left ..
  have h2 : γ*K≤a := le_max_right ..
  obtain ⟨ξ,hξ,hξ',hX⟩ := Coat.ready P L D hd H₂ (Y:=Y) (M:=C) hF
  have ha : 0<a := (show 0<C+1 by positivity) |>.trans_le h1
  let o : Order G W := ⟨η,r,Q,Y,K,γ,C,a,ξ,hF,ha,h2,hξ⟩
  obtain ⟨b,hb,H₃⟩ := steam_prices P D L hd R.table_exists ha hA hw η r Q Y γ K μ h2
  obtain ⟨s,hp,hq⟩ := exists_between R.start
  obtain ⟨q,hi,hQ⟩ := alarm_bills (η:=η) (r:=r) (Q:=Q) (Y:=Y) P L s hξ
  obtain ⟨T,ht,hY⟩ := exponent_fee G L R.halo R.relative R.ε s (topStorm D) he q hi
  let m := Census.tubularPrice G L
  have hz : ∀ᶠ x : ℝ in atTop, let B:=radiusB x
      scraps η r Q m B<1 ∧ Q*distPay η r Q m B < 1 := by
    let W := hF.physical G L (-1) m
    filter_upwards [W.below (by norm_num) (1/2) (by norm_num), ((W.mul_left (payE η r Q m)).mul_left Q).below
      (by norm_num) (1/2) (by norm_num)] with x hx hv
    dsimp only; exact ⟨((le_abs_self _).trans hx).trans_lt (by norm_num),((le_abs_self _).trans hv).trans_lt (by norm_num)⟩
  refine ⟨o,b,hb,?_⟩
  obtain ⟨e_v,hvā,hj⟩ := germ_charge R.table_exists L ha
  filter_upwards [hj,hM R.halo 0 (1:ℝ) 0 0 0 (by norm_num) le_rfl le_rfl (by norm_num),hV L,hG,
    room G P L,hU,hS,hQ,hX,H₃,hz, R.pay_for L hμ hb,
    H L (by omega) D hd η r Q Y W γ K C a s s hC ha hp (hq.trans R.stop) E hE hF,
    (Rate.power.add (Rate.power.add ht)) R.rate hq]
    with x HX₀ HV HV' HZ Hr HX HC HJ HG HK HS HE HQ HT c f S X hh hu
  have hL := hu.length_eq
  have hR := Hr c f S X hu
  have hs := HC c f S X hh hL hR
  have hj (F : Forest S.ratio) (Y' : Coat X F) (he : Y'.x=x) (hm : Y'.manifest) := HZ c f S X F Y' he hh hL hR hm
  have hΓ : Stamped P L η r Q Y W γ K C (|E x|) x X := by
    refine ⟨fun F Y' he hg hY => ⟨?_, HX _ _ S X F Y' he hg hh hL (hj F Y' he hY) hY hs⟩⟩
    exact ⟨hj F Y' he hY,hj F Y'.blank he (Y'.bowed (temp_nonneg _)), fun z => hj F (Y'.rinse z) he (Y'.retains z hY),hY⟩
  have hc : PointCharge X x W μ := HV.2.1 c f S X hL hu.fits hu.funds
  have hd : GrantBodies W x μ L R o b X := by
    refine ⟨hu,hR,hc,hμ,hw,?_,hs, fun F Y he ha hm => (hΓ.serves F Y he ha hm).1, ⟨hC,h1,hξ',?_⟩, HS⟩
    · let Y := dum X x K (Classical.choice (Tree.select S.ratio S.patch.odd_side))
      rw [← hL]; exact (HX₀ _ _ S X _ Y rfl hL hR.fiery).1
    intro F Y hX hx hy; have hp := (hΓ.serves F Y hX hx hy).2
    exact ⟨hp.mean, fun hs => HG _ _ S X F Y hX hh hL (hj F Y hX hy) hs hy hp.mean hp.cap (hX.symm ▸ ((HV' c f S X hu).2 Y.V).1)⟩
  refine ⟨hd,fun I hI hZ'=> ⟨hI,hd,?_,?_⟩⟩
  · rw [hL]
    have he := hI.window.1; rw [hL] at he
    exact HE _ he
  have hlh := (HV' c f S X hu).2
  have hHX (w) := (hlh w).1
  obtain ⟨v,z,hv,hr,he⟩ := (HQ _ _ S X hh hL hΓ hZ' hHX I hI).gifts
  have hy : topStorm D * q x=q x*topStorm S.patch := by rw [hh, mul_comm]
  have hg : Sales (radiusB x) R.relative R.ε (field_support S (radiusB x) R.halo)
      (fun _=> q x*topStorm S.patch) (fun _=>0) (T x) := by
    simp_rw [← hy]; have hh : 0≤ topStorm D * q x := mul_nonneg (zero_le_one.trans (topStorm_one _)) HJ.1
    exact hY x _ _ S hL (lt_of_lt_of_le (by norm_num) hR.sight.1) hh
  refine ⟨v,z,q x,HJ.1, (ratesCombine hv hr hg).raise ?_,fun F u H HH hA=> ?_⟩
  · exact (le_abs_self _).trans HT
  obtain ⟨h₁,h₂⟩ := he F u H HH hA
  obtain ⟨u₁,u₂⟩ := hΓ.serves F u H HH hA
  refine ⟨h₁,h₂,fun w l Z=> ?_,fun j => ⟨HJ.2 _ _ S X F u H hL u₁.sails I (H.symm ▸ hI) j,fun l z ht =>?_⟩⟩
  · apply (HK _ _ S X F u H hh hL u₁.sails u₁.empty HH (H.symm ▸ hs) (H.symm ▸ hc)
      (fun V=> H.symm ▸ hHX V) I (H.symm ▸ hI) Z l w).trans_eq
    suffices e : μ*u.t^2= μ*Pressure.fiery G x L^2 by unfold Target.costs Buy.quote Grant.credit; simp only [e]
    unfold Coat.t; rw [H,hL]
  apply u.shocks I.beta ξ W a I l z _ j ht
  intro i hx hp
  apply hx
  have h := ((hd.safety.2.2.2 F u H HH hA).2 hZ')
  rcases i with i|i
  · exact u.blowing (H.symm ▸ hI) u₁.sails hw z (fun i hi he=> h i hi _ hI.positive z he) i hp l
  change u.aura _ _ i = _
  unfold aura; split
  next hi =>
    have he := (u.watch_bonds _ (show 0<u.t from u₁.sails.room.fiery) hξ.le hI.positive hp i
      (show separation (atEdge S i) (atEdge S i) ≤ _ by simp) ((hd.safety.2.2.2 F u H HH hA).1 i)).2
    have hx : C +(Fintype.card G.ColorIndex:ℝ)*ξ≤ a := by linarith only [hξ',h1]
    exact sub_eq_zero.mpr (u.premiere (mul_pos ha u₁.sails.room.fiery) _ _ (he.trans (mul_le_mul_of_nonneg_right hx u₁.sails.room.fiery.le)))
  next => rfl
end Target
end YM.ConnectedActivityE6
