import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Voices
import YM.Extra.WEAK_SCALING_ACTLAW.Producer
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Offers
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Timers

/-!
# Arrivals before and after L (Heater)

Bind new pre gates and x-waits for weak sector. Mesa will imply
Opacity earnings; no claim of scalar or E from these price budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision Filter
    MeasureTheory SectorTools.PhysicalGaussianSwitch
    Display Display.Docking Push.AbsoluteSums AnalyticNext.ConnectedActivity
    Next.Rank Perch Tapes Atlas Supply RankCovariance
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
-- scheduled alongside Budget scale. Not memory of any completed calendar
structure Ports (P : Teller G) (J : ChartRatio G) (j : ℕ) (L : Side) (ξ : Purse) (W d s : ℝ):Prop where
  localizes : ∀ D : Patch,D.J=j → D.L=L → D.Branches P.bind G → Mesa J ξ P D W d s
  timing (x : ℝ) : x∈Set.Icc (s/2) s→ temp (retime x)=Paint.phase x ∧
    ∀ (A : Levels G) (i p), (A.clock.op i p).patch.J=j → (A.clock.op i p).patch.L=L → (A.clock.op i p).patch.Branches P.bind G → Atlas.clim A i=x →
      A.clock.loopCap (i+1) ≤ betaF G (retime x) L^(1/8:ℝ) ∧ A.clock.allowance (i+1) ≤ retime x^(-(1/2):ℝ)
private lemma score (G : Gauge) (D : Patch) : ∀ᶠ x in atTop,∀ (A : Levels G) (i p : ℕ), (A.clock.op i p).patch = D → clim A i=x →
    A.clock.loopCap (i+1) ≤ betaF G (retime x) D.L^(1/8:ℝ) ∧ A.clock.allowance (i+1) ≤ retime x^(-(1/2):ℝ) := by
  filter_upwards [Due.post_goods G D,burst_limit,eventually_ge_atTop (1:ℝ)] with x hx hv hf A i p he h
  let q := A.clock.hatBeta (i+1); let u:= retime x; let z:=A.clock.hatCoupling (i+1)
  have hs : q=betaF G x D.L:=by unfold q;rw [Due.carriage A i p, he,show A.clock.hatBeta _= x from h]
  have hp:x ≤ q:= hs.symm ▸ le_add_of_nonneg_right (Work.E04.shift_nonneg ..) -- ▸
  have hq:0<q:= hx.1.trans_le hp; have he' :0<x:= hx.1
  have hz:0<z:= by unfold z Calendar.hatCoupling; exact inv_pos.mpr (Real.sqrt_pos.mpr hq)
  have hh:z≤1:= inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (hf.trans hp)) -- sig
  obtain ⟨hr,hv',hg,hl⟩:=hx.2 _ _ _ he h
  constructor
  · refine le_trans hr (Real.rpow_le_rpow hq.le ?_ (by norm_num))
    change q ≤ _; rw [hs]; exact add_le_add_left hv.1 _
  unfold Calendar.allowance; apply le_trans (Real.rpow_le_rpow_of_exponent_ge hz hh (show (2:ℝ) ≤ 11/5 by norm_num)); rw [Real.rpow_two]; change ((Real.sqrt q)⁻¹)^2≤ _; rw [inv_pow,Real.sq_sqrt hq.le]
  have h':x⁻¹=(x^2)^(-(1/2):ℝ):= by rw [← Real.rpow_two,← Real.rpow_mul he'.le]; norm_num; rw [Real.rpow_neg_one]
  exact (inv_anti₀ he' hp).trans (h'.trans_le (Real.rpow_le_rpow_of_nonpos (he'.trans_le hv.1) hv.2.1 (by norm_num)))

/-- Stage X after L. Trim itself chosen after analytic gate; prepares even
for enlarged width. -/
def RangeOkay (P : Teller G) (L : Side) (i : Purse):Prop:= ∀ᶠ W in atTop,∀ J : ChartRatio G, LocalRatio J→ ∃ a d : ℝ,0<a∧0<d ∧
    ∀ (d' δ : ℝ),d≤d' → ∀ hp :0<δ,δ ≤ a → ∀ᶠ s in atTop,Ports P J P.j L (InteractingRank.trim i δ hp) W d' s
-- pre-L:X casts and opt independent
lemma billable (P : Teller G) (i : Purse):∃ n:ℕ,∀ L:Side,n≤ L.val → RangeOkay P L i:=by
  obtain ⟨n,hn⟩:= Wax.preheat P
  obtain ⟨C,hC⟩:= Aff.reserves P
  obtain ⟨u,hu⟩:= Jewels.pre P C
  let e:= Docking.increment (load i.era+1); let A:=P.top.supportExponent; let t:= A/4
  have he :0≤e:=by unfold e Docking.increment load Flux.ucap; linarith only [i.spend]
  have hA:0<A:=P.top.price_pos; have ht:0<t:=by unfold t; positivity
  obtain ⟨p,hp⟩:= Fees.exponent 1 ht he (show 2*t < A by unfold t; linarith only [hA])
  refine ⟨n+u+p,fun L hL=>?_⟩
  unfold RangeOkay
  filter_upwards [hn L (by omega),eventually_gt_atTop (0:ℝ), Jewels.settlers P C] with W hw hW h' J hJ
  obtain ⟨m,hm,hM⟩:=hw
  let α:=m/4; have ha:0<α:=div_pos hm zero_lt_four; let a:=α/8; have h:0<a:=by unfold a; positivity
  by_cases hz:∃ Q : Patch,Q.J=P.j ∧ Q.L=L ∧ Q.Branches P.bind G
  swap
  · refine ⟨a,1,h,zero_lt_one,fun d δ hD hh he=>?_⟩; obtain ⟨Y,hY⟩:=eventually_atTop.mp burst_limit
    filter_upwards [Perch.half.eventually_ge_atTop Y] with s hs
    exact ⟨fun Q h he hB=> (hz ⟨Q,h,he,hB⟩).elim,fun x hx => ⟨(hY x (hs.trans hx.1)).2.2, fun A i l hj hp h=> (hz ⟨(A.clock.op i l).patch,hj,hp,h⟩).elim⟩⟩
  obtain ⟨Q,hQ,hy,hK⟩:=hz; subst L
  obtain ⟨d,ε,hd,hε,H⟩:= excels J hJ P Q hK W hC (hu Q.L (by omega)) hW h'
  refine ⟨a,d,h,hd,fun d' δ hF hh hv=>?_⟩
  let i':= InteractingRank.trim i δ hh
  have hh : ∀ᶠ s in atTop, Mesa J i' P Q W d' s:=by
    refine vouches P Q hK J hJ i' (fun {c f} S hS=>hp c f S.ratio (by change p≤ S.patch.L.val; rw [hS]; omega)) ht (H d' hF) (hM _ _) hm ha hε (by unfold α; linarith only) hW (hd.le.trans hF) ?_
    change 2*δ≤_; unfold a at hv; linarith only [hv]
  have hD {D:Patch} (hj : D.J=P.j)(hL : D.L=Q.L): D=Q:= by cases Q; cases D; congr; simp_all
  obtain ⟨r,hr⟩:= eventually_atTop.mp (burst_limit.and (score G Q))
  filter_upwards [hh, Perch.half.eventually_ge_atTop r] with s H hs
  refine ⟨fun D hj hL _=> (hD hj hL).symm ▸ H,fun x hx=>?_⟩; obtain ⟨h,hh⟩:=hr _ (hs.trans hx.1); exact ⟨h.2.2,fun A i p hj hL hP he=>hh _ _ _ (hD hj hL) he⟩

-- Combustion pre & post stamps
variable (B : MapPrices)
section
-- L tests included with same gate. Expose existential W,d possibilities; never tie all portals to it unless proved.
variable (X : Supply.Sheet G)
structure Fair (k : ℕ→ Finset ℕ) (p : ∀ (d:ℕ),Tapes.Panel d) (M : ℕ→ℕ) : Prop where
  poles j L : M j ≤ L.val → ∀ i∈ k j, RangeOkay (G:=G) (initials B X.profile X.kernel j j) L ((p i).bag j)
-- offsets paid only once after P.head

lemma proclaimed {W d' d s : ℝ} {i : ℕ} {L : Side} {v : Purse} {J : ChartRatio G} (h : Ports (initials B X.profile X.kernel i i) J i L v W d' s) (hp : Posts J B X.profile X.kernel i v L W d s) : Posts J B X.profile X.kernel i v L W d' s:= by
  refine ⟨hp.monitor,hp.clamp,hp.mile,hp.melt,hp.wool,?_⟩
  intro x hx c f S T hL hv hk hs ht
  let Q:= h.localizes S.patch hv hL hk|>.march x hx
  obtain ⟨hp,H⟩:=Q.eligible S T rfl hs ht
  rw [← hL]; exact ⟨hp,Q.boom,Q.ride,fun Y h β hb D=>H Y D β h hb⟩
end
end YM.PhysicalNext.InteractingRank.Pump
