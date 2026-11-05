import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Stint
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Buyers
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Balancing
import YM.Progress.JOINT_CALENDAR.Branches
import YM.Push.LOCAL_SPLITTING.Leading
import YM.Push.STATIONARY_UNIFORM.Travel
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Extras
import YM.SectorNext.RECONNECTED_LOCALITY.First


/-!
# Auxiliary CAB affine prediction sold together with the rank prediction

Value-only comparison of two *different* realizations. Never assert CAB's
oriented affine operator or chart size, turns or shift or guards give the
real sector's. Compare instead to the SAME small log chart of the V argument,
using retained station and both actual sector estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Spindle WeightedGaussianMarginal45C.Venue PhysicalGuard7f546.Curved
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x C : ℝ} {d : ℝ}

section w
private lemma pace (G : Gauge) (P : Patch) : ∀ᶠ x : ℝ in atTop,
    let B := radiusB x; let t:=temp x; let a:=4*(↑(20*B+2:ℕ):ℝ)*t
    0<t ∧ clearanceFare x ≤ (poseRules G).c ∧ a ≤ (poseRules G).c ∧ 2*a ≤ clearanceFare x/2 ∧ clearanceFare x/2 ≤ Rates.allowance G P x 1 7:= by
  have hχ := poseRules G|>.radius
  filter_upwards [eventually_gt_atTop (0:ℝ), (boundary_limited 1 zero_le_one).eventually (ge_mem_nhds hχ),
    Rates.tariff_paid G P 6, Work.E01.radiusB_tendsto.eventually_ge_atTop 200, Rates.widen G P (n:=1) (by decide : 6≤7)] with x ht hx hp he hu
  intro B t a; have hv : 0<t:=Work.E09.temp_pos ht
  have hh: clearanceFare x≤ (poseRules G).c:= (one_mul _).symm.trans_le hx
  let N : ℝ := Fintype.card PlaqAxes
  have hN:1 ≤ N:=by unfold N; norm_cast
  have hb : 2≤(radiusB x:ℝ):=by exact_mod_cast he.trans' (by decide : 2 ≤ 200)
  have hK : 2*a ≤ clearanceFare x/2:= by
    unfold a B clearanceFare t
    push_cast
    let b := (radiusB x:ℝ); have hb' : 2≤b:=hb
    have hw : 2*b ≤ 2*(b+1)+1:=by linarith
    have h1 : 20*b+2 ≤ (2*(b+1)+1)^5*N := by
      refine le_trans ?_ (le_mul_of_one_le_right (by positivity) hN)
      let j:=2*b; have he' : 4≤j:=by unfold j; linarith
      have hg : j^2 ≤ (2*(b+1)+1)^5:= (pow_le_pow_right₀ ((by norm_num : (1:ℝ) ≤ 4).trans he') (show 2≤5 by decide)).trans (pow_le_pow_left₀ (by linarith : 0≤j) hw 5)
      unfold j at *; nlinarith only [hb',hg,show 200≤(b:ℝ) by unfold b; exact_mod_cast he]
    linarith only [mul_le_mul_of_nonneg_right h1 hv.le]
  refine ⟨hv,hh,by linarith only [hh,hK,hχ],hK,le_trans ?_ (hp.trans hu)⟩
  have ht : 0≤temp x:=hv.le
  apply (half_le_self (show 0 ≤ clearanceFare x by unfold clearanceFare; positivity)).trans
  unfold clearanceFare Aff.tariff; push_cast; gcongr; linarith only [hb]

lemma full_pose (G : Gauge) (P : Patch) : ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (A : Stores S) (V : Config G c), S.patch=P → 100*(1+radiusB x)≤c.val →
    A.flags=RG.flags (temp x) V → ∀ i : Site c, i∉ A.dome (30*radiusB x) →
    let z := fingers V i; let V':=Lattice.gauge z V
    ∃ v : Dir G c, AgreeNear id i (20*radiusB x) V' (represent v) ∧ ‖v‖ ≤ Rates.allowance G P x 1 7 ∧ ‖v‖≤ clearanceFare x/2 ∧
      paid S (replica S.ratio V') i (20*radiusB x) (clearanceFare x):= by
  filter_upwards [pace G P,Work.E01.radiusB_tendsto.eventually_ge_atTop 200] with x hx hv c f S A V he hp hF i hi
  let I:=poseRules G; let B:=radiusB x; let W:=20*B+2; let t:=temp x; let a:=4*(W:ℝ)*t
  obtain ⟨ht,hχ,h,h0,h1⟩:=hx
  have he:2*(W+1)< c.val:=by unfold W B; omega
  have hz:Healthy t (Spindle.patch W i) V:= by
    unfold Healthy; rw [←show A.flags=RG.flags t V from hF]; apply Finset.disjoint_left.mpr
    intro j hj hh; have he : separation j i ≤ W:= (separation_comm ..).trans_le ((Spindle.doors _).1 hj)
    exact hi (halo_spec.mpr ⟨j,mem_union_right _ hh, he.trans (by unfold W B; omega)⟩)
  intro z V'
  obtain ⟨hP,Hk,-⟩ := closer I he V hz 1 zero_lt_one ht h
  let b := wired 1 i W V
  have hx' : ‖b‖ ≤ clearanceFare x/2 := by
    change ‖b‖ ≤ (_:ℝ)/1 at hP; rw [div_one] at hP; exact hP.trans h0
  let J e := if h : e∈Room i W then b ⟨e,h⟩ else 0
  let v : Dir G c := fun y => J (y.1,axisEquiv.symm y.2)
  have hb : ‖v‖≤‖b‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg b)).2 fun e => by
    unfold v J; split
    · exact norm_le_pi_norm ..
    rw [norm_zero]; exact norm_nonneg _
  have hh : AgreeNear id i (20*B) V' (represent v) := by
    intro j h
    have he' : j∈ Room i W:= by
      have h0 : separation i (j.1+step j.2) ≤ 20*B+1:= (separation_triangle i j.1 _).trans (Nat.add_le_add h (Work.E01.sep_step_le .. ))
      exact mem_filter.mpr ⟨mem_univ _,(Spindle.doors _).2 (by unfold W; change separation i j.1≤20*B at h; omega), (Spindle.doors _).2 (h0.trans (by unfold W; omega))⟩
    change spine V i j=_; rw [← show G.lieExp ((1:ℝ) • b ⟨j,he'⟩)= _ from Hk ⟨j,he'⟩,represent,increment,one_smul,Pi.one_apply,mul_one, collect]
    unfold v; dsimp only; rw [← coord_map,axisEquiv.symm_apply_apply, Prod.mk.eta]; simp [J,he']
  refine ⟨v,hh,hb.trans (hx'.trans h1),hb.trans hx',fun j hj=>?_⟩
  rw [copyAgree V' _ i _ hh j hj,replica_rep v,represent,increment,Pi.one_apply,mul_one]
  let a:=collect G (blueprint S v) j
  have he' : ‖a‖ ≤ clearanceFare x / 2 := (norm_le_pi_norm _ (j.1,coord j.2)).trans ((blueprint_bill v).trans (hb.trans hx'))
  exact (I.light a (le_trans he' (by linarith only [hχ, poseRules G|>.radius]))).trans (by linarith only [he'])

lemma remote_pose (G : Gauge) (P : Patch) : ∀ᶠ x in atTop,
    ∀ {c f : Side} (S : StepData c f) (A : Stores S) (V : Config G c), S.patch=P → 100*(1+radiusB x)≤c.val →
    A.flags=RG.flags (temp x) V → ∀ i : Site c, i∉ A.dome (30*radiusB x) →
    let z := fingers V i; let V':=Lattice.gauge z V
    ∃ v : Dir G c, AgreeNear id i (6*radiusB x) V' (represent v) ∧ ‖v‖ ≤ Rates.allowance G P x 1 7 ∧ ‖v‖≤ clearanceFare x/2 ∧
      paid S (replica S.ratio V') i (6*radiusB x) (clearanceFare x):= by
  filter_upwards [full_pose G P] with x hx c f S A V hp he hF i hi
  obtain ⟨b,h,hb,hD,hP⟩:= hx S A V hp he hF i hi
  exact ⟨b,h.shrink (by rw [separation_self]; omega),hb,hD,fun j hj=> hP j (hj.trans (by omega))⟩
end w

section price
-- eventual quantity budget; over all needed n=1,2,3, ... and addresses
lemma trim_rate (G : Gauge) (D : Patch) (n e : ℕ) (a : ℝ) (ha : 0<a) : ∀ᶠ x in atTop, Rates.allowance G D x n e ≤ x^ (-(n:ℝ)/2+a) := by
  let δ:=a/(4*(n+1:ℝ)); have hd : 0<δ:=div_pos ha (by positivity)
  filter_upwards [eventually_ge_atTop (1:ℝ), Rates.closer G D,const_allow (show 0 ≤ (2:ℝ) by norm_num)
    (b:=-(1/2:ℝ)+2*δ) (show -(1/2:ℝ)+δ < -(1/2:ℝ)+2*δ by linarith), Work.E09.temp_cost δ hd, stride_tiny e (a/2) (half_pos ha)] with x hx hv hr ht hB
  obtain ⟨-,hβ⟩:=hv
  let d0 := (-(1/2):ℝ)+2*δ; let r:=x^d0
  have hx' := zero_lt_one.trans_le hx
  have hf : fiery G x D.L ≤ r:= hβ.trans ((mul_le_mul_of_nonneg_left ht (by norm_num)).trans hr)
  apply (mul_le_mul (b:=x^(a/2)) (d:=r^n) (show Rates.pieces x e ≤ x^(a/2) from le_trans ?_ hB.2) (pow_le_pow_left₀ (temp_nonneg _) hf n) (pow_nonneg (temp_nonneg _) _) (by positivity)).trans
  · unfold r; rw [← Real.rpow_natCast (_:ℝ) n,← Real.rpow_mul hx'.le,← Real.rpow_add hx']; apply Real.rpow_le_rpow_of_exponent_le hx
    have hh: δ*(4*(n+1:ℝ))=a:=div_mul_cancel₀ _ (by positivity)
    unfold d0; linarith only [hh,hd]
  unfold stride; push_cast; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) e

-- The exact active labels away from footprints. Compare globally also if all positions freeze.
lemma stillActive (F : Forest S.ratio) (A : Stores S) (x : ℝ) (i : F.Free) :
    i.val∈ Aff.activeB A F (radiusB x) ↔ ¬chill A x F i := by
  simp [Aff.activeB, Aff.points,pinPos,Finset.disjoint_left,chill,i.property]

lemma same_face (T : Tube G S) (F : Forest S.ratio) (b : Dir G c) : doc T F b=Aff.attempt T F b := by
  have he : Aff.station T F b=low T F b:= by
    funext i; ext j; exact (congr_fun (Work.F04.parts_stretch F (installed S.ratio T.R.A0) b j) i).symm
  unfold doc Aff.attempt; rw [he]
  exact Eq.symm (congr_arg (collect G (low T F b) - ·) (Flat.collected _).symm)

-- Compare BOTH predictions; no assertion of equality of their laws
lemma peers (hC : Aff.Reserve P C) (D : Patch) (he : D.Branches P.bind G) (q : Win.Promise.Turns) :
    ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S), (P).Funds S T→ S.patch=D → Larger (G:=G) S →
    ∀ (H K : Bed), Aff.Alongside H K T → Booth P S T → ∀ (F : Forest S.ratio) (A : Stores S) (Y : Aff.Mint T F A x),
    Aff.cert S x A Y.V → q.Takes (Aff.eyes S G (radiusB x)) Y.sheet (Aff.dcol S) (Aff.paceR x) →
    ∀ (i : Active A x F), Aff.home S i.val.val∉A.dome (30*radiusB x) → ∀ (χ : Chi) (d : ℝ) (p : LinkArray G (Frozen A x F)),
        ‖tape (portrait T A F Y.k x Y.V .endpoint χ d p) i-Aff.lie Y.μ i.val.val‖≤x^(-(3/4):ℝ) := by
  let N := (Fintype.card G.ColorIndex:ℝ)
  filter_upwards [Aff.velocity P C hC D he q, remote_pose G D, booster D P he,
    aperture G D P he 0 1 le_rfl,trim_rate G D 2 27 (1/8) (by norm_num),
    const_allow (show 0≤2*N from mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (show (-(7/8):ℝ) < -(3/4) by norm_num),
    eventually_gt_atTop (1:ℝ)] with x ha hB ho hp hd he hyᵤ c f S T hT hS h₀ H K hk hF F A Y hY hq i hi χ d p
  let j:=i.val.val; let B:= radiusB x; let o:=Aff.home S j; let z:=fingers Y.V o; let V':=Lattice.gauge z Y.V
  obtain ⟨hb,hD⟩:=hY
  obtain ⟨b,h,hb',hw,hl⟩:= hB S A Y.V hS hb hD o hi
  let Y':=GaugeRoute.sendFrozen S z x A F p
  let g:= Aff.unit F A x T z b; let y := x^(-(7/8):ℝ)
  have hv := ha c f S T hT hS H K hk F A Y ⟨hb,hD⟩ hq o (fun h=>hi (Aff.placed A _ _ (by omega) h)) z b hb' h
  have hc : Clears A x o (radiusB x):=fun hz=>hi (Aff.placed A _ _ (by have hh:0<radiusB x := Nat.ceil_pos.mpr (sq_pos_of_pos (Real.log_pos hyᵤ)); omega) hz)
  have hx : Positioned x A V':= Positioned.turn (A:=A) (U:=Y.V) (show Positioned _ _ _ from hD) z
  have hh : AgreeNear id o B V' (represent b):= h.shrink (show separation o o+B ≤ _ by rw [separation_self]; omega)
  have hw' : ‖b‖ ≤ 1*clearanceFare x := by linarith only [hw,norm_nonneg b]
  let t:= portrait T A F Y.k x V' .endpoint χ d Y'
  have hm (j' : G.ColorIndex) : |t (i,j')-portrait_head T F b (loadLink A F x (i,j'))| ≤ y :=
    (hp S T hS hF h₀ hb A o hc V' hx b hh hw' (fun i hi=> (hl i (le_trans hi (by change B ≤ _; unfold B; omega))).trans_eq (one_mul _).symm)
      F Y.k χ d .endpoint Y' (i,j') (by change separation o o ≤ _; rw [separation_self]; omega)).1
  have hA:=ho S T hS hb hT
  have hY:= (turned_law z A F x P T Y.V Y.k .endpoint p χ d hT (hA.fogged _ _ _ _ hx)).1
  let t':= portrait T A F Y.k x Y.V .endpoint χ d p
  let R:= G.adjoint (z o); have hr : tape t i=R (tape t' i) := by unfold t; change portrait _ _ _ _ _ V' _ χ d Y'= _ at hY; rw [hY]; exact turn_color ..
  have hs : doc T F b j=R (Aff.lie g j):= by rw [same_face]; exact (Aff.on_way F A x T z b j (Or.inr ((stillActive ..).mpr i.property))).symm
  have hy : 0≤ y:=by unfold y; positivity
  have hq: ‖tape t' i-Aff.lie g j‖ ≤ N*y:= by
    rw [← show ‖R (tape t' i-Aff.lie g j)‖=_ from G.norm_adjoint _ _, map_sub,← hr,← hs]
    exact UVNext.PricedKernels.color_count hy _ hm
  apply (norm_sub_le_norm_sub_add_norm_sub _ (Aff.lie g j) _).trans
  refine (add_le_add hq (d:=N*y) ?_).trans ?_
  swap; change N*y+N*y≤_; change 2*N*y≤_ at he; linarith only [he]
  rw [norm_sub_rev]; apply UVNext.PricedKernels.color_count hy
  intro z; refine le_trans (hv (j,z) (show separation o o≤_ from by rw [separation_self]; omega)) (hd.trans_eq ?_)
  unfold y; push_cast; norm_num
end price
end YM.PhysicalNext.InteractingRank.Milk
