import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Dollars
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Next.RANK.Flux.Chronicle
import YM.Next.RANK.Prepaid
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Rounds
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.UVNext.PRICED_KERNELS.Basin

/-!
# Price dropped F rows differently

Clipped direct is at Rank input t. Other tallies still priced on
sector annotation thresholds, knowing nothing of this t.
Use analogue of  for all tags, with Work.E06 technique at two
different temperatures. Re-establish revenue with new LaneCounts in Attic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Wax
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Paint Filter Finset Precision Tree
open Pressure.Tube Pressure.Teller Pressure.Stores YM.Bid UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {w x t C u d : ℝ} (T : Tube G S) (A : Stores S) {U : Config G f} {Q V : Config G c} {k : S.Choices}
    (hP : Plot A U k V x w)
local notation "ν" => fiery G x S.patch.L
include hP in
private lemma listed (hu : ν/2≤ t) (_E : LaneCounts T.up x t T.high C 1 S.ratio.parent)
    (p q : Cell f) (h : p∈ A.limit x) (hp : separation (S.ratio.parent p.1) (S.ratio.parent q.1) ≤ radiusB x/50) (ht : t < toll U q) : q∈ A.costs:= by
  have hf : S.ratio.parent q.1∈ A.dome (5*radiusB x):=by
    obtain ⟨i,hi,hh⟩:= halo_spec.mp (show _ from (mem_filter.mp (show p∈A.limit x from h)).2)
    refine halo_spec.mpr ⟨i,hi,(separation_triangle _ (S.ratio.parent p.1) _).trans ?_⟩; omega
  by_contra hn
  exact ht.not_ge (((hP.consumes q (fun h=> disjoint_left.mp h hf
    (mem_image_of_mem _ (Work.E01.base_touched q)))).2 hn).trans hu)

def scarf (p : Clip) := Fintype.card PlaqAxes * basin p.relaxation⁻¹
include hP in
private lemma relief (E : LaneCounts T.up x t T.high C 1 S.ratio.parent) (hu : ν/2 ≤ t) (ht : 0 ≤ t) (hC : 0≤C) :
    let D:= (A.limit x).filter (fun p : Cell f=> ¬PathData.kept T.high t p.1 U)
    ∑ i∈ D,‖shorten T.up (till x) 1 U i‖≤ (1+scarf T.high)*C*∑ j∈ A.swell U t,toll U j:=by
  intro D; let X:= A.swell U t; let M:=crunch (n:=f) T.up (till x) 1; let Z:=∑ j∈ X,toll U j
  have hd (p) (hi:p∈D): ∑ j, M p j*toll U j ≤ (∑ j∈X,M p j *toll U j) + C*t:= by
    have hh:p∈ A.limit x:= (mem_filter.mp hi).1
    rw [← sum_sdiff (subset_univ X), add_comm (∑ j∈ X,M p j*toll U j)]; apply add_le_add_left
    calc
      _ ≤ ∑ j∈univ \ X, M p j*t := by
        apply sum_le_sum
        intro i hv; obtain hh' := E.attic p i
        by_cases h : M p i=0
        · simp [h]
        apply mul_le_mul_of_nonneg_left _ hh'
        by_contra! hp
        exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨listed T A hP hu E p i hh (E.maps p i (lt_of_le_of_ne hh' (Ne.symm h))) hp,hp⟩)
      _ ≤ _:=by
        rw [← sum_mul]; apply mul_le_mul_of_nonneg_right _ ht
        exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> E.attic p i)).trans (E.finite p)
  have ht': ∑ i∈ D,(∑ j∈ X,M i j*toll U j) ≤ C*Z := by
    unfold Z; rw [sum_comm,mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg (subset_univ D) (fun j _ _=> E.attic j i)).trans (E.back i)) (G.chord_nonneg _)
  -- one falling carpet, not counting possible witnesses *per row*
  let R(p j:Cell f):= Real.exp (-T.high.relaxation⁻¹*separation j.1 p.1)
  have hv (p) (hp:p∈D): t ≤ ∑ j∈ X, R p j*toll U j := by
    obtain ⟨h,hp⟩:=mem_filter.mp hp
    simp only [PathData.kept,not_forall] at hp
    obtain ⟨i,hp⟩:=hp; have hf := lt_of_not_ge hp
    let z:= T.high.relaxation⁻¹*separation i.1 p.1
    have he : R p i=(Real.exp z)⁻¹:= by unfold R z; rw [neg_mul,Real.exp_neg]
    have hq:t * Real.exp z < toll U i:= by unfold z; rw [separation_comm i.1, ← div_eq_inv_mul]; exact hf
    have ha:t < toll U i:= lt_of_le_of_lt (le_mul_of_one_le_right ht (Real.one_le_exp (mul_nonneg (inv_nonneg.mpr T.high.radius_pos.le) (by positivity)))) hq
    apply le_trans _ (single_le_sum (f:=fun j=>R p j*toll U j) (fun a _=> mul_nonneg (Real.exp_pos _).le (G.chord_nonneg _)) (show i∈ X from mem_filter.mpr ⟨listed T A hP hu E p i h (E.dropped U p.1 i hf) ha,ha⟩))
    rw [he,← div_eq_inv_mul]; exact (le_div_iff₀ (Real.exp_pos _)).mpr hq.le
  have hz: (∑ i∈ D,t) ≤ scarf T.high*Z:= by
    apply (sum_le_sum hv).trans; unfold Z; rw [sum_comm, mul_sum]; refine sum_le_sum fun p _=>?_ ; rw [← sum_mul]
    apply mul_le_mul_of_nonneg_right _ (G.chord_nonneg _); apply le_trans (b:=∑ j,R j p) (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> (Real.exp_pos _).le))
    unfold Cell Face; rw [Fintype.sum_prod_type,sum_comm]; unfold R Prod.fst;
    simpa only [sum_const,card_univ, nsmul_eq_mul] using! sum_le_sum (s:=univ) (fun (_ : PlaqAxes) _=> funnel (inv_pos.mpr T.high.radius_pos) p.1)
  apply (sum_le_sum fun i hi=> (E.valued i U).trans (hd i hi)).trans; rw [sum_add_distrib,← mul_sum]; exact (add_le_add ht' (mul_le_mul_of_nonneg_left hz hC)).trans_eq (by unfold Z X; ring)

-- monetary principal at the ACTUAL other threshold
private def direct (T : Tube G S) (x t : ℝ) (U : Config G f) (V : Config G c) (p : Cell f):=
    let v:= T.Mv (till x) (temp x) V (p,false)
    PathData.clipped T.high t (toll U p) + ‖v‖^2/2 - inner ℝ v (Pressure.shoot T.high U p)
private def secondary (T : Tube G S) (x t : ℝ) (U : Config G f) (V : Config G c) (p : Cell f) :=
    let v:= T.Mv (till x) (temp x) V (p,true);let a:=shorten T.up (till x) 1 U p
    trunk T.up T.high (till x) 1 t U p + ‖v‖^2/2-inner ℝ v a
section
local notation "K"=> T.high
local notation "M"=> T.Mv (till x) (temp x) V
private lemma direct_dues (p : Cell f) (hi : toll U p ≤ t) :
    (Real.sqrt T.high.direct * toll U p- ‖T.Mv (till x) (temp x) V (p,false)‖)^2/2 ≤ direct T x t U V p:= by
  let f:= M (p,false); let q:=Pressure.shoot K U p; let a:=T.high.direct; let r:=toll U p
  have hh:= (real_inner_le_norm f q).trans (b:=_) (c:=_) (mul_le_mul_of_nonneg_left (show ‖q‖≤Real.sqrt a*r from by unfold q Pressure.shoot; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)) (norm_nonneg _))
  unfold direct PathData.clipped; dsimp only; rw [if_pos hi]; change (Real.sqrt a*r-‖f‖)^2/2≤ a*r^2/2+‖f‖^2/2-inner ℝ f q; linarith only [hh,show Real.sqrt a^2 *r^2=a*r^2 by rw [Real.sq_sqrt T.high.quadratic_pos.le]]

include hP in
private lemma pocket_price (E : LaneCounts T.up x t T.high C 1 S.ratio.parent) (hu : ν/2 ≤ t) (he : t ≤ 2*ν) (ht : 0≤t) (hm : ∀ i, ‖T.Mv (till x) (temp x) V i‖≤ d*t) (h1 : d ≤ Real.sqrt T.high.direct/16) (h2 : d*Real.sqrt T.high.direct ≤ T.high.linear/4):
    (3/4*T.high.linear)*t*(∑ j∈ A.swell U t,toll U j)+(T.high.direct/512)*t^2*((A.costs\A.swell U t).card:ℝ) ≤ ∑ p∈ A.limit x, direct T x t U V p:= by
  let X:= A.swell U t; let b:= T.high.linear; let a:= T.high.direct; let Z:= direct T x t U V
  have ht' (p) (hh:p∈A.costs) : (S.ratio.parent p.1)∈ A.place:=mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨_,hh,mem_image_of_mem _ (Work.E01.base_touched p)⟩))
  have hc : A.costs ⊆ A.limit x:= fun _ h=> mem_filter.mpr ⟨mem_univ _,halo_subset _ _ (ht' _ h)⟩
  have h₁ (p : Cell f) (hp:p∈ A.costs\X): a/512*t^2 ≤ Z p:= by
    let r:= toll U p; let v:= M (p,false)
    obtain ⟨hp,H⟩:= mem_sdiff.mp hp
    have hv : t/8≤ r:= by
      have h := (hP.consumes p (not_disjoint_iff.mpr ⟨_,halo_subset _ _ (ht' _ hp),mem_image_of_mem _ (Work.E01.base_touched p)⟩)).1 hp
      change _≤r at h; linarith only [he,h]
    have hs: Real.sqrt a*t/16 ≤ Real.sqrt a*r-‖v‖:= by
      have hh: ‖v‖ ≤ Real.sqrt a/16*t:= (hm _).trans (mul_le_mul_of_nonneg_right h1 ht)
      linarith only [hh,mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg a)]
    apply le_trans _ (direct_dues T p (le_of_not_gt (fun h=> H (mem_filter.mpr ⟨hp,h⟩))))
    rw [show a/512*t^2=(Real.sqrt a*t/16)^2/2 from by rw [div_pow,mul_pow,Real.sq_sqrt T.high.quadratic_pos.le];ring]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hs _) (by norm_num)
  have h₃ (p) (hp:p∈ X): 3/4*b*t*toll U p ≤ Z p:= by
    let v:= M (p,false); let q:= Pressure.shoot T.high U p; let r:=toll U p
    have hq : ‖q‖≤ Real.sqrt a*r:= by unfold q Pressure.shoot; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)
    have hr : t<r:= (mem_filter.mp hp).2
    have hh : inner ℝ v q ≤ d*t*(Real.sqrt a*r):=(real_inner_le_norm v q).trans (mul_le_mul (hm _) hq (norm_nonneg _) ((norm_nonneg v).trans (hm _)))
    unfold Z direct PathData.clipped; rw [if_neg (not_le.mpr hr)]; dsimp only; change _≤ b*t*r+‖v‖^2/2-inner ℝ v q; change _*r≤_; linarith only [hh,mul_le_mul_of_nonneg_right h2 (mul_nonneg ht (show 0≤r from ht.trans hr.le)),sq_nonneg ‖v‖]
  have h0:= add_le_add (sum_le_sum h₁) (sum_le_sum h₃); rw [sum_sdiff (show X⊆ A.costs from filter_subset ..),sum_const,nsmul_eq_mul, ← mul_sum] at h0
  rw [← add_comm, mul_comm _ (((A.costs \ _).card):ℝ)]; refine h0.trans (sum_le_sum_of_subset_of_nonneg hc ?_); intro i hi hf
  exact le_trans (b:=_) (by positivity) (direct_dues T i (le_of_not_gt fun h=> hf (listed T A hP hu E i i hi (by simp) h)))

include hP in
private lemma tilted_cost (E : LaneCounts T.up x t T.high C 1 S.ratio.parent) (hu : ν/2 ≤ t) (ht : 0≤t) (hm : ∀ i, ‖T.Mv (till x) (temp x) V i‖≤ d*t) (hd : 0 ≤ d) (hC : 0≤C) (h : d*((1+scarf T.high)*C) ≤ T.high.linear/4) :
    - (T.high.linear/4)*t*(∑ j∈ A.swell U t,toll U j) ≤ ∑ p∈ A.limit x, secondary T x t U V p:= by
  let D:= (A.limit x).filter (fun p : Cell f=> ¬ PathData.kept T.high t p.1 U)
  let b:=T.high.linear; let Z:=∑ j∈ A.swell U t,toll U j
  have hv(p) (hp:p∈ D): -(d*t)*‖shorten T.up (till x) 1 U p‖ ≤ secondary T x t U V p:=by
    let v:=M (p,true); let a:=shorten T.up (till x) 1 U p
    have hh:= (real_inner_le_norm v a).trans (mul_le_mul_of_nonneg_right (hm (p,true)) (norm_nonneg _))
    unfold secondary; rw [trunk,if_neg (mem_filter.mp hp).2]; change -(d*t)*‖a‖ ≤ 0+‖v‖^2/2-inner ℝ v a; linarith only [hh,sq_nonneg ‖v‖]
  have ht' := relief T A hP E hu ht hC
  have hs : d*t*(∑ p∈ D,‖shorten T.up (till x) 1 U p‖) ≤ b/4*t*Z:= by
    have h := mul_le_mul_of_nonneg_right h (mul_nonneg ht (show 0≤Z from sum_nonneg fun i _=> G.chord_nonneg _)); linarith only [h,mul_le_mul_of_nonneg_left ht' (mul_nonneg hd ht)]
  refine le_trans (b:=∑ p∈D, secondary T x t U V p) ?_ (sum_le_sum_of_subset_of_nonneg (filter_subset ..) ?_)
  · have hv:=sum_le_sum hv; rw [← mul_sum] at hv; change _≤_ * _ at hs; linarith only [hs,hv]
  intro p hp he
  let v:=M (p,true); let a:=shorten T.up (till x) 1 U p
  have hf : PathData.kept T.high t p.1 U:= Classical.not_not.mp fun h=>he (mem_filter.mpr ⟨hp,h⟩)
  unfold secondary; rw [trunk, if_pos hf]; change _≤ ‖a‖^2/2+‖v‖^2/2-inner ℝ v a; linarith only [real_inner_le_norm v a,sq_nonneg (‖v‖-‖a‖)]

def fineCharge (T : Tube G S) (A : Stores S) (x t : ℝ) (U : Config G f) (V : Config G c):= ∑ i∈ A.limit x, T.workF (till x) U V t (temp x) i
include hP in
lemma flickers (E : LaneCounts T.up x t T.high C 1 S.ratio.parent) (hu : ν/2≤t) (he : t ≤ 2*ν) (ht : 0≤t) (hm : ∀ i, ‖T.Mv (till x) (temp x) V i‖≤ d*t) (h₀ : 0≤d) (hC : 0≤C) (h1 : d ≤ Real.sqrt T.high.direct/16) (h2 : d*Real.sqrt T.high.direct ≤ T.high.linear/4) (h : d*((1+scarf T.high)*C) ≤ T.high.linear/4) :
    T.high.linear/2*t*(∑ j∈ A.swell U t,toll U j)+(T.high.direct/512)*t^2*((A.costs\A.swell U t).card:ℝ) ≤ fineCharge T A x t U V := by
  have h3:=pocket_price T A hP E hu he ht hm h1 h2; have h4:= tilted_cost T A hP E hu ht hm h₀ hC h
  have H (p): T.workF (till x) U V t (temp x) p=direct T x t U V p+secondary T x t U V p:= by simp [Tube.workF,direct,secondary,crown,Pressure.shoot,trunk,toll,Tube.Xf,plotted]; ring
  unfold fineCharge; simp_rw [H,sum_add_distrib]; linarith only [h3,h4]
end
end YM.PhysicalNext.InteractingRank.Wax
