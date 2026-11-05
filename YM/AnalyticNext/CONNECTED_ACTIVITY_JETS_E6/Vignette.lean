import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Coat
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites

/-!
# Genuine predictors tested on full neighborhoods with G colors

Reuse finite-chart proofs, transplant for all-order. Whole-step bound at
possibly VERY small constant post-L; no shrinking with period, includes
all tags arrays on same orbit. Does not force large/threshold behavior or
switch to branchless Q when unscaled. Replays the geometric transplant
from private `transplant_z` extending to linear array envelope at
all nearby fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Shadow
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Laurent Tree
open Next.Fluctuations Brush
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

variable (P : Patch) (o : Axis)

-- No particular geometric efficiency needed for this fixed-patch receipt.
private def frameSites : Finset Cover := univ.biUnion fun x : P.Points => univ.biUnion
  fun y : P.Points => univ.biUnion fun l : Lattice.Order => (visits x.val (route x.val y.val l)).toFinset

private def alongBond := List.replicate P.L.val (posDir o)
private def bondShift : Cover := centerRoot P (step o)

private def predSites := (frameSites P ∪ (frameSites P).image (· + bondShift P o)) ∪
  univ.biUnion (fun x : P.Points => (visits x.val (alongBond P o)).toFinset)

private lemma frame_eq (K : KernelChoices) (hb : P.Branches K G)
    (U W : CoverConfig G) (h : ∀ i : Edge Cover, i.1 ∈ frameSites P → U i = W i)
    (t : P.FrameTag) : P.frame K U t = P.frame K W t := by
  have he (x y : P.Points) (l : Lattice.Order) : travel U x.val (route x.val y.val l) =
      travel W x.val (route x.val y.val l) := by
    apply travel_local _ _ U W
    exact fun i hi _ => h i (mem_biUnion.mpr ⟨x,mem_univ x, mem_biUnion.mpr ⟨y,mem_univ y,
      mem_biUnion.mpr ⟨l,mem_univ l,List.mem_toFinset.mpr hi⟩⟩⟩)
  have hax (x : P.FrameTag) : P.axial U x = P.axial W x := funext fun i => he x.1 i x.2
  have hv (f : P.Frame G) : P.via f U = P.via f W := by funext x y l; rw [via, via, he]
  have hs : P.score U = P.score W := by funext r; simp only [score,hv]
  have hm : P.usesMin K U ↔ P.usesMin K W := by simp only [usesMin,hax,hv]
  unfold Patch.frame
  by_cases hh : P.usesMin K W
  · rw [if_pos hh, if_pos (hm.mpr hh)]
    have h' : P.minimizing W (P.selected U) := by
      simp only [minimizing, ← hs]
      exact (P.min_exists U).choose_spec
    exact (hb.frame_unique W hh).unique h' (P.min_exists W).choose_spec
  · rw [if_neg hh, if_neg (fun h => hh (hm.mp h)), hax]

-- Make the different evaluation origins into explicit finite-cover reads.
private def predictionAt (K : KernelChoices) (U : CoverConfig G) (l r : P.FrameTag) (j : P.Points) :=
  P.predict K (fun x => P.frame K U l x * travel U x.val (alongBond P o) *
    (P.frame K (translate (bondShift P o) U) r x)⁻¹) j

private lemma predAt_eq (K : KernelChoices) (hb : P.Branches K G) (U W : CoverConfig G)
    (h : ∀ i : Edge Cover, i.1 ∈ predSites P o → U i = W i)
    (l r : P.FrameTag) (j : P.Points) : predictionAt P o K U l r j = predictionAt P o K W l r j := by
  have he : P.frame K U l = P.frame K W l := frame_eq P K hb U W
    (fun i hi => h i (mem_union_left _ (mem_union_left _ hi))) l
  let y := bondShift P o
  have hh : P.frame K (translate y U) r = P.frame K (translate y W) r := frame_eq P K hb _ _ (by
    intro i hi; unfold Lattice.translate; apply h
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hi))) r
  have hu (x : P.Points) : travel U x.val (alongBond P o) = travel W x.val (alongBond P o) :=
    travel_local _ _ U W fun i hi _ => h i <| mem_union_right _ (mem_biUnion.mpr
      ⟨x,mem_univ x,List.mem_toFinset.mpr hi⟩)
  unfold y at hh
  simp only [predictionAt, he, hh, hu]

private lemma reads_at (U : Config G f) (k : S.Choices) (q : Site c) (i : Axis) :
    S.prediction U k (q,i) = predictionAt S.patch i S.kernel (expandAt (S.ratio.embed q) U)
      (k.1 q) (k.1 (q+step i)) (k.2 (q,i)) := by
  have he := levels S q U (step i)
  rw [plank, wrap_step, add_comm] at he
  unfold predictionAt StepData.prediction StepData.connector StepData.frames bondShift alongBond; rw [he]

private lemma reference_exists : ∃ c₀ : Side, 1 < c₀.val ∧
    ∀ i : Axis, ∀ x ∈ predSites P i, lift (wrap (c₀*P.L) x) = x := by
  let M := univ.sup (fun i : Axis => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs)))
  let c₀ : Side := ⟨2*M+2, by omega⟩
  refine ⟨c₀, by change 1 < 2*M+2; omega,fun i x hx => lift_eq_iff.mpr ⟨rfl,fun a => ?_⟩⟩
  have hv : (x a).natAbs ≤ M := le_trans (le_sup (s:=univ) (f:=fun a => (x a).natAbs) (mem_univ a))
    (le_trans (le_sup (s:=predSites P i) (f:=fun x => univ.sup (fun a : Axis => (x a).natAbs)) hx)
      (le_sup (s:=univ) (f:=fun i => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs))) (mem_univ i)))
  have ht : 2*M < (c₀*P.L).val := lt_of_lt_of_le (b:=c₀.val) (by change _ < 2*M+2; omega)
    (by exact le_mul_of_one_le_right (Nat.zero_le _) P.L.property)
  omega


lemma transfers (P : Patch) (K : KernelChoices) (G : Gauge) (k : ℕ) (h : P.Branches K G) :
    ∃ r C : ℝ,0<r ∧ 0<C ∧ ∀ (c f:Side) (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ i : Bond c, ∀ p : S.Choices, ∀ f' : LogField G f, ‖f'‖ ≤ r →
      Brush k C 1 (fun u: LogField G f=> G.mat (S.prediction (represent u) p i)) f' := by
  obtain ⟨s,hs,he⟩:= reference_exists P
  let T : StepData s (s*P.L) := ⟨P,K,rfl⟩
  let g (i : T.Choices × Bond s) (u : LogField G (s*P.L)) := G.mat (T.prediction (represent u) i.1 i.2)
  have hp x : ∃ d : ℝ, 0<d ∧ ∃ C : ℝ, 0<C ∧ ∀ t : LogField G _, t∈Metric.closedBall 0 d → Brush k C 1 (g x) t := by
    obtain ⟨B,hB,hF⟩ := neighborhood 0 (show ContDiffAt ℝ (↑ k) (g x) 0 from (Push.prediction_cont T h x.2 x.1).of_le le_top)
    obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hF; exact ⟨r,hr,B,hB,h⟩
  choose d hd D hC hg using hp
  let X:= univ.image d
  let r:= X.min' (univ_nonempty.image d); have he' : r∈X := min'_mem _ _
  have hr : 0<r := by obtain ⟨i,-,hi⟩:= mem_image.mp he'; rw [← hi]; exact hd i
  let C:=1+∑ i,D i; have hc i : D i ≤ C := (Finset.single_le_sum (fun i _ => (hC i).le) (mem_univ i)).trans
    (le_add_of_nonneg_left zero_le_one)
  have ht : 0<C := add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun i _=> (hC i).le)
  refine ⟨r,C,hr,ht,?_⟩
  rintro c f ⟨P',K',hF⟩ hb hS ⟨x,a⟩ p u hm; change P'=P at hb; subst P'; change K'=K at hS; subst K'
  let S : StepData c f := ⟨P,K,hF⟩; let V y := wrap f (lift (y-T.ratio.embed 0))+S.ratio.embed x
  let A : LogField G f →ₗ[ℝ] LogField G (s*P.L) := { toFun W t := W (V t.1,t.2), map_add' _ _:=rfl,map_smul' _ _:=rfl }
  let L := A.toContinuousLinearMap; let i: Bond s := (0,a)
  let q : T.Choices := (fun y=> if y=0 then p.1 x else p.1 (x+step a),fun _=> p.2 (x,a)); let j := (q,i)
  have hb (u : LogField G f) : ‖L u‖ ≤ ‖u‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w=> norm_le_pi_norm u _
  have hL := reading (g:=g j) (x:=u) L ((hg j _ (Metric.mem_closedBall.mpr (by
    rw [dist_zero_right]; exact (hb u).trans (hm.trans (min'_le _ _ (mem_image_of_mem _ (mem_univ j)))))))
    |>.climb (hc _) le_rfl) (e:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u=> by rw [one_mul]; exact hb _))
  have hq (u:LogField G f) : S.prediction (represent u) p (x,a)=T.prediction (represent (L u)) q (0,a) := by
    rw [reads_at,reads_at]; haveI : Fact (1<s.val) := ⟨hs⟩
    have hz : step a≠(0:Site s) := by
      intro h
      have hr : (1:ZMod s.val)=0 := by simpa using congr_fun h a
      exact one_ne_zero hr
    change predictionAt P a K _ _ _ _=predictionAt P a K _ _ _ _
    rw [show q.1 (0+step a)=p.1 (x+step a) from by dsimp only [q]; rw [zero_add,if_neg hz],
      show q.1 0=p.1 x from if_pos rfl]; apply predAt_eq P _ _ h
    rintro ⟨w,z⟩ hw; change G.lieExp (u _)*1=G.lieExp (u (V (wrap (s*P.L) w+T.ratio.embed 0),_))*1
    rw [show V (wrap (s*P.L) w+_)=wrap f w+S.ratio.embed x from by unfold V; rw [add_sub_cancel_right,he _ _ hw]]
  rw [one_mul] at hL; change Brush k C 1 (fun v=> G.mat (S.prediction _ _ _)) _; simp_rw [hq]; exact hL
end YM.ConnectedActivityE6.Blaze.Shadow
