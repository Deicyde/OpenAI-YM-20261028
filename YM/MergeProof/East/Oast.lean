import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Core
import YM.Next.RANK.Tilt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris

/-!
# Convex combination of stamps
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Thirst Baler Lattice Wilson MeasureTheory Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration Ribbon Price

open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{b D k i N p d q:ℕ} {C:Family G} {t a g δ e:ℝ}
open Extra.Histories Motion
local notation "A"=> C.path.levels
local notation "σ"=> Signed
def mir (F:Frame G d)(s:Signed):= F.act s.ortho
lemma mirrors (F:Frame G d)(s r:σ) (x:F.Coeff):mir F (s*r) x=mir F s (mir F r x):=by unfold mir; rw [show (s*r).ortho=s.ortho*r.ortho from map_mul Signed.inclusionO s r,Frame.act_mul]
lemma undone (F:Frame G d)(s:σ)(x:F.Coeff): mir F s (mir F s⁻¹ x)=x:=Motion.round F (s,false) x
lemma pirouette (F:Frame G d)(s:σ)(x:F.Coeff): F.coeffSize (mir F s x) ≤ orbitCost F * F.coeffSize x:=Motion.patch_cost F (s,false) x
lemma beginning (F:Frame G d)(s:σ) : mir F s F.e0=F.e0:=by unfold mir; rw [← F.coords_unit,Frame.act_coords]; apply congr_arg; apply Subtype.ext; exact map_one (Labels.rotated s.ortho)
-- combinations as actual dockets averaging polynomials rather than Polys on masks
variable {Q : Rep G (C.side k p)} {X:AtlasData G C.S p}
variable (P:σ→StampDuty C k N p d D Q q X)
local notation "F" => C.labels.level d
abbrev quota:ℝ := (Fintype.card Signed:ℝ)⁻¹
lemma quota_pos: 0<quota:=by exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
def blendT := (quota:ℂ) • ∑ s,(P s).T
private lemma conserve {E:Type*}[AddCommGroup E][Module ℂ E](v:E): (quota:ℂ) • (∑ _ : σ,v) = v:=by
    simp only [Finset.sum_const,Finset.card_univ,quota, Complex.ofReal_inv, Complex.ofReal_natCast, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]; rw [inv_mul_cancel₀ (by exact_mod_cast (show Fintype.card Signed≠0 from Fintype.card_pos.ne')),one_smul]
private lemma conserve_R(v:ℝ):quota*(∑ _ : σ,v)= v:=by unfold quota;simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')]
local notation "XW"=> StampDuty C k N p d D Q q X
lemma ruled : ∃ Y:XW,Y.T=blendT P:=by
   let H:= blendT P;let c:ℂ:= quota; let W:= fun (x:C.label d)=> c • ∑ s,(P s).W x;let u:= c • ∑ s,(P s).heater
   let r:= (P 1).r
   have hv:‖c‖=quota:=by rw [show ‖c‖ =_ from Complex.norm_real quota,Real.norm_of_nonneg quota_pos.le]
   have he(x):u x=c • ∑ s,(P s).heater x:=by unfold u; rw [LinearMap.smul_apply,LinearMap.sum_apply]
   have hV(x):H x=c • ∑ s,(P s).T x:=by unfold H blendT; rw [LinearMap.smul_apply,LinearMap.sum_apply]
   have hX(x):Spirit (W x):=by intro u g; unfold W; simp only [text,_root_.map_smul,_root_.map_sum]; exact congr_arg (c • ·) (Finset.sum_congr rfl fun i _=> (P i).crystal x u g)
   refine ⟨⟨r,W,hX,fun x=> ?_,fun x=> ?_,u,fun x=> ?_,H,?_,?_⟩,rfl⟩
   · exact (totalDegree_smul_le ..).trans ((totalDegree_finsetSum ..).trans (Finset.sup_le fun i _=> (P i).duration x))
   · exact (peak_cost _ _ _ _ zero_le_one).trans ((mul_le_mul_of_nonneg_left ((Rise.collect _ zero_le_one ..).trans (Finset.sum_le_sum fun i _=> (P i).weight x)) (norm_nonneg _)).trans_eq (by rw [hv,conserve_R]))
   · unfold W; rw [he]; simp only [map_smul,map_sum]; exact congr_arg (c • ·) (Finset.sum_congr rfl fun i _=> (P i).head x)
   · refine ⟨⟨?_,fun x=> ?_,?_⟩,fun x=>?_,fun x=>?_,fun x=>?_⟩
     · rw [hV]; simp_rw [fun (s:Signed)=> (P s).lights.span.unit]; exact conserve _
     · rw [hV,hV]; simp_rw [(P _).lights.span.preserves]; ext1 i; simp [c]
     · intro x Γ a; rw [hV,show a-c • ∑ s,(P s).T x= c • ∑ s,(a-(P s).T x) by rw [Finset.sum_sub_distrib,smul_sub,show c • ∑ _:σ, a=a from conserve a]]
       rw [Size.smul,hv]; exact (mul_le_mul_of_nonneg_left ((Size.finite ..).trans (Finset.sum_le_sum (fun i _=> (P i).lights.span.score x))) quota_pos.le).trans_eq (conserve_R _)
     · rw [he]; exact (peak_cost _ _ _ _ zero_le_one).trans ((mul_le_mul_of_nonneg_left ((Rise.collect _ zero_le_one ..).trans (Finset.sum_le_sum fun i _=> (P i).lights.primal x)) (norm_nonneg _)).trans_eq (by rw [hv,conserve_R]))
     · rw [he]; exact (totalDegree_smul_le ..).trans ((totalDegree_finsetSum ..).trans (Finset.sup_le fun i _=> (P i).lights.order x))
     · rw [he,hV]; unfold Perch.Verdict; let m:=Beamer.features d (Subtype.val : trimV (wood A k) G → _ ) 1
       change LiftMark.level Configuration.bear d (exchange m _) = _
       have ht(s): LiftMark.level Configuration.bear d (exchange m ((P s).heater x)) = rename Sum.inl (thawKey ((F).coords.symm ((F).scaled (Price.shrink C k N p) ((P s).T x)))):= (P s).lights.test x
       simp only [thawKey,map_smul, map_sum,SetLike.val_smul,AddSubmonoidClass.coe_finsetSum]; exact congr_arg (c • ·) (Finset.sum_congr rfl fun i _=> ht i)
   intro x; have hP(s):= (P s).coupon x
   obtain ⟨hI,hF,_⟩:= hP 1; let b:= (sizeQ C k); let g:=GaugeScale C k N p
   have ht (U): signet 0 g (W x) U= c*∑ s,signet (0:Site (C.side k p)) g ((P s).W x) U:=by unfold W signet text; rw [map_smul,map_sum,smul_eq_mul]
   refine ⟨hI,⟨?_,?_,?_⟩,fun U h=>?_⟩
   · intro t V; rw [ht,ht]; exact congr_arg (c*·) (Finset.sum_congr rfl (fun i _=> (hP i).fresh.inv ..))
   · rw [funext ht]; exact Measurable.const_mul (Finset.measurable_sum _ fun i _=> (hP i).fresh.meas) c
   · intro V Z h; rw [ht,ht]; exact congr_arg (c*·) (Finset.sum_congr rfl (fun i _=> (hP i).fresh.locally _ _ h))
   let a:= nearHol C x (scouts C k) k N p U; rw [ht]
   rw [show a-c* ∑ s,signet 0 g ((P s).W x) U = c* ∑ s,(a-signet 0 g ((P s).W x) U) by rw [Finset.sum_sub_distrib, mul_sub,show c*∑ _ : σ, a=a from conserve a],norm_mul,hv]
   exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> (hP i).loss U h))) quota_pos.le).trans_eq (conserve_R _)

def emblaze (Y:Frame G d)(s:σ)(P:Module.End ℂ Y.Coeff):= mir Y s ∘ₗ P ∘ₗ mir Y s⁻¹
lemma lawOf (T:Module.End ℂ (C.label d)) (h:∀ s,(P s).T=emblaze F s T) (z:σ)(x:C.label d): blendT P (mir F z x)= mir F z (blendT P x):= by
    unfold blendT; rw [LinearMap.smul_apply,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.sum_apply,map_smul,map_sum]
    conv_lhs=> rw [← Equiv.sum_comp (Equiv.mulLeft z)]
    apply congr_arg; exact Finset.sum_congr rfl fun i _=> by
       simp only [h, emblaze, LinearMap.comp_apply]; change mir F (z*i) (T (mir F (z*i)⁻¹ (mir F z x))) = mir F z (mir F i (T (mir F i⁻¹ x))); rw [mul_inv_rev, mirrors _ (i⁻¹) (z⁻¹), show mir (F) z⁻¹ (mir F z x)=x from (by simpa only [inv_inv] using undone F z⁻¹ x), mirrors]
end YM.Next.Rank.East
