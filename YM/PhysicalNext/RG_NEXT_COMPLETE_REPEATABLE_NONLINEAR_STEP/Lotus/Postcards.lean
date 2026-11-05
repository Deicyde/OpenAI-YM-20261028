import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Matter
import YM.Further.DENSE_MIXED_KERNELS.Compliance

/-!
 # Source markers in the ACTUAL paid unmarked Oxford/Arthur calendar
 Value supplier with lower tech. No conditional promises.
 Keep single address; regular source uses same unused letter address from
 the recipe, exact original E untouched (at occupancy witness). K address may
 even have nonzero vacuum coefficient on same K. Raw integral numerator.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
  -- open Connected separately
open ConnectedActivityE6 Mask Contract Work.F03 Presented  Sector Footprint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {W a r σ E Λ μ x κ w C : ℝ}
-- R absolute input data. Tag.E payload here AFTER masking. Stage.T read.
inductive Wing | logKey (i:ℕ) | gasKey (i:ℕ) deriving DecidableEq
namespace Wing
variable (i:Wing)
def support : Wing→ (R : Rep G f)→ Support f
 | .logKey i,R => (R.activities.reg i).support
 | .gasKey i,R=> (R.activities.forced i).support

def Occupied : Wing→ Finset ℕ→ Prop
 | .logKey _,_=>True
 | .gasKey i,k=>i∈k
def remaining : Wing→ Finset ℕ→ Finset ℕ
 | .logKey _,k=>k
 | .gasKey i,k=>k.erase i

def qualifies : Wing→ (R : Rep G f)→Config G f→Prop
 | .logKey i,R,U=> Healthy R.p.threshold (R.activities.reg i).support U
 | .gasKey i,R,U=> (R.activities.forced i).eligible R.p.threshold U

def blank : Wing→(R:Rep G f)→Prop
 | .logKey i,R=> R.activities.E i=0
 | .gasKey _,_=>True

def badge : Wing→ (S : StepData c f)→ Head S
 | .gasKey i,_ => .inr (.inl i)
 | .logKey i,_=> .inr (.inr (.inl (.inl (.inl i))))


lemma badge_area (R : Rep G f) (T : Tube G S) (l B : ℕ) : Matter.areas R T l B (i.badge S)=enlargement S.ratio l B (RG.inspected (i.support R)):=by cases i <;> rfl
end Wing

structure Leaf (R : Rep G f) where
  turn : Wing
  ingredient : Config G f→ℝ
  scopedR : UsesFinal R.p.threshold (turn.support R) ingredient
  grant : ∀ U, ingredient U≠0→ turn.qualifies R U
  blank : turn.blank R
  weight : ℝ
  earn : ∀ V, ‖ingredient V‖≤weight
  glows : GaugeInvariant ingredient
  borel : Measurable ingredient

namespace Leaf
variable (M : Leaf R)
abbrev crest:= M.turn.support R
lemma specific : LocalOn (RG.inspected M.crest) M.ingredient:=UsesFinal.allReads _ _ _ M.scopedR 

lemma profit : 0≤M.weight:=(norm_nonneg _).trans (M.earn 1)
-- Marker coefficient at b.True vertices. multiplies real payload; K requires actual same masks at input.
def bill (k : Finset ℕ) (U : Config G f) := if M.turn.Occupied k then M.ingredient U * ∏ i∈M.turn.remaining k, R.activities.K i U else 0

def bun (k : Finset ℕ) (U : Config G f) := if R.activities.admissible R.p U k then M.bill k U else 0

def cicada (U: Config G f):ℝ := Real.exp (R.exponent U)*(∑' k,M.bun k U)

lemma proud (h: R.Lawful σ C Λ x w) (k : Finset ℕ) : Measurable (M.bun k) := by
  unfold bun; apply Measurable.ite (R.activities.admissible_borel R.p k) _ measurable_const
  unfold bill; by_cases hp:M.turn.Occupied k
  · simp_rw [if_pos hp]; exact M.borel.mul (Finset.measurable_fun_prod _ fun i _=> h.labels.forced.meas i)
  simp_rw [if_neg hp]; exact measurable_const


lemma bud (h: R.Lawful σ C Λ x w) : Dominated M.bun := by
  obtain ⟨b,hB,h⟩:= R.activities.K_total h.labels.boundK
  obtain hh:(∀ i:ℕ,0≤b i):=fun i=>(h i).1
  cases hi:M.turn with
  | logKey i=>
    refine ⟨_,(summable_finsetProd_of_summable_nonneg hh hB).mul_left M.weight,fun k U=>?_⟩
    unfold bun; split
    · unfold bill; simp only [hi,Wing.Occupied,Wing.remaining, if_true,norm_mul,norm_prod]; exact mul_le_mul (M.earn _) (prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> (h i).2 _)) (prod_nonneg fun _ _=> norm_nonneg _) M.profit
    rw [norm_zero]; exact mul_nonneg M.profit (prod_nonneg fun i _=> hh i)
  | gasKey i=>
    let e := fun j=> if j=i then M.weight else b j
    have hz j:0≤e j:=by unfold e; split; exact M.profit; exact hh _
    have he: Summable e := (summable_congr_cofinite (f:=b) (g:=e) ?_).mp hB
    · refine ⟨_,summable_finsetProd_of_summable_nonneg hz he,fun k U=>?_⟩
      by_cases h₃:i∈k
      · unfold bun; split
        · unfold bill; simp only [hi,Wing.Occupied,h₃,Wing.remaining,if_true,norm_mul,norm_prod]
          rw [← mul_prod_erase _ _ h₃]; apply mul_le_mul (show ‖M.ingredient U‖≤e i by simpa [e] using M.earn U) (prod_le_prod (fun i _=> norm_nonneg _) (fun j hj => by simpa only [e,if_neg (ne_of_mem_erase hj)] using (h j).2 U)) (prod_nonneg fun i _=> norm_nonneg _) (hz i)
        rw [norm_zero]; exact prod_nonneg fun i _=> hz i
      have hc : M.bun k U=0:=by simp [bun,bill,hi,Wing.Occupied,h₃]
      rw [hc,norm_zero]; exact prod_nonneg fun i _=> hz i
    filter_upwards [((Set.finite_singleton i).compl_mem_cofinite)] with j hj using by rw [show e j=b j from if_neg hj]

lemma sells (h: R.Lawful σ C Λ x w) : Envelope M.cicada ∧ GaugeInvariant M.cicada:=by
  have hb:Envelope (fun U=>∑' k,M.bun k U):= ⟨Measurable.tsum (M.proud h),(M.bud h).bound⟩
  refine ⟨(R.exponentEnv h|>.exp).mul hb,fun t U=>?_⟩; unfold cicada
  rw [Further.DenseMixedKernels.Throng.phase h t U]
  exact congr_arg (Real.exp (R.exponent U)*·) (tsum_congr fun i=> (by simp only [bun,bill,M.glows t U,h.labels.forced.sym _ t U, Activities.admissible,gauge_flags]))

lemma counted (h : R.Lawful σ C Λ x w) (k : Finset ℕ) (U : Config G f) (ht : Contract.sealed R k) : M.bun k U=Contract.order R k univ U*M.bill k U:=by
  unfold bun; split
  next hp =>
    have hq : Contract.order R k univ U=1:=by
      apply prod_eq_one; intro i _; unfold Contract.charges; apply if_neg
      rintro ⟨h₁,h₂⟩; apply h₁; rw [←hp.2] at h₂; obtain ⟨a,ha,hb⟩:= mem_biUnion.mp h₂; exact mem_biUnion.mpr ⟨a,ha,(R.activities.forced a).inventory_sup hb⟩
    rw [hq,one_mul]
  next hz=>
    by_contra! h'
    have he:=left_ne_zero_of_mul (Ne.symm h'); have hp:=right_ne_zero_of_mul (Ne.symm h')
    unfold bill at hp; split at hp
    swap; · exact hp rfl
    next hκ=>
    have hF (j:ℕ) (hj:j∈k) : (R.activities.forced j).eligible R.p.threshold U:=by
      by_cases hi:j∈M.turn.remaining k
      · exact h.labels.forced.permit j U fun hn=> right_ne_zero_of_mul hp (prod_eq_zero hi hn)
      have h:=M.grant U (left_ne_zero_of_mul hp)
      cases ha:M.turn with
      | logKey u=> exact (hi (by simpa only [ha,Wing.remaining] using hj)).elim
      | gasKey a=>
        apply (show a=j from ?_) ▸ (ha ▸ h : Wing.qualifies (Wing.gasKey a) R U)
        exact by_contra fun hx=> hi (by rw [ha,Wing.remaining]; exact mem_erase.mpr ⟨Ne.symm hx,hj⟩)
    refine hz ⟨ht,?_⟩; ext i; constructor
    · intro hi; obtain ⟨v,hv,hj⟩:= mem_biUnion.mp hi; exact (mem_inter.mp ((hF v hv).1.symm ▸ hj : i∈(R.activities.forced v).support∩RG.flags R.p.threshold U)).2
    intro hi
    have hs:i∈ covered R k:= by by_contra hn; exact he (prod_eq_zero (mem_univ _) (show charges R k U i=0 from if_pos ⟨hn,hi⟩))
    obtain ⟨v,hv,hj⟩:=mem_biUnion.mp hs; exact mem_biUnion.mpr ⟨v,hv,(hF v hv).1 ▸ mem_inter.mpr ⟨hj,hi⟩⟩
end Leaf
end YM.PhysicalNext.Repeat.Lotus
