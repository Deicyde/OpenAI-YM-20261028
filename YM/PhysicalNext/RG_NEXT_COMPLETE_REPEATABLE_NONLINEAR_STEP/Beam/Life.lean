import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.FromWords
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Docket
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Level
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Skills

/-!
# Paid inherited-vs-high sectors on authenticated birthdays. Keep their
 ORIGINAL E values (no registration of extra compansion in K for these).
 For others Lai only. α_Lift remains outside until complete stencil budget.
 `Local` here is on **full canopy**, nothing erased inside it.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Beam
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    (H : Cash W s μ L Q o α T I) (p : BudgetPoint) {J : Cash W s μ L Q o α T R} (χ : Chi)
    (X : Alliance H J 1 0)

section money
-- suppose f spills across g. (Nonnegative actual occupancy only.)
lemma wallet {ι κ : Type} (e : ι↪κ) {f : κ→ℝ} (hf : SumBudget (fun i=> f (e i)) γ) (h : ∀ b : κ, b∉Set.range e → f b=0) : SumBudget f γ := by
  have hh k : 0≤f k := by
    by_cases he:k∈ Set.range e
    · obtain ⟨w,rfl⟩:=he; exact hf.1 w
    exact (h k he).ge
  refine budget_of_sum hh fun S=> ?_
  let U:= S.filter (·∈ Set.range e)
  let V:= U.preimage e e.injective.injOn
  have hU : U= V.map e:= by
    ext k; constructor <;> intro he
    · obtain ⟨i,hi⟩:= (Finset.mem_filter.mp he).2; subst k; apply Finset.mem_map.mpr; exact ⟨_,Finset.mem_preimage.mpr he,rfl⟩
    obtain ⟨i,hi,rfl⟩:= Finset.mem_map.mp he; exact Finset.mem_preimage.mp hi
  have hs : S.sum f= U.sum f := Eq.symm (Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hk=> h _ fun hv=> hk (mem_filter.mpr ⟨hi,hv⟩)))
  rw [hs,hU,Finset.sum_map]; exact budget_sum hf V

variable {β β' : ℝ} (hf : I.path=R.path) (hg : I.activities.reg=R.activities.reg) (hc : I.activities.forced=R.activities.forced) (hv : X.units=Equiv.refl _) (ht : p.B=radiusB s)
variable {κ q' : Chi} {g h K : ℝ} {D : JointLoad.Heir.Record}

def lit (t : H.fragrances) := tired H t ∨ t∈ Set.range (icon H)
lemma plates (he : I.activities.reg=R.activities.reg) (i : ℕ) : Brim.plate H i=Brim.plate J i:= by unfold Brim.plate; rw [he]
lemma shall (i : ℕ) (h : ¬tired H (icon H i)) : coverNumber (radiusB s) (H.unionP (Brim.head i))≤ radiusB s := by
  have he : depth H (icon H i)<Pressure.Stores.till s := lt_of_not_ge (fun ht=> h (Or.inr (Or.inr ht)))
  have hv : depth H (icon H i)= H.shapeW (Brim.head i):= by simp [depth,icon,once]
  rw [hv] at he
  have hx: Ac.Spark H.supportP (Brim.head i):= by
    unfold Brim.head; refine ⟨singleton_nonempty _, fun i hi j hj=>?_⟩; rw [mem_singleton.mp hi,mem_singleton.mp hj]; exact .refl
  have hk:= ((shaped (H:=H) (Brim.head i) hx).trans he.le).trans (show (Pressure.Stores.till s:ℝ) ≤ radiusB s from by exact_mod_cast Nat.div_le_self ..)
  exact_mod_cast hk
include ht hf hc hv hg
omit hf hc in
lemma estate (U : H.fragrances → ℝ) (W : ∀ i, tired H i → p.Regular (dashboard H i).support (sequence H X χ i) ∧ p.supBounds (dashboard H i).site (dashboard H i).support (sequence H X χ i) (U i))
    (hH : Quotes.early p (dashboard H) (fun i=> if tired H i then U i else 0) β) (ha : preExponent p ≤ γ) (hP : Brim.Houses J D q' κ χ g p γ h K) :
    ∃ f, Quotes.early p (contents H p) f (β+(h+K)) ∧ ∀ i, p.Regular (contents H p i).support (skilled H X χ (lit H) i) ∧ p.supBounds (contents H p i).site (contents H p i).support (skilled H X χ (lit H) i) (f i) := by
  obtain ⟨⟨v,hv,Hv⟩,s,Hs,hs⟩:= hP -- shadows
  let w j := v j+s j; let e' : ℕ ↪ H.fragrances:= ⟨icon H,icon_inj H⟩; let f z:= extend e' w 0 z
  let u z:= if tired H z then U z else if z∈ Set.range e' then f z else 0
  let c:= Sum.elim u (fun _ : Songbook c=>0)
  have hy i: p.Regular (contents H p i).support (skilled H X χ (lit H) i) ∧ p.supBounds (contents H p i).site (contents H p i).support (skilled H X χ (lit H) i) (c i) := by
    have he i (h : ¬chosen H (lit H) i) (ht : c i=0): p.Regular (contents H p i).support (skilled H X χ (lit H) i) ∧ p.supBounds (contents H p i).site (contents H p i).support (skilled H X χ (lit H) i) (c i) := by
      rw [pivot H X χ (lit H) 0,if_neg h,ht]; refine ⟨CouplingShape.reg_const _,?_⟩
      simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (o:=(contents H p i).site) (X:=(contents H p i).support) 0)
    rcases i with i|i
    swap; · exact he _ (fun h=> h) rfl
    by_cases ht':tired H i
    · have h : chosen H (lit H) (.inl i):= Or.inl ht'
      rw [Height.pivot H X χ (lit H) 0, if_pos h,show c (.inl i)=_ from (if_pos ht' : u i = _)]; exact W i ht'
    by_cases hk: i∈Set.range e'
    swap; · have hh : ¬chosen H (lit H) (.inl i):=not_or.mpr ⟨ht',hk⟩
            apply he _ hh; change u i= _; unfold u; rw [if_neg ht',if_neg hk]
    obtain ⟨j,rfl⟩:= hk
    rw [Height.pivot H X χ (lit H) 0,if_pos (show chosen H (lit H) (.inl (e' j)) from Or.inr (show e' j ∈ Set.range e' from ⟨j,rfl⟩)), show c (.inl (e' j))=w j from
      (by change u _= w _; unfold u f; rw [if_neg ht',if_pos (Set.mem_range_self (f:=e') j),e'.injective.extend_apply]), show contents H p (.inl (e' j))=Brim.plate J j from (impact H j).trans (plates H hg j),
      show opus H X χ 0 (Sum.inl (e' j))=announced J D q' κ g j-glyph J D q' κ χ g j from (by
        ext V; change (-1:ℝ) * stream J χ V (X.furrow (icon H j))=announced J D q' κ g j V- (stream J χ V (icon J j)+_); rw [mimics H X (by assumption)]
        ring)]
    have hd := shall H j ht'; rw [← ht,concern H,plates H (J:=J) hg] at hd
    exact ⟨CouplingShape.reg_sub (hv j).1 (hs j).1, CouplingShape.sup_sub (hv j).1 (hs j).1 (hv j).2 ((hs j).2 hd)⟩
  refine ⟨c, fun x=> ?_,hy⟩; rw [← add_zero (β+(h+K))]
  suffices hh : SumBudget (fun i=>if (dashboard H i).site=x then u i*Real.exp (preExponent p*coverNumber p.B (dashboard H i).support) else 0) (β+(h+K)) from Cost.sum hh (by simp [c,SumBudget])
  let Z i:= if (dashboard H i).site=x then u i*Real.exp (preExponent p*coverNumber p.B (dashboard H i).support) else 0
  let A i:= if tired H i then Z i else 0
  let B i:= if tired H i then 0 else Z i
  have hz i : Z i=A i+B i := by by_cases hi:tired H i <;> simp [A,B,hi]
  change SumBudget Z _; rw [funext hz]
  have hh: SumBudget A β:= by
    refine budget_mono (hH x) ?_ ?_
    · intro i; unfold A Z; split_ifs <;> first| exact le_rfl| exact mul_nonneg (hy (.inl i)).2.1 (Real.exp_pos _).le
    intro i; unfold A Z u; dsimp only; split_ifs <;> simp
  apply budget_plus hh
  apply wallet e'
  · refine budget_mono (budget_plus (Hv x) (Hs x)) (fun i=> ?_) (fun i=>?_)
    · unfold B Z; split_ifs <;> first| exact le_rfl| exact mul_nonneg (hy (.inl (e' i))).2.1 (Real.exp_pos _).le
    · by_cases ht':tired H (e' i)
      · rw [show B (e' i)=0 from if_pos ht']; exact (budget_plus (Hv x) (Hs x)).1 i
      unfold B Z; rw [if_neg ht', show dashboard H (e' i)=Brim.plate J i from (impact H i).trans (plates H hg i)]
      split
      next hi => dsimp only; refine le_trans (b:=u _*Real.exp (γ*coverNumber p.B (Brim.plate J i).support)) (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (hy (.inl _)).2.1) ?_
                 unfold u f w; rw [if_neg ht', if_pos (Set.mem_range_self (f:=e') i),e'.injective.extend_apply,add_mul]
      simp
  intro b hb; unfold B Z u; split_ifs <;> simp [*]
end money
end YM.PhysicalNext.Repeat.Beam
