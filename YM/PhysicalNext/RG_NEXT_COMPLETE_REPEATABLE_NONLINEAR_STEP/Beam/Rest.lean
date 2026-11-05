import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Life
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Wing

/-! # Booked contribution: E6/V9 actual inheritance and high-degree strands
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
variable (ha : X.units=Equiv.refl _) (hp : I.path=R.path) (hr : I.activities.reg=R.activities.reg) (hk : I.activities.forced=R.activities.forced) {g h u : ℝ} {κ q' : Chi} {D : JointLoad.Heir.Record}

include ha hp hr hk
lemma shines (hF : Cash.Renewed ℓ a δ e J) (N : Captain J j C' d v Y A b r B q k χ) (hP : p.threshold=Pressure.temp s) (hj : p.order ≤ j) (ht : p.B=radiusB s)
    (hv : preExponent p ≤ a) (hn : p.power ≤ n) (he : preExponent p ≤ γ)
    (hX : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) (fun z=> if tired J z then N.markΦ z n else 0) a n')
    (hH : Brim.Houses J D q' κ χ g p γ h u) :
    Collection.Local (marquee H p) p (serve H X χ (lit H)) (turnFee p*(n'+(h+u))) (Cash.armK Q L μ s 0 ℓ) := by
  let T: H.fragrances → ℝ:= fun i=> N.markΦ (X.furrow i) n
  have hf i:tired H i → p.Regular (dashboard H i).support (sequence H X χ i) ∧ p.supBounds (dashboard H i).site (dashboard H i).support (sequence H X χ i) (T i) := by
    intro _; have hk := N.gloryBudget (X.furrow i) p hP hj
    have hz : (dashboard H i).support=perf J (X.furrow i):= (see H i).trans (reconnects H X i)
    rw [hz]; refine ⟨CouplingShape.reg_scale _ hk.2.1,?_⟩
    have hh:= CouplingShape.sup_scale (-1) (hk.2.2 n hn (dashboard H i).site (show (dashboard H i).site ∈ perf J (X.furrow i) from hz ▸ (dashboard H i).anchor))
    rw [abs_neg,abs_one,one_mul] at hh; exact hh
  have hb: Quotes.early p (dashboard H) (fun i=> if tired H i then T i else 0) n':= by
    intro z
    refine budget_mono (Cost.equiv X.furrow (hX z)) (fun i=> ?_) fun i=> ?_
    · dsimp only; split_ifs; rotate_left; all_goals first | exact le_rfl | simp | skip
      exact mul_nonneg (hf i (by assumption)).2.1 (Real.exp_pos _).le
    dsimp only; rw [see,reconnects H X i,ht]; split
    next hi=>
      have hu : z∈perf J (X.furrow i) := hi ▸ ((see H i).trans (reconnects H X _) ▸ (dashboard H i).anchor : (dashboard H i).site∈perf J (X.furrow i))
      rw [if_pos (show z∈Captain.reachability _ from hu)]; by_cases hh:tired H i
      · rw [if_pos hh,if_pos ((stilled X (hp:=hp) (hα:=hr) (hA:=hk) ha i).1 hh)]
        exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _))) (hf i hh).2.1
      rw [if_neg hh,zero_mul]; have hh:= (Cost.equiv X.furrow (hX z)).1 i; dsimp only at hh; rwa [if_pos (show z∈Captain.reachability _ from hu)] at hh
    exact (Cost.equiv X.furrow (hX z)).1 i
  obtain ⟨T,h,hT⟩:=estate H p χ X hr ha ht T hf hb he hH
  obtain ⟨h,hq⟩:= spiral _ _ _ (fun i=> (hT i).1) (fun i=> (hT i).2) h
  exact ⟨fun i=>(h (pennant H i)).1, qualified p H X χ _ _ hP, fun s t=> moves H p χ X s t _,⟨_,fun i=> (h (pennant H i)).2, fun o=> Cost.equiv (pennant H) (hq o)⟩, chargesOut p H X χ hF ht (show p.supportExponent+1 ≤ a by unfold preExponent at hv; linarith)⟩
end YM.PhysicalNext.Repeat.Beam
