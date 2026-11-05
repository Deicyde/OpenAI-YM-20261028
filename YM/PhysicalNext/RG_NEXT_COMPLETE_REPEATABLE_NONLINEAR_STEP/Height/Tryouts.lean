import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Paps

/-!
# Surviving E reading in year, exact reduction

Species that remain in the unforced wall paper have no compulsory
 packet and NO K (even as an inherited unmasked letter). Still can read
 external flags. No truncation claim about chain LENGTH of a leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Precision Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Time Song
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ}
    {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R}

structure Solo (p : J.ThinP) : Prop where
  connected : Ac.Spark J.supportP p.val
  shares : 1 ≤ p.val.card ∧ p.val.card ≤ 2
  unseeded : p.val.toLeft=∅
  oneK : own p.val = ∅
-- inappropriate species are zero as unmasked extensions, not just once masked.
def trio (J : Cash W s μ L Q o α T R) (i : J.fragrances) := ¬ veteran J i ∧ i.fst≤1 ∧ ∀ j,Solo (i.2 j)

lemma solo_cost (p : J.ThinP) (h : Ac.Spark J.supportP p.val) (hp : troupe T R Q.halo (radiusB s) p.val) (hz : p.val.card ≤ 2) (hu : Cash.numP p.val < 1) : Solo p := by
  have he : p.val.toLeft= ∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨i,hi⟩=> by
    have hx : 1 ≤ i.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hp.1.checkpoints i hi).1
    exact (Nat.not_lt.mpr (hx.trans (show i.shares≤Cash.numP p.val from Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hi)))) hu
  refine ⟨h,⟨Finset.card_pos.mpr h.1,hz⟩,he,Finset.not_nonempty_iff_eq_empty.mp ?_⟩
  rintro ⟨i,hi⟩; obtain ⟨j,hj⟩ := (R.activities.forced i).inventory_ne; obtain ⟨z,hy,hv⟩:=hp.2.2 _ hi _ hj
  unfold roster Packets.store at hy; rw [he] at hy; simp at hy

open Stained Shield
lemma vacuity {F : Tree.Forest S.ratio} {χ : Chi} (V) (p : J.ThinP) (h : ¬(Ac.Spark J.supportP p.val ∧ troupe T R Q.halo (radiusB s) p.val)) :
    fringe (prism T s χ o.K V F) W o.a p.val R Q.table Q.halo=0 := by
  unfold fringe; let X:=prism T s χ o.K V F
  have ht (z) : shelter (X.rinse z) W o.a p.val R Q.table Q.halo=0:= if_neg h
  change (∫ z,shelter (X.rinse z) W o.a p.val R Q.table Q.halo ∂ _)=_; simp_rw [ht]; exact integral_zero ..
lemma excited (χ : Chi) (p : J.fragrances) (hu : ¬veteran J p) (V) (he : stream J χ V p≠0) : trio J p := by
  have hh i : leaflet J χ V (p.2 i) ≠ 0:= fun h=> he (by unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) h,mul_zero,zero_div])
  have hp i : Solo (p.2 i) := by
    have hv: Ac.Spark J.supportP (p.2 i).val ∧ troupe T R Q.halo (radiusB s) (p.2 i).val := by
      by_contra h; apply hh i; unfold leaflet likely; simp_rw [vacuity V (p.2 i) h,sum_const_zero,mul_zero]
    have ha := not_or.mp hu
    have hz : breadth J p≤2:=Nat.le_of_lt_succ (lt_of_not_ge ha.1)
    exact solo_cost (p.2 i) hv.1 hv.2 ((single_le_sum (f:=fun j=> (p.2 j).val.card) (fun i _=> Nat.zero_le _) (mem_univ i)).trans hz)
      (lt_of_le_of_lt (single_le_sum (f:=fun j=> Cash.numP (p.2 j).val) (fun i _=> Nat.zero_le _) (mem_univ i)) (lt_of_not_ge ha.2))
  refine ⟨hu,?_,hp⟩
  have hh': 3>breadth J p:= lt_of_not_ge (not_or.mp hu).1
  have hU : p.fst+1 ≤ breadth J p := by
    refine le_trans ?_ (Finset.sum_le_sum (s:=univ) (fun i _ => (hp i).shares.1)); simp
  omega

section solution
variable (p : BudgetPoint) (X : Alliance H J 1 0) (χ : Chi) (γ : ℝ)



lemma pieces (i : ℕ) (U : Config G c) :
    let k:=posting p H; let X':=plusone H X χ γ; let A:=retain H X χ; let B:=rest H X χ γ
    (k.read A).regularOccurrence p i U+(k.read B).regularOccurrence p i U=(k.read X').regularOccurrence p i U := by
  intro k X' A B
  let F (g:Collection.Source G c):=(k.read g).regularOccurrence p i U
  let P:= (k.reg i).support
  have hG g : F g=masked p.threshold P (g.logRead i) U := rfl
  obtain ⟨he,hk⟩:= shade H X χ γ i
  have h : masked p.threshold P (0:Config G c→ℝ) U=0:= by by_cases he:Healthy p.threshold P U; exact masked_eq _ _ _ _ he; exact masked_ne _ _ _ _ he
  change F A+F B= F X'; unfold A B X'; rw [hG,hG,hG,he,hk]; split <;> simp [h]

end solution
end YM.PhysicalNext.Repeat.Height
