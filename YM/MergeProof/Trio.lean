import YM.MergeProof.Lakes



set_option autoImplicit false
noncomputable section
namespace YM.Merge.Palette
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι] {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(Y:Cash W x μ L Q o C T R) (χ:Chi)
local notation "sx"=> radiusB x
open Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable (rA:ι→ℝ)
variable (i:ι) (U:Config G c)
omit [Fintype ι] in
lemma monoAct (p:Molecule S) : act M Y χ U p (Tickets.mono _ i)= (M i).lotus T x χ o.K W o.a Q.table Q.halo U p:=by
  let Z:= team M (Tickets.mono (sign M S) i);have hv: Z.own={M i}:= by simp [Z,team,Tickets.mono]
  have hp {F:Forest S.ratio}(X:Coat T F): Z.into X W o.a Q.table (own p) Q.halo p = (M i).into X W o.a Q.table (own p) Q.halo p:=by
    funext z; unfold Team.into Team.premium Team.paidU Team.signs Leaf.into Leaf.premium
    simp [hv]; rw [← Finset.sdiff_singleton_eq_erase]
  refine congr_arg likely (funext fun j=>?_); let X:= prism T x χ o.K U (allot j)
  change Z.bloom X W o.a Q.table Q.halo p=(M i).bloom X W o.a Q.table Q.halo p
  unfold Team.bloom Leaf.bloom;split;· exact congr_arg likely (funext fun j=>by unfold Team.tithe Leaf.tithe; rw [hp])
  rfl
lemma active (t:ℝ) : color M Y χ U (ways rA t {i})= Daisy.Charity.color (M i) Y χ U (rA i*t):=by -- charity?
  ext a; let w:=sign M S; unfold color Daisy.Charity.color; rw [← add_sum_erase _ _ (mem_univ (Tickets.none w))];simp only [amplitudes]; rw [quiet]; simp only [Tickets.none,prod_empty,Switch.click,empty_subset,if_true,card_empty,pow_zero,one_mul]; congr 1
  rw [sum_eq_single (Tickets.mono w i), monoAct]; simp [Tickets.mono,mul_comm]
  · intro b hb ht; have he:b≠Tickets.none _:=ne_of_mem_erase hb
    have hx: ¬ b.val⊆{i}:=by intro hz; rcases Finset.subset_singleton_iff.mp hz with hz|hz;exact he (Subtype.ext hz); exact ht (Subtype.ext hz)
    rw [if_neg hx,zero_mul]
  intro hn; apply False.elim; apply hn; refine mem_erase.mpr ⟨fun h=> singleton_ne_empty i (congr_arg Subtype.val h),mem_univ _⟩
open Switch Daisy.Charity
omit [Fintype ι] in
lemma offWays (t:ℝ): ways rA t ∅=fun _=> 0:=by ext; simp [ways]
variable {e a z q t A₁ B v:ℝ} {l : ℕ}

end YM.Merge.Palette
