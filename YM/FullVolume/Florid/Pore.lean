import YM.FullVolume.Florid.HeatR
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
open Crew Lotus -- edit
lemma awake (V:Mill U)(r:ℝ)(hr:0 < r)(hp:Daisy.foam Q L)(hv:R.p.B≤2*Pressure.radiusB x₀)
   (h: r * jewelDebt V.pole (stella Q) L x₀ ≤ 1) : Pave (fun _:Unit=>V) (fun _=>r):=by
   have ht:= scentL V.pole H; let f:= Crew.extra (fun _:Unit=>V) (fun _=>r)
   have hu:= sustainsL V.pole H hp hv; let g:= colly (n:=c) (fun _=>0) V.pole (stella Q) L x₀
   have he i:0 ≤ f i ∧ f i ≤ g i := by
       unfold f Crew.extra Merge.Tickets.extra; simp only [Fintype.sum_unique]; unfold g colly
       change 0≤ (if sparkling c _ (V.pole).turn=i then r * _ else 0) ∧ _
       by_cases hx:sparkling c _ (V.pole).turn=i
       · rw [if_pos hx,if_pos hx.symm,if_pos (show Merge.Palette.mark (faces fun _:Unit=>V) default=i from hx)]
         refine ⟨mul_nonneg hr.le V.pole.profit,?_⟩; change r * V.pole.weight ≤ _; rw [ht.2.2, ← mul_assoc]; exact mul_le_of_le_one_left ht.1.le h
       have hz : ¬Merge.Palette.mark (faces fun _:Unit=> V) default=i:= hx
       rw [if_neg hx]; simp_rw [if_neg hz,if_neg (Ne.symm hx)];exact ⟨le_rfl,le_rfl⟩
   refine ⟨fun _=>hr.le,fun i=>budget_mono (hu i) (fun j=>?_ ) fun j=>?_⟩
   · split;next=> exact mul_nonneg (mul_nonneg (he _|>.1) (Real.exp_nonneg _)) (Real.exp_nonneg _)
     next=>rfl
   split;next=> exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he _|>.2) (Real.exp_nonneg _)) (Real.exp_nonneg _)
   next=> rfl
end YM.ConnectedActivityE6.Empire.Imago
