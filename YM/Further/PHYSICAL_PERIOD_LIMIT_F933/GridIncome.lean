import YM.Next.ROTATIONS.Response
import YM.Push.COMMON_WITNESSES.Scheduler
import YM.Push.GRID_APPROXIMATION.Produce
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free


/-!
# Reuse Grid.Approx finite station supplies after reaching the corrected Seed

Enough for the particular invoice shape under *any* Risen/Rank Income,
even if starting at BOUNDARY.AtMaterials (doesn't ask for the needed
herb bounds or readiness of plots). Hold together Plate and order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Grid
open Set Function Filter Lattice Wilson Extraction Cells Table
  Next.BOUNDARY Push.Common Next.Extract Push.GridApprox
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

lemma degree {d : ℕ} (i : Flavour C d) : (herb i).1 ≤ d := by
  unfold herb Extraction.Spin.token; split <;> exact Nat.le_of_lt_succ i.1.isLt
lemma herbs {d : ℕ} (i : Flavour C d) : star (herb i).2 = (herb i).2 := by
  let v : Next.UVStress.Entitled C d := ⟨⟨i.1.val,(Pi.basisFun ℂ ((C.labels.level i.1).Index)) i.2.1⟩, Nat.le_of_lt_succ i.1.isLt,?_⟩
  · exact (Next.UVStress.encore (C:=C) v i.2.2).2
  change star ((Pi.basisFun ℂ ((C.labels.level i.1).Index)) i.2.1) = _
  ext j; by_cases h : j=i.2.1 <;> simp [h]

/-- At one h. Arity-independent. Ask on just the finite named directions
(Supplies); fill quantitative on rotated flavors before Grill. -/
lemma mix_single {d h : ℕ} (H : C.Makes) (T : MixAt C f d h) (l : ℕ) : ∃ R : ℝ, 0≤R ∧ Prox C f d h l R := by
  obtain ⟨Z,-,hZ⟩ := figures_all H T
  let Y (i : Flavour C d) := palette (Z (herb i).1 (degree i)) (herb i).snd
  have hp i : (Y i).Gives f := hZ _ _ _ (herbs i)
  choose q hq using fun i : Flavour C d => Metric.tendsto_atTop.mp (hp i).cost (toll l) (toll_pos l)
  let R := ∑ i : Flavour C d,(Y i).cap (q i)
  have hh i := (hp i).cap_pos (q i)
  refine ⟨R, Finset.sum_nonneg (fun i _ => (hh i).le),?_⟩
  unfold Prox
  have hΩ : ∀ᶠ j : ℕ×ℕ in f.fuse, ∀ i : Flavour C d, PictureAt C (herb i) h j.1 j.2 ((Y i).plot (q i) j.1 j.2)
      ((Y i).cap (q i)) ((Y i).err (q i)) ((Y i).radius (q i)) :=
    eventually_all.mpr (fun i => (hp i).late (q i))
  change ∀ᶠ j : ℕ×ℕ in f.fuse, ∃ hN : h ≤ j.1, ∀ i : Flavour C d, ∃ P, DirectedField hN i (p:=j.2) P R (toll l)
  filter_upwards [hΩ,Next.UVStress.large_mesh f h] with j hj hk
  refine ⟨hk,fun i => ⟨_,(hj i).target,fun x => (hj i).bound x|>.trans ?_, (hj i).real, (hj i).cost.trans ?_⟩⟩
  · exact Finset.single_le_sum (fun i _ => (hh i).le) (Finset.mem_univ _)
  apply le_trans (by exact Real.le_norm_self _) (show ‖(Y i).err (q i)‖ ≤ toll l from ?_)
  simpa [dist_zero_right] using (hq i (q i) (le_refl _)).le

lemma supplies (T : AtMaterials C f S) (p : Extraction.Order) (H : Spec.Seed C (f.refine p) S) : Study C (f.refine p) := by
  rintro ⟨d,m⟩ u
  have hu := keep_seed H u
  obtain ⟨h,hh,q,hq⟩ := T (p.refine u) hu d m
  refine ⟨q,h,hh,?_⟩
  intro i g
  obtain ⟨R,hr,hR⟩ := mix_single H.cutoff hq i
  exact ⟨Extraction.Order.full,R,hr,hR.upon (Tails.refine (f.refine ((p.refine u).refine q)) g)⟩

/-- Application even at `rank` bills not produced by our source factory. -/
lemma ready {b : Presentation C} {p : Push.Common.Snap C} {u : Push.Common.Snap.Upper p}
    (T : AtMaterials C f u.T) (g : Extraction.Order) (r : Risen u b (f.refine g)) (D : Holder u.T) (H : D.Income b (f.refine g)) :
    GrillInputs C (f.refine g) :=
  studying r.first.center r.first.family (supplies T g (r.base.seed (Push.Common.valid_offers (C:=C) (X:=D.X) H)))
end YM.Further.PhysicalPeriodLimitF933.Grid
