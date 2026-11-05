import YM.Pert.Lattice.Action
import YM.LocalH.Haar
import YM.Primitives.HAAR_LOG_JETS.Differential
/-! Independent Haar factors on the inversion regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Filter LocalH
open scoped Topology ContDiff
variable {G : Gauge} {n : Side}
def serial (l : Orb.Links n) := Fintype.equivFin (Orb.Links n) l
def positive (n : Side) := Finset.univ.filter fun l : Orb.Links n => serial l < serial (image l)
@[simp] lemma mem_positive {l : Orb.Links n} : l ∈ positive n ↔ serial l < serial (image l) := by simp only [positive,Finset.mem_filter,Finset.mem_univ,true_and]
lemma switches (l : Orb.Links n) (hn : Admissible n) : image l ∈ positive n ↔ l ∉ positive n := by
  simp only [mem_positive,image_image]
  have hne : serial (image l) ≠ serial l := ((Fintype.equivFin (Orb.Links n)).injective.ne (image_ne_self hn l))
  exact ⟨LT.lt.not_gt, fun h => lt_of_le_of_ne (not_lt.mp h) hne⟩

def Jacob (a : Potential G n) := ∏ l ∈ positive n, spin G (a.val l)
def RatioAgree (a : Precision.ChartRatio G) := (∀ᶠ x in 𝓝 0, a.J x = spin G x)
lemma haar_prod_match (a : Precision.ChartRatio G) (ha : RatioAgree a) :
    Jacob (G:=G) (n:=n) =ᶠ[𝓝 0] fun P : Potential G n => ∏ l ∈ positive n, a.J (P.val l) := by
  refine Filter.Eventually.mono (p:=fun (P : Potential G n) => ∀ l : Orb.Links n, a.J (P.val l)=spin G (P.val l)) ?_ (fun P H => Finset.prod_congr rfl fun l _ => (H l).symm)
  apply Filter.eventually_all.mpr; intro l
  exact ((takeLink (G:=G) l).toContinuousLinearMap.continuous.continuousAt (x:=0)).tendsto.eventually ha
lemma exists_haar : ∃ a : Precision.ChartRatio G, Precision.LocalRatio a ∧ RatioAgree a := by
  obtain ⟨a,ha⟩ := LocalH.actual G
  have e : ∀ᶠ x in 𝓝 0, a.J x = |spin G x| := Filter.mem_of_superset (Metric.ball_mem_nhds _ ha.patch) fun x hx => Next.SectorChange.contracted ha hx
  have h : ContinuousAt (spin G) 0 := (spin_deriv G 0).continuousAt
  refine ⟨a,ha, ((h.eventually_mem (Ioi_mem_nhds (by simp [spin_zero] : 0 < spin G 0))).and e).mono fun x h => h.2.trans (abs_of_pos h.1)⟩
lemma spin_diff : ContDiffAt ℝ ω (spin G) 0 := by
  obtain ⟨a,h,hg⟩ := exists_haar (G:=G)
  exact (h.germ 0 (Metric.mem_ball_self h.patch)).congr_of_eventuallyEq (hg.mono fun x h => h.symm)
lemma jacobian_smooth : ContDiffAt ℝ ω (Jacob (G:=G) (n:=n)) 0 := by
  unfold Jacob; refine contDiffAt_prod (fun l _ => ?_)
  exact spin_diff.comp (f:=takeLink l) (0:Potential G n) ((takeLink l).toContinuousLinearMap.contDiff.contDiffAt)
@[simp] lemma jacobian_flat : Jacob (0 : Potential G n)=1 := by unfold Jacob; simpa only [Submodule.coe_zero,Pi.zero_apply,spin_zero,Finset.prod_const_one]
end YM.Pert.Orb
