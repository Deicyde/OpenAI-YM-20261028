import YM.Extra.WILSON_STARTUP.Ownership

/-! # Full signed average split of the Wilson action -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter Tensor RG Wilson Lattice Design Work
open scoped Classical Matrix.Norms.Frobenius BigOperators Topology
variable {G : Gauge} {n : Side} (c : Clip) (b : BudgetPoint)

lemma translate_face (x : Site n) (p : Cell n) (U : Config G n) :
    faceValue (pull 1 x U) p = faceValue U (p.1+x,p.2) := by
  unfold faceValue; rw [travel_pull]; simp [affine]

lemma translate_test (x : Site n) (z : Site n) (U : Config G n) :
    PathData.kept c b.threshold z (pull 1 x U) ↔ PathData.kept c b.threshold (z+x) U := by
  constructor
  · intro h p
    have he := h (p.1-x,p.2)
    rw [translate_face] at he
    simpa [← separation_translate z (p.1-x) x] using he
  intro h p
  rw [translate_face]; simpa using h (p.1+x,p.2)

lemma translate_health (x : Site n) (p : Cell n) (t : ℝ) (U : Config G n) :
    Healthy t (touched p) (pull 1 x U) ↔ Healthy t (touched (p.1+x,p.2)) U := by
  rw [Healthy, Healthy, show touched (p.1+x,p.2) = (touched p).image (affine 1 x) from ?_,
    ← H03.flags_send 1 x t U, Finset.disjoint_image (aff_inj ..)]
  simp [four_visit,affine,add_right_comm]

def Key.shift (s : Signed) : Cell n ≃ Cell n :=
    Equiv.prodCongr (frameSites s 0) (Equiv.refl PlaqAxes)

def Key.shifted (s : Signed) (p : Cell n) : Key n := (s,Key.shift s p)

theorem Key.shift_frame (s : Signed) (p : Cell n) (U : Config G n) :
    (shifted s p).frame U = pull 1 p.1 (pull s 0 U) := by
  rw [pull_pull, mul_one]; rfl

theorem Key.shift_mask (i : Cell n) (s : Signed) (U : Config G n) (t : ℝ) :
    masked t (shifted s i).skin (shifted s i).accrual U = masked t (touched i) (residual G i) (pull s 0 U) := by
  have hh : Healthy t (shifted s i).skin U ↔ Healthy t (touched i) (pull s 0 U) := by
    rw [spins_healthy, shift_frame, translate_health]
    change Healthy t (touched ((0:Site n)+_,i.2)) _ ↔ _; simp
  by_cases hU : Healthy t (touched i) (pull s 0 U)
  · rw [masked_eq _ _ _ _ (hh.mpr hU), masked_eq _ _ _ _ hU, accrual, shift_frame, residual,
      translate_face, residual, show ((shifted s i).root.1+i.1,(shifted s i).root.2)=i from by change (0+i.1,i.2)=i; simp]
  rw [masked_ne _ _ _ _ (fun h => hU (hh.mp h)),masked_ne _ _ _ _ hU]

theorem Key.shift_due (s : Signed) (p : Cell n) (U : Config G n) :
    owed c b (shifted s p) U = due c b (pull s 0 U) p := by
  rw [owed,shift_frame]; simp only [due,translate_face,translate_health,translate_test]
  simp only [show (shifted s p).root = ((0:Site n),p.2) from rfl,zero_add,Prod.mk.eta]

lemma direct_split (U : Config G n) (hc : c.direct ≤ 1) (β : ℝ) :
    (top G c).principal c b β U + (β * bulk c * ∑ i : Cell n, masked b.threshold (touched i) (residual G i) U) +
      β * ∑ i, due c b U i = β * energy U := by
  unfold PathData.principal energy
  simp_rw [(core_top c b _ U).1, (core_top c b _ U).2.1, (core_top c b _ U).2.2]
  rw [show (∑ x : Site n, (0:ℝ)) = 0 by simp,add_zero]
  simp only [zero_add]
  rw [← Fintype.sum_prod_type']
  rw [mul_assoc β, ← mul_add, ← mul_add, Finset.mul_sum]; congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => (due_eq c b hc U i).symm

def share := (Fintype.card Signed : ℝ)⁻¹
theorem share_pos : 0 < share := by unfold share; positivity
theorem fair (x : ℝ) : share * ∑ _s : Signed, x = x := by
  have hs : 0 < (Fintype.card Signed : ℝ) := by positivity
  simp [share,hs.ne']

theorem channel_split (U : Config G n) (hc : c.direct ≤ 1) (β : ℝ) :
    (top G c).inChannels c b β U + β * share * bulk c *
      (∑ i : Key n, masked b.threshold i.skin i.accrual U) + β * share * ∑ i : Key n, Key.owed c b i U = β * energy U := by
  have hm (s : Signed) : (∑ p : Cell n, masked b.threshold (Key.skin (s,p)) (Key.accrual (s,p)) U) =
      ∑ p : Cell n, masked b.threshold (touched p) (residual G p) (pull s 0 U) := by
    rw [← Equiv.sum_comp (Key.shift s)]; refine Finset.sum_congr rfl fun p _ => Key.shift_mask p s U _
  have hd (s : Signed) : (∑ p : Cell n, Key.owed c b (s,p) U) = ∑ p, due c b (pull s 0 U) p := by
    rw [← Equiv.sum_comp (Key.shift s)]; exact Finset.sum_congr rfl fun p _ => Key.shift_due ..
  unfold PathData.inChannels; simp_rw [Fintype.sum_prod_type (fun i : Key n => _),hm,hd]
  change share * _ + _ + _ = _
  rw [mul_comm β share,mul_assoc share, mul_assoc share, mul_assoc share, ← mul_add, ← mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← fair (β*energy U)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact (direct_split c b (pull s 0 U) hc β).trans (by rw [energy_pull])
end YM.WilsonStartup
