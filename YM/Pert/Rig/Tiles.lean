import YM.Extraction.Round
import YM.Pert.Fourier.Riemann
import YM.Pert.Lattice.Bundles
/-! Reporting cells around quarter-period inversion center. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Rig
open Maxwell Lattice Extraction Set MeasureTheory Function Filter Full Topology Next.Rank.Radian
variable {n c : Side} {r : ℕ} {t₀ : ℝ}
abbrev field (r : ℕ):=Fin r→Cover
def tent (c : Side) (A : ℕ) := Fintype.piFinset (fun _i : Fin r=> room c A)
def place (n : Side) (u : field r) : Full.Grid n r := fun i=> Full.center n + wrap n (u i)
lemma center_eq (t : ℝ) (ht : t≠0) (u : field r) : address t (tag t u)=u := by -- nonzero mesh
  funext i a; change ⌈t * (u i a : ℝ) / t⌉ = _; rw [mul_div_cancel_left₀ _ ht]; exact Int.ceil_intCast _
lemma emb_eq (u : Full.Grid n r) (z : ℝ): Full.embedding z u = tag z (fun i=> lift (u i-Full.center n)) := rfl
lemma tent_eq (u : field r) (R : ℕ) (hu : u ∈ tent c R) (hn : 2*(R*c.val)<n.val) : embedding t₀ (place n u) = tag t₀ u := by
  rw [emb_eq]; congr 1; funext i; dsimp only [place]; rw [add_sub_cancel_left, Band.centered_sample (u i) R (Fintype.mem_piFinset.mp hu i) hn]
lemma tent_valid (u : field r) {R : ℕ} (h : ‖tag ((c.val:ℝ)⁻¹) u‖≤ R) : u∈ tent c R := Fintype.mem_piFinset.mpr fun i=>addressBW _ _ ((PiLp.norm_apply_le (tag ((c.val:ℝ)⁻¹) u) i).trans h)
lemma place_injectiveOn {R : ℕ} (hn : 2*(R*c.val)<n.val) : InjOn (place (r:=r) n) ((tent c R : Finset (field r)) : Set (field r)) := fun _ hx _ hy h=> funext fun i=> by
  have hv := Band.centered_sample _ R (Fintype.mem_piFinset.mp hx i) hn
  have hu := Band.centered_sample _ R (Fintype.mem_piFinset.mp hy i) hn
  rw [←hu,←hv]; exact congrArg _ (add_left_cancel (congrFun h i))

def scans (t:ℝ) (c:Side) (u : field r→ℂ) (R : ℕ) := (t:ℂ)^(4*r) * ∑ x∈tent c R,u x
theorem scans_eq (R : ℕ) (hn : 2*(R*c.val)<n.val) (t : ℝ) (heq : t=((c.val:ℝ)⁻¹)) (g : Points r→ℂ) (hg : ∀ x : Points r, R < ‖x‖ → g x=0) (K : Grid n r→ℂ) : scans t c (fun u=>g (tag t u)*K (place n u)) R = (↑t:ℂ)^(4*r) * ∑ x:Grid n r,g (embedding t x)*K x := by
  classical
  unfold scans; congr 1
  rw [← Finset.sum_subset (s₁:=(tent c R).image (place n)) (Finset.subset_univ _) ?_]
  · rw [Finset.sum_image (place_injectiveOn hn)]
    refine Finset.sum_congr rfl (fun i (hi : i∈tent c R)=>by rw [tent_eq _ _ hi hn])
  intro v _ hv; rw [hg _ ?_,zero_mul]; contrapose! hv
  let u : field r := fun i=>lift (v i-Full.center n)
  apply Finset.mem_image.mpr ⟨u,tent_valid _ ?_,?_⟩
  · rw [← heq]; exact hv
  funext i; unfold u place; simp only [wrap_lift]; abel

lemma scans_integral (c : Side) {R : ℕ} (t : ℝ) (hh : 0<t) (g : field r→ℂ) (hg : ∀ x, x∉tent c R→g x=0):
   let F := g ∘ address t
   Integrable F volume ∧ (∫ x : Points r, F x) = scans t c g R := by
  classical
  intro f; let a(v : field r) := (segment t v).indicator (fun _=>g v)
  have eq (x:Points r) : f x = ∑ v∈tent c R,a v x := by
    by_cases h:address t x ∈ tent c R
    · rw [Finset.sum_eq_single (a:=address t x)]
      · exact (indicator_of_mem (show x∈segment t _ from rfl) _).symm
      · intro _ _ hj; exact (indicator_of_notMem (fun hi=>hj (Eq.symm hi)) _)
      simp only [h,not_true_eq_false,false_implies]
    unfold f; rw [comp_apply,hg _ h]; exact (Finset.sum_eq_zero fun v hv=>indicator_of_notMem (fun (h':x∈segment t v)=> h (by rwa [h'])) _).symm -- f
  have hp : ∀ i∈tent c R, Integrable (a i) := by
    intro i H; apply (integrable_indicator_iff (measurable_segment hh _)).mpr; exact integrableOn_const (by simp [cell_volume hh i])
  constructor
  · rw [funext eq]; exact integrable_finsetSum _ hp
  rw [funext eq, integral_finsetSum _ hp]; unfold scans; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; unfold a; rw [integral_indicator (measurable_segment hh _), setIntegral_const, Measure.real, cell_volume hh, ENNReal.toReal_ofReal (by positivity), Complex.real_smul];push_cast;rfl
end YM.Pert.Rig
