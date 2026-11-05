import YM.Planned.ATOM_REGULAR_ESTIMATE.Sampled
import YM.Planned.ATOM_REGULAR_ESTIMATE.Vest


/-!
`Cube` launches an arbitrary finite *ordered* output variation in an
actual bounded-support extension (near a Healthy V, incl. equality). Keep
cost in normalized output direction fields even near the anchor,
independent of radius R or #bonds. The sup-costed extension can then be
used for `panelBill` in Ducts.lean. No claiming `Sample.Measures` is implemented with
this extension, double-check it on a protected kernel expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage.Cube
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform Next.Foundations
open WardBin.Lies Sample Exterior
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {n : Side} {r k l : ℕ} {G : Gauge} {T : Collar G k}

-- single-bond chug; unit matrices
abbrev carriage (G : Gauge) (l : ℕ) := Fin l → G.Color
def starts (G : Gauge) (l : ℕ) : carriage G l → G.El :=
    match l with
    | 0 => fun _ => 1
    | k+1 => fun x => starts G k (Fin.tail x) * G.lieExp (x 0)
lemma starts_diff (G : Gauge) (l : ℕ) : ContDiff ℝ ω (fun x => G.mat (starts G l x)) := by
  induction l with
  | zero => exact contDiff_const
  | succ l ih =>
    unfold starts; simp_rw [G.mat_mul]; apply ContDiff.mul
    · exact ih.comp (f:=fun z : carriage G (l+1) => Fin.tail z) (contDiff_pi.mpr (fun i => contDiff_apply ..))
    exact G.exp_jet.comp (f:=fun x : carriage G (l+1) => x 0) (contDiff_apply ..)
@[simp] lemma starts_zero (l : ℕ) : starts G l 0=1 := by
  induction l with
  | zero => rfl
  | succ l ih => change starts G l (Fin.tail (0:carriage G (l+1))) * G.lieExp 0=1; rw [show Fin.tail (0:carriage G (l+1))=0 from rfl,ih]; simp
lemma starts_expanded (V : Config G n) (A : Slab G n l) (e : Link n) :
    chug l V A e= starts G l (fun i => A i e) * V e := by
  induction l generalizing V with
  | zero => change _ = 1 * V e; rw [one_mul]; rfl
  | succ l ih => simp only [chug,ih]; dsimp only [starts]; unfold increment; rw [mul_assoc]; rfl

lemma stamps (G : Gauge) (T : Collar G k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ l, l ≤ k →
    ∀ u v w : G.El, G.mat (u*v*w) ∈ closedBall 1 T.r →
      Allows k (fun x : carriage G l => G.plog (G.mat (u*(starts G l x*v)*w))) 0 C := by
  obtain ⟨M,hM⟩ := isCompact_univ (X:=G.El) |>.exists_bound_of_continuousOn G.continuous_mat.continuousOn
  have hm (z : G.El) : ‖G.mat z‖ ≤ M := hM z (mem_univ _)
  choose a ha using fun l : ℕ => show ∃ a, Allows k (fun x => G.mat (starts G l x)) 0 a from by
    obtain ⟨a,h,h'⟩ := exists_allows (f:=fun x => G.mat (starts G l x)) (isCompact_singleton (x:=(0:carriage G l)))
      (fun x _ => (starts_diff G l).contDiffAt) k; exact ⟨a,h' 0 (mem_singleton _)⟩
  let W (l : ℕ) := composeCost k T.count (2^k*(2^k*M*(2^k*a l*M))*M)
  refine ⟨1+∑ i ∈ Finset.range (k+1), |W i|, le_add_of_nonneg_right (by positivity),fun l hl u v w hw => ?_⟩
  let f (x : carriage G l) := G.mat (u*(starts G l x*v)*w)
  have he (u : G.El) : Allows k (fun _ : carriage G l => G.mat u) 0 M := allows_const _ (hm u)
  have ht := (T.log (f 0) (by simpa [f] using hw)).comp (f:=f) (((he u).times ((ha l).times (he v))).times (he w))
  exact ht.mono (((le_abs_self (W l)).trans (Finset.single_le_sum (f:=fun i => |W i|) (fun i _ => by positivity)
    (Finset.mem_range.mpr (by omega)))).trans (le_add_of_nonneg_left zero_le_one))

def cap (T : Collar G k) := (stamps G T).choose
def fee (T : Collar G k) := cap T + T.count*(G.colorScale*4)
lemma fee_one (T : Collar G k) : 1 ≤ fee T := (stamps G T).choose_spec.1.trans
    (le_add_of_nonneg_right (mul_nonneg T.count_pos.le (by positivity [G.colorScale_pos])))

variable {P : BudgetPoint} {o : Site n} {V : Config G n} {A : Slab G n l} {g : Site n → G.El}
    {c a : ℝ} {z : Link n}


end YM.Planned.AtomRegular.Foliage.Cube
