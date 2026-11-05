import YM.Corona.Spend
import YM.Next.EXTRACTION.Tails

/-!
# Exact rebuilding of support-exponent room under projection and paths

No new localization assumptions on the law. Transfer lemmas condition on all
sites being covered as indicated (not just a displayed tested-center set).
`inspected` puts back the one-time extra flag read. Arbitrary periodic sites.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Shapes
open Function Lattice Lattice.Corona RG Wilson Relation Finset
open scoped Topology BigOperators
variable {n c f : Side} {G : Gauge} {k : ℕ}

lemma pdist_vec (s : Step) : pdist (s.vec : Site n) ≤ 1 := by unfold Step.vec; split; rw [pdist_neg]; exact pdist_step _; exact pdist_step _
lemma visits_dist (x y : Site n) (w : Walk) (he : y ∈ visits x w) : separation x y ≤ w.length := by
  induction w generalizing x with
  | nil => simp [show y=x by simpa [visits] using he]
  | cons s w ih =>
    rcases List.mem_cons.mp he with rfl|he
    · simp
    have hx : separation x (x+s.vec) ≤ 1 := by rw [separation_comm,separation,add_sub_cancel_left]; exact pdist_vec _
    have hv := separation_triangle x (x+s.vec) y; have ht := ih _ he
    rw [List.length_cons]; omega
lemma inspect_dist (X : Support n) {x : Site n} (h : x ∈ inspected X) : ∃ y∈X, separation x y ≤ 8 := by
  rcases mem_union.mp h with h|h
  · exact ⟨x,h,by simp⟩
  obtain ⟨p,_,ht⟩ := mem_biUnion.mp h
  by_cases he : Disjoint X (touched p)
  · simp [he] at ht
  rw [if_neg he] at ht
  obtain ⟨y,hy,hh⟩ := Finset.not_disjoint_iff.mp he
  refine ⟨y,hy,?_⟩
  have hz z (h : z ∈ touched p) : separation p.1 z ≤ 4 := visits_dist _ _ _ (List.mem_toFinset.mp h)
  have hx := separation_triangle x p.1 y; rw [separation_comm x p.1] at hx; exact hx.trans (Nat.add_le_add (hz _ ht) (hz _ hh))



private lemma visits_span (z : Cover) (w : Walk) : (visits z w).length = w.length+1 := by
  induction w generalizing z with
  | nil => rfl
  | cons s w ih => rw [visits,List.length_cons,List.length_cons, ih]



lemma steps (a : Atom G k) (x : Site n) : (a.footprint x).card ≤ 2*(a.length+1) := by
  unfold Atom.footprint Atom.stencil
  have he (s : Slot) : s.stencil.card ≤ 2*s.length := by
    refine (card_union_le ..).trans ((Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)).trans ?_)
    simp only [visits_span,Slot.length]; change s.walk.length+1+(4+1) ≤ _; omega
  apply card_image_le.trans ((card_insert_le ..).trans ?_)
  have hx := card_biUnion_le.trans (Finset.sum_le_sum fun i (_:i∈univ) => he (a.leg i))
  rw [← Finset.mul_sum] at hx; unfold Atom.length; omega

def pad (s : ℕ) : ℕ := ((s+6)+(s+6)+1)^4





lemma enlarge_reads (q : Ratio c f) (X : Support f) (s B : ℕ) (hB : 0 < B) :
    halo (s*B) ((inspected X).image q.parent) ⊆ halo ((s+9)*B) (X.image q.parent) := by
  intro v hv; obtain ⟨y,hy,hV⟩ := halo_spec.mp hv; obtain ⟨y,hy0,rfl⟩ := mem_image.mp hy
  obtain ⟨x,hx,hxy⟩ := inspect_dist X hy0
  have h := q.count.pos
  have he : separation (q.parent y) (q.parent x) ≤ 9 := Nat.le_of_mul_le_mul_left ((foreshorten q ..).trans
    (by nlinarith only [h,hxy] : _ ≤ q.count.val*9)) h
  rw [separation_comm] at he
  exact halo_spec.mpr ⟨_,mem_image_of_mem _ hx,(separation_triangle _ (q.parent y) _).trans (by
    simp only [Nat.add_mul]; omega)⟩

def raw (q : Ratio c f) (s : ℕ) (input output : BudgetPoint) (extra : ℝ) :=
    input.B ≤ 2*output.B ∧ 0 ≤ extra ∧ 20*pad (s+9)*(output.supportExponent+extra) ≤ input.supportExponent*q.count.val

lemma reset {q : Ratio c f} {s : ℕ} {input output : BudgetPoint} {extra : ℝ} (h : raw q s input output extra)
    {X : Support f} {Y : Support c} (he : Y ⊆ halo (s*output.B) ((inspected X).image q.parent)) :
    (output.supportExponent+extra)*coverNumber output.B Y ≤ (pad (s+9):ℝ)*(output.supportExponent+extra) +
        (input.supportExponent/2)*coverNumber input.B X := by
  obtain ⟨h1,h2,h3⟩ := h
  have hv := cover_mono (he.trans (enlarge_reads q X s output.B output.B_pos)) output.B
  have hw := (Nat.mul_le_mul_left q.count.val hv).trans (collapse q X input.B output.B output.B_pos h1 _)
  change q.count.val*coverNumber output.B Y ≤ (q.count.val+10*coverNumber input.B X)*pad (s+9) at hw
  have hO := output.exponent_pos
  have hx : 0 < (q.count.val:ℝ) := by exact_mod_cast q.count.pos
  have ht : (q.count.val:ℝ)*coverNumber output.B Y ≤ ((q.count.val:ℝ)+10*coverNumber input.B X)*pad (s+9) := by exact_mod_cast hw
  apply le_of_mul_le_mul_left (a:=(q.count.val:ℝ)) ?_ hx
  linarith only [mul_le_mul_of_nonneg_left ht (show 0 ≤ output.supportExponent+extra by linarith),
    mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ coverNumber input.B X)]

lemma reserve {q : Ratio c f} {s : ℕ} {input output : BudgetPoint} {extra : ℝ} (h : raw q s input output extra)
    {X : Support f} {Y : Support c} (he : Y ⊆ halo (s*output.B) ((inspected X).image q.parent)) {t : ℝ} (ht : 0 ≤ t) :
    Mix.loaf output Y extra t ≤ Real.exp (pad (s+9)*(output.supportExponent+extra)) * Real.exp (-(input.supportExponent/2)*coverNumber input.B X) * input.mass X t := by
  unfold Mix.loaf BudgetPoint.mass; rw [← mul_assoc _ _ t, ← Real.exp_add, ← Real.exp_add]; gcongr
  linarith only [reset h he]
end YM.Extra.Iteration.Shapes
