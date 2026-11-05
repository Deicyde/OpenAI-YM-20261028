import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics
import YM.Bid.Craft

/-!
# Optional raw factors: keep the actual path/read costs

These expansions are *on the real fields*, no
condition that V/U lies in one weak patch or injective link chart (in
particular no such assumption on winding paths). `pairTail` is the
full same-occurrence row with kept-row selector followed by the two
true path labels; don't replace it by a collapsed cluster at the same
endpoint. Apply the coarse and fine version with **different** s,t and
costs. Also allows inspecting the true mask/flag halo before estimating
optional costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push.AbsoluteSums.Paths
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side}

/-- True base minus truncated row on that level and in one channel. Same
as `Pressure.cuff` when t is the BudgetPoint threshold. -/
def tails (T : PathData G) (p : Clip) (R d : ℕ) (t : ℝ) (x : Cell n) (U : Config G n) : ℝ :=
    if PathData.kept p t x.1 U then
      ‖T.ell U x‖^2/2-‖shorten T R d U x‖^2/2
    else 0

lemma cuff_tails (T : PathData G) (p : Clip) (B : BudgetPoint) (R d : ℕ) (U : Config G n) (x : Cell n) :
    cuff T p B d R U x = tails T p R d B.threshold x U := by
  unfold cuff PathData.baseTerm crown trunk tails; split <;> abel

/-- At least one genuinely omitted row (criterion stays on the labels
when the endpoints coincide). d = 1 on the fine tail, L on the coarse. -/
def long (T : PathData G) (R d : ℕ) (p : PlaqAxes) (i : ℕ×ℕ) :=
    ¬ ((T.row p i.1).2.length*d ≤ R ∧ (T.row p i.2).2.length*d ≤ R)

def pairTail (T : PathData G) (p : Clip) (R d : ℕ) (t : ℝ) (x : Cell n) (U : Config G n) (i : ℕ × ℕ) : ℝ :=
    if long T R d x.2 i ∧ PathData.kept p t x.1 U then
        inner ℝ (T.ellTerms x i.1 U) (T.ellTerms x i.2 U) / 2
    else 0

private lemma paired_sum (v : ℕ → G.Color) (hv : Summable v) :
    HasSum (fun i : ℕ×ℕ => inner ℝ (v i.1) (v i.2) / 2) (‖∑' i, v i‖^2/2) := by
  have he : Summable (fun i : ℕ×ℕ => inner ℝ (v i.1) (v i.2)) :=
    Summable.of_norm_bounded ((hv.norm).mul_of_nonneg hv.norm (fun i => norm_nonneg _) (fun i => norm_nonneg _))
      (fun i => abs_real_inner_le_norm ..)
  have hi (w : G.Color) : inner ℝ w (∑' i, v i)=∑' i, inner ℝ w (v i) := (innerSL ℝ w).map_tsum hv
  have hg : (∑' i : ℕ×ℕ, inner ℝ (v i.1) (v i.2)) = ‖∑' i, v i‖^2 := by
    rw [he.tsum_prod, ← real_inner_self_eq_norm_sq]
    rw [hi]
    exact tsum_congr fun i => (hi (v i)).symm.trans (real_inner_comm ..)
  rw [← hg]; exact he.hasSum.div_const _

private lemma cut_pair (T : PathData G) (R d : ℕ) (U : Config G n) (x : Cell n) (i : ℕ×ℕ) :
    inner ℝ (shortenTerm T R d U x i.1) (shortenTerm T R d U x i.2) =
      if long T R d x.2 i then 0 else inner ℝ (T.ellTerms x i.1 U) (T.ellTerms x i.2 U) := by
  unfold shortenTerm long; split_ifs <;> first | tauto | simp

lemma pair_sum {T : PathData G} {p : Clip} {σ C Λ : ℝ} (h : T.Bounds p σ C Λ) (R d : ℕ) (t : ℝ) (x : Cell n) (U : Config G n) :
    HasSum (pairTail T p R d t x U) (tails T p R d t x U) := by
  have hx : Summable (fun i : ℕ => T.ellTerms x i U) := (T.ell_dominated h x).summable _
  have hs : Summable (fun i : ℕ => shortenTerm T R d U x i) := by
    refine Summable.of_norm_bounded hx.norm ?_; intro i; unfold shortenTerm; split
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  unfold tails; split
  next hh =>
    apply ((paired_sum _ hx).sub (paired_sum _ hs)).congr_fun
    intro i; unfold pairTail
    rw [cut_pair]; by_cases hg : long T R d x.2 i <;> simp [*,and_true]
  next hh =>
    refine (show HasSum (fun _ : ℕ × ℕ => (0:ℝ)) 0 from hasSum_zero).congr_fun ?_
    intro i; unfold pairTail; simp only [hh,and_false,↓reduceIte]

/-- Per-pair cost including the essential true length test. -/
def pairPrice (T : PathData G) (R d : ℕ) (x : PlaqAxes) (i : ℕ × ℕ) :=
    if long T R d x i then 2*mate T x i else 0

lemma pairPrice_nonneg (T : PathData G) (R d : ℕ) (x : PlaqAxes) (i : ℕ × ℕ) : 0 ≤ pairPrice T R d x i := by
  unfold pairPrice mate; split <;> positivity

lemma pair_le (T : PathData G) (p : Clip) (R d : ℕ) (t : ℝ) (x : Cell n) (U : Config G n) (i : ℕ × ℕ) :
    |pairTail T p R d t x U i| ≤ pairPrice T R d x.2 i := by
  unfold pairTail; split
  next h =>
    have hs (j : ℕ) : ‖T.ellTerms x j U‖ ≤ |(T.row x.2 j).1| * 2 := by
      rw [PathData.ellTerms,norm_smul,Real.norm_eq_abs];
      exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
    refine le_trans ?_ (le_of_eq (show (|(T.row x.2 i.1).1| *2*(|(T.row x.2 i.2).1| *2))/2 = _ from ?_))
    · rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      exact div_le_div_of_nonneg_right ((abs_real_inner_le_norm ..).trans
        (mul_le_mul (hs _) (hs _) (norm_nonneg _) (by positivity))) (by norm_num)
    · rw [pairPrice, if_pos h.1]; unfold mate; ring
  next h => rw [abs_zero]; exact pairPrice_nonneg ..

@[fun_prop] lemma pair_measurable (T : PathData G) (p : Clip) (R d : ℕ) (t : ℝ) (x : Cell n) (i : ℕ×ℕ) :
    Measurable (fun U => pairTail T p R d t x U i) := by
  unfold pairTail
  by_cases hi : long T R d x.2 i
  · simp_rw [hi,true_and]; refine (Continuous.measurable ?_).ite (PathData.kept_closed .. |>.measurableSet) measurable_const
    unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
  simp_rw [if_neg (not_and_of_not_left _ hi)]; exact measurable_const

section locality

lemma slot_local (s : Slot) (o : Site n) : LocalOn (s.stencil.image (fun x => wrap n x+o))
    (fun U : Config G n => s.atSite U o) := by
  rw [Finset.coe_image]; exact LocalOn.expandAt _ _ s.covered _

/-- Same signed input orientations applied later. In these coordinates the
actual kept decision only uses this extra halo, a condition on the threshold,
NOT requiring the current plaquette to be good. -/
lemma kept_agrees (p : Clip) (t : ℝ) (B : ℕ) (o : Site n) (U V : Config G n)
    (hm : ∀ k : ℕ, t*Real.exp ((k:ℝ)/p.relaxation) < 2 → k+2 ≤ B)
    (h : Agrees (halo B {o}) U V) : PathData.kept p t o U ↔ PathData.kept p t o V := by
  have hh (W Z : Config G n) (hw : Agrees (halo B {o}) W Z)
      (hk : PathData.kept p t o W) : PathData.kept p t o Z := by
    intro b
    by_cases he : t*Real.exp (separation o b.1/p.relaxation)<2
    · refine le_trans ?_ (hk b)
      apply le_of_eq; congr 1; symm
      apply travel_local _ _
      refine agrees_mono hw ?_
      intro x hx
      have hz := YM.Work.E01.sep_touched b x (show x∈RG.touched b from List.mem_toFinset.mpr hx)
      apply halo_spec.mpr; refine ⟨o,Finset.mem_singleton_self _,?_⟩
      apply (separation_triangle o b.1 x).trans; exact (Nat.add_le_add_left hz _).trans (hm _ he)
    exact (G.chord_le_two _).trans (le_of_not_gt he)
  exact ⟨hh U V h,hh V U fun e ha hb => (h e ha hb).symm⟩

/-- Include both mates' entire paths and the real row decision reads. -/
def pairFoot (B : ℕ) (T : PathData G) (x : Cell n) (i : ℕ×ℕ) :=
    halo B {x.1} ∪ bundle x.1 (duplex T x.2 i)

lemma pair_local (T : PathData G) (p : Clip) (R d : ℕ) (t : ℝ) (x : Cell n) (i : ℕ×ℕ) (B : ℕ)
    (h : ∀ k : ℕ, t*Real.exp ((k:ℝ)/p.relaxation)<2 → k+2 ≤ B) :
    LocalOn (pairFoot B T x i) (fun U => pairTail T p R d t x U i) := by
  intro U V hX
  have hi := kept_agrees p t B x.1 U V h (agrees_mono hX fun _ hx => Finset.mem_union_left _ hx)
  let s := duplex T x.2 i
  have hp (j : Fin 2) : (s j).atSite U x.1=(s j).atSite V x.1 :=
    slot_local (s j) x.1 U V (agrees_mono hX (fun z hz => Finset.mem_union_right _
      (mem_insert_of_mem (mem_biUnion.mpr ⟨j,mem_univ _,hz⟩))))
  unfold pairTail PathData.ellTerms
  dsimp only; rw [hi, (show (T.row x.2 i.1).2.atSite U x.1=_ from hp 0),
    (show (T.row x.2 i.2).2.atSite U x.1=_ from hp 1)]; rfl

lemma placed_local {k : ℕ} (A : Atom G k) (p : BudgetPoint) (o : Site n) :
    LocalOn (inspected (A.footprint o)) (fun U => A.placed p U o) := by
  refine UsesFinal.allReads p.threshold _ _ ?_
  intro U V h he
  dsimp only [Atom.placed]
  have hZ : Healthy p.threshold (A.footprint o) U ↔ Healthy p.threshold (A.footprint o) V := by
    unfold Healthy; simp_rw [Finset.disjoint_iff_inter_eq_empty]; rw [he]
  by_cases hV : Healthy p.threshold (A.footprint o) V
  · rw [masked_eq _ _ _ _ (hZ.mpr hV),masked_eq _ _ _ _ hV]
    apply congr_arg A.poly
    funext i
    apply slot_local
    exact agrees_mono h fun z hz => Finset.image_subset_image
      (show (A.leg i).stencil ⊆ A.stencil from fun y hy =>
        mem_insert_of_mem <| mem_biUnion.mpr ⟨i,mem_univ _,hy⟩) hz
  rw [masked_ne _ _ _ _ (hZ.not.mpr hV),masked_ne _ _ _ _ hV]
end locality
end YM.ConnectedActivityE6.Raw
