import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Motion
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Spin


/-!
# Anchored exact recurrence of the connected integral

Motion of a rooted block against all the rest, iterate through fusions.
Designed for local probes even with unbounded arguments. The resulting
term has not divided by a coefficient of a packet; read directly in the
existing accepted marker-log algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Filter Function Set Finset
open YM.Multi.Vacuum.Gauss Probe Quadratic Moment Spin Anchor Marker
open YM.Extra.Trajectories
open scoped Topology BigOperators Interval

variable {I J V : Type} [Fintype J] [DecidableEq V]
namespace Fused
variable (R : Census V) (q : Rows V I J) (v : Probes V I)
def accounts : Poly R := Poly.inject fun s => total s.val q v
lemma accounts_part (s : R.Mode) : (accounts R q v).part s=total s.val q v := rfl
lemma accounts_quiet : (accounts R q v).part R.quiet=1 := total_empty q v

variable {R} [Fintype V]

def mixed (t : R.Mode) (A : Finset V) := (quotient t.val A (accounts R q v)).part t
lemma done_mixed (t : R.Mode) : mixed q v t t.val=total t.val q v := quotient_end _ _ (accounts_quiet ..)

lemma final_mixed (t : R.Mode) (A : Finset V) : mixed (path A q high) v t A=mixed q v t A := by
  unfold mixed; rw [show accounts R (path A q high) v=accounts R q v from Poly.ext fun i => final_total ..]

lemma initial_mixed (t : R.Mode) (A : Finset V) (ha : A ⊆ t.val) (hh : A ≠ t.val) : mixed (path A q 0) v t A=0 := by
  let a : R.Mode := ⟨A,R.down t.property A ha⟩
  unfold mixed; rw [quotient_alone t a ha _ (accounts_quiet ..),Poly.part_send, if_neg]
  · intro hw; exact hh ((congr_arg Subtype.val hw).symm)
  intro s hs ht
  simp only [accounts_part]
  have hb : Disjoint (Anchor.diff s a.val).val A := (separates s a hs).1.symm
  have hr : total a.val (path A q 0) v=total a.val q v := by simpa only [Finset.union_empty,total_empty,mul_one] using apart_total A q v a.val ∅ (Finset.Subset.refl _) (disjoint_empty_left _)
  rw [hr, alone_total A q _ v _ hb,← apart_total A q v a.val (Anchor.diff s a.val).val (Finset.Subset.refl _) hb,(separates s a hs).2]

variable [Fintype I] [DecidableEq I]
variable (t : R.Mode) (A : Finset V) {w : V → Row I} {H : V → ℕ → ℝ}

-- When embedding these comparisons, cos rates in the cost are real
-- scalars; actual probe coefficients and orientation rotations pair
-- COMPLEX bilinearly, never a hermitian square.

def currency (q : Rows V I J) (x : ℝ) (i : V) (a : I) (j : V) (b : I) :=
    Complex.ofReal (Real.cos x * crossed (q i a) (q j b))

def pipe (q : Rows V I J) (v : Probes V I) (t : R.Mode) (A : Finset V) (x : ℝ) :=
    ∑ i∈A,∑ a,∑ j∈(t.val \ A),∑ b,currency q x i a j b * mixed (path A q x) (marked (marked v i a) j b) t (insert j A)

private def pushed (x : ℝ) (i : V) (a : I) (j : V) (b : I) :=
    root t.val (insert j A) (accounts R (path A q x) (marked (marked v i a) j b))

omit [Fintype V] in
private lemma probe_deriv (s : R.Mode) (x : ℝ) (h : Valid t.val 2 v w H) (hc : base q t.val w) :
    HasDerivAt (fun y => (root t.val A (accounts R (path A q y) v)).part s)
      ((∑ i∈A,∑ a,∑ j∈(t.val \ A),∑ b,currency q x i a j b • pushed q v t A x i a j b).part s) x := by
  simp_rw [Poly.part_sum, Poly.part_smul, pushed, root_part, accounts_part]
  by_cases hz : s.val ⊆ t.val ∧ A ⊆ s.val
  swap
  · have he (j : V) : ¬(s.val ⊆ t.val ∧ insert j A ⊆ s.val) := fun h => hz ⟨h.1,(Finset.subset_insert j _).trans h.2⟩
    simp_rw [if_neg hz,if_neg (he _),mul_zero,sum_const_zero]; apply hasDerivAt_const
  simp_rw [if_pos hz]
  let L := t.val
  let B := s.val
  have h1 := supported_flow s.val (path A q) (flux A q) h hz.1 x Set.univ univ_mem (fun t _ => keeps A q hc t) (fun i _ a => ⟨_,squares_nn _,fun t _ => stable A q t i a⟩) (fun t _ i _ a => Spin.rate A q i a t)
  convert! h1 using 1
  symm; let X := B \ A
  let E i (a : I) j (b : I) := total B (path A q x) (marked (marked v i a) j b)
  let F i (a : I) j := ∑ b : I,currency q x i a j b*E i a j b
  let G (i : V) (a : I) (j : V) := ∑ b : I,crossed (path A q x j b) (flux A q x i a) • E i a j b
  have hg i a j : G i a j = if i∈A ∧ j ∉ A then F i a j else 0 := by
    unfold G F; simp_rw [clear_rate]; split
    · simp_rw [Complex.real_smul]; rfl
    rename_i h0; simp only [zero_smul,sum_const_zero]
  change ∑ i∈B,∑ a,∑ j∈B,G i a j = _
  have hy i (hi : i∈A) (a : I) : ∑ j∈B,G i a j = ∑ j∈(t.val \ A),∑ b : I,currency q x i a j b *
      (if s.val ⊆ t.val ∧ insert j A ⊆ s.val then E i a j b else 0) := by
    let W j := ∑ b : I,currency q x i a j b * (if s.val ⊆ t.val ∧ insert j A ⊆ s.val then E i a j b else 0)
    change _=∑ j∈(L \ A),W j
    rw [← sum_subset (s₁:=X) sdiff_subset ?_, ← sum_subset (s₁:=X) (sdiff_subset_sdiff hz.1 (Finset.Subset.refl _)) ?_]
    · apply sum_congr rfl; intro j hj
      rcases mem_sdiff.mp hj with ⟨hb,hc⟩
      have hx : s.val ⊆ t.val ∧ insert j A ⊆ s.val := ⟨hz.1,insert_subset hb hz.2⟩
      unfold W; simp_rw [hg,if_pos (show i∈A ∧ j ∉ A from ⟨hi,hc⟩),if_pos hx]; rfl
    · intro j hj he
      have hw : ¬(s.val ⊆ t.val ∧ insert j A ⊆ s.val) := fun h => he (mem_sdiff.mpr ⟨h.2 (mem_insert_self ..), (mem_sdiff.mp hj).2⟩)
      unfold W; simp_rw [if_neg hw,mul_zero,sum_const_zero]
    intro j hj he; rw [hg,if_neg]; intro h; exact he (mem_sdiff.mpr ⟨hj,h.2⟩)
  rw [← sum_subset hz.2]; rotate_left
  · intro i hi he; simp_rw [hg]; simp only [he,false_and,↓reduceIte,sum_const_zero]
  exact sum_congr rfl fun i hi => sum_congr rfl fun a _ => hy i hi a

omit [Fintype V] [Fintype I] [DecidableEq I] in
private lemma fixed_outer (x : ℝ) :
    outer t.val A (accounts R (path A q x) v)=outer t.val A (accounts R q v) := by
  ext j
  simp only [outer_part]; split
  next h => exact alone_total A q _ _ x h.2
  rfl

/-- Fusion prices with the correct denominator after differentiation. -/
lemma fusion_rate (x : ℝ) (h : Valid t.val 2 v w H) (hc : base q t.val w) :
    HasDerivAt (fun y => mixed (path A q y) v t A) (pipe q v t A x) x := by
  let Q y := path A q y
  let B := inverseMass (outer t.val A (accounts R (Q x) v))
  let P := pushed q v t A x
  let f := currency q x
  let D := ∑ i∈A,∑ a,∑ j∈(t.val \ A),∑ b,f i a j b • P i a j b
  have hv y : mixed (Q y) v t A = (root t.val A (accounts R (Q y) v)*B).part t := by
    unfold mixed quotient Q B
    rw [fixed_outer q v t A y,fixed_outer]
  have he : HasDerivAt (fun y => mixed (Q y) v t A) ((D*B).part t) x := by
    simp_rw [hv,Poly.part_mul]
    apply HasDerivAt.fun_sum; intro s _
    apply HasDerivAt.fun_sum; intro u _
    split
    · exact (probe_deriv q v t A s x h hc).mul_const _
    apply hasDerivAt_const
  have hp i (hi : i∈A) a j b :
      (P i a j b * B).part t = mixed (Q x) (marked (marked v i a) j b) t (insert j A) := by
    let F := marked (marked v i a) j b
    change (root _ _ (accounts R _ F)*B).part _=(quotient _ _ (accounts R _ F)).part _
    have hb (u : R.Mode) (hu : u.val ⊆ t.val) (hf : Disjoint u.val (insert j A)) :
        (accounts R (Q x) v).part u=(accounts R (Q x) F).part u := by
      suffices h : values u.val (Q x) v=values u.val (Q x) F by simp_rw [accounts_part,total,h]
      funext y; refine prod_congr rfl fun k hk => ?_
      have hx : k≠j := fun e => disjoint_left.mp hf hk (e ▸ Finset.mem_insert_self ..)
      have hy : k≠i := fun e => disjoint_left.mp hf hk (e ▸ mem_insert_of_mem hi)
      simp only [F,marked,update_of_ne hx,update_of_ne hy]
    unfold B Q
    rw [change_outer _ _ _ hb]
    exact Finset.subset_insert _ _
  convert! he using 1
  unfold D
  simp_rw [Finset.sum_mul,smul_mul_assoc,Poly.part_sum,Poly.part_smul]
  unfold pipe
  apply sum_congr rfl; intro i hi
  simp_rw [hp _ hi]; rfl

private lemma pass_continuous {F : ℝ → Poly R} (h : ∀ s : R.Mode, Continuous (fun x => (F x).part s)) :
    ∀ s : R.Mode, Continuous (fun x => (Poly.pass (F x)).part s) := by
  have he : Continuous F := continuous_pi h
  exact fun s => (Poly.part_cont s).comp (Poly.pass_cont.comp he)

/-- Continuity not asserting regularity of ANY larger moments.
Precisely those subsets contained in t. -/
lemma mixed_continuous {n : ℕ} (h : Valid t.val n v w H) (hc : base q t.val w) (B : Finset V) :
    Continuous (fun x => mixed (path A q x) v t B) := by
  let Q := fun x => path A q x
  let L := fun y => accounts R (Q y) v
  have ht (s : Finset V) (hs : s⊆t.val) : Continuous (fun x => total s (Q x) v) := by
    apply continuousOn_univ.mp
    apply total_stays _ _ hs h (fun t _ => keeps A q hc t)
    exact fun i _ a => continuous_iff_continuousAt.mpr fun t => (Spin.rate A q i a t).continuousAt
  have hr (s : R.Mode) : Continuous (fun x => (root t.val B (L x)).part s) := by
    simp_rw [root_part]; split
    next H => exact ht _ H.1
    exact continuous_const
  have ho (s : R.Mode) : Continuous (fun x => (outer t.val B (L x)).part s) := by
    simp_rw [outer_part]; split
    next H => exact ht _ H.1
    exact continuous_const
  have hR : Continuous fun x => root t.val B (L x) := continuous_pi hr
  let F := fun x => outer t.val B (L x)
  have he (m : ℕ) : ∀ s : R.Mode, Continuous (fun x => (iteration (F x) m).part s) := by
    induction m with
    | zero => exact fun _ => continuous_const
    | succ m ih =>
      simp only [iteration, Poly.part_plus,part_sub]
      exact fun s => (ih s).add ((ho s).sub (pass_continuous ih s))
  have hh : Continuous fun x => inverseMass (F x) :=
    continuous_pi (pass_continuous fun s => ((he (Fintype.card V) s).neg))
  exact (Poly.part_cont t).comp (hR.mul hh)

lemma pipe_continuous (h : Valid t.val 2 v w H) (hc : base q t.val w) :
    Continuous (pipe q v t A) := by
  refine continuous_finsetSum _ fun i hi => continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun j hj =>
    continuous_finsetSum _ fun b _ => Continuous.mul (by unfold currency; fun_prop) ?_
  exact mixed_continuous q (marked (marked v i a) j b) t A ((h.mark i a).mark j b) hc (insert j A)

lemma fusion (ha : A ⊆ t.val) (he : A ≠ t.val) (h : Valid t.val 2 v w H) (hc : base q t.val w) :
    mixed q v t A = ∫ x in 0..high, pipe q v t A x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => fusion_rate q v t A x h hc)
      ((pipe_continuous q v t A h hc).intervalIntegrable 0 high), final_mixed, initial_mixed q v t A ha he,sub_zero]

end Fused
end YM.Primitives.GCC
