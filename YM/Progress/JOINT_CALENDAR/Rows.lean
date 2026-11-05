import YM.Progress.JOINT_CALENDAR.Issue

/-!
# Issuing real path-width and price budgets for the ℓ requirement

A port from the joint calendar toward RPathBounds/RScene.

Not just hoping
pre-L numbers suffice: the transported rows can be constructed with their
actual *cover path* price at that order of budgets, retaining every calculated
Bed.

Other curvature coefficients
not provided except when working with JUST the base; `Charges` below exposes
those requirements separately.

No top quartic or loop matching claim here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open RG Precision RG.Supply Bid Next Next.Scheduling Pressure Filter Lattice Laurent Exterior Bloch
open scoped Topology BigOperators

variable {G : Gauge}

def alphabet : ℕ ≃ PlaqAxes × Cover := by
  have : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
  exact Classical.choice nonempty_equiv_of_countable

def script (p : PlaqAxes × Cover) : RG.Slot := ⟨Lattice.route 0 p.2 1,p.1⟩

def note (M : Bed) (q : PlaqAxes) (p : PlaqAxes × Cover) := M.roots (plaquette q) (plaquette p.1) p.2

/-- Retain all row entries (even zero), path on the cover in fixed
coordinate order, actual transport along the slot incl inverse where
called in its adjoint action. `inChannels`, `quadratic`, etc still use
their prescribed whole-orientation conventions; no tie-equivariance assumed.
The other arrays can be ANY supplied candidates at this point. -/
def scribe (M : Bed) (W : PathData G) : PathData G :=
    { W with row := fun p i => (note M p (alphabet i),script (alphabet i)) }

lemma script_offset (p : PlaqAxes × Cover) : (script p).offset=p.2 := route_end ..
lemma script_length (p : PlaqAxes × Cover) : (script p).length=size p.2+4 := by
  have ha : allAxes 1 = [0,1,2,3] := by decide
  simp [script,RG.Slot.length,route, axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]

lemma scribe_attached (M : Bed) (W : PathData G) : Attached M (scribe M W) := by
  constructor
  intro p q y
  apply (alphabet.hasSum_iff.mpr (hasSum_ite_eq (q,y) (note M p (q,y)))).congr_fun
  intro i
  change (if (alphabet i).1=q ∧ (script (alphabet i)).offset=y then note M p (alphabet i) else 0) = _
  rw [script_offset]
  rcases ht : alphabet i with ⟨b,u⟩; simp [ht]; split_ifs with h <;> simp_all

def rowBill (K : MapPrices) (j : ℕ) := Fintype.card PlaqAxes * Real.exp (4:ℝ) * max (K.Ω j) 1



lemma pencil (M : Bed) {K : MapPrices} {j} (h : M.covered (K.α j) (K.Ω j)) (q : PlaqAxes) :
    SumBudget (fun p => Real.exp ((K.α j)*size p.2) * |note M q p|) (Fintype.card PlaqAxes * (K.Ω j)) := by
  let f := fun p => Real.exp ((K.α j)*size p.2) * |note M q p|
  have H (b : PlaqAxes) : SumBudget (fun x => f (b,x)) (K.Ω j) := by
    simpa only [Width,Real.norm_eq_abs,f,note] using h.2.2.2.1 (plaquette q) (plaquette b)
  have hs : Summable f := (summable_prod_of_nonneg (fun i => by unfold f; positivity)).2
    ⟨fun b => (H b).2.1, .of_finite⟩
  change SumBudget f _
  refine ⟨fun i => (H i.1).1 i.2,hs,?_⟩
  rw [hs.tsum_prod, tsum_fintype]
  exact (Finset.sum_le_sum (fun i _ => (H i).2.2)).trans_eq (by simp)

lemma scribe_price (M : Bed) (W : PathData G) {K : MapPrices} {j σ}
    (h : M.covered (K.α j) (K.Ω j)) (hσ : σ ≤ K.α j) (h₁ : σ ≤ 1) (q : PlaqAxes) :
    SumBudget (fun i ↦ |((scribe M W).row q i).1| * Real.exp (σ * ((scribe M W).row q i).2.length)) (rowBill K j) := by
  let f (p) := Real.exp (4:ℝ)*(Real.exp ((K.α j)*size p.2) * |note M q p|)
  have H := pencil M h q
  have hf : Summable f := H.2.1.mul_left _
  have hB : SumBudget (f ∘ alphabet) (rowBill K j) := by
    refine ⟨fun i => by unfold f; dsimp; positivity, alphabet.summable_iff.mpr hf,?_⟩
    simp only [Function.comp_apply]
    rw [alphabet.tsum_eq]; unfold f; rw [tsum_mul_left]
    apply le_trans (mul_le_mul_of_nonneg_left H.2.2 (Real.exp_nonneg _))
    unfold rowBill; rw [mul_left_comm,← mul_assoc]; gcongr; exact le_max_left ..
  refine smaller hB (fun i => ⟨by positivity,?_⟩) le_rfl
  change |note M _ _| * Real.exp (σ*(script _).length) ≤ f _
  rw [script_length]; unfold f; rw [← mul_assoc, ← Real.exp_add, mul_comm]
  gcongr
  push_cast
  have hx := mul_le_mul_of_nonneg_right hσ (Nat.cast_nonneg (α:=ℝ) (size (alphabet i).2))
  linarith

private local instance : Subsingleton (Site 1) := (inferInstance : Subsingleton (Four (ZMod 1)))

lemma acts_point {m n : Type*} (R : Row m n) (a : m) (b : n) :
    R.acts 1 (0,a) (0,b) = ∑' x, R a b x := by
  unfold Row.acts
  exact tsum_congr (fun x => if_pos (Subsingleton.elim ..))

lemma scribe_symbol (M : Bed) (W : PathData G) {σ C} (h : M.roots.strip σ C) (hσ : 0 ≤ σ) (i j : PlaqAxes) :
    HasSum (fun b => if ((scribe M W).row i b).2.plaq=j then ((scribe M W).row i b).1 else 0)
      (M.roots.acts 1 (0,plaquette i) (0,plaquette j)) := by
  let f := fun p : PlaqAxes × Cover => if p.1=j then note M i p else 0
  change HasSum (f ∘ alphabet) _
  rw [alphabet.hasSum_iff,acts_point]
  have hw := M.roots.rights σ C h hσ
  have hv (x : PlaqAxes) : Summable (fun b : Cover => ‖f (x,b)‖) := by
    by_cases hx : x=j
    · simpa [f,hx,note] using hw (plaquette i) (plaquette j)
    simp [f,hx]
  have he : Summable fun i => ‖f i‖ := (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨hv,.of_finite⟩
  have hsum : ∑' b, f b = ∑' b, M.roots (plaquette i) (plaquette j) b := by
    rw [he.of_norm.tsum_prod,tsum_fintype,Finset.sum_eq_single j]
    · simp [f,note]
    · intro b _ h; simp [f,h]
    simp
  rw [← hsum]; exact he.of_norm.hasSum

lemma read_zero (M : Bed) : ∀ a b, M.metric.read 0 a b = ((M.metric.acts 1 (0,a) (0,b) : ℝ) : ℂ) := by
  intro a b
  rw [acts_point,Complex.ofReal_tsum]
  simp only [Row.read,Matrix.of_apply,Laurent.read,mode_constant,one_smul]

lemma metric_point (M : Bed) (h : M.metric.read 0=1) (i j : PlaqAxes) :
    M.metric.acts 1 (0,plaquette i) (0,plaquette j) = if i=j then 1 else 0 := by
  have H := read_zero M (plaquette i) (plaquette j); simp only [h, Matrix.one_apply,plaq_iff] at H
  split <;> rename_i he <;> simp only [he,if_true,if_false] at * <;> exact_mod_cast H.symm

lemma scribe_metric (M : Bed) (W : PathData G) {σ C} (h : M.covered σ C) (hσ : 0 ≤ σ) {c : Clip} {η A}
    (hg : Floor M c 1 η A) : (scribe M W).metric_zero c := by
  intro i j
  have hh := Free.full_cover M c 1; rw [hg.roots] at hh
  have H := congr_fun (congr_fun hh (0,plaquette i)) (0,plaquette j)
  simp_rw [PathData.symbol0, (scribe_symbol M W h.2.2.2.1 hσ _ _).tsum_eq]
  rw [metric_point M hg.starts] at H
  rw [H, Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply]
  have hg := Equiv.sum_comp plaqEquiv (fun y => M.roots.acts 1 (0,y) (0,plaquette i) * M.roots.acts 1 (0,y) (0,plaquette j))
  have hs : c.direct * (if i=j then 1 else 0) = if i=j then c.direct else 0 := by split <;> simp
  simp only [Prod.mk.injEq,true_and, plaq_iff,hs,smul_eq_mul,Matrix.mul_apply, Matrix.transpose_apply,Fintype.sum_prod_type]
  rw [Fintype.sum_subsingleton _ (0 : Site 1),← hg]; rfl


end YM.Progress.Joint

namespace YM.Progress.Joint
open RG Precision Next Next.Scheduling Lattice Filter
open scoped Topology BigOperators
variable {G : Gauge}

/-! ## Bills for the remaining curvature coefficients -/
lemma walk_bound (w : Walk) (a : Axis) (x : Cover) : (Lattice.stop x w a - x a).natAbs ≤ w.length := by
  induction w generalizing x with
  | nil => simp [Lattice.stop]
  | cons d w ih =>
    have hh := ih (x+d.vec)
    unfold Step.vec at hh
    simp only [Lattice.stop,List.length_cons]
    unfold Step.vec
    cases hd : d.neg <;> by_cases ha : a=d.dir <;> simp [hd,ha] at * <;> omega

lemma leg_bound {k : ℕ} (A : Atom G k) (i : Fin k) (a : Axis) : ((A.leg i).offset a).natAbs ≤ A.length := by
  have hi := walk_bound (A.leg i).walk a 0
  rw [Pi.zero_apply,sub_zero] at hi
  apply (hi.trans (Nat.le_add_right _ 4)).trans
  exact Finset.single_le_sum (f:=fun i => (A.leg i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma loop_moments (W : PathData G) {σ Λ : ℝ} (hσ : 0 < σ) (h : SumBudget (fun i => (W.loop i).budget σ) Λ)
    (p x) : Summable (W.loop_coeff p x) ∧ ∀ l : Axis,
      Summable fun k => W.loop_coeff p x k * ((((W.loop k).leg 1).offset l - ((W.loop k).leg 0).offset l : ℤ) : ℝ) := by
  have hb i : ‖W.loop_coeff p x i‖ ≤ (W.loop i).magnitude := by
    unfold PathData.loop_coeff Atom.magnitude; rw [Real.norm_eq_abs]
    split
    · exact Finset.single_le_sum (f:=fun j => |(W.loop i).coeff j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    rw [abs_zero]; positivity
  refine ⟨Summable.of_norm_bounded h.2.1 (fun i => (hb i).trans ((W.loop i).lower_budget σ hσ)),fun l => ?_⟩
  refine Summable.of_norm_bounded (h.2.1.mul_left (2/σ)) (fun i => ?_)
  let A := W.loop i; let z : ℝ := (↑((A.leg 1).offset l - (A.leg 0).offset l) : ℝ)
  have ht : ∀ k, |((A.leg k).offset l : ℝ)| ≤ A.length := by
    intro k; exact_mod_cast (show |(A.leg k).offset l| ≤ (A.length:ℤ) by have := leg_bound A k l; rw [abs_le]; omega)
  have hz : ‖z‖ ≤ 2*(A.length : ℝ) := by
    obtain ⟨h1,h2⟩ := abs_le.mp (ht 1); obtain ⟨h3,h4⟩ := abs_le.mp (ht 0)
    unfold z; push_cast; rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [norm_mul]; change _*‖z‖ ≤ _
  refine (mul_le_mul (hb i) hz (norm_nonneg _) (le_trans (norm_nonneg _) (hb i))).trans ?_
  change A.magnitude * _ ≤ _*A.budget σ
  unfold Atom.budget; rw [mul_left_comm (2/σ)]; apply mul_le_mul_of_nonneg_left _ (le_trans (norm_nonneg _) (hb _))
  have he := Real.add_one_le_exp (σ*A.length)
  rw [div_mul_eq_mul_div,le_div_iff₀ hσ]; linarith

structure Charges (W : PathData G) (σ C Λ : ℝ) : Prop where
  two : SumBudget (fun i ↦ (W.loop i).budget σ) Λ
  three : SumBudget (fun i ↦ (W.cubic i).budget σ) C
  four : SumBudget (fun i ↦ (W.quartic i).budget σ) C
  invariant (i : ℕ) : (W.loop i).Invariant ∧ (W.cubic i).Invariant ∧ (W.quartic i).Invariant
  jets : W.loop_jets

lemma charged (M : Bed) (W : PathData G) {K : MapPrices} {j σ C Λ} (hσ : 0 < σ)
    (h : M.covered (K.α j) (K.Ω j)) (ht : σ ≤ K.α j) (h₁ : σ ≤ 1) {c : Clip} {η A}
    (hg : Floor M c 1 η A) (hb : rowBill K j ≤ C) (hh : Charges W σ C Λ) :
    (scribe M W).Bounds c σ C Λ := by
  have hp := K.alpha_pos j
  exact ⟨hσ,fun i => ⟨(scribe_price M W h ht h₁ i).1,(scribe_price M W h ht h₁ i).2.1,(scribe_price M W h ht h₁ i).2.2.trans hb⟩,
    hh.two,hh.three,hh.four, hh.invariant, fun i j => (scribe_symbol M W h.2.2.2.1 hp.le i j).summable,
    scribe_metric M W h hp.le hg, loop_moments W hσ hh.two,hh.jets⟩

def silence (G : Gauge) : PathData G := by
  let s := script (⟨(0,1),by decide⟩,0)
  let A k (_i : ℕ) : Atom G k := ⟨fun _ => s,0⟩
  exact ⟨fun _ _ => (0,s),A 2,A 3,A 4⟩

/-- Test/nonlinear base, NOT claiming that zero atom corrections give
matching (even at the Wilson top). -/
lemma muted {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 ≤ Λ) (σ : ℝ) : Charges (silence G) σ C Λ := by
  constructor
  all_goals simp [SumBudget,silence,Atom.budget,Atom.magnitude,Atom.Invariant,Atom.poly,PathData.loop_jets,PathData.loop_coeff, hC,hΛ]

/-! ## Actual pricing ingredients for Quote -/

/-- Reserve the linear widths besides some additional POSITIVE rates
supplied as attainable for *the other operations*. Loads may be replaced
later e.g. using final widths without changing width. -/
def drawing (K : MapPrices) (s : Strips) : Strips := { s with
  launch := fun i => min (K.α i) (min 1 (s.launch i))
  emits := fun j i => min (K.α i) (min 1 (s.emits j i))
  top_rate := fun i => lt_min (K.alpha_pos _) (lt_min zero_lt_one (s.top_rate i))
  rate := fun j i => lt_min (K.alpha_pos _) (lt_min zero_lt_one (s.rate j i)) }

def ink (K : MapPrices) (r : Figures) : Figures where
  beginCost i := max (rowBill K i) (r.beginCost i)
  classic j i := max (rowBill K i) (r.classic j i)
  pos i := le_max_of_le_right (r.pos i)
  pos_ij i j := le_max_of_le_right (r.pos_ij i j)

structure Designing (K : MapPrices) (q : Quote) : Prop where
  launch i : q.widths.launch i ≤ K.α i ∧ q.widths.launch i ≤ 1
  emits j i : Adj j i → q.widths.emits j i ≤ K.α i ∧ q.widths.emits j i ≤ 1
  beginCost i : rowBill K i ≤ q.classicalCost.beginCost i
  classic j i : Adj j i → rowBill K i ≤ q.classicalCost.classic j i



open RG.Supply
variable {K : MapPrices} {s : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {T : Protection D} {V : Delays T} {Y : Bar V} {I : Wait Y} {a : Levels G} {H : Horizon a}

lemma Designing.scripted (h : Designing K q) (ha : Paid I a) (hf : H.Suffices K) {m N : ℕ} (hm : m ≤ N) (W : PathData G)
    (hW : Charges W (a.params m).width (a.params m).paths (a.clock.loopCap m)) :
    (scribe (H.H N m) W).Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m) := by
  refine charged _ _ (a.params m).width_pos (hf.rows N m hm) ?_ ?_ (hf.all N m hm 1) ?_ hW
  all_goals rw [Deployment.params ha m]
  · exact (q.widths.le_top _).trans (h.launch _).1
  · exact min_le_left ..
  exact (h.beginCost _).trans (q.classicalCost.le_top _)

/-- Actual simultaneous analytic base presentations; can choose uniformly on
all depths and still at widths compatible with provisional top/next costs.
Includes harmonic normalization and no volume factor. Fill other arrays
with `charged` as constructed later; zero is not a nonlinear invoice. -/
lemma Designing.display (h : Designing K q) (ha : Paid I a) (hf : H.Suffices K) :
    ∃ W : ℕ → ℕ → PathData G, ∀ N m,m≤N → Attached (H.H N m) (W N m) ∧
      (W N m).Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m) ∧
      ∀ i,((W N m).cubic i).coeff=0 ∧ ((W N m).quartic i).coeff=0 ∧ ((W N m).loop i).coeff=0 := by
  have hl m : 0 ≤ a.clock.loopCap m := by unfold Calendar.loopCap Calendar.monitor; positivity
  exact ⟨fun N m => scribe (H.H N m) (silence G),fun N m hm => ⟨scribe_attached ..,
    h.scripted ha hf hm _ (muted (a.params m).paths_pos.le (hl m) _),fun _ => ⟨rfl,rfl,rfl⟩⟩⟩

end YM.Progress.Joint
