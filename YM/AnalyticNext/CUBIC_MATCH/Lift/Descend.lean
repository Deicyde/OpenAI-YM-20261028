import YM.AnalyticNext.CUBIC_MATCH.Lift.Boundary
import YM.Next.FREE_KERNELS.Lifts

set_option warningAsError false

/-!
# Periodization of the three-leg problem, including column tests

Coefficients keep their prescribed universal values, even at coinciding
points, noncanonical base points, period one. `downX/Y/Z` include the
nonprojected origin and keep any exterior-type arguments. This is about
actual counting cochains on the full periodic lattice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter RG Supply Precision Lattice Wilson Tree Exterior Matrix Bloch Laurent Lift
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {r s t : ℕ} {n : Side} {D E : Type*}
variable [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [CompleteSpace D] [NormedSpace ℝ D] {η C : ℝ}

def squeeze (n : Side) : Couple →+ Site n × Site n := (wrap n).prodMap (wrap n)

def same (u : Couple → E) (a : Site n × Site n) (x : Couple) := if squeeze n x=a then u x else 0

def unroll (u : Couple → E) (a : Site n × Site n) := ∑' x, same u a x

/-- Anchored coefficient, read the *full* periodic tensor. -/
def acts (n : Side) (K : Three E r s t) (x : Body r n) (y : Body s n) (z : Body t n) : E :=
    unroll (K x.2 y.2 z.2) (x.1-z.1, y.1-z.1)

omit [CompleteSpace E] [NormedSpace ℝ E] in
lemma same_norm {u : Couple → E} (hu : Summable fun i => ‖u i‖) (a : Site n × Site n) :
    Summable fun x => ‖same u a x‖ :=
  hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by unfold same; split <;> simp)

omit [CompleteSpace D] in
lemma unroll_map (L : E →L[ℝ] D) {u : Couple → E} (hu : Summable fun i => ‖u i‖)
    (a : Site n × Site n) : unroll (L ∘ u) a = L (unroll u a) := by
  rw [unroll,unroll,L.map_tsum (same_norm hu a).of_norm]; refine tsum_congr fun i => ?_
  unfold same; split
  · rfl
  simp only [map_zero]

/-- Periodization commutes with even the moving anchors in a coboundary.
Only apply this *after* having obtained a joint width on the kernel. -/
lemma clipped {A : Line Couple E (r+1)} (p : ∀ i, Decay length2 η C (A i)) (he : 0<η)
    (w : Axis → Couple) (j : TypeFace r) (v : Site n × Site n) :
    unroll (bite w A j) v = bite (fun a => squeeze n (w a)) (fun i => unroll (A i)) j v := by
  have H (k) : Summable fun z => ‖A k z‖ := (p k).summable_norm (summable_two he)
  let X k i x := if squeeze n x=v then A k (x-w i) else 0
  have hs k a : Summable fun z => ‖A k (z-w a)‖ := by
    simp_rw [sub_eq_add_neg]; exact (Equiv.addRight (-w a)).summable_iff.mpr (H k)
  have hx k i : Summable (X k i) := (same_norm (hs k i) v).of_norm
  have hp k : Summable (same (A k) v) := (same_norm (H k) v).of_norm
  have hg k i : (∑' x, X k i x)=unroll (A k) (v-squeeze n (w i)) := by
    rw [← (Equiv.addRight (w i)).tsum_eq]; unfold unroll
    refine tsum_congr fun b => ?_
    change (if squeeze n (b+w i)=v then A k (b+w i-w i) else 0) = _
    simp only [same,map_add,add_sub_cancel_right]
    simp only [eq_sub_iff_add_eq]
  have hc (k i) := ((hx k i).sub (hp k)).const_smul (left ℝ r i k j)
  change ∑' x, same _ v x = _
  rw [show same (bite w A j) v=fun x => ∑ i : TypeFace (r+1),
    ∑ a : Axis, left ℝ r a i j • (X i a x-same (A i) v x) from ?eq, Summable.tsum_finsetSum]; swap
  · exact fun i _ => summable_sum (fun j _ => show Summable _ from hc i j)
  unfold bite; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum]; swap
  · exact fun j _ => hc _ _
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tsum_const_smul'', (hx i a).tsum_sub (hp i),hg]; rfl
  case eq => funext x; unfold bite; by_cases hh : squeeze n x=v <;> simp [same,X,hh]

omit [CompleteSpace E] in
/-- transpose against a column indexed by *any* exterior type. -/
lemma column (i : Body r n) (A : TypeFace (r+1) → Site n → E) :
    (∑ j : Body (r+1) n, d r n j i • A j.2 j.1)=bite step A i.2 i.1 := by
  rcases i with ⟨x,i⟩; unfold bite
  simp_rw [d, acts_apply,Fintype.sum_prod_type]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [Finset.sum_smul]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he (z : Site n) : x=z+step a ↔ z=x-step a := by rw [eq_sub_iff_add_eq,eq_comm]
  simp_rw [he,mul_sub, sub_smul, mul_ite, ite_smul, mul_one,mul_zero,zero_smul]
  simp [Finset.sum_sub_distrib,smul_sub]

lemma downX {K : Three E (r+1) s t} (h : Pace η C K) (he : 0<η) (i j l) :
    acts n (δx K) i j l=∑ x : Body (r+1) n, d r n x i • acts n K x j l := by
  let A a := K a j.2 l.2
  rw [show (∑ x : Body (r+1) n, _)=_ from column i (fun b x => acts n K (x,b) j l)]
  rw [acts,δx,clipped (A:=A) (fun k => h k j.2 l.2) he]; unfold bite
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show (i.1-l.1,j.1-l.1)-squeeze n (aheadX a)=(i.1-step a-l.1,j.1-l.1) from ?_]; rfl
  ext1
  · change i.1-l.1-wrap n (step a)=_; rw [wrap_step,sub_right_comm]
  change j.1-l.1-wrap n 0=_; rw [map_zero,sub_zero]
lemma downY {K : Three E r (s+1) t} (h : Pace η C K) (he : 0<η) (i j l) :
    acts n (δy K) i j l=∑ x : Body (s+1) n, d s n x j • acts n K i x l := by
  let A a := K i.2 a l.2
  rw [show (∑ x : Body (s+1) n, _)=_ from column j (fun b x => acts n K i (x,b) l)]
  rw [acts,δy,clipped (A:=A) (fun k => h i.2 k l.2) he]; unfold bite
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show (i.1-l.1,j.1-l.1)-squeeze n (aheadY a)=(i.1-l.1,j.1-step a-l.1) from ?_]; rfl
  ext1
  · change i.1-l.1-wrap n 0=_; rw [map_zero,sub_zero]
  change j.1-l.1-wrap n (step a)=_; rw [wrap_step,sub_right_comm]
lemma downZ {K : Three E r s (t+1)} (h : Pace η C K) (he : 0<η) (i j l) :
    acts n (δz K) i j l=∑ x : Body (t+1) n, d t n x l • acts n K i j x := by
  rw [show (∑ x : Body (t+1) n, _)=_ from column l (fun b x => acts n K i j (x,b))]
  rw [acts,δz,clipped (h i.2 j.2) he]; unfold bite
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show (i.1-l.1,j.1-l.1)-squeeze n (behind a)=(i.1-(l.1-step a),j.1-(l.1-step a)) from ?_]; rfl
  ext1
  · change i.1-l.1-wrap n (-step a)=_; rw [map_neg,wrap_step]; dsimp only; abel_nf
  change j.1-l.1-wrap n (-step a)=_; rw [map_neg,wrap_step]; dsimp only; abel_nf

omit [NormedSpace ℝ E] in
lemma entry_value {u : Couple → E} (h : Summable fun i => ‖u i‖) (z : ℕ → Side)
    (hz : Tendsto (fun i => (z i).val) atTop atTop) (x : Couple) :
    Tendsto (fun i => unroll u (squeeze (z i) x)) atTop (𝓝 (u x)) := by
  let f i a := same u (squeeze (z i) x) a
  let g a := if a=x then u a else 0
  have he a : Tendsto (fun i => f i a) atTop (𝓝 (g a)) := by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [Next.Free.eventually_unfold z hz x.1, Next.Free.eventually_unfold z hz x.2,
      Next.Free.eventually_unfold z hz a.1, Next.Free.eventually_unfold z hz a.2] with i h1 h2 h3 h4
    by_cases hy : a=x
    · simp [hy,f,g,same]
    have hh : squeeze (z i) a ≠ squeeze (z i) x := fun e => hy (Prod.ext
      (h3.symm.trans ((congr_arg (fun q : Site (z i) × Site (z i) => lift q.1) e).trans h1))
      (h4.symm.trans ((congr_arg (fun q : Site (z i) × Site (z i) => lift q.2) e).trans h2)))
    simp [hy, hh,f,g,same]
  have hs := tendsto_tsum_of_dominated_convergence h he (Eventually.of_forall (fun i a => show ‖f i a‖ ≤ _ by unfold f same; split <;> simp))
  rw [show ∑' i,g i=u x by simp [g]] at hs; exact hs

omit [CompleteSpace D] in
lemma unroll_sum_apply (a : Couple → E) (ha : Summable fun i => ‖a i‖)
    (v : (Site n × Site n) → E →L[ℝ] D) :
    ∑ t : Site n × Site n, v t (unroll a t)=∑' i,v (squeeze n i) (a i) := by
  let f t i := v t (same a t i)
  have he t : Summable (f t) := ((v t).hasSum (same_norm ha t).of_norm.hasSum).summable
  calc
    _ = ∑ t, ∑' i,f t i := Finset.sum_congr rfl fun i _ => (v i).map_tsum (same_norm ha i).of_norm
    _ = ∑' i,∑ t,f t i := (Summable.tsum_finsetSum (fun i _ => he i)).symm
    _ = _ := tsum_congr fun i => by
      rw [Finset.sum_eq_single (squeeze n i)]
      · simp [f,same]
      · intro b _ h; simp only [f,same, if_neg h.symm, map_zero]
      simp
end YM.CubicMatch
