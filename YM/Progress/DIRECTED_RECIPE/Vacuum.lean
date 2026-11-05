import YM.Progress.DIRECTED_RECIPE.EvalBounds

/-!
# Don't assume the evaluation continuous on a baked Curve

Prove the parameter variation, in sup norm across all fields despite
hard tests. Here still at one period/configuration size. Does not evaluate
new families or solve β reset. Does not require global continuity of E or
K across fields (though the whole eval of a surviving history will turn out
to have nice properties separately). This continuity uses actual `Lives`
identity path and Clip channels. Even using subsequences in later estimates,
it is on this SAME family's field density and tag distributions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius

/-- A uniform fixed-point parameter notion across all V. -/
def Varies {U : Type*} (f : ℝ → U → ℝ) (x : ℝ) (T : Set ℝ) :=
    ∀ ε : ℝ, 0<ε → ∀ᶠ y in 𝓝[T] x, ∀ v, ‖f x v - f y v‖ ≤ ε

section var
variable {U : Type*} {f g : ℝ → U → ℝ} {x : ℝ} {T : Set ℝ}
namespace Varies
lemma pure {a : ℝ → ℝ} (h : ContinuousWithinAt a T x) : Varies (fun y (_ : U) => a y) x T := by
  intro ε he; filter_upwards [Metric.tendsto_nhds.mp h ε he] with y hy u
  rw [dist_comm, dist_eq_norm] at hy; exact hy.le

lemma fixed (F : U → ℝ) : Varies (fun _ => F) x T := fun _ he => Eventually.of_forall fun y v => by simp [he.le]

lemma add (h : Varies f x T) (hp : Varies g x T) : Varies (fun x u => f x u + g x u) x T := by
  intro ε he; filter_upwards [h (ε/2) (half_pos he),hp (ε/2) (half_pos he)] with y hy hy' u
  calc
    _ = ‖(f x u-f y u)+(g x u-g y u)‖ := by ring_nf
    _ ≤ ε/2+ε/2 := (norm_add_le ..).trans (add_le_add (hy u) (hy' u))
    _ = ε := by ring

lemma neg (h : Varies f x T) : Varies (fun x u => -f x u) x T := by
  intro ε he; filter_upwards [h ε he] with y hy u
  rw [neg_sub_neg,norm_sub_rev]; exact hy u
lemma sub (h : Varies f x T) (hp : Varies g x T) : Varies (fun x u => f x u-g x u) x T := by
  simp only [sub_eq_add_neg]; exact h.add hp.neg

variable [Nonempty U]
lemma product (h : Varies f x T) (hp : Varies g x T) {C D : ℝ}
    (hc : ∀ v, ‖f x v‖ ≤ C) (hd : ∀ v, ‖g x v‖ ≤ D) : Varies (fun x u => f x u * g x u) x T := by
  intro ε he
  have hzD := (norm_nonneg _).trans (hd (Classical.arbitrary U))
  have hzC := (norm_nonneg _).trans (hc (Classical.arbitrary U))
  let A := C+(1+D)
  have ha : 0<A := by unfold A; linarith
  let z := min 1 (ε/A)
  have hz : 0<z := lt_min zero_lt_one (div_pos he ha)
  filter_upwards [h z hz, hp z hz] with y hy hv u
  have hx : ‖g y u‖ ≤ 1+D := calc
    _ ≤ ‖g x u - g y u‖+‖g x u‖ := by
      rw [norm_sub_rev]; simpa only [sub_add_cancel] using norm_add_le (g y u - g x u) (g x u)
    _ ≤ _ := add_le_add ((hv _).trans (min_le_left ..)) (hd u)
  calc
    _ = ‖f x u*(g x u-g y u)+(f x u-f y u)*g y u‖ := by ring_nf
    _ ≤ ‖f x u*(g x u-g y u)‖ + ‖(f x u-f y u)*g y u‖ := norm_add_le ..
    _ ≤ C*z + z*(1+D) := by
      rw [norm_mul,norm_mul]; exact add_le_add
        (mul_le_mul (hc u) (hv u) (norm_nonneg _) hzC) (mul_le_mul (hy _) hx (norm_nonneg _) hz.le)
    _ = z*A := by unfold A; ring
    _ ≤ _ := (le_div_iff₀ ha).mp (min_le_right ..)

omit [Nonempty U] in
lemma exp (h : Varies f x T) {C : ℝ} (hc : ∀ v, Real.exp (f x v) ≤ C) (hC : 0<C) :
    Varies (fun x u => Real.exp (f x u)) x T := by
  intro ε he
  let z := min (ε/(2*C)) 1
  have hz : 0<z := lt_min (by positivity) zero_lt_one
  filter_upwards [h z hz] with y hy u
  have hu : |f y u - f x u| ≤ z := by
    rw [abs_sub_comm]; exact hy _
  calc
    _ = ‖(Real.exp (f y u-f x u)-1) * Real.exp (f x u)‖ := by
      rw [norm_sub_rev, sub_mul, ← Real.exp_add, sub_add_cancel, one_mul]
    _ ≤ 2*z*C := by
      rw [norm_mul]; exact mul_le_mul ((Real.abs_exp_sub_one_le (hu.trans (min_le_right ..))).trans
        (mul_le_mul_of_nonneg_left hu (by norm_num))) ((Real.norm_of_nonneg (Real.exp_pos _).le).trans_le (hc u))
        (norm_nonneg _) (by positivity)
    _ = z*(2*C) := by ring
    _ ≤ ε := (le_div_iff₀ (by positivity : (0:ℝ)<2*C)).mp (min_le_left ..)

omit [Nonempty U] in
lemma on_domain (h : Varies f x T) (hx : x∈T) (he : EqOn g f T) : Varies g x T := by
  intro ε hp; filter_upwards [self_mem_nhdsWithin, h ε hp] with y hy ht u
  rw [he hx,he hy]; exact ht u
end Varies
end var

variable {G : Gauge} {n : Side} {P : BudgetPoint}
lemma activities_motion {T : Set ℝ} {x : ℝ} (hx : x∈T) {Q : ℝ → Rep G n} (H : Curve P Q T)
    {δ w : ℝ} (hv : ∀ y∈T, (Q y).activities.Valid P δ w) :
    Varies (fun y => (Q y).activities.additive P) x T ∧ Varies (fun y => (Q y).activities.gas P) x T := by
  let A y := (Q y).activities
  obtain ⟨b,hb,hp⟩ := Activities.K_total (hv x hx).boundK
  let C := ∑' j, b j
  have ht : SumBudget b C := ⟨fun j => (hp j).1,hb,le_rfl⟩
  have he ε (he : 0<ε) : ∀ᶠ y in 𝓝[T] x, ∀ U, ‖(A x).additive P U-(A y).additive P U‖ ≤ ε ∧
      ‖(A x).gas P U-(A y).gas P U‖ ≤ Real.exp C*(Real.exp ε-1) := by
    filter_upwards [self_mem_nhdsWithin,H.continuous ε he x hx] with y hy hw U
    exact Payment.rep_perturb (hv x hx) (hv y hy) (H.reg x hx y hy) (H.forced x hx y hy) ht
      (fun i => (hp i).2) hw U
  refine ⟨fun ε hx => (he ε hx).mono fun y hy u => (hy u).1,?_⟩
  intro ε hε
  let D := Real.exp C
  have hf : 0<D := Real.exp_pos _
  let z := min (ε/(2*D)) 1
  have hz : 0<z := lt_min (by positivity) zero_lt_one
  filter_upwards [he z hz] with y hy u
  apply (hy u).2.trans
  have hm := Real.abs_exp_sub_one_le (x:=z) (by rw [abs_of_pos hz]; exact min_le_right ..)
  rw [abs_of_pos hz] at hm
  calc
    _ ≤ D * (2*z) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hm) hf.le
    _ = z * (2*D) := by ring
    _ ≤ ε := (le_div_iff₀ (by positivity : 0 < 2*D)).mp (min_le_left ..)

private lemma channels_linear (W : PathData G) (b : Clip) (P : BudgetPoint) (β : ℝ) (U : Config G n) :
    W.inChannels b P β U = β * (W.inChannels b P 1 U-W.inChannels b P 0 U) + W.inChannels b P 0 U := by
  have ht (i : Config G n) := (show W.principal b P β i = β*(W.principal b P 1 i-W.principal b P 0 i)+W.principal b P 0 i by
    unfold PathData.principal; ring)
  unfold PathData.inChannels
  rw [show (∑ s : Signed, W.principal b P β (pull s 0 U)) =
    ∑ s : Signed, (β*(W.principal b P 1 (pull s 0 U)-W.principal b P 0 (pull s 0 U))+W.principal b P 0 (pull s 0 U)) from
    Finset.sum_congr rfl fun _ _ => ht _, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]; ring

/-- Fixed volume, no inverse-gas uniformity throughout the campaign. -/
lemma eval_varies {T : Set ℝ} {x : ℝ} (hx : x∈T) {Q : ℝ → Rep G n} (H : Curve P Q T)
    {δ w m u v} {W : PathData G} {c : Clip} (Hv : ∀ y∈T, (Q y).Lawful m u v δ w)
    (Hb : ∀ y∈T, (Q y).p = P) (Hc : ∀ y∈T, (Q y).clip=c) (Hw : ∀ y∈T, (Q y).path=W) :
    Varies (fun y => (Q y).eval) x T := by
  have Hp y (hy : y∈T) : (Q y).activities.Valid P δ w := Hb y hy ▸ (Hv y hy).labels
  obtain ⟨hA,hK⟩ := activities_motion hx H Hp
  have hW : W.Bounds c m u v := by
    have hz := (Hv x hx).paths; rwa [Hc x hx,Hw x hx] at hz
  let f := fun y (U : Config G n) => (Q y).beta * (W.inChannels c P 1 U-W.inChannels c P 0 U) + W.inChannels c P 0 U
  have hf : Varies f x T := by
    obtain ⟨C,hC⟩ := (PathData.channels_env (n:=n) hW P 1).cost
    obtain ⟨D,hD⟩ := (PathData.channels_env (n:=n) hW P 0).cost
    have ht := Varies.pure (U:=Config G n) (H.beta x hx)
    refine Varies.add (Varies.product (U:=Config G n) ht (Varies.fixed (U:=Config G n) _)
      (C:=‖(Q x).beta‖) (fun _ => le_rfl) (D:=C+D) ?_) (Varies.fixed (W.inChannels c P 0))
    exact fun i => (norm_sub_le ..).trans (add_le_add (hC _) (hD i))
  have ht : Varies (fun y => (Q y).exponent) x T := by
    have hm : Varies (fun y (_ : Config G n) => (Q y).v * Fintype.card (Site n)) x T :=
      Varies.pure ((H.v x hx).mul_const _)
    refine Varies.on_domain ((hm.sub hf).sub hA) hx (fun y hy => ?_)
    funext U; unfold Rep.exponent; simp only [Hb y hy,Hc y hy,Hw y hy]
    -- targeted at the varies hypothesis, same mask in both orientations
    rw [channels_linear]
  let gx (y : ℝ) (U : Config G n) := Real.exp ((Q y).exponent U)
  obtain ⟨C,hC⟩ := ((Q x).exponentEnv (Hv x hx)).exp.cost
  have hc : 0 < C := lt_of_lt_of_le (norm_pos_iff.mpr (Real.exp_pos _).ne') (hC 1)
  have hs : Varies gx x T := Varies.exp ht (fun i => (Real.norm_of_nonneg (Real.exp_pos _).le).ge.trans (hC i)) hc
  obtain ⟨D,hD⟩ := (Activities.gasSeries (Hv x hx).labels).bound
  have H : Varies (fun i U => gx i U * (Q i).activities.gas P U) x T :=
    hs.product hK hC (D:=D) (fun i => by rw [← Hb x hx]; exact hD i)
  refine H.on_domain hx ?_
  intro y hy; funext U; simp only [Rep.eval,gx,Hb y hy]
end YM.Progress.DirectedRecipe
