import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Forests
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Fused


/-!
# Exact interpolation-tree identity

Contributions indexed by honest parent maps on T alone. Avoid permutation
quotients; recursion *inside* a tree includes all choices of attachment
order, as well as all counting coordinates at both ends of every edge. For
the tree bound that follows take the norm `inside` also.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Filter Set Function Finset Marker
open YM.Multi.Vacuum.Gauss Probe Grove Fused Moment Spin
open scoped Topology BigOperators Interval

variable {V I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq V]
namespace Expansion

section calculus
variable {E : Type} [NormedCommRing E] [NormedAlgebra ℝ E]

/-- T is the whole marker occurrence set. n counts the nonroot vertices
still to be included, A is the root group. Each step selects one more
vertex j adjacent to that group in the given tree, interpolates the cross
covariances once and charges one derivative at each end. Earlier time
parameters affect the later bond prices through the path covariance; don't
reset them after performing a new attachment. -/
def report (T : Finset V) (L : ℂ → E) (n : ℕ) {J : Type} [Fintype J] (A : Finset V)
    (f : Parent V) (q : Rows V I J) (v : Probes V I) : E :=
  match n with
  | 0 => ∫ x,L (values T q v x) ∂standard J
  | k+1 => ∑ j∈buds T A f,∑ a,∑ b,∫ x in 0..high,
      L (currency q x (f j) a j b) * report T L k (insert j A) (cut f j) (path A q x) (marked (marked v (f j) a) j b)
termination_by n

omit [Fintype I] [DecidableEq I] [Fintype J] in
private lemma path_cont {S : Type} [TopologicalSpace S] (A : Finset V) (i : V) (a : I)
    (u : S → Rows V I J) (he : Continuous fun t => u t i a) :
    Continuous (fun p : S × ℝ => path A (u p.1) p.2 i a) := by
  unfold path; split
  · apply continuous_pi; intro j
    have hh (k : J) : Continuous (fun p : S × ℝ => u p.1 i a k) :=
      (continuous_apply k).comp (he.comp continuous_fst)
    cases j with
    | inl k => exact (Real.continuous_sin.comp continuous_snd).smul (hh k)
    | inr k => exact (Real.continuous_cos.comp continuous_snd).smul (hh k)
  apply continuous_pi; intro j
  have hh (k : J) : Continuous (fun p : S × ℝ => u p.1 i a k) :=
    (continuous_apply k).comp (he.comp continuous_fst)
  cases j with
  | inl k => exact Continuous.smul (continuous_const (y:=(1:ℝ))) (hh k)
  | inr k => exact Continuous.smul (continuous_const (y:=(0:ℝ))) (hh k)

omit [Fintype I] [DecidableEq I] [DecidableEq V] in
private lemma currency_cont {S : Type} [TopologicalSpace S] (q : S → Rows V I J) {i j : V} {a b : I}
    (h : Continuous fun t => q t i a) (hh : Continuous fun t => q t j b) :
    Continuous (fun p : S × ℝ => currency (q p.1) p.2 i a j b) := by
  unfold currency crossed
  apply Continuous.comp Complex.continuous_ofReal
  exact Continuous.mul (Real.continuous_cos.comp continuous_snd) (continuous_finsetSum _ fun x _ =>
    ((continuous_apply x).comp (h.comp continuous_fst)).mul ((continuous_apply x).comp (hh.comp continuous_fst)))

/-- Authenticate report also at each intermediate law. `L` used only to
read values or norms. Continuity proves all intermediate integrabilities;
no composed change at endpoints by continuity unless each part paid for. -/
lemma report_continuous (T : Finset V) (L : ℂ → E) (he : Continuous L) (hl : ∀ x,‖L x‖ ≤ ‖x‖) (n : ℕ) :
    ∀ {J S : Type} [Fintype J] [TopologicalSpace S] [FirstCountableTopology S]
    (A : Finset V), A⊆T → ∀ f : Parent V, Good T A f →
    ∀ (q : S → Rows V I J) (v : Probes V I) (w : V → Row I) (H : V → ℕ → ℝ),
    Valid T n v w H → (∀ i∈T, ∀ a : I, Continuous fun t => q t i a) → (∀ t,base (q t) T w) →
    Continuous (fun t => report T L n A f (q t) v) := by
  induction n with
  | zero =>
    intro J S _ _ _ A ha f hf q v w H hq h hC
    let F := fun t => values T (q t) v
    have hc t : Continuous (F t) := values_continuous hq.read _
    have hv (x : Row J) : Continuous (fun t => F t x) := by
      apply continuous_finsetProd
      intro i hi
      apply Continuous.comp (hq.read i hi)
      apply continuous_pi; intro a; change Continuous fun t => crossed (q t i a) x
      simp_rw [crossed_comm _ x]; exact (crossed_cont _).comp (h i hi a)
    let U := Set.univ (α:=S)
    have hr := values_growth U q (Finset.Subset.refl _) hq
    have hp : Growth U (fun t => sumCharge T (q t) w) (fun t x => L (F t x)) := by
      obtain ⟨k,C,hc,ht⟩ := hr; exact ⟨k,C,hc,fun t ht' x => (hl _).trans (ht t ht' x)⟩
    simp only [report]
    exact continuousOn_univ.mp (hp.continuity (works U q (Finset.Subset.refl _) (fun t _ => hC t))
      (fun t _ => he.comp (hc t)) (fun x => (he.comp (hv x)).continuousOn))
  | succ k ih =>
    intro J S _ _ _ A ha f hf q v w H hq h hC
    simp only [report]; refine continuous_finsetSum _ fun j hj => continuous_finsetSum _ fun a _ =>
      continuous_finsetSum _ fun b _ => ?_
    let B := insert j A
    let i := f j
    let V' := marked (marked v i a) j b
    let P (t : S × ℝ) := path A (q t.1) t.2
    have hh := Buds.kids hj
    obtain ⟨hr,hτ⟩ := mem_sdiff.mp hh
    have hp : i∈A:= Buds.roots hj
    have ht : i≠j := by intro h; exact hτ (h ▸ hp)
    have hk := ih B (Finset.insert_subset hr ha) (cut f j) (hf.cut_at hh) P V' w _ (hq.double ht a b)
      (fun i hi a => path_cont A i a q (h i hi a)) (fun t => keeps A (q t.1) (hC t.1) t.2)
    let g t x := L (currency (q t) x i a j b) * report T L k B (cut f j) (P (t,x)) V'
    have hx : Continuous (uncurry g) := (he.comp (currency_cont q (h i (ha hp) a) (h j hr b))).mul hk
    have hb : Continuous (fun p : S × ℝ => ∫ t in (0:ℝ)..p.2,g p.1 t) :=
      intervalIntegral.continuous_parametric_primitive_of_continuous hx
    exact hb.comp (continuous_id.prodMk (continuous_const (y:=high)))

-- The simple precursor costs needed to commute integrations and finite sums.
lemma report_priceable (T A : Finset V) (L : ℂ → E) (he : Continuous L) (hl : ∀ x,‖L x‖ ≤ ‖x‖)
    (n : ℕ) {f : Parent V} (hf : Good T A f) (B : Finset V)
    (q : Rows V I J) (v : Probes V I) (w : V → Row I) (H : V → ℕ → ℝ) (ha : A⊆T)
    (h : base q T w) (hv : Valid T n v w H) (i j : V) (a b : I) :
    IntervalIntegrable (fun x => L (currency q x i a j b) * report T L n A f (path B q x) v) volume 0 high := by
  have hc := report_continuous T L he hl n A ha f hf (path B q) v w H hv
    (fun i _ a => continuous_iff_continuousAt.mpr fun t => (Spin.rate B q i a t).continuousAt)
    (fun t => keeps B q h t)
  exact ((he.comp (by unfold currency; fun_prop)).mul hc).intervalIntegrable 0 high
end calculus

private lemma priced_sum {ι : Type} (s : Finset ι) {g : ι → ℝ → ℂ}
    (h : ∀ i∈s, IntervalIntegrable (g i) volume 0 high) :
    IntervalIntegrable (fun x => ∑ i∈s, g i x) volume 0 high := by
  rw [show (fun x => ∑ i∈s, g i x) = ∑ i∈s,g i from funext fun x => (Finset.sum_apply ..).symm]
  exact IntervalIntegrable.sum _ h

variable [Fintype V] {R : Census V}

/-- Exact funded identity: only authenticate the submoments actually needed
for this marker. Quantity left is either the exact joint cumulant (for a
singleton A) including any non-Gaussian CONSTANT, or the fused ratio used
in proving it. -/
lemma detail (t : R.Mode) (n : ℕ) :
    ∀ {J : Type} [Fintype J] (A : Finset V) (_ha : A ⊆ t.val)
    (_hn : (t.val \ A).card=n) (q : Rows V I J) (v : Probes V I)
    (w : V → Row I) (H : V → ℕ → ℝ), base q t.val w → Valid t.val (n+1) v w H →
    mixed q v t A = ∑ f ∈ options t.val A, report t.val id n A f q v := by
  induction n with
  | zero =>
    intro J _ A ha hn q v w H h hv
    obtain rfl : A=t.val := Finset.Subset.antisymm ha (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hn))
    rw [done_mixed,options_self,sum_singleton,report]; rfl
  | succ n ih =>
    intro J _ A ha hn q v w H h hv
    have he : A≠t.val := by intro he; rw [he] at hn; simp at hn
    let X := t.val \ A
    let L j := insert j A
    let Q x := path A q x
    let V' (j i : V) (a b : I) := marked (marked v i a) j b
    let G (j i : V) (a b : I) (f : Parent V) x := currency q x i a j b * report t.val id n (L j) f (Q x) (V' j i a b)
    let m (j i : V) (a b : I) x := currency q x i a j b * mixed (Q x) (V' j i a b) t (L j)
    -- choose each child j outermost (before sum a)
    have hx (x : ℝ) : pipe q v t A x = ∑ j∈X,∑ i∈A,∑ a,∑ b,m j i a b x := by
      unfold pipe
      change ∑ i∈A,∑ a,∑ j∈X,∑ b,m j i a b x=_
      rw [sum_comm (s:=X) (t:=A)]
      apply sum_congr rfl; intro i _; exact sum_comm
    have hb j (hj : j∈X) : (L j ⊆ t.val) ∧ (t.val \ L j).card=n := by
      refine ⟨Finset.insert_subset (mem_sdiff.mp hj).1 ha,?_⟩
      unfold L; rw [leaves,card_erase_of_mem hj,hn]; simp
    have hp j (hj : j∈X) i (hi : i∈A) a b := hv.double (i:=i) (j:=j) (by intro e; exact (mem_sdiff.mp hj).2 (e ▸ hi)) a b
    have hm j (hj : j∈X) i (hi : i∈A) a b : m j i a b=fun x => ∑ f∈ options t.val (L j), G j i a b f x := by
      funext x
      unfold m G
      rw [ih (L j) (hb j hj).1 (hb j hj).2 (Q x) (V' j i a b) w _ (keeps A q h x) (hp j hj i hi a b),Finset.mul_sum]
    have ht j (hj : j∈X) i (hi : i∈A) a b f (hf : f∈ options t.val (L j)) :
        IntervalIntegrable (G j i a b f) volume 0 high := report_priceable t.val (L j) _ continuous_id (fun _ => le_rfl) n ((choices ..).1 hf) A q (V' j i a b) w _ (hb j hj).1 h ((hp j hj i hi a b).lower n.le_succ) i j a b
    have hz j (hj : j∈X) i (hi : i∈A) a b : IntervalIntegrable (m j i a b) volume 0 high := by
      rw [hm j hj i hi]; exact priced_sum _ (fun f hf => ht j hj i hi a b f hf)
    rw [fusion q v t A ha he (hv.lower (by omega)) h, funext hx,intervalIntegral.integral_finsetSum]
    swap
    · intro j hj; exact priced_sum _ (fun i hi => priced_sum _ fun a _ => priced_sum _ fun b _ => hz j hj i hi a b)
    let W (j i : V) (f : Parent V) := ∑ a,∑ b, ∫ x in 0..high,G j i a b f x
    have hZ j (hj : j∈X) : (∫ x in 0..high,∑ i∈A,∑ a,∑ b,m j i a b x) =
        ∑ i∈A,∑ f∈options t.val (insert j A),W j i f := by
      rw [intervalIntegral.integral_finsetSum]; swap
      · intro i hi; exact priced_sum _ (fun a _ => priced_sum _ fun b _ => hz j hj i hi a b)
      apply sum_congr rfl; intro i hi
      rw [intervalIntegral.integral_finsetSum]; swap
      · intro a ha; exact priced_sum _ fun b _ => hz j hj i hi a b
      unfold W; rw [sum_comm]; apply sum_congr rfl; intro a _
      rw [sum_comm (s:=options ..),intervalIntegral.integral_finsetSum (fun b _ => hz j hj i hi a b)];
      apply sum_congr rfl; intro b _
      rw [hm j hj i hi a b,intervalIntegral.integral_finsetSum]; intro f hf; exact ht j hj i hi a b f hf
    apply (sum_congr rfl hZ).trans
    apply (swap_orders ha W).trans
    refine sum_congr rfl fun f _ => ?_
    rw [report]; rfl
end Expansion
end YM.Primitives.GCC
