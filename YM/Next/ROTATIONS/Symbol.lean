import YM.Next.ROTATIONS.Charge
import YM.Next.ROTATIONS.Journal
/-! # Conservation up to contacts. No analyticity assumption on the kernel at collision.
The normalization removes the linear term; bounds needed here only for separable tests. -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius

abbrev TestMap := MultilinearMap ℝ (fun _ : Axis => Profile) ℂ
def polar (f : Grouping) (i) := hat (stamp (f i))
def sent (T : Paper) : TestMap := (T.restrictScalars ℝ).compLinearMap (fun _ => (((hat : Form→L[ℂ] Form).restrictScalars ℝ).comp stamp).toLinearMap)
lemma sent_at (T : Paper) (f) : sent T f=T (polar f) := rfl
abbrev stepAt (k : ℕ) (f : Grouping) (i : Axis) := update f i (pump k (f i))
lemma polar_flat (f : Grouping) (i : Axis) (n : ℕ) (h : Centred n (f i)) : flat n (polar f i) := by
  intro j hj; rw [polar,jet_at_origin,h j hj]; simp
lemma replaces (f : Grouping) (i : Axis) (g : Profile) : polar (update f i g)=update (polar f) i (hat (stamp g)) := by
  ext1 j; by_cases h : j=i <;> simp [polar,h]
lemma D_hat (i : Axis) (f : Grouping) : moved i (polar f) = update (polar f) i ((-I) • hat (stamp (pump 1 (f i)))) := by
  unfold moved; congr 1
  ext1 x; exact (slope (f i) x).deriv
lemma hat_rhs (i : Axis) (g : Grouping) (x : E4) : tensor (moved i (polar g)) x =
    -I*tensor (polar (stepAt 1 g i)) x := by rw [D_hat, stepAt,replaces,tensor_update,tensor_update]; simp [mul_assoc]

def source (R : Series) (b c d : Axis) := (I:ℂ) • sent (delta R b c d)
lemma source_at (R : Series) (b c d) (f) : source R b c d f=∑ a,sent (R a b c d) (stepAt 1 f a) := by
  change I*delta _ _ _ _ (polar f)=_
  rw [delta_at,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  rw [D_hat, sent_at,stepAt,replaces,MultilinearMap.map_update_smul]; simp [← mul_assoc]

lemma lifted_cost {f : Grouping} {w : Axis → ℝ} {D : ℕ} {T : Paper} (a : ℝ) (ha : a ≤ 0) (hw : ∀ i,w i ≤ a)
    (hp : ∀ h : Panels, T h = T (projections h D))
    (hz : ∀ g, (∑ i,g i)<3 → T (formal g)=0) : Budget (a*3) (fun n => T (polar (mails w f n))) := by
  have he (g : Panels) : T g=∑ p∈ Fintype.piFinset (fun i : Axis => Finset.range D),
      (∏ j,iteratedDeriv (p j) (g j) 0)*T (formal p) := by
    conv_lhs => rw [hp g]
    unfold projections collect; rw [T.map_sum_finset (fun i j => _) (fun i => Finset.range D)]
    apply Finset.sum_congr rfl; intro p hp; exact T.map_smul_univ (fun j => _) (formal p)
  have hx (b : Axis → ℕ) (j : Axis) : Budget (a*b j) (fun n => iteratedDeriv (b j) (polar (mails w f n) j) 0) := by
    have ht := (budget_fuel (w j)).pow (b j)
    have hr : Budget (w j*b j) (fun n => ((fuel (w j) n ^ b j:ℝ):ℂ)) := ht.reduce (Eventually.of_forall (fun n => le_of_eq (norm_real _)))
    refine ((hr.times ((-I)^b j * (tally (b j) (f j):ℂ))).rise (by gcongr; exact hw j)).same <| .of_forall fun n => ?_
    change _=iteratedDeriv _ (hat (stamp (width (fuel _ n) _))) _
    rw [jet_at_origin,tally_width _ _ (fuel_pos ..)]
    push_cast; ring
  have hl (b : Axis→ℕ) (s : Finset Axis) : Budget (∑ i∈s,a*b i)
      (fun n => ∏ j∈s, iteratedDeriv (b j) (polar (mails w f n) j) 0) := by
    induction s using Finset.induction_on with
    | empty => simpa using constant_budget (1:ℂ)
    | insert i s h ih => simp_rw [Finset.sum_insert h, Finset.prod_insert h]; exact (hx b i).prod ih
  simp_rw [show ∀ n, T (polar (mails w f n))=_ from fun n => he (polar (mails w f n))]; refine budget_sum _ (fun b n => _) _ fun b hb => ?_
  by_cases h : ∑ j : Axis,b j < 3
  · simp_rw [hz b h,mul_zero]; exact no_budget _
  have hi := hl b Finset.univ
  have hh := hi.times (T (formal b))
  simp_rw [mul_comm _ (T (formal b))]; apply hh.rise
  rw [← Finset.mul_sum,← Nat.cast_sum]
  exact mul_le_mul_of_nonpos_left (by exact_mod_cast le_of_not_gt h) ha

variable {G : Gauge} {L : Register G} {S : Table L}

private lemma pair_head (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S)
    (v w : S.Tag) (T : Panels) (a i) (D) (ht : ScaleCap D (pair v w))
    (hh : ScaleCap D (pair (Ward.rise P a v) w)) (hF : flat (D+1) (T i)) :
    integral volume (fun x => pair v w x*tensor (moved a T) x)= - ∫ x, pair (Ward.rise P a v) w x*tensor T x := by
  have hk : flat D (T i) := fun j hv => hF j (by omega)
  have hx : flat D (moved a T i) := by
    unfold moved; by_cases h : i=a
    · subst i; rw [update_self]; exact prime_zero_order D (T a) hF
    rw [Function.update_of_ne h]; exact hk
  refine integrate_both _ (tensor T) _ _ a (radical T D i hk _ ht (pair_meas H ..)) (radical _ D i hx _ ht (pair_meas H ..))
    (radical T D i hk _ hh (pair_meas H ..)) (pair_dif H v w P hp a) (fun x _ y => ?_)
  exact moved_deriv ..

structure Strong (J : Stress S) (P : DiffPlan S) (D : ℕ) : Prop where
  bound a b c d : ScaleCap D (linePair J a b c d)
  total a b c d : ScaleCap D (pair (Ward.rise P a (tag J a b)) (tag J c d))
lemma stronger (H : S.Hierarchy) (J : Stress S) (P : DiffPlan S) : ∃ D : ℕ,0<D ∧ Strong J P D := by
  let t (i : Axis × Axis × Axis × Axis) (n : ℕ) := ScaleCap n (linePair J i.1 i.2.1 i.2.2.1 i.2.2.2) ∧
       ScaleCap n (pair (Ward.rise P i.1 (tag J i.1 i.2.1)) (tag J i.2.2.1 i.2.2.2))
  have he : ∀ᶠ D in atTop, ∀ i,t i D := by
    refine eventually_all.mpr fun i => ?_; rcases i with ⟨a,b,c,d⟩
    obtain ⟨x,hx⟩ := pair_bound H (tag J a b) (tag J c d)
    obtain ⟨y,hy⟩ := pair_bound H (Ward.rise P a (tag J a b)) (tag J c d)
    filter_upwards [eventually_ge_atTop x,eventually_ge_atTop y] with n h k
    exact ⟨hx.loosen h,hy.loosen k⟩
  obtain ⟨D,hD,h⟩ := ((eventually_gt_atTop (0:ℕ)).and he).exists
  exact ⟨D,hD,⟨fun a b c d => (h (a,b,c,d)).1,fun a b c d => (h (a,b,c,d)).2⟩⟩

lemma closed_shell (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) {J : Stress S} {D : ℕ} {R : Series}
    (hp : Portrait J D R) (he : Conserved P H.spin J) (hS : Strong J P D) :
    ∀ b c d (f : Panels) i, flat (D+1) (f i) → delta R b c d f = 0 := by
  intro b c d f i hi
  let g (a) := pair (Ward.rise P a (tag J a b)) (tag J c d)
  have hk : flat D (f i) := fun k h => hi k (by omega)
  have hv a : flat D (moved a f i) := by
    unfold moved; by_cases h:i=a; · subst a; rw [update_self]; exact prime_zero_order D (f i) hi
    rw [update_of_ne h]; exact hk
  have hx a : R a b c d (moved a f)= -(∫ x,g a x*tensor f x) := by
    rw [hp.agrees a b c d (moved a f) i (hv a)]
    exact pair_head H P h _ _ f a i D (hS.bound ..) (hS.total ..) hi
  have hh a : Integrable (fun x => g a x*tensor f x) := radical _ D i hk _ (hS.total ..) (pair_meas H ..)
  have hf x : ∑ a,g a x=0 := by
    let w := tag J c d
    let z : Fin 2 → S.Tag := ![⟨4,J c d⟩,w]
    let T := points ![x,0]
    have heq a : g a x= here z T 0 5 (P.deriv 4 a (J a b)) := by
      rw [takes]; unfold g pair; congr 2; ext1 i; fin_cases i <;> simp [tag,z,w,Ward.rise]
    simp_rw [heq]; rw [← _root_.map_sum, he.divergence,map_zero]
  rw [delta_at]; simp_rw [hx,Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ => hh i)]
  simp_rw [← Finset.sum_mul,hf]; simp

lemma pupils (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) {J : Stress S} {D : ℕ} {R : Series}
    (hp : Portrait J D R) (he : Conserved P H.spin J) (hS : Strong J P D) (b c d f) :
    delta R b c d f = delta R b c d (projections f (D+1)) := by
  let T (s : Finset Axis) (j : Axis) := if j∈s then collect (D+1) (f j) else f j
  let A := delta R b c d
  have hh (s : Finset Axis) : A f = A (T s) := by
    induction s using Finset.induction_on with
    | empty => simp [T]
    | insert i s hi ih =>
      rw [ih, show T (insert i s)=Function.update (T s) i (collect (D+1) (f i)) from funext fun k => by by_cases h:k=i <;> simp [T,h]]
      let p := f i-collect (D+1) (f i)
      have hp : A (update (T s) i p)=0 := closed_shell H P h hp he hS b c d _ i (by rw [update_self]; exact missed (D+1) (f i))
      change A (_)=A _; unfold p at hp; rw [A.map_update_sub,sub_eq_zero] at hp
      rw [show f i=T s i from by simp [T,hi],update_eq_self] at hp
      simpa [T,hi] using hp
  have ht : T Finset.univ=projections f (D+1) := by ext1 i; simp only [T, projections,Finset.mem_univ,ite_true]
  rw [← ht]; exact hh _
lemma source_cost (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) {J : Stress S} {D : ℕ} (hd : 0<D) {R : Series}
    (hp : Portrait J D R) (he : Conserved P H.spin J) (hS : Strong J P D) (a : ℝ) (ha : a≤0) (b c d) (w : Axis→ℝ) (hw : ∀ i,w i ≤ a)
    (f : Grouping) : Budget (a*3) (fun n => source (joint R) b c d (mails w f n)) :=
  (lifted_cost a ha hw (pupils H P h (joined hp hd) he hS b c d) (joint_null hp hd b c d)).times I
end YM.Outer
