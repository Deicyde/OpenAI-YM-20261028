import YM.Next.ROTATIONS.Vanishing
/-!
# A compact compensated angular packet in position space
-/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Row OS Table Ward
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Classical

def nab (f : Profile) := SchwartzMap.derivCLM ℝ ℝ f
lemma nab_at (f : Profile) (x : ℝ) : nab f x=deriv f x := SchwartzMap.derivCLM_apply ℝ f x
lemma nab_d (f : Profile) (x : ℝ) : HasDerivAt f (nab f x) x := (nab_at f x).symm ▸ f.differentiableAt.hasDerivAt

def leaf : Profile := pump 1 center
def crown := nab leaf
lemma leaf_bud (x : ℝ) (hx : |x| < 1) : leaf x=x := by simp [leaf,pump_at,center_plane _ hx.le]
lemma scalesmall (x : ℝ) (h : |x| < 1) : ∀ᶠ y in 𝓝 x, |y| < 1 := continuous_abs.continuousAt.preimage_mem_nhds (Iio_mem_nhds h)
lemma crown_bud (x : ℝ) (h : |x| < 1) : crown x=1 := by unfold crown; rw [nab_at,(EventuallyEq.deriv_eq (f:=fun y : ℝ=>y) ((scalesmall x h).mono leaf_bud))]; simp
lemma still_crown (x : ℝ) (h : |x| < 1) : nab crown x=0 := by
  rw [nab_at, (EventuallyEq.deriv_eq (f:=fun _ : ℝ => (1:ℝ)) ((scalesmall x h).mono crown_bud))]; simp
lemma leaf_ends : Ends leaf := by
  exact Ends.pumps center_ends 1
lemma crown_ends : Ends crown := by unfold crown Ends; rw [show ⇑(nab leaf)=deriv leaf from funext (nab_at leaf)]; exact HasCompactSupport.deriv leaf_ends
lemma leaf_odd (p : ℝ) : leaf (-p)= -leaf p := by
  unfold leaf; rw [pump_at,pump_at, center_even]; simp
lemma crown_even (p : ℝ) : crown (-p)=crown p := by
  have h := (nab_d leaf (-p)).scomp p (hasDerivAt_neg' p)
  have he : HasDerivAt (fun x : ℝ => -leaf x) (-crown (-p)) p := by simpa [Function.comp_def,crown,leaf_odd] using h
  exact neg_injective (he.unique (nab_d leaf p).neg)
lemma nab_odd (p : ℝ) : nab crown (-p)= -nab crown p := by
  have h := (nab_d crown (-p)).scomp p (hasDerivAt_neg' p)
  have he : HasDerivAt crown (-nab crown (-p)) p := by simpa [Function.comp_def,crown_even] using h
  have hh := he.unique (nab_d crown p); linarith

abbrev orchard (a : Axis) : Grouping := update (fun _ => crown) a leaf
abbrev shiftPlot (d : Axis) (f : Grouping) := update f d (nab (f d))
abbrev weighIn (f : Grouping) (w : Axis→ℝ) (n : ℕ) := fun x : E4 => ∏ j : Axis,f j (fuel (w j) n*x j)
lemma weigh_smooth (f : Grouping) (w n) : ContDiff ℝ ∞ (weighIn f w n) := by unfold weighIn; apply contDiff_prod; intro i _; exact (show ContDiff ℝ ∞ (f i) from (f i).smooth ⊤) |>.comp (by fun_prop)
lemma weigh_short (f : Grouping) (w n) (h : ∀ i, Ends (f i)) : HasCompactSupport (weighIn f w n) := by
  let Y (i : Axis) (x : ℝ) := f i (fuel (w i) n*x)
  let e (i : Axis) : ℝ≃L[ℝ]ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 (fuel (w i) n) (fuel_pos ..).ne')
  have he i : HasCompactSupport (Y i) := HasCompactSupport.comp_homeomorph (h i) (e i).toHomeomorph
  apply HasCompactSupport.intro ((isCompact_pi_infinite he).image (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)).symm.continuous)
  intro p hp; by_contra hy; unfold weighIn at hy
  apply hp; refine ⟨p.ofLp,fun i => subset_tsupport _ ?_,rfl⟩
  change Y i (p i)≠0; intro hz; exact hy (Finset.prod_eq_zero (Finset.mem_univ i) hz)
lemma cut_one (f : Grouping) (i : Axis) (w : Axis→ℝ) (n : ℕ) (p : E4) : weighIn f w n p=
    f i (fuel (w i) n*p i)*∏ j∈other i, f j (fuel (w j) n*p j) := by unfold weighIn; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
lemma weigh_dif (f : Grouping) (w n) (i : Axis) (p : E4) : Analysis.D (basis i) (weighIn f w n) p = fuel (w i) n*weighIn (shiftPlot i f) w n p := by
  let v := fuel (w i) n; let Q := ∏ j∈other i, f j (fuel (w j) n*p j)
  let y := fun t : ℝ => p+t • basis i
  have he t : weighIn f w n (y t)=f i (v*(p i+t))*Q := by
    rw [cut_one f i]; simp only [y,PiLp.add_apply,PiLp.smul_apply,basis_eq,if_true,smul_eq_mul,mul_one]
    unfold v Q; congr 1; exact Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_erase.mp hj).1]
  have hv : weighIn (shiftPlot i f) w n p= nab (f i) (v*p i)*Q := by
    rw [cut_one _ i,shiftPlot,update_self]; unfold Q v; congr 1; exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.mem_erase.mp hj).1]
  have hx : HasDerivAt y (basis i) 0 := by
    simpa [y] using (ContinuousLinearMap.toSpanSingleton ℝ (basis i)).hasDerivAt (x:=0) |>.const_add p
  have hh : HasDerivAt (weighIn f w n ∘ y) (Analysis.D (basis i) (weighIn f w n) p) 0 := by
    have H := ((weigh_smooth f w n).differentiable (by simp) (y 0)).hasFDerivAt.comp_hasDerivAt 0 hx
    rw [show y 0=p by simp [y]] at H
    exact H
  rw [show weighIn f w n ∘ y=_ from funext he] at hh
  exact hh.unique (by
    rw [hv]; dsimp only
    let g (x : ℝ) := v*(p i+x)
    have hp : HasDerivAt g v 0 := by simpa [g] using ((hasDerivAt_id' (0:ℝ)).const_add (p i)).const_mul v
    have hh := ((nab_d (f i) (g 0)).scomp 0 hp).mul_const Q
    simp only [g,add_zero,smul_eq_mul,mul_assoc] at hh
    exact hh)

abbrev petal (a b l : Axis) (n : ℕ) := fun x : E4 => fuel 100 n*weighIn (orchard a) (chart a b l) n x
lemma petal_d (a b l : Axis) (d n x) : Analysis.D (basis d) (petal a b l n) x=
    fuel 100 n * (fuel (chart a b l d) n * weighIn (shiftPlot d (orchard a)) (chart a b l) n x) := by
  rw [← weigh_dif (orchard a),Analysis.D, Analysis.D]; unfold petal; rw [fderiv_const_mul ((weigh_smooth (orchard a) _ _).differentiable (by simp) _) _]
  rfl
lemma petal_self (a b l : Axis) (n x) : Analysis.D (basis a) (petal a b l n) x=weighIn (fun _ => crown) (chart a b l) n x := by
  rw [petal_d,← mul_assoc,fuel_mul, chart_symm a b, chart_there b a]
  have he : shiftPlot a (orchard a)=(fun _ => crown) := by unfold shiftPlot orchard crown; rw [update_self,update_idem,update_eq_self]
  rw [he]; simp [fuel0]
lemma petal_smooth (a b l : Axis) (n) : ContDiff ℝ ∞ (petal a b l n) := contDiff_const.mul (weigh_smooth ..)
lemma petal_short (a b l : Axis) (n) : HasCompactSupport (petal a b l n) := HasCompactSupport.mul_left (f:=fun _ => fuel 100 n) (weigh_short _ _ _ fun i => by
  unfold orchard; by_cases h:i=a; · subst i; rw [update_self]; exact leaf_ends
  rw [update_of_ne h]; exact crown_ends)
lemma petal_mid (a b l : Axis) (n : ℕ) (x : E4) (h : ∀ i, |fuel (chart a b l i) n*x i| < 1) : petal a b l n x=x a := by
  unfold petal; rw [cut_one _ a,orchard,update_self,leaf_bud _ (h a)]
  rw [Finset.prod_eq_one (fun i hi => by rw [update_of_ne (Finset.mem_erase.mp hi).1]; exact crown_bud _ (h i)),mul_one,← mul_assoc,fuel_mul,chart_symm a b,chart_there]; simp [fuel0]
lemma petal_home (a b l : Axis) (x : E4) : ∀ᶠ n in atTop, petal a b l n =ᶠ[𝓝 x] fun y : E4 => y a := by
  have he i : ∀ᶠ n in atTop, |fuel (chart a b l i) n*x i| < 1 := by
    have hv : chart a b l i<0 := (chart_bounds a b l i).2.trans_lt (by norm_num)
    have hz : Tendsto (fun n => fuel (chart a b l i) n*x i) atTop (𝓝 0) := by simpa using (fuel_falls hv).mul_const (x i)
    exact hz.eventually (scalesmall 0 (by norm_num))
  filter_upwards [eventually_all.mpr he] with n hn
  have hz i : ∀ᶠ y in 𝓝 x, |fuel (chart a b l i) n*y i| < 1 :=
    (show Continuous (fun p : E4 => fuel (chart a b l i) n*p i) by fun_prop).continuousAt.tendsto.eventually (scalesmall _ (hn i))
  exact (eventually_all.mpr hz).mono (fun p hp => petal_mid a b l n p hp)

abbrev canvas (f : Grouping) : Panels := fun i => port (stamp (f i))
lemma portrait_track (f : Grouping) (w : Axis→ℝ) (n : ℕ) (d : Axis) (x : E4) : positionTest (tracks w d n (canvas f)) x=
    Complex.ofReal (fuel (w d) n * weighIn f w n x) := by
  let u (i : Axis) := fuel (w i) n
  have he : hat (tracks w d n (canvas f) d) (x d)=↑(u d)*(f d (u d*x d):ℂ) := by
    unfold tracks; rw [update_self,frozen_hat _ _ (fuel_pos ..),canvas,travels]; rfl
  unfold positionTest; rw [tensor_at,← Finset.mul_prod_erase _ _ (Finset.mem_univ d),he,cut_one f d,ofReal_mul,ofReal_mul,mul_assoc]
  change (u d:ℂ) *((f d _:ℂ)*_)= (u d:ℂ) *((f d _:ℂ)*_)
  rw [ofReal_prod]
  congr 2; refine Finset.prod_congr rfl fun i hi => ?_; unfold tracks; rw [update_of_ne (Finset.mem_erase.mp hi).1,large_hat _ _ (fuel_pos ..),canvas,travels]; rfl
lemma track_pose (a b l d : Axis) (n : ℕ) (x : E4) :
    Complex.ofReal (Analysis.D (basis d) (petal a b l n) x:ℝ)= (fuel 100 n:ℂ) * positionTest (tracks (chart a b l) d n (canvas (shiftPlot d (orchard a)))) x := by
  rw [portrait_track,petal_d,ofReal_mul]
lemma pose_far (a d : Axis) (h : d≠a) (p : ℝ) (hp : hat (canvas (shiftPlot d (orchard a)) d) p≠0) : 1≤|p| := by
  unfold canvas shiftPlot orchard at hp; rw [update_self,update_of_ne h,travels,stamp_at] at hp
  by_contra hz; rw [still_crown _ (lt_of_not_ge hz)] at hp; simp at hp
lemma pose_sign (a b l d k : Axis) (h : d≠a) (n : ℕ) (y : E4) : let f := positionTest (tracks (chart a b l) d n (canvas (shiftPlot d (orchard a))))
    f (Ortho.move (Signed.reflect k) y) = signValue (spar a d k) * f y := by
  intro f
  let t := shiftPlot d (orchard a)
  have he p : t k (-p)= if spar a d k then -t k p else t k p := by
    by_cases hx:k=d; · subst k; unfold t shiftPlot orchard; rw [update_self,update_of_ne h,nab_odd]; simp [spar,h]
    by_cases hl:k=a; · subst k; unfold t shiftPlot orchard; rw [update_of_ne hx, update_self,leaf_odd]; simp [spar,hx]
    unfold t shiftPlot orchard; rw [update_of_ne hx,update_of_ne hl,crown_even];simp [spar,hx,hl]
  let M := Ortho.move (Signed.reflect k) y; let w i := fuel (chart a b l i) n
  have hp : (∏ j∈other k,t j (w j*M j))=∏ j∈other k,t j (w j*y j) := Finset.prod_congr rfl fun j hj => by simp [M,(Finset.mem_erase.mp hj).1]
  unfold f; rw [portrait_track t,portrait_track t,cut_one t k,cut_one t k]
  dsimp only [w,M] at hp; rw [hp,Signed.mirrored k, if_pos rfl]
  rw [mul_neg,he]; cases spar a d k <;> simp [signValue]
end YM.Outer
