import YM.Next.RANK.Domes
import YM.Next.RANK.ParticleMoment

/-!
# Removing a guard in the chosen conditional law

The relevant kernels need be close only on the common stencil. Keep genuine
moments, including second moments for the removal. Includes real coordinates
and Cauchy estimate valid with correlations everywhere. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value MeasureTheory Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {Ω V Z : Type*} {m : V→ℂ} {Q Q' : Normal.Symmetric V}
section
open Common
private def clip (Q : Normal.Symmetric V) (f : Finset V) : Normal.Symmetric V where
  cov i j:= if i∈ f ∧ j∈f then Q.cov i j else 0
  symm i j:= by by_cases h:i∈f ∧ j∈f; rw [if_pos h, if_pos (And.symm h), Q.symm]; rw [if_neg h,if_neg (mt (fun ht=>And.symm ht) h)]
private def pin (m : V→ℂ) (f : Finset V) (i : V):= if i∈f then m i else 0
private lemma pinned (m : V→ℂ) (v : Normal.poly V) (X : Finset V) (P : Normal.Symmetric V) (h : v.vars⊆X) : blend P m v=blend (clip P X) (pin m X) v:= by
  obtain ⟨u,hu⟩:= trim_sigma X v h
  let f:= fun x:↥X => Finsupp.single x.val (1:ℂ)
  rw [←hu,Normal.labelled,wets,wets]
  exact DFunLike.congr_fun (congr_arg₂ Normal.blend (show scope f P=scope f (clip P X) from by apply Normal.Symmetric.ext; funext i j; rw [match_name Subtype.val,match_name Subtype.val]; exact (if_pos ⟨i.property,j.property⟩).symm) (show Normal.reads f m=Normal.reads f (pin m X) from by funext i; simp only [Normal.reads,f,Finsupp.linearCombination_single,pin,i.property,↓reduceIte])) u
lemma fits_clip (m : V→ℂ) (X : Finset V) {B} (h : 1≤B) (hp : ∀ i∈X, ‖m i‖≤B) (he : ∀ i∈X, ∀ j∈X, ‖Q.cov i j‖≤B) : Sorts (clip Q X) (pin m X) B:= by
  refine ⟨h,fun i=>?_,fun i j=>?_⟩
  · unfold pin; split
    · exact hp _ (by assumption)
    rw [norm_zero]; exact zero_le_one.trans h
  unfold clip; dsimp only; split
  · rename_i h; exact he i h.1 j h.2
  rw [norm_zero]; exact zero_le_one.trans h
lemma differently {m : V→ℂ} (X : Finset V) (p : Normal.poly V) (hx : p.vars⊆X) {B d ε} (h : 1≤B)
    (hQ : p.totalDegree ≤ d) (hu : ∀ i∈X,‖m i‖ ≤ B) (hP : ∀ i∈X, ∀ j∈X, ‖Q.cov i j‖ ≤ B) (hp' : ∀ i∈X, ∀ j∈X, ‖Q'.cov i j‖ ≤ B)
    (he : 0 ≤ ε) (hk : ∀ i∈X, ∀ j∈X, ‖Q.cov i j-Q'.cov i j‖ ≤ ε) : ‖blend Q m p-blend Q' m p‖ ≤ coin p * (ε*Common.priced B d):= by
  rw [pinned m p X Q hx,pinned m p X Q' hx]
  refine Common.differs p d ⟨fits_clip _ _ h hu hP,fits_clip _ _ h hu hp',he,fun i=>by simp only [sub_self,norm_zero]; exact he,fun i j=>?_⟩ hQ
  dsimp only [clip]; split
  · rename_i H; exact hk i H.1 j H.2
  rw [sub_self,norm_zero]; exact he
lemma bound_v (p : Normal.poly V) {B d} (P : Normal.Symmetric V) (h : p.totalDegree ≤ d) (hB : 1≤B) (hu : ∀ i∈p.vars, ‖m i‖ ≤ B) (hP : ∀ i∈p.vars,∀ j∈p.vars, ‖P.cov i j‖ ≤ B): ‖blend P m p‖ ≤ coin p * Common.priced B d:= by rw [pinned m p p.vars P le_rfl]; exact Common.width p d (fits_clip _ _ hB hu hP) h
lemma priced_up (d) {B : ℝ} (h : 1≤ B) : 1 ≤ Common.priced B d:= one_le_pow₀ (by
  have hb : (1:ℝ) ≤ (d+1:ℝ):= by linarith [Nat.cast_nonneg (α:=ℝ) d]
  linarith [mul_le_mul_of_nonneg_left hb (zero_le_one.trans h)])
lemma view_v (m : V→ ℝ) (p : Normal.poly V) {B d} (h : totalDegree p≤d) (hB : 1≤B) (hp : ∀ i∈p.vars, |m i|≤B) : ‖text m p‖ ≤ coin p * Common.priced B d:= by
  rw [show text m p= blend (0: Normal.Symmetric V) (fun i=>(↑(m i):ℂ)) p by rw [blend_components,froze]]
  exact bound_v _ _ h hB (fun i hi=> by rw [Complex.norm_real,Real.norm_eq_abs]; exact hp i hi) (fun i _ j _=> (show ‖(0:ℂ)‖≤B by rw [norm_zero]; exact zero_le_one.trans hB))
lemma spot_trial (X : Normal.poly V) (m m' : V→ℝ) {d B ε} (hz : X.totalDegree≤d) (hB : 1≤ B) (hu : ∀ i∈X.vars, |m i|≤B) (hV : ∀ i∈X.vars, |m' i|≤B)
    (he : 0 ≤ ε) (hx : ∀ i∈X.vars, |m i-m' i|≤ ε) : ‖text m X-text m' X‖ ≤ coin X*((d:ℝ)*B^d*ε):= by
  let u:= fun i=> if i∈X.vars then m i else 0; let v:= fun i=> if i∈X.vars then m' i else 0
  rw [reads_eq X m u (fun i hi=> (if_pos hi).symm), reads_eq X m' v (fun i hi=> (if_pos hi).symm)]
  refine Spindle.amove X d hz B hB u v ?_ ?_ ε he ?_
  · intro i; by_cases h:i∈X.vars; simpa [u,h] using hu i h; simpa only [u,if_neg h,abs_zero] using zero_le_one.trans hB
  · intro i; by_cases h:i∈X.vars; simpa [v,h] using hV i h; simpa only [v,if_neg h,abs_zero] using zero_le_one.trans hB
  intro i; by_cases h:i∈X.vars; simpa only [u,v,h,↓reduceIte] using hx i h; simpa only [u,v,if_neg h,sub_self,abs_zero] using he
end

section norm
variable {p : Normal.poly V}
private lemma backorg (p : Normal.poly V) : (retro _ p).support=p.support:= by ext i; simp only [mem_support_iff,retro,coeff_map, starRingEnd_apply, ne_eq, star_eq_zero]
private lemma coinRetro : coin (retro _ p)=coin p:= by rw [metal,metal,backorg]; apply Finset.sum_congr rfl; intro i _; simp [retro,coeff_map]
private lemma taxret : totalDegree (retro _ p)=totalDegree p:= by unfold totalDegree; rw [backorg]
end norm
variable [MeasurableSpace Ω] {μ : Measure Ω}

structure Guarded (g : Ω→ℝ) (η : ℝ) (μ : Measure Ω) : Prop where
  lower u : 0≤ g u
  up u : g u ≤ 1
  meas : Measurable g
  price : (∫ u, 1-g u ∂μ) ≤ η

variable {g z : Ω→ℝ} {x : Ω → V → ℝ} {P : Normal.Symmetric V}
lemma affordable {ε} (Q : Ω→ ℂ) (h : Guarded g ε μ) (H : Integrable Q μ) : Integrable (fun U=> (↑(g U):ℂ)*Q U) μ:= H.bdd_mul (Complex.continuous_ofReal.measurable.comp h.meas |>.aestronglyMeasurable)
  (Eventually.of_forall (p:=fun U=> ‖((↑(g U)):ℂ)‖ ≤ (1:ℝ)) (fun U=> by rw [Complex.norm_real,Real.norm_of_nonneg (h.lower U)]; exact h.up U))
lemma got {ε} [IsFiniteMeasure μ] (h : Guarded g ε μ) : Integrable g μ:= Integrable.of_bound h.meas.aestronglyMeasurable 1 (Eventually.of_forall fun i=> by rw [Real.norm_of_nonneg (h.lower i)]; exact h.up i)
lemma guards_mul {η ε} [IsFiniteMeasure μ] (h : Guarded g η μ) (H : Guarded z ε μ) : Guarded (fun U=>g U*z U) (η+ε) μ:= by
  let w:=fun U=>g U*z U
  have hw i:w i≤1:= mul_le_one₀ (h.up i) (H.lower i) (H.up i)
  have hh i:0 ≤ w i:= mul_nonneg (h.lower i) (H.lower i); have hb: Measurable w:=h.meas.mul H.meas
  refine ⟨hh,hw,hb,?_⟩
  have hi: Integrable w μ:= Integrable.of_bound hb.aestronglyMeasurable 1 (Eventually.of_forall fun x=> by rw [Real.norm_of_nonneg (hh x)]; exact hw x)
  have hf i:1-w i ≤ 1-g i+(1-z i):= by unfold w; nlinarith [mul_nonneg (sub_nonneg.mpr (h.up i)) (sub_nonneg.mpr (H.up i))]
  have hx : Integrable (fun i=>1-g i) μ:=(integrable_const _).sub (got h); have hu : Integrable (fun i=>1-z i) μ:=(integrable_const _).sub (got H)
  apply (integral_mono ((integrable_const _).sub hi) (hx.add hu) hf).trans
  simp only [Pi.add_apply]; rw [integral_add hx hu]; exact add_le_add h.price H.price

lemma squareFits (m : V→ℝ) (p : Normal.poly V) (h : VMeasure Ω V μ x P) {B d} (hp : totalDegree p ≤ d) (hB : 1≤ B)
    (hT : ∀ i∈p.vars, |m i| ≤ B) (hP : ∀ i∈p.vars, ∀ j∈p.vars, ‖P.cov i j‖ ≤ B) :
    let f:= fun u=> ‖carry x m p u‖^2
    Integrable f μ ∧ (∫ u,f u ∂μ) ≤ coin p^2 * Common.priced B (2*d):= by
  intro f; let S:=p*retro _ p
  have he: f=fun u=> RCLike.re (carry x m S u) := by
    ext u; let a:=carry x m p u
    have ht:carry x m S u=a*star a := by unfold carry S; have hv:=escorted (m+x u) p; unfold text at *; rw [map_mul, hv]; rfl
    rw [ht,show a*star a=_ from Complex.mul_conj a]; exact Complex.sq_norm a
  have hi:= carries_int h m S; let Q:=Common.priced B (2*d)
  have hc : coin S ≤ coin p^2:= by rw [sq]; exact (funds _ zero_le_one ..).trans (le_of_eq (show coin p*coin (retro V p)=_ by rw [coinRetro]))
  have hh : totalDegree S ≤ 2*d:= by refine (totalDegree_mul ..).trans ?_; rw [taxret];omega
  have hf : S.vars⊆p.vars:= Finset.Subset.trans (vars_mul ..) (union_subset (by rfl) (vars_map p _))
  rw [he]; refine ⟨hi.re, ?_⟩; change (∫ x,RCLike.re (carry _ _ S x) ∂μ)≤ _
  rw [integral_re hi,payment m h]; apply ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans
  apply (bound_v S P hh hB (fun i hi=> by rw [Complex.norm_real, Real.norm_eq_abs]; exact hT i (hf hi)) (fun i hi j hj=> hP i (hf hi) j (hf hj))).trans; gcongr; exact zero_le_one.trans (priced_up _ hB)

-- elementary integrated Young inequality, includes measurable fractional guards
lemma escaped {B ε ε'} [IsProbabilityMeasure μ] (H : Guarded g ε μ) (h : 0<ε') {f : Ω → ℂ} (hx : Integrable f μ) (u : Integrable (fun i=> ‖f i‖^2) μ)
    (he : (∫ U, ‖f U‖^2 ∂μ) ≤ B) : ‖(∫ U, (↑(g U):ℂ)*f U ∂μ)-∫ U, f U ∂μ‖ ≤ ε'*B + ε/ε':= by
  let v:=fun U=> (↑(g U):ℂ)*f U
  let s:=fun U=>‖v U-f U‖
  have hs i: s i= (1-g i)*‖f i‖:= by unfold s v; rw [← sub_one_mul, norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (H.up i)),neg_sub]
  have hv := affordable f H hx; rw [← integral_sub hv hx]; apply (norm_integral_le_integral_norm ..).trans
  change (∫ i,s i ∂μ) ≤ _
  have ht i : s i ≤ ε'*‖f i‖^2+(1-g i)/ε':= by
    rw [hs]
    let x:= 1-g i; have hx:0≤ x:= sub_nonneg.mpr (H.up _); have hw:x≤1:=by unfold x; linarith only [H.lower i]
    apply le_of_mul_le_mul_left _ h; change ε' * (x*_) ≤ ε'*(_+x/_);
    have hh: ε'*(ε'*‖f i‖^2+x/ε')=(ε'*‖f i‖)^2+x:= by field_simp
    rw [hh]; nlinarith only [sq_nonneg (ε'*‖f i‖-x),mul_le_mul_of_nonneg_right hw hx,hx]
  let a:= fun i=> 1-g i
  have hE: Integrable a μ:=(integrable_const _).sub (got H)
  apply (integral_mono ((hv.sub hx).norm) ((u.const_mul ε').add (hE.div_const ε')) ht).trans
  simp only [Pi.add_apply]; rw [integral_add (u.const_mul ε') (hE.div_const ε'), integral_const_mul, integral_div]
  exact add_le_add (mul_le_mul_of_nonneg_left he h.le) (div_le_div_of_nonneg_right H.price h.le)
end YM.Next.Rank.Tapes
