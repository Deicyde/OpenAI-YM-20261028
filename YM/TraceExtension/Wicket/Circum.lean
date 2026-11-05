import YM.TraceExtension.Wicket.Shelves
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n){σ A Λ δ w ε:ℝ}{U:Config G n}
variable (hp:R.Lawful σ A Λ δ w) (ht:Geo.Width R.p R.clip σ)
include hp ht
-- finite uniform approximation.Enorme.
lemma repriseC : ∃ f:Badge n→ℝ, (∀ i,0≤ f i ∧ ∀ U, ‖pieceC R i U‖ ≤ f i)∧Summable f:=by
   obtain ⟨e,he,he'⟩:=hp.labels.boundE
   let P(i:Barley):= VerifiedReset.factor*bingo R i; let F:Badge n→ℝ:= Sum.elim (fun i=> P i.2) e; have hm(i):0≤ bingo R i:= (abs_nonneg _).trans (canto R i 1); have hP(i):0 ≤ P i:= mul_nonneg VerifiedReset.factor_pos.le (hm _)
   refine ⟨F,?_,?_⟩
   · rintro (j|j)
     · refine ⟨hP _,fun u=>?_⟩; change |- VerifiedReset.factor * _|≤ VerifiedReset.factor*_; rw[abs_mul,abs_neg,abs_of_nonneg factor_pos.le]; exact mul_le_mul_of_nonneg_left (canto R _ _) factor_pos.le
     refine ⟨(he j).1,fun U=>?_ ⟩; let k:=R.activities.reg j; change |- masked R.p.threshold k.support _ _| ≤ e j; rw[abs_neg]; unfold masked Set.indicator; split_ifs with h; exact (he j).2 U h [] (by simp) (by simp); rw [abs_zero]; exact (he j).1
   apply Summable.sum
   · have hy : Summable (bingo R):= Summable.of_nonneg_of_le hm (fun i=> le_mul_of_one_le_right (hm _) (Real.one_le_exp (by positivity[R.p.exponent_pos]))) (grand R hp ht).2.1
     exact (summable_prod_of_nonneg (f:= F ∘ Sum.inl) (fun i=>hP i.2)).mpr ⟨fun i=> hy.mul_left _,Summable.of_finite⟩
   let g(x:Site n)(i:ℕ):= if (R.activities.reg i).site=x then R.p.mass (R.activities.reg i).support (e i) else 0
   have hx : Summable e:= Summable.of_nonneg_of_le (f:=fun i=>∑ x,g x i) (fun i=> (he i).1) (fun i=> by simp only[g,sum_ite_eq,mem_univ, ↓reduceIte]; exact R.p.loMass _ _ ((he i).1)) (summable_sum (f:=g) (fun i _=> (he' i).2.1))
   exact hx
lemma framed_c (m:ℕ)(I:Vest n)(he:WilsonStartup.Decent R.clip R.p) : Envelope (cabinet R m I):=by
   obtain ⟨f,hf,hg⟩:=repriseC R hp ht; exact Envelope.add (Envelope.const _) (Envelope.sum _ _ (fun i=>⟨bare_not R hp he|>.1,f i,(hf i).2⟩))
abbrev stripeR(m:ℕ)(U:Config G n)(i:Badge n):ℝ:= if coverNumber R.p.B (boothC R i) ≤ m then pieceC R i U else 0
lemma wearer (m:ℕ)(U:Config G n): field R m U= R.v*Fintype.card (Site n)+∑' i:Badge n,stripeR R m U i:=by
   obtain ⟨f,hf,hg⟩:= repriseC R hp ht; let P:={p:Support n// coverNumber R.p.B p ≤ m}; let Z(p:P)(i:Badge n):ℝ:= if boothC R i=p.val then pieceC R i U else 0
   have ht(p:P) : Summable (Z p):=Summable.of_norm_bounded hg (fun i=>by unfold Z; split; exact (hf i).2 _; rw[norm_zero];exact (hf i).1)
   unfold Shepherd.field stockC; simp_rw [MergeProof.expand_eq]; refine congr_arg₂ (· + ·) rfl ?_; change ∑ p:P, ∑' i,Z p i=_; rw [← Summable.tsum_finsetSum (f:=Z) (fun i _=> ht i)]; refine tsum_congr fun j=>?_
   unfold stripeR; split
   next h=>
       let p:P:=⟨_,h⟩; rw [sum_eq_single p]; exact if_pos rfl; intro i _ hi; exact if_neg (fun he=> hi (Subtype.ext (by exact he.symm))); simp
   next h=> exact sum_eq_zero (fun i _=> show Z i j=0 from if_neg (fun (he:boothC R j=i.val)=> h (he.symm ▸ i.property)))
lemma patterns (m:ℕ)(hh:0<ε) :∀ᶠ I:Vest n in atTop,∀ U:Config G n, |field R m U-cabinet R m I U|≤ε:=by
   obtain ⟨f,hf,hg⟩:= repriseC R hp ht
   filter_upwards [clips_out f (fun i=> (hf i).1) hg hh] with I hI U
   let Z:= stripeR R m U; have hy(i): ‖Z i‖ ≤ f i:=by unfold Z stripeR; split; exact (hf i).2 U; rw [norm_zero]; exact (hf i).1
   let V(i):= if i∈I then Z i else 0; have ht'(i):‖V i‖ ≤ f i:=by unfold V; split; exact hy _; rw [norm_zero]; exact (hf i).1
   have hx: (∑ i∈ stageZ R m I,pieceC R i U)=∑' j,V j:=by
      rw[tsum_eq_sum (s:=I)]; swap; · intro i hi; exact if_neg hi
      unfold stageZ; rw[sum_filter]; apply sum_congr rfl fun i hi=> (if_pos hi|>.symm)
   let HZ:= Summable.of_norm_bounded hg hy; let HV:= Summable.of_norm_bounded hg ht'
   rw [wearer R hp ht m U]; unfold cabinet; rw [hx,add_sub_add_left_eq_sub,← Summable.tsum_sub HZ HV]; apply (norm_tsum_le_tsum_norm (HZ.sub HV).norm).trans; apply le_trans (Summable.tsum_le_tsum ?_ (HZ.sub HV).norm hI.2.1) hI.2.2; intro i; change ‖Z i-V i‖≤_; unfold V; split; simp [*]; simp [*]; exact hy i
lemma exp_forms (m:ℕ)(he:WilsonStartup.Decent R.clip R.p)(hD:4 ≤ R.p.supportExponent)(hh:0< ε):∀ᶠ I:Vest n in atTop,∀ U V:Config G n, |Real.exp (field R m U-field R m V)-Real.exp (cabinet R m I U-cabinet R m I V)|≤ ε:=by
   obtain ⟨C,hC⟩:= (froth R hp ht he hD m).cost; let g:=field R m; let d:= 2*C; let p:= d+2; let L:= Real.exp p; let F:=min 1 ((ε/L)/2); have hc:0 ≤ C:= (norm_nonneg _).trans (hC 1); have ht':0<L:= Real.exp_pos _; have hL:0<F:=lt_min zero_lt_one (by positivity); have hv:F≤1:= min_le_left ..
   filter_upwards [patterns R hp ht m hL] with I hx U V
   let f:= cabinet R m I; have hw(U V:Config G n):|g U-g V|≤d:= (abs_sub ..).trans ((add_le_add (hC _) (hC _)).trans_eq (two_mul _).symm)
   let x:=g U-g V; let y:= f U-f V; have hy:|x-y| ≤ 2*F:=by rw [show x-y=(g U-f U)-(g V-f V) from by unfold x y; ring,two_mul]; exact (abs_sub ..).trans (add_le_add (hx _) (hx _))
   have hp : p ≥ 0:=by unfold p d; positivity
   have hx : |x| ≤ p:= (hw ..).trans (le_add_of_nonneg_right zero_le_two); have hY: |y| ≤ p:=by rw[show y= x-(x-y) by ring]; exact (abs_sub ..).trans ((add_le_add (hw U V) (hy.trans (by linarith only[hv]:2*F≤2))))
   have hz : ‖Real.exp x-Real.exp y‖ ≤ L*‖x-y‖:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s:=closedBall (0:ℝ) p) (fun v _=> (Real.hasDerivAt_exp _).hasDerivWithinAt) (fun z hz=> (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le (Real.exp_monotone ((le_abs_self z).trans (by simpa [Real.norm_eq_abs] using hz)))) (convex_closedBall ..) (by simpa [Real.norm_eq_abs] using hY) (by simpa [Real.norm_eq_abs] using hx)
   apply hz.trans; apply (mul_le_mul_of_nonneg_left hy ht'.le).trans; have ht:F ≤ ε/L/2:= min_le_right ..; exact (mul_le_mul_of_nonneg_left (show 2*F ≤ ε/L by linarith only [ht]) ht'.le).trans_eq (by field_simp)
end YM.Trace.Wicket
