import YM.TraceExtension.Pi.Morn
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory
open Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Interval Classical InnerProductSpace
variable {G:Gauge}{n:Side}{F:Peat G n}{P:Support n}
open Complex
variable (i:Axis)(a:G.ColorIndex)
abbrev petB (p q:ℕ)(x:Land)(j k:Lines G n 1):ℂ:=(pulseB (x 0) i j:ℂ)^p * (pulseB (x 1) i k:ℂ)^q * cashB i a j * cashB i a k * Kane F j k
abbrev moon (F:Peat G n)(p q:ℕ)(x:Land):ℂ:= ∑ j,∑ k, petB (F:=F) i a p q x j k
lemma moon_w (p q:ℕ)(x:Land): moon i a F p q x=(↑(sheen F (XR (x 0) i a p) (XR (x 1) i a q)):ℂ):=by
   rw[show (↑(sheen F _ _):ℂ)=beat _ 0 2 _ from (beat_duo ..).symm,stiff_body]; unfold dotProduct Matrix.mulVec
   simp only[dotProduct,mul_sum]; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=>?_ ; rw [← standU, ← standU]; unfold petB; ring
lemma chant0 (F:Peat G n)(x:Land): neap 0 (mush i a F) 0 x=moon i a F 0 0 x:=by
   rw [exp_run]; apply sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; simp [petB,setM];ring
lemma chant1 (F:Peat G n)(x:Land): neap 1 (mush i a F) 0 x=I*(moon i a F 0 1 x+ moon i a F 1 0 x):=by
   rw [exp_run]; unfold moon; rw [← sum_add_distrib,Finset.mul_sum]; refine sum_congr rfl fun j _=> ?_; rw [← sum_add_distrib,Finset.mul_sum]; refine sum_congr rfl fun k _=> ?_; unfold petB wash setM; push_cast; simp only [pow_zero,pow_one, Nat.factorial_one,Nat.cast_one,_root_.inv_one]; ring
lemma chant2 (F:Peat G n)(x:Land): neap 2 (mush i a F) 0 x= -(1/2:ℂ)*(moon i a F 2 0 x+2* moon i a F 1 1 x+ moon i a F 0 2 x):=by
   rw [exp_run]; unfold moon; rw [Finset.mul_sum,← sum_add_distrib,← sum_add_distrib,Finset.mul_sum]; refine sum_congr rfl fun j _=> ?_; rw [Finset.mul_sum,← sum_add_distrib, ← sum_add_distrib,Finset.mul_sum]; refine sum_congr rfl fun k _=> ?_; unfold petB wash setM; rw[mul_pow,I_sq]; push_cast; norm_num only[pow_zero,pow_one,Nat.factorial];push_cast;ring
lemma chant3 (F:Peat G n)(x:Land): neap 3 (mush i a F) 0 x= -I*(1/6:ℂ)*(moon i a F 3 0 x+3* moon i a F 2 1 x+ 3*moon i a F 1 2 x+ moon i a F 0 3 x):=by
   rw [exp_run]; unfold moon; simp_rw [mul_add,Finset.mul_sum];
   repeat rw [← sum_add_distrib]
   apply sum_congr rfl fun j _=> ?_; repeat rw [← sum_add_distrib]
   refine sum_congr rfl fun k _=>?_ ; unfold petB wash setM; rw[mul_pow, show Complex.I^(3:ℕ)= -Complex.I by rw[pow_succ, I_sq]; ring]; push_cast; norm_num only[pow_zero,pow_one,Nat.factorial];push_cast;ring
variable (h:Cleric F)(hp:LocalOn P F)(hs:Nonwrapping P 0)(hG:G.Simple)(hn: 2 ≤ n.val)
include h hp hs hG hn
lemma darkL (x:Land): mush i a F 0=0 ∧ fderiv ℝ (mush i a F) 0 x=0:=by
   have he(d:ℕ): moon i a F 0 d x=0∧moon i a F d 0 x=0:=by
      rw[moon_w,moon_w]; unfold sheen; rw[evenQ h (XR _ _ _ 0)]; change (↑(sheen F _ _):ℂ) =0 ∧ (↑(sheen F _ _):ℂ)=0; exact ⟨by rw[stitch0 _ _ _ h hp hs hG hn];rfl,by rw[stitch0 _ _ _ h hp hs hG hn];rfl⟩
   rw[← neap0 (mush i a F) 0 x,← neap1,chant0, chant1, (he 1).1, (he 1).2, (he 0).1]; simp
lemma cold3 (x:Land): neap 3 (mush i a F) 0 x= -I*(1/2:ℂ)*(↑(sheen F (bang0 (x 1) i a) (bang1 (x 0) i a)+sheen F (bang0 (x 0) i a) (bang1 (x 1) i a)):ℂ):=by
   rw[chant3]; simp_rw [moon_w]; rw [stitch0 _ _ _ h hp hs hG hn]; rw[show sheen F _ (XR _ _ _ 3)=0 from ?_]; rotate_left
   · rw [sheen_symm F h, stitch0 _ _ _ h hp hs hG hn]
   simp_rw [stitch1 _ _ _ h hp hs hG hn, stitch2 _ _ _ h hp hs hG hn]; rw [sheen_symm F h (XR (x 0) i a 2),sheen_symm F h (XR (x 0) i a 1),stitch1 _ _ _ h hp hs hG hn,stitch2 _ _ _ h hp hs hG hn]; rw [sheen_symm F h (bang1 (x 1) i a)];push_cast; ring
end YM.Trace.Kits
