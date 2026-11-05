import YM.TraceExtension.Pi.Arcus
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory
open Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Interval InnerProductSpace Classical
variable {G:Gauge}{n:Side}{F:Peat G n}{P:Support n}{v:Labels.Label G 5}{H: Hol G}
open Complex
variable (d i b:Axis)(a:G.ColorIndex)
lemma mushC (F: Peat G n) : ContDiff ℝ ω (mush i a F):=by
   rw[funext (expo _ _ _)]; apply ContDiff.sum; intro j _; apply ContDiff.sum; intro k _;
   have hx(j':Fin 2)(k:Lines G n 1): ContDiff ℝ ω (fun z:Land=> pulseB (z j') i k):=by unfold pulseB midV; simp_rw[mind_t]; fun_prop
   unfold wash; have hr:= hx 0 j |>.add (hx 1 k); exact ContDiff.mul ((contDiff_exp (𝕜:=ℝ)).comp ((Complex.ofRealCLM.contDiff.comp hr).const_smul Complex.I)) contDiff_const
abbrev mornA : Land→ℝ:=fun x=> x 0 i+x 1 i
def miry (x:Land):= aper i x-1
lemma apT (z:Land): AnalyticAt ℝ (aper i) z:=by
   unfold aper; apply ContDiffAt.analyticAt; have hp: ContDiff ℝ ω (fun x:Land=> x 0 i+x 1 i):=by fun_prop
   exact (((contDiff_exp (𝕜:=ℝ)).comp (((Complex.ofRealCLM.contDiff.comp hp).const_smul Complex.I).div_const (2:ℂ)))).contDiffAt
lemma apsi(x:Land) : neap 1 (aper i) 0 x = Complex.I*(x 0 i+x 1 i:ℝ)/2:=by
   rw[← chord_n _ _ _ (apT i 0 |>.contDiffAt)]; let K:ℂ:=Complex.I*↑(x 0 i+x 1 i)/2
   have he(t:ℝ): aper i (0+t • x) = Complex.exp (↑t*K)*1:=by rw[mul_one]; unfold aper K; simp only [zero_add,Pi.smul_apply,smul_eq_mul]; push_cast;ring_nf
   simp_rw [he]; rw [exp_lead]; simp[K]
variable (h:Cleric F)(hp:LocalOn P F)(hs:Nonwrapping P 0)(hG:G.Simple)(hn:2 ≤ n.val)
include h hp hs hG hn
lemma col_hush(x:Land): ContDiffAt ℝ ω (colM i a F) 0 ∧ colM i a F 0=0 ∧ neap 1 (colM i a F) 0 x = 0:=by
   let M:=colM i a F; let N:=aper i
   have hN:N 0=1:=by simp[N,aper]
   have hA:=apT i 0|>.contDiffAt (n:=ω)
   have he: ContDiffAt ℝ ω M 0:=by
      have hx : M=mush i a F/N := by funext x; rw[Pi.div_apply, aimed, eq_div_iff (show N x≠0 from Complex.exp_ne_zero _)]; exact mul_comm ..
      rw[hx]; change ContDiffAt ℝ ω (fun x=>mush i a F x / N x) 0; simp_rw[div_eq_mul_inv]; exact (mushC i a F).contDiffAt.mul (hA.inv (show N 0 ≠ 0 from hN ▸ one_ne_zero))
   obtain ⟨hz,hv⟩:= darkL i a h hp hs hG hn x
   have hw: mush i a F=N*M:= funext fun x=> aimed _ _ _ _; rw [hw,Pi.mul_apply,hN,one_mul] at hz
   rw[hw,fderiv_mul (hA.differentiableAt (by simp)) (he.differentiableAt (by simp)),show aper i 0=1 from hN,hz] at hv
   refine ⟨he,hz,(neap1 _ _ _).trans (show fderiv ℝ M 0 x=0 from ?_)⟩; change (1:ℂ)*fderiv ℝ M 0 x + 0* fderiv ℝ (aper i) 0 x=0 at hv; simpa using hv
lemma burnt (x:Land): neap 3 (mush i a F) 0 x=neap 3 (colM i a F) 0 x+ Complex.I*↑(mornA i x)/2*neap 2 (colM i a F) 0 x:=by
   let N:=colM i a F; let P':=aper i; obtain ⟨hC,hz,hv⟩:=col_hush i a h hp hs hG hn x
   rw[show mush i a F=(fun x=>N x*aper i x) from funext fun y=>(aimed i a F _).trans (mul_comm ..), neap_prop hC ((apT i 0).contDiffAt) hz]; rw [apsi,hv,zero_mul,zero_add,neap0,show aper i 0=1 from by simp[aper] ]; unfold mornA; ring
lemma moments : Deb (fun y=>neap 3 (mush i a F) 0 (lawn d b y))= pia d i a b (F ∘ input G n) - (if i=b then (1/2:ℂ)*floft d i a (F ∘input G n) else 0):=by
   let N:=colM i a F; let P(y:Dish):= lawn d b y
   let f(y:Dish):= Complex.I *(↑(mornA i (P y)):ℂ)/2*neap 2 N 0 (P y)
   have hx : Deb (fun y=> neap 3 (mush i a F) 0 (lawn d b y))=Deb (fun y=> neap 3 N 0 (lawn d b y))+Deb f:=by rw [← map_add]; exact congr_arg _ (funext fun j=> burnt i a h hp hs hG hn _)
   rw [hx]; have he(y): mornA i (P y)= if i=b then y.2 else 0:=by simp [P,lawn,flee,mornA,step,Pi.single_apply, mul_ite];
   by_cases h':i=b
   · subst b; simp only [if_true]; change pia _ _ _ _ _ + Deb f=_
     have hv(x:ℤ): FlopZ (fun y=>f (x,y))=(x:ℂ)^ (2:ℕ)*( Complex.I/2*neap 2 N 0 (![step d,-step d])):=by
         rw[flopi]; unfold f; simp_rw [he,if_true]; simp only [P,lawn,flee_run,neap2,map_add,map_smul,_root_.smul_apply,_root_.add_apply,Complex.real_smul]; push_cast;ring
     rw[show Deb f= Complex.I*PanZ _ from rfl]
     rw[funext hv,pan_coeff _ _ (by omega),if_pos rfl]; unfold N Loft.floft; rw [← mul_assoc,mul_div_assoc',I_mul_I];ring
   simp only [h',↓reduceIte,sub_zero]; change pia _ _ _ _ _+_= _; suffices hf:f=0 by rw[hf,map_zero,add_zero]
   ext1 y; unfold f; rw [he,if_neg h'];simp
omit h hp in
lemma height (F: Axis→ Peat G n)(h:∀ i, Cleric (F i))(hp:∀ i, LocalOn P (F i)): Holt a (fun i=> F i∘ input G n)= suite fun d i=> ∑ b:Axis, Deb fun y => neap 3 (mush i a (F b)) 0 (lawn d b y):=by
   unfold Holt crest suite
   rw [mul_sum,← sum_sub_distrib]; apply Finset.sum_congr rfl fun d _ => ?_; rw [mul_sum,← sum_sub_distrib]; apply Finset.sum_congr rfl fun i _=> ?_; by_cases he:d=i
   · simp[he]
   simp only[he,↓reduceIte]; simp_rw [moments d i _ _ (h _) (hp _) hs hG hn]; rw [sum_sub_distrib]; simp
end YM.Trace.Kits
