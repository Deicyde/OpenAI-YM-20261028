import YM.RG08.Cairn.Book
import YM.RG08.Tack.Stamp
/-! # Normalized Haar measure log and individual rung grains. !-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cairn
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}

def faded (B:ChartRatio G):Still G.ColorIndex:=Real.log ∘ B.J ∘ vase G
lemma faded_pace {B:ChartRatio G}(h:LocalRatio B):Pace (faded B):=by
 let j:G.ColorIndex→ℝ :=0
 have hb:=h.germ 0 (Metric.mem_ball_self h.patch)
 have ht:Pace (B.J ∘ vase G):=ContDiffAt.comp (0:Cellar G.ColorIndex) (g:=B.J) (by change ContDiffAt ℝ ω B.J (vase G 0);rw [map_zero];exact hb) (vase G).contDiff.contDiffAt
 apply (Real.contDiffAt_log.mpr ?_).comp _ ht
 simp [h.anchored,map_zero]
def style (i:Axis):G.ColorIndex→Market (Loc G 1):= fun j=>(0,(coord i,j))
def vanity (B:ChartRatio G)(n:ℕ): Flake n (Market (Loc G 1)):= ∑ i:Axis,Tack.trace n (faded B) (style i)
def layer (B:ChartRatio G)(σ:ℝ)(n:ℕ):ℝ:=∑ i:Axis,Tack.price n σ (faded B) (style i)
lemma layer_nn (B:ChartRatio G) (σ:ℝ)(n):0≤ layer B σ n:=Finset.sum_nonneg (fun _ _=>price_nn ..)
lemma vanity_bill (B:ChartRatio G)(n:ℕ){σ:ℝ}: Held (carpet _) σ (layer B σ n) (vanity B n) ∧ Forms.Sym (vanity B n) ∧ Cohort (vanity B n):=
 ⟨Held.sum _ _ _ (fun _ _=>price_nn ..) (fun _ _=> (trace_bill ..).1), (show Forms.Sym _ from fun x=>funext fun v=>by unfold woven vanity; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro i _; exact congrFun ((trace_bill (σ:=σ) n _ _).2.1 x) v), Cohort.sum _ _ (fun _ _=> (trace_bill (σ:=0) n _ _).2.2)⟩

def incense (B:ChartRatio G) (c:Side): Still (Lines G c 1):=∑ i:Axis, ∑ x:Site c, faded B ∘ Camera.roll (glance x (style i))
lemma sticker {B:ChartRatio G}(h:LocalRatio B)(x:Site c)(i:Axis):Pace (faded B ∘ Camera.roll (glance x (style i))):=by
 apply ContDiffAt.comp _ _ (roll_pace (glance_pace x (style i (G:=G))))
 exact faded_pace h
lemma sticker' {B:ChartRatio G}(h:LocalRatio B)(c:Side)(i:Axis):Pace (∑ x:Site c,faded B ∘ Camera.roll (glance x (style i))):=Tack.Pace.metal _ _ fun _ _=>sticker h _ _
lemma lit {B:ChartRatio G}(h:LocalRatio B)(c:Side):Pace (incense B c):=Tack.Pace.metal _ _ fun _ _=>sticker' h c _
lemma named {B:ChartRatio G}(h:LocalRatio B)(c:Side):incense B c 0=0:=by unfold incense; simp only [Finset.sum_apply]; refine sum_eq_zero fun _ _=>sum_eq_zero fun _ _=>?_; change Real.log (B.J (vase G 0))=0; rw [map_zero,h.anchored,Real.log_one]
lemma reflected {B:ChartRatio G}(c:Side)(v:Cellar (Lines G c 1)): incense B c v= ∑ x:Edge (Site c), Real.log (B.J (arm G c 1 v (x.1,coord x.2))):=by
 unfold incense; simp_rw [Finset.sum_apply]; rw [Finset.sum_comm,Fintype.sum_prod_type];iterate 2 (apply Finset.sum_congr rfl; intro i _)
 unfold faded Function.comp roll glance style
 simp only [map_zero,zero_add]; rfl
open MvPolynomial in
lemma glance_priced (f:Still I)[Fintype I][Fintype J](m:I→Market J)(z:Site c)(h:Pace f): tap n (flask (f ∘ roll (glance z m)))= rename (fun i => (wrap c (m i).1+z,(m i).2)) (tap n (flask f)):=by
 let E (i:I):Cove c J:= (wrap c (m i).1+z,(m i).2)
 have he:rescaleFields (glance z m)=fun i=>rod (E i):=by
   funext i; unfold glance rescaleFields;rw [Camera.lamp]; ext b :1;change tap _ _=tap _ _;rw [look,hopper]
 rw [flask_comp (glance_pace z m) rfl h,he,censor]
open MvPolynomial in
lemma vanity_read {B:ChartRatio G}(h:LocalRatio B)(o:Fin n):parley (pour (P:=c) (vanity B n) o)=tap n (flask (incense B c)):=by
 rw [vanity, flow o _ _ (fun i=>Tack.price n 0 _ _) 0 (by norm_num) (fun i _=> (trace_bill ..).1),parley_sum,incense,slurry _ _ (fun i _=>sticker' h c i)]
 unfold tap;rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [slurry _ _ (fun _ _=>sticker h ..),map_sum];apply MvPolynomial.funext;intro x
 rw [Tack.picture,map_sum]; apply sum_congr rfl; intro y _; change _=(MvPolynomial.eval _ ((tap n) _));rw [glance_priced _ _ _ (faded_pace h),eval_rename];rfl

def aroma (S:StepData c f)(B:ChartRatio G): Port (Epic S.patch G c):= belt (fun i:Lines G f 1=>rod (lowSlot S i)) (flask (incense B f))
lemma aroma_read {B:ChartRatio G}(h:LocalRatio B)(S:StepData c f)(o:Fin n): tap n (aroma S B)=parley (pour (P:=c) (box S.patch (vanity B n)) o):=by
 unfold aroma;rw [censor,←vanity_read h o,low_poly S _ (vanity_bill B n (σ:=1)).2.2]

-- record semantic charge after ANY formal re-expression and physical analytic mapping
lemma smell [Fintype I]{B:ChartRatio G}(h:LocalRatio B)(S:StepData c f)(A:Strip (Epic S.patch G c) I)(hp:∀ i,Pace (A i))(ht:roll A 0=0):belt (rescaleFields A) (aroma S B)= flask (fun x=>∑ z:Edge (Site f),Real.log (B.J (low S (roll A x) (z.1,coord z.2)))):=by
 rw [aroma,driven];let M:=A ∘ lowSlot S
 have he:roll M 0=0:=funext fun i=>show _=0 from congrFun ht (lowSlot S i)
 change belt (rescaleFields M) _=_
 rw [←flask_comp (h:=M) (fun j=>hp _) he (lit h f)]
 congr 1; funext x; rw [Function.comp_apply,reflected];rfl
end YM.RG08.Cairn
