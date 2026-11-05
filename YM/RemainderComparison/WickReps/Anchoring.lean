import YM.RemainderComparison.WickReps.Shapes

/-!
# Centered would-be valuation. No orientation shift on root packet,
 preserve exact support masks at every point. Volume comparison only calls
 prescribers on globally flag-free pairs
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.WickReps
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n c C f L : Side} {Y:Stars→Side} {P:BudgetPoint}{r z k w m p:ℕ}{a b β v R e x:ℝ}

-- Strictly interior box assembled on `neighbors k o`. Reserve start z+z; never wrap assumed outside injectivity
variable (g:Config G f→ℝ)(h:2*w ≤ f.val)(hr:2*r≤w)
def podium (r:ℕ) : Cover:= fun _=> r
def home (f:Side)(r:ℕ) : Site f:= wrap f (podium r)
def ploy (o:Site c)(r:ℕ) := o-wrap c (podium r)
def garment (o:Site c)(r:ℕ) : Config G c→ Config G f := shape (cognac h) (ploy o r)
variable (o:Site c)(hp:w+1 ≤ z)(hC:2*z<c.val) (hv:2*z≤k)
lemma meters : separation o (ploy o r) ≤ r:= by
   rw [separation_comm]; trans separation (ploy o r) (wrap c (podium r)+ploy o r)
   · unfold ploy; rw [add_sub_cancel ..] -- identity?
   exact Slide.sep _ _ (box_test.mpr ⟨fun i=> by unfold podium; omega,fun i=> le_rfl⟩)
include hr hp hv
lemma reaches : neighbors z (ploy o r) ⊆ neighbors k o:= by
   intro i hi; apply (neighbors_mem ..).2; apply le_trans (separation_triangle o (ploy o r) i); have hh:= meters (r:=r) o; have h': separation (ploy o r) i≤ z:=(neighbors_mem ..).1 hi; omega

omit hp hv in
lemma linked (U: Config G c): Agrees (Lattice.box r) (expandAt o U) (expandAt (home f r) (garment h o r U)):=by
   let x:= podium r; have hz i (hi:i∈Lattice.box r) : i+x∈ crystal w:=by obtain ⟨ht,h⟩:= box_test.mp hi; refine (cryst _).2 ⟨fun j=>?_,fun j=>?_⟩ <;> simp only [Pi.add_apply,x,podium] <;> specialize ht j <;> specialize h j <;> omega
   rintro ⟨i,j⟩ hi hk; obtain he:= hz _ (show i+step j∈ Lattice.box r from hk); have hv:= Slide.vested h (i+x) (hz _ hi) j (by rw [add_right_comm]; exact he) U (ploy o r)
   simp_rw [map_add] at hv; unfold ploy at hv; change U (_,_)=shape (cognac h) _ U (_,j); change U (wrap c i+o,j)= shape (cognac h) _ _ (wrap _ i+home f r,j)
   refine Eq.symm (hv.trans ?_); unfold x; rw [show wrap c i+wrap c (podium r)+(o-wrap c (podium r))=wrap c i+o from (by abel)]

-- ROOT correspondence
structure Matches (g' : Config G c → ℝ)(g : Config G f→ℝ)(P : BudgetPoint)(r:ℕ)(o:Site c) (b:ℝ) : Prop where
   localP : LocalOn (neighbors r o) g'
   levy (V : Config G c) (U : Config G f) : flags P.threshold V=∅→flags P.threshold U=∅→Agrees (Lattice.box r) (expandAt o V) (expandAt (home f r) U)→ g' V=b*g U

variable {g' : Config G c → ℝ} (U:Config G c)
lemma refined (hm: 4*r+16 ≤ c.val)(hT:Matches g' g P r o b) (hU: Healthy P.threshold (neighbors k o) U) : g' U=b*g (garment h o r U):=by
   have hb: flags P.threshold (garment h o r U)=∅:= allFlag (cognac h) (ploy o r) U _ (fun i=> reaches hr o hp hv ((neighbors_mem ..).2 ((village h (ploy o r) i).trans (by omega)))) _ P.threshold_pos.le hU
   obtain ⟨V,hV,hL⟩:= Slide.shifts U o r (by omega) P.threshold P.threshold_pos.le (hU.mono_left (fun i (hi:i∈neighbors r o)=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega))))
   have hg:=linked h hr o U
   exact (hT.localP V U (readNear o (by omega) hL)).symm.trans (hT.levy V (garment h o r U) hV hb (fun i hi hj=> (hL _ hi hj).trans (hg _ hi hj)))
omit hv hp hr in
lemma postage (o:Site c) (g : Config G c→ℝ) {X: Support c}(h :P.Regular X g)(hp:P.supBounds o X g a) (x:Site c) (hX:separation o x ≤ k) : P.supBounds x X g (((1+(k:ℝ))^P.power)^P.order * a):=by
   let Q:= Complex.ofRealCLM; have hz:P.Regular X (Q∘g):= regular_mapped _ h
   have ht:P.supBounds o X (Q ∘ g) a:=by
      refine ⟨hp.1, fun U hU l hl hv=>?_⟩; rw [Local.left_linear _ _ (h.smooth _ hU) hl]; simpa [Q] using hp.2 U hU l hl hv
   have hh:= Push.Local.bound_shift ht hz x; refine ⟨mul_nonneg (by positivity) hp.1, fun U hU l hl hv=>?_⟩; have hj:= hh.2 U hU l hl hv; rw [Local.left_linear _ _ (h.smooth _ hU) hl] at hj; simp only [Q, Complex.ofRealCLM_apply,Complex.norm_real] at hj
   apply hj.trans; apply mul_le_mul_of_nonneg_right _ hp.1; gcongr

def burse (P:BudgetPoint) (k z:ℕ)(B: ℝ):= ((1+((k+z:ℕ):ℝ))^P.power)^P.order * (Trio.tilt P z * B)
include hC
lemma opal (he:Arc.Deduct G P β z R)(hf:P.Regular univ g)(hg:0≤a)(hb: Portal.Mare P g β R a):
     let f:=g∘(garment h o r); P.Regular (neighbors k o) f ∧ ∀ x∈ neighbors k o, P.supBounds x (neighbors k o) f (burse P k z a):=by
   intro g'; have hh := calibrated g he hC h hp hf hg hb (ploy o r)
   refine ⟨CouplingShape.reg_extend hh.1 (reaches hr o hp hv), fun x hx=> sup_larger (postage (ploy o r) g' hh.1 hh.2 x ?_) (reaches hr o hp hv)⟩
   apply le_trans (separation_triangle _ o x); rw [separation_comm]; have hf:=meters (r:=r) o; have hQ : separation o x≤ k:= (neighbors_mem ..).1 hx; omega
end YM.RemainderComparison.WickReps
