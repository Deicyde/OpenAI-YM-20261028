import YM.UVExtension.Wren.Winners
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo
namespace Chains
namespace Ski
-- certified Low loans independent V, mask sample even at equality with unmasked charge reconstructed.
variable {R:ι→PathData G}{S:PathData G}{C:Clip} (h:Revenues v u R S) (P:BudgetPoint) (C)
include h
lemma bases (d:Low)(i): d.length (R i)=d.length S:=by unfold Low.length Low.left Low.right; simp_rw [h.slots]
lemma lands (d:Low)(i)(o:Site c): d.home (R i) P o=d.home S P o:=by unfold Low.home Low.left Low.right; simp_rw [h.slots]
lemma pays (d:Low)(i)(o:Site c): d.plain (R i) o=d.plain S o:=by unfold Low.plain Low.left Low.right; simp_rw [h.slots]
lemma pins (d:Low)(i)(o:Site c): d.proxy (R i) o=d.proxy S o:=by unfold Low.proxy Low.analogue Low.left Low.right; simp_rw [h.slots]
lemma foots (i) : lowEntry G (R i) P=lowEntry (n:=c) G S P:=by ext1 v; unfold lowEntry; congr 1; exact lands h P ..
lemma marks (i:Low): Tendsto (fun n=> i.mark (R n) C) v (𝓝 (i.mark S C)):=by
    rcases i with ⟨z,i|⟨p,q⟩⟩; exact tendsto_const_nhds
    exact (h.starts z p).mul (h.starts z q)

-- fixed (axes×duo) finite-assembly glue
omit h in
private lemma rotate [Finite α](f:ι→α×κ→ℝ)(h:∀ i,Swift v (fun n k=> f n (i,k))) : Swift v f:=by
    -- sigma cast
    let q n (i: Sigma (fun _ : α=> κ)):= f n (i.fst,i.snd); choose a ha using fun i=> (h i).books
    have he := eventually_all.mpr ha; have hf:Swift v (fun _ (i:α)=> |a i|):= Swift.sight (fun i=> ⟨_, he.mono fun n hn=> ⟨abs_nonneg _,le_refl _⟩⟩)
    let s:=Equiv.sigmaEquivProd α κ; exact (Swift.finances (f:=q) hf h (he.mono fun n he i=> budget_loosen (he i) (le_abs_self _))).letters _ s.symm.injective
variable [NeBot v]
lemma thunder : Swift v (fun n (d:Low)=>|d.mark (R n) C| *Real.exp (u*d.length (R n))) := by
    apply rotate; intro i; let f n (d:Duo):= Low.mark (R n) C (i,d); let k n(j):=|f n j| *Real.exp (u*Low.length (R n) (i,j)); have hC: Swift v (fun i (x:Unit)=> k i (.inl x)):= Swift.sight <| fun x=> ⟨|C.direct|,Eventually.of_forall (by intro i; unfold k f Low.mark Low.length; simp)⟩
    have he:= (h.fees i).2
    let a n (p:ℕ×ℕ):= k n (.inr p); have hh:Swift v a:=by refine (he.mixes he).eq (Eventually.of_forall (fun i'=> funext (fun v=>?_))); unfold a k f Low.mark Low.length Low.left Low.right; simp_rw [h.slots]; simp; rw [mul_add, Real.exp_add]; ring
    exact (hC.onion hh).eq (Eventually.of_forall (by intro i; funext j; cases j <;> rfl))
lemma acclaim : Swift v (fun n (d:Low)=> |d.mark (R n) C| * lowCost G P (d.length (R n))) :=by
   let A:= Geo.lowFee G P u; have ha:0 ≤ A:= lowFee_nonneg G P h.pos
   apply ((thunder h (C:=C)).scales A ha).le; filter_upwards with i d; let t:= |d.mark (R i) C|; let l:= d.length (R i); refine ⟨mul_nonneg (abs_nonneg _) (low_nonneg ..),?_⟩
   let k:=rowDegree P; have hb:= ((low_vs G P l).trans (mul_le_mul_of_nonneg_left (spendMoment k (half_pos h.pos) (Nat.cast_nonneg l)) (low_nonneg ..)))
   have hk: lowCost G P l ≤ A*Real.exp (u*l):=by
       refine hb.trans (le_trans (b:=A*Real.exp ((u/2)*(l:ℝ))) ?_ ?_); exact Eq.le (mul_assoc .. |>.symm); apply mul_le_mul_of_nonneg_left _ ha; exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith only [h.pos]) (Nat.cast_nonneg _))
   exact (mul_le_mul_of_nonneg_left hk (abs_nonneg (d.mark (R i) C))).trans_eq (mul_left_comm t A _)

variable (hc:Decent C P)
include hc
lemma tones : Notes v P (lowEntry (n:=c) G S P) (fun i=> Song.tuneLow (R i) C (γ:=1)) :=by
   let w n j:= mezzo (R n) C P 1 j; let f n (j: Tally c):= tuneLow (R n) C 1 j
   have hh i (j:Tally c): P.Regular ((lowEntry G S P j).support) (f i j)∧P.supBounds ((lowEntry G S P j).site) (lowEntry G S P j).support (f i j) (w i j.2):=by
       rw [← foots h P i]; exact tally_charge (R i) C P j 1 hc
   have hP : Swift v w:= by
       let t:= |(VerifiedReset.factor * (1:ℝ))| *turnFee P*P.threshold^2; apply ((acclaim h P (C:=C)).scales t (by unfold t; have :=turnFee_pos P; positivity)).eq; filter_upwards with n
       funext j; unfold w mezzo t; ring
   have he {E V:Config G c→ℝ}(i:Tally c)(α:ℝ)(e: E=α • V)(k:Choir.onstage P (lowEntry G S P) i G): k.read E= α*k.read V:=by rw [e]; exact WilsonStartup.Start.left_mult _ _ _
   have ht (i:Tally c)(u:Low)(F:i.2=u): Tune v (fun n (k:Choir.onstage P (lowEntry G S P) i G)=>k.read (f n i)):=by
       subst u; let A (V: Config G c) := VerifiedReset.factor* i.2.plain S 0 (i.1.view V)
       let L: ℝ:=VerifiedReset.factor; have hf n:f n i=i.2.mark (R n) C • A:=by funext i'; change L*1*(i.2.mark (R n) C * i.2.plain (R n) 0 _)=i.2.mark (R n) C *A i'; rw [pays h]; unfold L A; ring
       simp_rw [he i _ (hf _)]; apply (Tune.constant _ _ (marks h (C:=C) i.2)).mul
       -- A's multiplicative mark may zero at all R. use plain sup bound from Decent.
       let U :Config G c→ ℝ:= i.2.plain S 0; have hv:=i.2.plain_bill S C (0:Site c) hc
       have hM:P.Regular (i.2.home S P 0) U:= reg_bill hv (Low.plain_cont ..).measurable (i.2.plain_local S P hc.radius 0) (i.2.plain_gauge S 0)
       have hD : P.supBounds (lowEntry G S P i).site _ A _:=CouplingShape.sup_scale L (Seat.sup i.1 hM (Bill.sup hv (fun _ h=>h)))
       refine ⟨⟨_,Eventually.of_forall fun n k=>tap_bound.mp hD|>.2 k⟩,fun ε he=> Eventually.of_forall (fun i x=> by rw [sub_self,norm_zero]; exact he.le)⟩
   have hv : Swift v (fun i (_:Seat c)=> (1:ℝ)):=Swift.sight (fun i=>⟨1,Eventually.of_forall fun _=>⟨zero_le_one,le_rfl⟩⟩)
   exact ⟨fun i j=> (hh i j).1,⟨_,hv.mixes hP,Eventually.of_forall (fun n j k=> by rw [one_mul]; exact tap_bound.mp (hh n j).2|>.2 k)⟩,fun i=> ht i i.2 rfl⟩
lemma vibes (b:ι→ℝ){t:ℝ}(he:Tendsto b v (𝓝 t)): Notes v P (lowEntry (n:=c) G S P) (fun i => tuneLow (R i) C (b i)):=by
    have hP: (fun i n=>b i • tuneLow (R i) C 1 (n:=c) n)= (fun i n=>tuneLow (R i) C (b i) n):=by funext i n; unfold tuneLow; rw [smul_smul,mul_one,mul_comm]
    rw [←hP]; exact (tones h P hc).swells b he
end Ski
end Chains
end YM.UVExtension.Wren
