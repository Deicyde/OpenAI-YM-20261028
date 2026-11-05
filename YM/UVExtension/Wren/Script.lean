import YM.UVExtension.Wren.Sodium
import YM.UVExtension.Tabernacle.Sway
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
open Song Strata Gala Concert Geo Chains Lamppost Tabernacle
-- measured slots. from τ-transit to high weights and vice versa. Every anchor costs bounded above, some bounded below when forgetting tags. PRESERVE all indicated scalars, incl unhealthy K.
namespace Verso
open Meter BoundedContinuousFunction
variable {B:Type} {M:Meter.{0,0,0} κ B}[Fintype B][Nonempty B]
def Upper (M:Meter κ B):=∃ q:ℝ,0<q∧∀ i j,M.cost i j≤q
def lower (M:Meter κ B):= ∀ i,∃ j,1≤M.cost j i
lemma fetch (g:κ→ℝ)(f:M.Slot)(hA:SumBudget g a)(hp:∀ x k,‖f x k‖≤g x){t:ℝ}(hx:0≤ t)(he:∀ i j,M.cost i j≤t): M.MeasureP f (t*a):= ⟨g,fun i=>⟨hA.1 _,hp i⟩,fun i=> budget_mono (budget_scale hx hA) (fun j=>mul_nonneg (M.nonneg ..) (hA.1 _)) (fun i=> mul_le_mul_of_nonneg_right (he _ _) (hA.1 _))⟩ -- t add
variable {F:ι→ Meter.Slot M} [v.NeBot]
lemma start (h:Transit v F)(hu: Upper M):∃ t,Tendsto (fun n=> vibe M (F n)) v (𝓝 t):=by
   obtain ⟨b,hb,hB⟩:=hu; obtain ⟨f,hf,hR⟩:=h.rain; obtain ⟨y,hr⟩:=hf.books; have hp n (hm:SumBudget (f n) y) (hv:∀ j x,‖F n j x‖≤ f n j):= fetch _ _ hm hv hb.le hB
   have hv:= (hr.and hR).mono fun n hn=> hp n hn.1 hn.2
   apply cauchy_map_iff_exists_tendsto.mp; rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero]; rw [Metric.tendsto_nhds]; intro ε he; let z:=ε/(2*b); have hz:0<z:= div_pos he (by positivity)
   filter_upwards [h.drought z hz,(tendsto_fst.eventually hv).and (tendsto_snd.eventually hv)] with n hn hi
   obtain ⟨g,hg,hV⟩:=hn; let G i j:=F n.1 i j-F n.2 i j; have h':=fetch (M:=M) g G hg hV hb.le hB; have hk:=ticks _ h' (mul_nonneg hb.le hz.le)
   rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]; change dist (vibe _ _) (vibe _ _) < _; rw [dist_eq_norm,← subPrint M G (F n.1) (F n.2) (fun _ _=> rfl) ⟨_,h'⟩ ⟨_,hi.1⟩ ⟨_,hi.2⟩]; exact hk.trans_lt ((show b*z=ε/2 by unfold z; field_simp).trans_lt (half_lt_self he))
-- use sup envelope gauge complete at level.
lemma unearth {f:κ→ℝ}(hh:∀ i,0 ≤ f i)(h:∀ i,SumBudget (fun j=> M.cost i j*f j) a) (hp: lower M): SumBudget f (Fintype.card B * a):=by
    have hz:=budget_over Finset.univ (c:=fun _=> a) (fun i j=> M.cost i j*f j) (fun i _=>h i); rw [sum_const,card_univ,nsmul_eq_mul] at hz; apply budget_mono hz hh; intro i; obtain ⟨x,hx⟩:= hp i; exact (le_mul_of_one_le_left (hh i) hx).trans (single_le_sum (fun j _=> (h j).1 i) (mem_univ x))
variable (F)
def ferns (n:ι)(x:κ) := sSup (Set.range (fun t:Option (M.test x)=>t.elim (0:ℝ) (fun j=>‖F n x j‖)))
lemma act (n:ι)(h:∃ b,M.MeasureP (F n) b):  (∀ j,0 ≤ ferns F n j∧∀ x,‖F n j x‖≤ ferns F n j)∧ ∀ (j:κ)(x:ℝ), 0≤x → (∀ y, ‖F n j y‖ ≤ x)→ ferns F n j≤ x :=by
    obtain ⟨t,f,hf,hp⟩:=h; let g j(v:Option (M.test j)):=v.elim 0 (fun i=> ‖F n j i‖); have hh j: BddAbove (range (g j)):=⟨f j,forall_mem_range.mpr (fun i=> by cases i; exact (hf _).1; exact (hf j).2 _)⟩
    exact ⟨fun i=> ⟨(show g i none ≤ ferns F n i from le_csSup (hh i) (Set.mem_range_self _)),fun y=> le_csSup (hh i) (Set.mem_range.mpr ⟨some y,rfl⟩)⟩,fun i x hx h=> csSup_le (range_nonempty (g i)) (forall_mem_range.mpr (fun k=>by cases k; exact hx; exact h _))⟩
lemma lacks (hv: lower M)(ht: ∀ n,∃ b,M.MeasureP (F n) b) {T:Chime M}(h:Tendsto (fun i=> vibe M (F i)) v (𝓝 T)): Transit v F:=by
    let p:=ferns F
    let β (n:ι×ι) i x:= F n.1 i x-F n.2 i x
    have he(n:ι×ι):∃ b,M.MeasureP (β n) b:=by
       obtain ⟨k,a,hA,h⟩:=ht n.1; obtain ⟨v,b,hb,h'⟩:=ht n.2
       exact ⟨k+v,⟨fun i=> a i+b i,fun i=> ⟨add_nonneg (hA i).1 (hb i).1,fun x=>(norm_sub_le ..).trans (add_le_add (hA i|>.2 x) (hb i|>.2 x))⟩,fun x=> by simpa only [mul_add] using budget_plus (h x) (h' x)⟩⟩
    let s:ℝ:= ↑(Fintype.card B);
    have hs:0<s:=by unfold s; positivity
    have hP(n:ι): Summable (p n):=by obtain ⟨y,k,hK,h⟩:= ht n; exact (budget_mono (unearth (fun i=>(hK i).1) h hv) (fun i=> (act F n (ht n)|>.1 i).1) (fun i=> act F n (ht n)|>.2 _ _ (hK i).1 (hK i).2)).2.1
    have hR:∃ r,∀ᶠ n in v, SumBudget (p n) r:=by
       refine ⟨s*(‖T‖+1),?_⟩; filter_upwards [h.norm.eventually_le_const (show ‖T‖ < ‖T‖+1 by simp)] with n hn
       obtain ⟨a,hA,hz⟩:= (paper M (ht _) hn).afloat; exact budget_mono (unearth (fun i=>(hA i).1) hz hv) (fun i=>(act F n (ht n)|>.1 i).1) fun i=> act F n (ht n)|>.2 _ _ (hA i).1 (hA i).2
    have hV(ε:ℝ)(hε:0<ε): ∀ᶠ n in v ×ˢ v, ∃ c: κ→ℝ,SumBudget c ε ∧ ∀ j y, ‖β n j y‖ ≤ c j:=by
       filter_upwards [(((h.comp tendsto_fst).sub (h.comp tendsto_snd)).norm).eventually_le_const (show ‖T-T‖ < ε/s by rw [sub_self,norm_zero]; positivity)] with n hn
       have hT (n:ι×ι):vibe M (β n)=vibe M (F n.1)-vibe M (F n.2):= subPrint _ _ _ _ (fun _ _=>rfl) (he _) (ht _) (ht _)
       obtain ⟨a,hA,h⟩:=(paper M (he n) (show ‖vibe M (β n)‖≤ ε/s from hT n ▸ hn)).afloat; refine ⟨a,budget_loosen (unearth (fun i=> (hA i).1) h hv) (le_of_eq ?_),fun i=> (hA i).2⟩
       change s*(ε/s)=ε; field_simp
    have hh: Swift v p:=by
        apply Swift.absorbs hR; intro ε hε; obtain ⟨P,ht',Q,hQ,hm⟩:=eventually_prod_iff.mp (hV ε hε); obtain ⟨n,hn⟩:=hQ.exists
        choose c hc hC using fun i (hi:P i)=>hm hi hn
        let w i:= if h:P i then c i h else 0
        refine ⟨fun _=>p n,w,Swift.nil _ (u:=∑' x,p n x) ⟨fun i=> (act _ n (ht n)|>.1 i).1,hP _,le_rfl⟩,ht'.mono fun i hi=> ?_,ht'.mono fun i hi k=>?_⟩
        · unfold w; rw [dif_pos hi]; exact hc i hi
        unfold w; rw [dif_pos hi]; refine act _ i (ht i)|>.2 _ _ (add_nonneg ((act F n (ht n)|>.1 k).1) ((hc i hi).1 _)) ?_; intro j; exact (norm_le_norm_add_norm_sub' (F i k j) (F n k j)).trans (add_le_add ((act _ n (ht n)|>.1 k).2 j) (hC i hi k j))
    obtain ⟨r,hr⟩:=hR
    refine ⟨⟨p,hh, Eventually.of_forall fun n i=> (act F n (ht n)|>.1 i).2⟩,fun x=> ⟨⟨r,hr.mono fun n hn i=> ((act F n (ht n)|>.1 x).2 i).trans (budget_single hn _)⟩,fun ε hε=> (hV ε hε).mono fun n hn U=>?_⟩⟩
    obtain ⟨b,hb,hp⟩:=hn; exact (hp x U).trans (budget_single hb _)
end Verso
end YM.UVExtension.Wren
