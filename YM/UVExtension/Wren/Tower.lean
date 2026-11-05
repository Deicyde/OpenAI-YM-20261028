import YM.UVExtension.Wren.Dew
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
open Badge Chains Marlin Trio Slide Animals
namespace Gold
-- used also for post carries
lemma pops {f:ι→κ→ α→ℝ}(h:Transit v f):Transit v (fun i j V=> Real.exp (f i j V)-1):=by
    obtain ⟨a,ha,hF⟩:=h.rain; obtain ⟨B,hB,hb⟩:= ha.tills
    let t:=2+(Real.exp B+1); have ht:0<t:=by unfold t; positivity
    refine ⟨⟨_,ha.scales t ht.le,(hF.and hb).mono fun i h j V=>?_⟩,fun i=> (h.meters i).cont (Real.continuous_exp.sub continuous_const)⟩
    have hx:= h.1 j V; have hp:= hx.trans (budget_single h.2 _); let s:=f i j V; change |Real.exp s-1|≤t*a i j
    by_cases hh: |s| ≤ 1
    · exact (Real.abs_exp_sub_one_le hh).trans (mul_le_mul (by unfold t; linarith [Real.exp_pos B]) hx (abs_nonneg _) ht.le)
    refine le_trans (norm_sub_le (Real.exp s) (1:ℝ)) ?_; rw [Real.norm_of_nonneg (Real.exp_pos _).le,norm_one]; exact ((add_le_add_left (Real.exp_monotone ((le_abs_self _).trans hp)) 1).trans (le_add_of_nonneg_left zero_le_two)).trans (le_mul_of_one_le_right ht.le (((not_le.mp hh).le).trans hx)) -- le directions
open Ovens Ovens.Pipes in
lemma earnS {X:Pipes G n}{E: ℕ≃X.Pellet}{a:ι→ Ovens.Tap G n} (P: BudgetPoint)(h:Transit v (fun i j V=> (a i).forced j V))(he:Transit v (fun i j V=> (a i).logarithm j V)): Transit v (fun i j U=> solid E P (a i) j U):=by
    let f i j V:= reach (a i) j V; have ht:Transit v f:=by
        let g:= h.merge (pops he); refine g.fade ?_; filter_upwards with i j; cases j <;> rfl -- fun
    obtain ⟨C,hC,hK⟩:=ht.rain; let g n(s:Finset Label)(X):=∏ j∈s,f n j X; have hp: Transit v g:=by
        obtain ⟨r,hr⟩:= hC.books
        refine ⟨⟨_,hC.powerList,hK.mono fun i hi s V=> ?_⟩,fun i=> Sheets.tunes _ _ fun x _=> ht.meters _⟩; unfold g; rw [norm_prod]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun _ _=> hi _ _)
    exact (hp.many _ (Subtype.val_injective.comp E.injective) (fun _ (x:Config G n)=> x)).masks (fun i x=> (addr E P i).eligible P.threshold x)
end Gold
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k Chi.canonical)(h:StableR v R)
variable (j:ι)(P:BudgetPoint)(d:ι→ℝ)(u:ι→ℕ)(hp:Tendsto u v atTop)(hf:∃ t,Tendsto d v (𝓝 t))(hP:P.threshold=temp s)(ht:P.order ≤ k)(hC:Decent (T j).low P)
variable [NeBot v][v.IsCountablyGenerated]
local notation "Y" => (Beam.marquee (H j) P)
include p h j hP ht hC hp hf
omit hP ht hC hp hf in
lemma twiner (o:Site c)(n i x): Meadow.garnerAt (H n) P o i*(((Beam.marquee (H n) P).read (plusone (H n) (helm (H:=H) n) Chi.canonical (d n))).regularOccurrence P i x)= Meadow.garnerAt (H j) P o i*masked P.threshold ((Beam.marquee (H j) P).reg i).support ((plusone (H n) (helm (H:=H) n) Chi.canonical (d n)).logRead i) x:=by
   rw [p.tiles h j P]; apply congr_arg; unfold Activities.regularOccurrence; change masked P.threshold ((Beam.marquee (H n) P).reg i).support _ _=_; rw [siteD p h j P n i]; rfl
lemma advances (o:Site c): Tune v (fun n (U:Config G c)=> Trio.earned P (helm (H:=H) n) (d n) (u n) o U):=by
    let A n:=(plusone (H n) (helm (H:=H) n) Chi.canonical (d n)).logRead; have ht':=TransitM.under (p.armory h j P hP ht d hf hC)
    let X(i:ℕ):= Meadow.garnerAt (H j) P o i
    apply (TransitM.sorted (TransitM.scaled X (a:=1) (fun i=>by unfold X; rw [abs_of_nonneg (Meadow.nonnegative ..)]; exact Meadow.portions ..) ht' zero_le_one) (fun i=> Meadow.panel (H i) (u i)) _ (p.upper h j u hp)).switch
    filter_upwards with n; funext x; unfold Trio.earned; exact sum_congr rfl fun i _=> (p.twiner h j P d o n i x).symm
variable {Qp:Stars→Side}{κ w':ℕ} (hq:∀ i:Stars,(Qp i).val=2*(κ+i.val))(hw:κ+5≤w')(g:ι→ ∀ i:Stars,Trio.Offer G (Qp i))(hh:∀ i,Aside.Stars v P (fun n=> g n i))
include hq hh hw
lemma seeks (x:Site c): Tune v (fun n V=> insight P (helm (H:=H) n) (d n) (u n) hq w' (g n) x V):=by
    let X:= (skyline p h j P d u hp hf hP ht hC).small x; exact ((p.advances h j P d u hp hf hP ht hC x).sub (X.cues (fun _=> Fly.star G P c))).sub (Gold.mirrored hq hw g hh x)

def freshW (n:ι):= shapeP (H n) (helm (H:=H) n) hq (u n) w' P (g n) (d n)
def salts (n:ι):= bison (chants (χ:=Chi.canonical) (H:=H) d u n) (ornament (c:=c) hq (g n)) (insight P (helm (H:=H) n) (d n) (u n) hq w' (g n))
-- Outputs on deterministic R. Loan layout preserved. signs true.
lemma barline : let F:= bookA Y w' P; Notes v P F.reg (fun n=> (freshW (H:=H) P d u hq (w':=w') g n).logRead) ∧
    Transit v (fun n=>(freshW (H:=H) P d u hq (w':=w') g n).hardRead) :=by
    let A:= salts (w':=w') (H:=H) P d u hq g; let X n:= poursP P (lodge Y w' (2*w')) (A n)
    intro F; have hv (n):freshW (H:=H) P d u hq (w':=w') g n=X n:=by unfold freshW shapeP; rw [p.versed h j]; rfl
    simp_rw [hv]; constructor
    · exact (((p.tinted h j P d u hp hf hP ht hC).plucks ((Gold.august hq hw g hh).rotary))).draws (leanU c) (leanU c).injective
    let J:= Door c; let t n:= Trio.insight P (helm (H:=H) n) (d n) (u n) hq w' (g n)
    have he(x:J): Tune v (fun n V=> choir (-t n) x V) :=by
       have hp:= seeks p h j P d u hp hf hP ht hC hq hw g hh x.2
       exact (hp.cues x.1.view).cont (F:=fun u=> Song.Rim c * -u) (by fun_prop)
    have hz:Transit v (fun n (i:ℕ)(x:Config G c)=> (A n).logarithm i x):=by
        let f n i V:= choir (-t n) i V
        let H := ((Transit.zero (κ:=ℕ)).merge (Transit.ready (R:=f) he)).many (leanU c) (leanU c).injective (fun _ x=> (x:Config G c)) -- eta nonrfl
        apply H.fade; filter_upwards with n k; let z:= leanU c k; change Sum.elim _ _ z= _; exact (show ∀ i:Civ c, Sum.elim (fun _:ℕ=>fun _:Config G c=> (0:ℝ)) (f n) i=Sum.elim (fun _=>0) (choir (-t n)) i from Sum.rec (fun _=> rfl) (fun _=>rfl)) z
    exact Gold.earnS P (psy p h j P d u hp hf hP ht hC) hz
end Choir
end YM.UVExtension.Wren
#print axioms YM.UVExtension.Wren.Choir.barline
