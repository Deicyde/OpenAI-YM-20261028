import YM.FullVolume.Renew.Reforms
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Ledgers
open Geo WilsonStartup
lemma Twin.ul (f g:ℕ→ℝ)(h:Twin f g)(hx:(J:Filter ℕ)≤ atTop):Glints J f g:=by
    refine Glints.time ?_ (h.goes.mono_left hx); obtain ⟨C,hC,_⟩:=h.bound; exact FullVolume.Shadow.flowers (x:=0) (f:=f) (b:=C) (Eventually.of_forall fun i=> by rw [dist_zero_right]; exact hC _)
variable {U V:ℕ→ Cad G}{ω' a e d:ℝ}{c:Side}{B:BudgetPoint}{p:Clip} (hd:Decent p B)
lemma meter (R:Cad G) : ∀ k:ℕ,∃ T:Finset Low,∀ i,Low.length R.path i ≤ k →i∈ T:=by
          intro k; obtain ⟨A,hA⟩:=tagSet k; refine ⟨Finset.univ ×ˢ ((Finset.univ:Finset Unit).disjSum (A×ˢ A)),fun i hi=>?_⟩
          rcases i with ⟨i,u|⟨u,v⟩⟩
          · simp
          change (Beacon.flag u).length+(Beacon.flag v).length≤k at hi
          exact mem_product.mpr ⟨mem_univ _,Finset.inr_mem_disjSum.mpr (mem_product.mpr ⟨hA u (by omega),hA v (by omega)⟩)⟩
private lemma noble (p:Clip) (d: Low):∃ V: Cad G,Low.mark V.path p d ≠ 0:=by
    let V:Cad G:= ⟨fun i j=>1,0,0,0⟩; refine ⟨V,?_⟩; rcases d with ⟨p',i|i⟩; · exact p.quadratic_pos.ne'
    change (1:ℝ)*1≠0; norm_num
private lemma broil (h:Soul atTop U V)(p:Clip) (i:Low): Glints atTop (fun n=>Low.mark (U n).path p i) (fun n=> Low.mark (V n).path p i):=by
    rcases i with ⟨i,i'|i'⟩; · exact ⟨p.direct,tendsto_const_nhds,tendsto_const_nhds⟩
    exact (h.1 i i'.1).prods (h.1 i i'.2) continuous_mul
include hd
lemma loch (h:∀ n,(U n).path.Bounds p ω' a e)(he:∀ n,(V n).path.Bounds p ω' a e)(hv:Soul atTop U V): Canopy B (lowEntry (n:=c) G (U 0|>.path) B) (fun n i=> i.2.fresh (U n).path p 0 1 ∘ (Seat.view i.1)) (fun n i=> i.2.fresh (V n).path p 0 1 ∘ (Seat.view i.1)) :=by
    let f(T:ℕ→Cad G) n(i: Tally c):= Low.fresh (T n).path p i.2 0 1 ∘ Seat.view i.1
    have hf (U:ℕ→Cad G) (h:∀ n,(U n).path.Bounds p ω' a e):PulseWise B (lowEntry G (U 0|>.path) B) (f U):=by
         let V n i:= |Low.mark (U n|>.path) p i| *lowCost G B (Low.length (U 0|>.path) i); have hs: Sparse V:= neptune _ (meter (U 0)) (fun i x=>mul_nonneg (abs_nonneg _) (low_nonneg ..)) (half_pos (h 0|>.width)) (fun n=> Geo.low_budget G B (U n).path (h n))
         let C:= turnFee B*B.threshold^2; have he : 0≤C:= mul_nonneg (turnFee_pos _).le (sq_nonneg _); refine ⟨fun i k=> k.1.regular (k.2.fresh_regular (U i|>.path) p 0 hd 1),_,(trep (ι:=Seat c) hs).climb he,fun n i=>?_⟩
         apply VerifiedReset.sup_le (Seat.sup i.1 (i.2.fresh_regular (U n|>.path) p 0 hd 1) (Bill.sup (Low.fresh_bill _ p i.2 0 hd 1) (fun _ h=>h))); change turnFee B*(|(1:ℝ)| *B.threshold^2* (V n i.2)) ≤ _; unfold C; simp only [abs_one,one_mul, mul_assoc]; rfl
    refine ⟨hf U h,hf V he,fun i b hb=>?_⟩; obtain ⟨s,hs⟩:=noble (G:=G) p i.2
    have hh T n:(f T n i) = (Low.mark (T n|>.path) p i.2/Low.mark s.path p i.2) • f (fun _=>s) 0 i:=by funext u; unfold f; dsimp only [Function.comp_apply,Low.fresh,Pi.smul_apply,smul_eq_mul]; change (1*_)*_=_ *((1*_)*(Low.proxy (T n|>.path) _ _ _-Low.plain (T n|>.path) _ _ _)); field_simp
    have hx:= i.1.sup (i.2.fresh_regular s.path p 0 hd 1) (Bill.sup (Low.fresh_bill s.path p i.2 0 hd 1) (fun _ h=>h)); let g T n:= Low.mark ((T:ℕ→Cad G) n).path p i.2/ Low.mark s.path p i.2
    let F':=lowEntry (n:=c) G s.path B i; let J:= turnFee B*(|(1:ℝ)| *B.threshold^2*(|Low.mark s.path p i.2| * lowCost G B (Low.length s.path i.2))); have he : Glints atTop (g U) (g V):= (broil hv p _).bin (Q:=fun x=>x/(Low.mark s.path p i.2)) (fun _ _=> continuousAt_id.div_const _)
    have hm := (he.shrank.abs.mul_const J); simp only [abs_zero, zero_mul] at hm
    filter_upwards [hm.eventually (ge_mem_nhds hb)] with n hn; change B.supBounds F'.site F'.support (f U n i-f V n i) _; rw [hh U,hh V, ←sub_smul]; exact VerifiedReset.sup_le (CouplingShape.sup_scale _ hx) hn
omit hd in
private lemma sine {B:BudgetPoint}(s:Cad G)(p:Clip)(i:Faces c)(Y:Cad G)(hh:i.2.mark s.path p≠0) (a b:ℝ): let q:= i.2.mark Y.path p/i.2.mark s.path p
     i.2.loan Y.path p 0 B a b ∘ i.1.view=i.2.loan s.path p 0 B (q*a) (q*b) ∘ i.1.view:=by
   intro q; have hx: q*i.2.mark s.path p=i.2.mark Y.path p:= div_mul_cancel₀ _ hh
   have hz : i.2.live Y.path p B (0:Site c)= q • i.2.live s.path p B 0:=by
       unfold q
       obtain ⟨j,k,d|d⟩:= i
       · ext U
         change _=( (p.direct/p.direct) :ℝ) * Low.live s.path p (k,Sum.inl d) B 0 U
         rw [div_self p.quadratic_pos.ne',one_mul]; rfl
       funext V
       simp only [Low.live,Sum.elim,Pi.smul_apply]; -- implication split
       split
       next h =>
            change Low.mark _ _ (k,Sum.inr d) * Low.plain s.path (k,Sum.inr d) _ _= q*(_*_)
            dsimp only at hx; rw [← mul_assoc q,hx]
       rw [smul_zero]
   funext x; let u:= i.1.view x; let z:=i.2.home Y.path B (0:Site c); unfold Function.comp Low.loan
   change (if Healthy _ z _ then _ else _)=if Healthy _ z _ then _ else _; split; rfl
   rw [hz]; split
   · simp only [Pi.smul_apply, smul_eq_mul]; rw [← hx, show i.2.proxy s.path (0:Site c)=i.2.proxy Y.path (0:Site c) from rfl]; ring
   · simp only [sub_zero, Pi.smul_apply, smul_eq_mul]; ring
set_option maxHeartbeats 350000 in
omit hd in
lemma disused (h:∀ n,(U n).path.Bounds p ω' a e)(he:∀ n,(V n).path.Bounds p ω' a e)(hv:Soul atTop U V) (hw:Geo.Width B p ω') {f f' g g':ℕ→ℝ}(hf:Twin f f')(hg:Twin g g'): Angel (fun n (i:Faces c)=> i.2.loan (U n|>.path) p 0 B (f n) (g n) ∘ i.1.view) (fun n (i:Faces c)=> i.2.loan (V n|>.path) p 0 B (f' n) (g' n) ∘ i.1.view):=by
   obtain ⟨b,hb,hb'⟩:=hf.bound; obtain ⟨t,ht,ht'⟩:=hg.bound
   let F (U:ℕ→Cad G)(f g:ℕ→ℝ)(n:ℕ)(i: Faces c):= i.2.loan (U n|>.path) p 0 B (f n) (g n) ∘ i.1.view
   have ha {U:ℕ→ Cad G}{f g:ℕ→ℝ} (h:∀ n,(U n).path.Bounds p ω' a e)(hb:∀ i,|f i| ≤ b)(he:∀ i,|g i| ≤ t): Vented (F U f g):=by
        let v n (k:Low):= Real.exp ((k.length (U 0|>.path):ℝ)/p.relaxation)*|k.mark (U n|>.path) p|
        have hv:Sparse v:= neptune _ (meter (U 0)) (fun i k=>mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (show 0<3*ω'/4 from by have h:=hw.1; positivity) (fun i=> Geo.kept_debit G B (U i).path hw (h i))
        have h1:0≤t:=(abs_nonneg _).trans (he 0);have h2:0≤b:=(abs_nonneg _).trans (hb 0); let H:= (b+t)*(2*B.threshold)+t*2⁻¹*pairBill G B*B.threshold^2; have hp:= B.threshold_pos; have hi:=pair_nonneg G B
        have hc:0≤ H:=by unfold H; positivity
        refine ⟨_, (trep (ι:=Seat c) hv).climb hc,fun n x i=>?_⟩
        apply (Low.loan_bound (U n).path p i.2 (0:Site c) B (f n) (g n) _).trans; change _≤H*v n i.2; change _ ≤ H*(Real.exp ((i.2.length (U n|>.path):ℝ)/p.relaxation) * |i.2.mark (U n|>.path) p|); unfold shapeLoss; rw [← mul_assoc H]; unfold H; gcongr
        · exact (abs_add_le ..).trans (add_le_add (hb n) (he n))
        exact he n
   refine ⟨ha h hb ht,ha he hb' ht',fun i b hb=>recover (F:=fun n=> F U f g n i) (H:=fun n=> F V f' g' n i) (fun X=>?_ ) b hb⟩
   refine (tendsto_iff_ultrafilter ..).mpr fun J hj=>?_
   obtain ⟨s,hs⟩:=noble (G:=G) p i.2; let W:=s.path
   let q T n:= i.2.mark ((T:ℕ→Cad G) n).path p/i.2.mark s.path p
   have hX k k' (n) (T:ℕ→ Cad G):F T k k' n i= i.2.loan s.path p 0 B (q T n*k n) (q T n*k' n) ∘ i.1.view:= sine s p i _ hs ..
   have hF:Glints J (q U) (q V):=by
       obtain ⟨C,hC,h⟩:= (broil hv p i.2).bin (Q:=fun x=>x/(Low.mark s.path p i.2)) (fun _ _=> continuousAt_id.div_const _); exact ⟨C,hC.mono_left hj,h.mono_left hj⟩
   obtain ⟨A,hA,hP⟩:= hF.prods (Twin.ul f f' hf hj) (Q:=fun u v=>u*v) continuous_mul; obtain ⟨a,hn,hv'⟩:= hF.prods (Twin.ul g g' hg hj) (Q:=fun u v=>u*v) continuous_mul
   simp_rw [hX];
   let H(n):=q U n*f n - q V n*f' n; let G' n:= q U n*g n-q V n*g' n; let Y(n:ℕ):=shapeLoss B p G (H n) (G' n) (i.2.length W)*|i.2.mark W p|
   have hH : Tendsto Y J (𝓝 0):=by
        let P(x:ℝ×ℝ):=shapeLoss B p G x.1 x.2 (i.2.length W)*|i.2.mark W p|
        have hs : Continuous P:=by unfold P shapeLoss; fun_prop
        have hx:P (A-A,a-a)=0:=by simp [P,shapeLoss]
        have hM: Tendsto (fun n=> (H n,G' n)) (J:Filter ℕ) (𝓝 (A-A,a-a)):= (hA.sub hP).prodMk_nhds (hn.sub hv')
        have hO: Tendsto (P ∘ fun n:ℕ=> (H n,G' n)) (J:Filter ℕ) (𝓝 (P (A-A,a-a))) := hs.continuousAt.tendsto.comp hM
        rw [hx] at hO; exact hO
   apply Metric.tendsto_nhds.mpr; intro C hC
   filter_upwards [hH.eventually (gt_mem_nhds hC)] with n hn
   rw [dist_zero_right]; dsimp only [Function.comp_apply]; rw [Low.loan_sub]; exact lt_of_le_of_lt (Low.loan_bound ..) hn
end Ledgers
end YM.ConnectedActivityE6.Lim
