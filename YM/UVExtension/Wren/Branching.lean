import YM.UVExtension.Wren.Tower
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Comparison
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
open Song Strata Gala Concert Geo Chains
namespace Crumble
-- elementwise projection at fixed masks, no equality Faces assumptions. Delta read = t trend.
variable {A:Listing G c}{K:ι→ Collection.Source G c} (h:Notes v P A.reg (fun n=> (K n).logRead)) (hG:G.Simple)
include h hG
lemma caramel (x y:PlaqAxes)(o: Site c):Transit v (fun n i (_:Unit)=> Averaging.censusAt (A.read (K n)) o x y i) :=by
   obtain ⟨q,hq,hQ⟩:= h.invests.rain; obtain ⟨r,hc⟩:=hq.books; let B:= P.threshold; have hB:= P.threshold_pos; let t:=3/(P.threshold^2); have ht: 0< t:= div_pos (by norm_num) (sq_pos_of_pos hB)
   let F n i := (K n).logRead i; have hp(k:ℕ)(i:Config G c→ℝ)(a:ℝ)(hp:P.Regular (A.reg k).support i)(hv:P.supBounds (A.reg k).site (A.reg k).support i a): |projection (A.reg k) i x y| ≤ t*a:=by
      have hh:= projection_bound _ hG hp hv x y
      change _≤3/P.threshold^2*a; rw [div_mul_eq_mul_div]; exact (le_div_iff₀ (sq_pos_of_pos hB)).2 ((mul_comm ..).trans_le hh)
   let f n i (_:Unit): ℝ:= projection (A.reg i) (F n i) x y; have hh: ∀ᶠ n in v, ∀ i U, ‖f n i U‖≤ t*q n i:= ((hQ.and hc).mono fun n H i _=> hp _ _ _ (h.available _ _) (tap_bound.mpr ⟨H.2.1 _,H.1 i⟩))
   have hv: Transit v f:=by
       refine ⟨⟨_,hq.scales t ht.le,hh⟩,fun k=> ⟨⟨_,(hh.and hc).mono fun n hn i=> (hn.1 k i).trans (mul_le_mul_of_nonneg_left (budget_single hn.2 _) ht.le)⟩,fun ε hε=>?_⟩⟩
       filter_upwards [(Notes.rates.mp h).2.2 k (ε/t) (by positivity)] with n hn U; unfold f; rw [← projection_sub (A.reg k) (h.available n.1 k) (h.available n.2 k)]; exact (hp _ _ _ (CouplingShape.reg_sub (h.available _ _) (h.available _ _)) hn).trans_eq (by field_simp)
   refine (hv.masks (fun i _=> (A.reg i).site=o)).fade (Eventually.of_forall ?_); intro j i; funext x; unfold Averaging.censusAt; dsimp only [Listing.read]; split_ifs <;> rfl
omit h hG in
lemma succeeds {g:ι→ℝ}[NeBot v](p:Tune v (fun n (_:Unit)=>g n)): ∃ x,Tendsto g v (𝓝 x):=by
   apply cauchy_map_iff_exists_tendsto.mp; rw [cauchy_map_iff', tendsto_uniformity_iff_dist_tendsto_zero];
   exact (p.leaf (fun (x:ι×ι) b=> if b then x.1 else x.2) (fun b=> by cases b; exact tendsto_snd; exact tendsto_fst) (fun _=>())).2
variable [v.NeBot]
lemma pursuit :∃ t,Tendsto (fun n=> Averaging.delta (A.read (K n))) v (𝓝 t):= succeeds ((caramel h hG Averaging.axes01 Averaging.axes01 0).includes (fun x (_ : ℕ)=>x))
-- historical arrays adjustment
lemma bells: Notes v P (enlarges ∘ A.reg) (fun n i=> Residual.rebate (A.reg i) ((K n).logRead i)):=by
   obtain ⟨ht,⟨a,ha,hp⟩,he⟩:= Notes.rates.1 h; let t:=Residual.resetLoss G P; have hx:0<t:=Residual.loss_pos ..
   apply Notes.rates.mpr; refine ⟨fun i j=>Residual.rebate_regular _ (ht i j), ⟨_,ha.scales t hx.le,hp.mono (fun i hn j => Residual.rebate_sup _ hG (ht i j) (hn j))⟩,fun k ε hε=>?_⟩
   filter_upwards [he k (ε/t) (by positivity)] with n hn
   rw [← (Residual.label_sub _ _ P.threshold _ P (ht _ k) (ht _ k)).1]; exact (show Residual.resetLoss G P*(ε/t)=ε from (by change t*_=_; field_simp)) ▸ (show P.supBounds _ _ _ (Residual.resetLoss G P*(ε/t)) from Residual.rebate_sup _ hG (CouplingShape.reg_sub (ht n.1 k) (ht n.2 k)) hn)
lemma faults: Transit v (fun n i x=> Residual.fault (A.reg i) ((K n).logRead i) P.threshold x):=by
   obtain ⟨ht,⟨a,ha,hp⟩,he⟩:= Notes.rates.1 h; let t:=Residual.resetLoss G P; have hx:0<t:=Residual.loss_pos ..
   have hf : ∀ᶠ n in v,∀ k U, ‖Residual.fault (A.reg k) ((K n).logRead k) P.threshold U‖≤ t*a n k:= hp.mono fun n hn k=> Residual.fault_sup _ hG (ht n k) (hn k)
   obtain ⟨r,hr⟩:=ha.books; refine ⟨⟨_,ha.scales t hx.le, hf⟩,fun k=> ⟨⟨_,(hf.and hr).mono fun n hn i=> (hn.1 k i).trans (mul_le_mul_of_nonneg_left (budget_single hn.2 _) hx.le)⟩,fun ε hε=>?_⟩⟩
   filter_upwards [he k (ε/t) (by positivity)] with n hn i
   rw [← show Residual.fault _ (((K n.1).logRead k)-((K n.2).logRead k)) P.threshold i= Residual.fault (A.reg k) ((K n.1).logRead k) P.threshold i - Residual.fault (A.reg k) ((K n.2).logRead k) P.threshold i from congr_fun (Residual.label_sub (A.reg k) _ P.threshold _ P (ht _ k) (ht _ k)|>.2) i] -- motive
   exact (Residual.fault_sup _ hG (CouplingShape.reg_sub (ht _ k) (ht _ k)) hn i).trans_eq (show Residual.resetLoss G P*(ε/t)=ε from (by change t*_=_; field_simp))
end Crumble
end YM.UVExtension.Wren
