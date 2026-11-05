import YM.TraceExtension.Prom.Order.State
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n k N p l:ℕ} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S'"=> Cells.standard C
variable (F : Extraction.Order)(a : (Cells.standard C).Hierarchy)
variable {S: Table C.book} (P:F.Ordered C S) (hc:S.Smooth)(he:F.PointLimits C S)
abbrev PoleC (C:Family G) (d:ℕ):= Module.finBasis ℂ ((Cells.standard C).Field d)
abbrev PegC (C:Family G) (d:ℕ): Type:= Fin (Module.finrank ℂ ((Cells.standard C).Field d))
-- comparison END over d-probes; its own L film; use even at every period, before choosing phase
structure SeqPair (i:ℕ)(b:ℝ)(d:ℕ)(R:ℕ→ℕ→ TableL C d)(ε:ℝ):Prop where
   width (x:Fin 2→ Cover):
     let y:= Extraction.tag ((mag A b i)⁻¹) x
     y∈generic 2 → ‖y‖ ≤ 100 → FitSky A b i y
   boot (w : Fin (d+1))(p:Fin 2 → PegC C w)(N l:ℕ)(h:i<N) :
     let y:Fin 2→ C.label w:= fun j=> ladder C w (PoleC C w (p j))
     let v(j):= ladd C (mag A b i) i N l _ (R N l w) (y j)
     ∀ (x : Points 2), (Next.Rank.Station.tested A b i x)∈Scaling.window 100 2 →∀ ht:FitSky A b i x,∀ s : modes (Fin 2),s.val.Nonempty →
       (Ship.yardSky C b h.le l).rootTest (C.beta N l) (fun U=> (Ship.invoiceSky (jointX (d0:=fun _=>w.val) y) (q_asked (C:=C) (d:=fun _=> w.val) v) ht N l U).part s) ≤ ε
include H
private lemma await (hG:G.Simple)(hX: Scrim C W u ψ φ δ (fly C.path.levels) r L) {z:ℝ}(hZ:∀ i≤d,generator G i≤z) (x:ℕ→ Fin 3→ Tapes.Panel d)(K:ArcSky x)(i:ℕ→ℕ)(he:Tendsto i atTop atTop)(R : ℕ→ℕ→ℕ→TableL C d) (hv:∀ j,PoisedSky (x (i j)) B H O J (trays d) z (i j) (R j))(ε:ℝ)(hp:0<ε):∀ᶠ j in atTop, SeqPair (i j) (x (i j) 0).arc d (R j) ε:=by
    let D:= Scaling.window 100 2; let t(w:Fin (d+1)):=fun _ : Fin 2=>w
    have hz(w:Fin (d+1)) (p:Fin 2→ PegC C w):= he.eventually (lava_vSky x K B H hG hX O J z hZ (t:=t w) (fun i=> ladder C w (PoleC C w (p i))) 0 (window_closed (100:ℝ) 2) (fun x hx=> spaced_conf (by norm_num) hx.1) (n:=trays d) (Nat.le_add_left ..) (Nat.le_add_left ..))
    filter_upwards [eventually_all.mpr (fun w=>eventually_all.mpr (hz w)),he.eventually (open_readSky hG 100 A 2),((Ship.diminishes A (trays d) hG (by unfold trays;omega)).comp he).eventually (ge_mem_nhds hp)] with j hh hA hB
    constructor
    · have he:= (hv j).supply 0; obtain ⟨q,r,Q,H⟩:= he
      exact hA _ (by rw [← (x (i j) 0).factor ((A).clock.J (i j))]; exact Q.age.allot.permitted)
    intro w p N l hn y v z h ht s hs
    exact (hh w p (R j) (hv j) N l hn z h ht s hs).trans hB
omit H
-- Keep crisp price after extracting.Leading rank panels.
structure TimberSky (F:Extraction.Order)(a:(Cells.standard C).Hierarchy) (d i j:ℕ)(b c:ℝ)(R: ℕ→ℕ→TableL C d) : Prop where
   high : 5 < b ∧ b ≤ Perch.y (clim A i)
   early : ∀ u: Fin (d+1), C.ref u ≤ i
   rate : ∀ N p,i<N→ Charting d i (R N p) N p ∧ ∀ u : Fin (d+1), Next.Rank.East.InvoiceSky C i N p u (R N p u)
   plate : SeqPair i b d R (costHint j)
   fares : (wok C d i b c R).toStation.Admissible F a.spin j (sizeHint j) (costHint j)
include H P hc he
lemma boatsSky (hG:G.Simple)(hX: Scrim C W u ψ φ δ (fly C.path.levels) r L) {z:ℝ}
   (hZ:∀ i≤d, generator G i≤z) (h : FiresSky B H O J d z) (hj:l ≤ trays d) (s:ℕ→ℝ)(hS:Tendsto s atTop (𝓝 0))(hp:∀ i,0<s i) (Y:ℕ)(θ:ℝ)(hθ:0<θ):∃ k≥Y, s k<θ ∧ ∃ i≥Y,∃ b c R, s k=Station.gap A b i ∧ TimberSky F a d i l b c R:=by
    obtain ⟨b,hb,T⟩:= fliesSky B H O J hG h; obtain ⟨f,i,hF,K⟩:= T s hS hp; have hk:= K.rates.tendsto_atTop
    obtain ⟨hi,P',R,c,q,e,hζ,hD,hd,Ht,hQ,hV,hσ⟩:= K
    let x:=fun k=> (P' (i k) 0).arc
    have hh k:x k ≤ b+1:=by unfold x; rw [hD,hζ]; exact add_le_add_right (hd _).2 _
    have hχ:= await B H O J hG hX hZ P' hQ i hk R hV (costHint l) (cost_pos _)
    have hz:= podiumSky P' hQ B H hG hX O J z hZ F (Nat.le_add_left ..) (sizeHint l) (by unfold sizeHint;positivity) a.smooth a.spin q e (fun i=>(hd i).1) hD Ht i hk R hV
    have hq:0<sizeHint l:=by unfold sizeHint; positivity
    have he':=supply_wheel _ hz P hc H he a.smooth hq (costHint l) (cost_pos _)
    obtain ⟨k,⟨hE,hhp⟩,hΩ,hr,hu,hχ,hM⟩:= ((he'.and hχ).and ((hF.tendsto_atTop.eventually_ge_atTop Y).and ((hk.eventually_ge_atTop Y).and (((Perch.y_rate.comp ((hat_rate A hG).comp hk)).eventually_ge_atTop (b+1)).and ((hk.eventually (eventually_all.mpr (fun k : Fin (d+1)=> eventually_ge_atTop (C.ref k)))).and ((hS.comp hF.tendsto_atTop).eventually (gt_mem_nhds hθ))))))).exists
    refine ⟨f k,hΩ,hM,i k,hr,x k,c,R k, hσ k, ⟨lt_of_lt_of_le hb (show b ≤ (P' (i k) 0).arc by rw[hD,hζ]; exact le_add_of_nonneg_right (hd _).1), (hh k).trans hu⟩,hχ, (fun N p hi=> ⟨(hV k).charts _ _ hi,(hV k).bank _ _ hi⟩),hhp,?_⟩
    refine { lift_bound:=hE.lift_bound, lift_unit:=hE.lift_unit, lift_signed:=hE.lift_signed, lift_real:=hE.lift_real, short:=fun {n} hn=> hE.short (le_trans ?_ hj) }
    assumption

omit H P hc he
structure Vane (C:Family G) (d : ℕ) where
   k : ℕ
   b : ℝ
   c : ℝ
   R : ℕ→ℕ→TableL C d

def Vane.wheel (K : Vane C d):= wok C d K.k K.b K.c K.R
def Vane.checked (V : Vane C d)(i:ℕ):= TimberSky F a d V.k i V.b V.c V.R

include H P hc he
lemma wakesSky (hG:G.Simple)(hX: Scrim C W u ψ φ δ (fly C.path.levels) r L) {z:ℕ →ℝ}
   (hZ:∀ i j, i≤j→ generator G i≤z j) (h : ∀ d,FiresSky B H O J d (z d)) (s:ℕ→ℝ)(hS:Tendsto s atTop (𝓝 0))(hp:∀ i,0<s i): ∃ (p:ℕ→ℕ) (V: ∀ d,Vane C d), StrictMono p ∧ StrictAnti (s∘p) ∧ Tendsto (fun d=>(V d).k) atTop atTop ∧ ∀ d,(V d).checked F a d ∧ (V d).wheel.r=s (p d):= by
    have hy (d N:ℕ) (y:ℝ) (hv:0<y): ∃ k:ℕ,N<k ∧ s k < y ∧ ∃ v:Vane C d,d ≤ v.k ∧ v.checked F a d ∧ v.wheel.r=s k:=by
       obtain ⟨k,hk,ht,i,hi,b,c,t,hE,hP⟩:= boatsSky B H O J F a P hc he hG hX (fun i=> hZ i d) (h d) (l:=d) (Nat.le_add_right ..) s hS hp (max d (N+1)) y hv
       exact ⟨k,by omega,ht, ⟨i,b,c,t⟩,by change d ≤ i;omega,hP,hE.symm⟩
    let W d:= {v:ℕ × Vane C d // d ≤ v.2.k ∧ v.2.checked F a d ∧ v.2.wheel.r=s v.1}
    have hn(d):Nonempty (W d):= by obtain ⟨k,-,-,v,h⟩:=hy d 0 1 zero_lt_one;exact ⟨⟨(k,v),h⟩⟩
    have hx (d) (w: W d):∃ v: W (d+1), w.val.1<v.val.1∧s v.val.1 < s w.val.1:=by
       obtain ⟨k,hk,hS,v,H⟩:=hy (d+1) w.val.1 (s w.val.1) (hp _); exact ⟨⟨(k,v),H⟩,hk,hS⟩
    let f(d): W d:= Nat.rec (motive:=W) (Classical.choice (hn 0)) (fun n i=> (hx n i).choose) d; let p(d):=(f d).val.1; let V(d):=(f d).val.2
    have hD(d): p d < p (d+1) ∧ (s∘p) (d+1)< (s∘p) d:= (hx d (f d)).choose_spec
    refine ⟨p,V,strictMono_nat_of_lt_succ (fun i=>(hD i).1),strictAnti_nat_of_succ_lt (fun i=>(hD i).2),?_,fun i=>(f i).property.2⟩
    apply tendsto_atTop.2; intro n; filter_upwards [eventually_ge_atTop n] with k hk; exact hk.trans (f k).property.1
end YM.MergeProof.East
