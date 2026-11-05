import YM.TraceExtension.Prom.Order.Road
import YM.TraceExtension.Prom.Orion.Ramp
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Supply Accent
variable {G : Gauge}{X:Sheet G}{D: Rolls X}{T: Protection D}{E: Delays T}{Z: Bar E}
variable (B:MapPrices)
structure RelaySky (m:ℕ → ℕ): Prop where
   asks : ∃ a:ℕ → Fin 3→ℝ, (∀ d i, d+6 ≤ a d i) ∧ (∀ d,∃ c,Checks (a d 0) (a d 1) (a d 2) c (trays d) d) ∧
       ∃ P:∀ d, Fin 3→Tapes.Panel d,∃ K,AskSky X B trays m P K ∧ ∀ i d,(P d i).arc=a d i+1
lemma submits (X:Sheet G) (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop): ∃ m,RelaySky B m (X:=X):=by
   choose a ha c hf using fun d => raises d (trays d)
   obtain ⟨m,K,V,hP,H⟩:= asks_sky X B trays (fun d i=> a d i+1) (fun d i=> by linarith only [ha d i]) (fun _=>Nat.le_add_left ..) ht
   exact ⟨m,⟨a,ha,fun i=> ⟨c i,hf i⟩,K,V,H,fun i d=> hP d i⟩⟩

private def curb (d:ℕ)(P:Tapes.Panel d)(b:ℝ) (h:d+6 ≤ b)(hp:b ≤ P.arc): Tapes.Panel d:={P with
     arc:=b,huge:=h,bag:= fun i=> vent (P.bag i) b,factor:=fun _=>rfl, stable:=P.stable, vital:=P.vital,
     loose:=fun i=> (le_trans (add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)) _) _) (P.loose i)) }

/-- Stretched appointments: preserves All ancestors and pin innovations, for arbitrary queried common curve. -/
structure FiresSky {C:Family G}(B:Binding C) (H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)(d:ℕ) (z:ℝ):Prop where
    earns : ∃ (P:ℝ → Fin 3→Tapes.Panel d)(b : Fin 3→ℝ)(κ:ℝ), Checks (b 0) (b 1) (b 2) κ (trays d) d ∧
       (∀ s∈Icc (0:ℝ) 1, ∀ i,(P s i).arc=b i+s ∧ (P s i).currency=(P 0 i).currency ∧ (P s i).θ=(P 0 i).θ) ∧
       ∀ᶠ k in atTop,∀ s ∈ Icc (0:ℝ) 1, ∃ Y, PoisedSky (P s) B H O J (trays d) z k Y
lemma embalms (m:ℕ→ℕ)(h: RelaySky (X:=X) B m) (O:HaarBudget G)(J:ChartRatio G)(hp:LocalRatio J)(hm:∀ i,m i ≤ (D.L i).val)(hG:G.Simple) (z:ℕ→ℝ)(hZ:∀ i,0≤ z i)(U:Wait Z): ∃ W: Wait Z,U.minLength ≤ W.minLength∧ U.readyHere ≤ W.readyHere ∧ U.window ≤ W.window ∧
      ∀ C:Family G, Paid W C.path.levels → ∀ B': Binding C, B'.prices=B → ∀ H:C.Makes,ParadeX C→ ∀ d, FiresSky B' H O J d (z d):=by
    obtain ⟨a,ha,hb,P,K,hT,hK⟩:=h.asks
    obtain ⟨V,Q,hM,hV,h1,ht,hq,hX⟩:= forwardSky B U hT O J hp hm (fun _=> Nat.le_add_left ..) hZ hG
    refine ⟨V,hM,hV,h1,fun C H B' he H' S d=> ?_⟩
    let A:= C.path.levels
    have hp(i): (Q d i).arc= a d i+1:= (ht d i).1.symm.trans (hK i d)
    let f(s:ℝ):= max 0 (min 1 s)
    have hv(s): f s∈Icc (0:ℝ) 1:= ⟨le_max_left ..,max_le zero_le_one (min_le_left ..)⟩
    let D' s i:= curb d (Q d i) (a d i+f s) ((ha _ _).trans (le_add_of_nonneg_right (hv s).1)) ((hp i).symm ▸ add_le_add_right (hv s).2 _)
    obtain ⟨c,hc⟩:= hb d
    refine ⟨D',a d,c,hc,fun s hs i=>⟨?_,rfl,rfl⟩,?_⟩
    · refine congr_arg (a d i+·) (show f s=s from ?_); unfold f; rw [min_eq_right hs.2,max_eq_right hs.1]
    filter_upwards [eventually_all.mpr (fun i=> hX C H B' he d i),stagingSky (ι:=Fin 3) (n:=trays d) (z:=z d) B' H' O J hG 0 S (Q d 0).θ (Q d 0).enough] with k hD hH s hs
    have hx i : topL C.path.levels k ≤ (A).clock.monitor k ∧ ∃ l r, LegacyCostSky B' J (-3) (z d) ((D' s i).bag (A.clock.J k)) k (trays d) d O l r:= by
      let b:= a d i+f s; have hP':0 ≤ b:= by unfold b; linarith only [ha d i,Nat.cast_nonneg (α:=ℝ) d,(hv s).1]
      refine hD i b hP' ?_; rw [(Q d i).factor, hp]; exact add_le_add_right (hv s).2 _
    apply hH (D' s) rfl (fun i=> hq d 0 i) (hx 0).1 (fun i=> (hx i).2)

variable {C:Family G}{d n k N p l:ℕ} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> Cells.standard C
structure LeapSky (d:ℕ)(z:ℝ)(b:ℝ)(s:ℕ→ℝ)(k:ℕ→ℕ) : Prop where
    -- for any actual resolution along sequence. granular at this Plate chart.
    rates : StrictMono k
    supply : ∃ (P:ℕ → Fin 3 → Tapes.Panel d)(Y:ℕ→ℕ→ℕ→TableL C d)(κ:ℝ)(a:Fin 3→ℝ)(Lz:ℕ→ℝ), (a 0=b) ∧ (∀ i t,(P i t).arc=a t+Lz i)∧(∀ i,Lz i∈Icc 0 1) ∧ Checks (a 0) (a 1) (a 2) κ (trays d) d∧
       ArcSky P ∧ (∀ i,PoisedSky (P (k i)) B H O J (trays d) z (k i) (Y i)) ∧ ∀ i,s i=Station.gap A (P (k i) 0).arc (k i)
lemma agendasSky {b:ℝ}{k:ℕ→ℕ}{s:ℕ→ℝ}{z:ℝ}(U:LeapSky B H O J d z b s k)(h: G.Simple)(hp: Scrim C W u ψ φ δ (fly C.path.levels) r L)(hZ:∀ i≤d,generator G i≤ z) (F:Extraction.Order)(hx:(S).Smooth)(Hs:(S).RealSpin) : ∃ (Y:ℕ→ℕ→ℕ→TableL C d)(φ:ℕ→ℝ)(c:ℝ),
       (∀ i, s i=Station.gap A (φ i) (k i)) ∧ (∀ i,b ≤ φ i ∧ φ i≤ b+1)∧
       (∀ i N p,k i < N → Charting d (k i) (Y i N p) N p ∧ ∀ j:Fin (d+1), Next.Rank.East.InvoiceSky C (k i) N p j (Y i N p j)) ∧
       ∀ R:ℝ,0<R → Granular (fun i=> wok C d (k i) (φ i) c (Y i)) F Hs (trays d) R:=by
    obtain ⟨Hk,P,Y,c,a,X,rfl,ht,hL,Ht,hU,hV,hE⟩:= U
    refine ⟨Y,(fun i=> (P (k i) 0).arc),c,hE,fun i=> ?_,fun i N p hi=>⟨(hV i).charts _ _ hi,(hV i).bank _ _ hi⟩, fun R hR=>podiumSky P hU B H h hp O J _ hZ F (Nat.le_add_left ..) R hR hx Hs a X (fun i=>(hL i).1) ht Ht k Hk.tendsto_atTop Y hV⟩
    dsimp only; rw[ht]; exact ⟨le_add_of_nonneg_right (hL _).1,add_le_add_right (hL _).2 _⟩
lemma fliesSky (hG:G.Simple){z:ℝ}(F:FiresSky B H O J d z) : ∃ b:ℝ,5 < b ∧ ∀ s:ℕ→ℝ, Tendsto s atTop (𝓝 0)→(∀ k,0<s k) → ∃ f:ℕ→ℕ,∃ k:ℕ→ℕ, StrictMono f ∧ LeapSky B H O J d z b (s∘f) k:=by
    obtain ⟨P,a,c,hK,hX,hZ⟩:= F.earns; have hx : (0:ℝ)∈ Icc 0 1:=⟨le_rfl,zero_le_one⟩
    have hβ := (P 0 0).huge;rw [(hX 0 hx 0).1] at hβ; have he : 5 < a 0:=by linarith only [hβ,Nat.cast_nonneg (α:=ℝ) d]
    obtain ⟨k,hk⟩:= eventually_atTop.mp hZ
    refine ⟨a 0,he,fun s hS hz=>?_⟩
    have h : ∀ᶠ k in atTop,topL A k ≤ (A).clock.monitor k:= hZ.mono (fun k h=> (h _ hx).choose_spec.limit)
    obtain ⟨f,w,hF,hW,H⟩:= gap_orders A hG (a 0) (le_trans (by norm_num) he.le) h s hS hz k
    choose t ht hs using fun i=> (H i).2
    let e(k):= if h:∃ j, w j=k then t (Classical.choose h) else 0
    have he(k):e k∈ Icc (0:ℝ) 1:= by unfold e; split; exact ht _; exact hx
    have hφ(i): e (w i)=t i:=by
       unfold e; split
       · rename_i hp; exact congr_arg t (hW.injective (Classical.choose_spec hp))
       rename_i hp; exact (hp ⟨i,rfl⟩).elim
    let U(k):= P (e k); choose Y hY using fun i=> hk _ (H i).1 _ (he (w i))
    refine ⟨f,w,hF,hW,U,Y,c,a,e,rfl,fun i j=>(hX _ (he i) _).1,he,hK,⟨⟨a,e,he,fun i j=>(hX _ (he _) _).1⟩,fun i=> ⟨_, fun k=>(hX _ (he k) _).2.1⟩,fun i=>⟨_,fun k=>(hX _ (he k) _).2.2⟩⟩, hY,fun i=>?_⟩
    unfold U; rw [(hX _ (he _) _).1,hφ]; exact hs i
end YM.MergeProof.East
