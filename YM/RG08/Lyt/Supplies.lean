import YM.RG08.Lyt.Spindle
/-! # Exp shoulders in arbitrary Mink-gauge jets, no retaining collapsed costs through moves. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Lyt
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Taste
open scoped BigOperators Topology Real ContDiff Classical
open Wings Summit
variable {X:Chain}{G:Gauge}{D d k t n τ s E e i j r:ℕ}{w':ℝ}{T:Labels.Frame G d}{H:SectionData T}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{hp:1/2≤w'}{hD:d+1 ≤ D}{h:Hol G}{M:Signals P Q E τ h H hp hD}{ν:G.ColorIndex}{D':ChartRatio G}{S:Prism G X.kernel g Q E}
variable {I J:Type}{u:I→Windows}{b:J→ShoreP u}{v:Wall b 1→ Wings u 1}
local notation "Ⓨ"=> wallY X
variable (K:Tights M S ν D' u)
variable {U:J→ BoardU D w' G}{p:J→ℝ}
structure Starts (M:Signals P Q E τ h H hp hD)(b:J→ ShoreP u)(U:J→ BoardU D w' G)(p:J→ℝ): Prop where
   pos (i:J):0 < p i
   yes (i:J):Marvel τ (U i)
   ripe i:Lank (U i)
   budget :∀ i≤E,∀ r,Tin (topY X b) p (fun j=> U j i r) (fun i=> ώ M (Wall.tip b i).i)
variable (H':Starts M b U p)
local notation "Θ"=>Starts
local notation "[↓]"=> offerD b
local notation "◈"=>strideP X b p
include K H'
private lemma walls_w (i:ℕ): ώ M i≤1:= ((tick_t M _|>.1).trans (tick_t M _|>.2)).trans (min_le_right ..)
lemma wind_feed (hp:e≤E)(v:Letter T) : Dig (topY X b) p (fun i=> coeff e (call h T (U i) v)):=by
   have hz: Weighed (topY X b) (fun i:J=>(ώ M (Wall.tip b i).i)⁻¹):= ((Wall.invested X (b:=b)|>.sway (Wall.plusOne X) (K.he.costs.transfer (fun i:Wall b 0=> i.world.toLaunch))).transfer (Wall.tip b))
   simp_rw [call,coeff_mk,auditT]; refine Dig.sums _ (fun i=>Wall.plusOne X _) (fun i hi=>?_) -- parameter names
   split_ifs with h; swap; exact Dig.zero
   exact digs _ (H'.budget _ (by have he:=mem_range_succ_iff.mp hi; omega) _) (fun _=>M.pos _) (fun i=>walls_w K H' _) hz _
lemma aureole (hp:e≤E)(r:ℕ): Stems M p (riseV ν D' M [↓] U) (arcV ν D' M [↓] U) e r:=by
    let y:= wallY X (b:=b) (n:=0); have hx:Audience y:= Wall.plusOne X
    refine tribal_pay K (barriers ν D' M [↓] U K H'.yes H'.ripe) H'.pos hp ?_
    intro i hi j
    simp only [riseV,openingP, Taste.curtain, eject,Pi.sub_apply]
    apply Tin.less (H'.budget i hi j) ?_ (fun _=>hx _)
    refine over_s (fun i=>hx (Wall.tip b i)) (fun i hi' z j=>?_) (fun i=> (K.firs _).toBoards) (fun i hi' p=> wind_feed K H' (by omega) _)
    have hv:= (cashIn K (le_trans hi' hi) z j).move (fun i=> (Wall.tip b i).world); exact ⟨_, ((Wall.invested X|>.transfer (Wall.tip b)).sway (fun i=> hx (Wall.tip b i)) hv.serves.choose_spec.1),hv.serves.choose_spec.2⟩
-- heap ages (without tighter exp norm transfer downhill polynomial bases). optional canon representation same width.
lemma offs (hp:e≤E)(v:Letter T) : Dig Ⓨ (strideP X b p) (fun i:Wall b 0=> coeff e (offerUp ν D' M [↓] U i v)):=by
   let z:= shiftV ν D' M [↓] U
   have hDig(j)(hk:j≤E)(v:Letter T): Tonic Ⓨ ◈ (tiltP X) (fun i=>coeff j (z i v)) (fun i=> coeff j (z i v)):= by
      have hv:=(aureole K H' hk (slot v)).paid v rfl; exact ⟨hv,hv,by rw [sub_self]; exact Dig.zero⟩
   let f(i:Stem b):= fragment i; let L i:=(f i).fromR; let Y(i:Stem b):=Ⓨ i.i
   have hz:Audience Y:= fun i=>Wall.plusOne X _
   have hw:Weighed Y Y:= by simpa only [pow_one] using Weighed.power Y hz 1
   let V i:= freightP ν D' M [↓] i (z (inside i)); have hC (n)(hn:n≤E) (v:Letter T): Dig Y (fun i=> ◈ i.i) (fun i:Stem b=>coeff n (V i v)) := by
      have hv t: ◈ (inside t) ≤ ◈ t.i:= by apply mul_le_mul_of_nonneg_left _ (H'.pos _|>.le); apply Real.exp_monotone; change -(1/4:ℝ)*(X.S.scale (b t.i.a).next.i-X.S.scale (inside t).i) ≤ -(1/4:ℝ)*(X.S.scale (b t.i.a).next.i-X.S.scale t.i.i); have hl : (Taste.inside t).i ≤ t.i.i:=along_roof _; linarith [age_scale_mono X.S hl]
      have h1(i:Stem b):0 ≤ ◈ i.i:= mul_nonneg (H'.pos ..|>.le) (gain_pos ..).le
      have hP (i:Stem b): (f i).rate X ≤ tiltP X i.i := race_b X i
      have hV(i): (L i).cost X ≤ (f i).rate X := by
        apply Real.exp_monotone; have ht:= age_scale_mono X.S (max_le_max (f i).init (le_refl (f i).next.main)); change -(1/4:ℝ)*(X.S.scale (f i).next.N-X.S.scale (max (f i).low (f i).next.main))≤ -(1/4:ℝ)*(X.S.scale (f i).next.N- X.S.scale (max (f i).next.i (f i).next.main)); linarith
      have hh: Weighed Y (fun i=> (f i).y X):= hw.mono (fun i=>zero_le_one.trans (city_one ..)) (fun _=>race_a X _)
      have hL : Weighed Y (fun i=> (L i).measure X):= hw.mono (fun i=> zero_le_one.trans (sh X _)) (fun i=> (le_max_left (L i|>.measure X) ((f i).next.measure X)).trans (race_a X i))
      have hR j (hj:j≤E) a:= forward_p (A:=fun i:Stem b=> z (Taste.inside i)) (B:=fun i=>z (Taste.inside i)) K hL (fun i=> (hV i).trans (hP _)) h1 hz (fun n hn a=> ?_) hj a
      · exact (trump_d K f hh hP h1 hz (fun i hi a=> hR i (hi.trans hn) a) hn v).one
      have ht:= Tonic.rises (Tonic.viaD (hDig n (hn.trans hj) a) inside) hv (fun i:Stem b=> (gain_pos ..).le)
      exact ht
   let B:=heap ν D' M [↓] U
   have hV i (hi:i≤E)(a:Letter T) : Dig Ⓨ ◈ (fun j:Wall b 0=> coeff i (B j a)):= by
      unfold B Taste.heap spreads; simp_rw [Finset.sum_apply, _root_.map_sum]; apply Taste.Dig.swing (raceL (w:=b)) _ (race_c X) (fun i=>mul_nonneg (H'.pos _|>.le) (gain_pos ..).le) (Wall.plusOne X); convert hC i hi a using 1 <;> first| rfl| (ext1 j; rw [dif_pos (show j.k < raceL j.i from j.hw)])
   let A (i:Wall b 0): Roam u:= ⟨i.world,(b i.a).next.fromK,(b i.a).next.ends⟩
   refine (forward_d (b:=A) K (Wall.invested X) (fun i=>le_refl _) (ρ:=◈) (fun i=>mul_nonneg (H'.pos _|>.le) (gain_pos ..).le) (Wall.plusOne X) (A:=B) (B:=B) (fun j hj a=>?_ ) hp v).one
   exact ⟨hV j (hj.trans hp) a,hV j (hj.trans hp) a,by rw [sub_self]; exact Dig.zero⟩
lemma remnant_p (hp:e≤E)(r:ℕ): Tin Ⓨ ◈ (fun i:Wall b 0=> remnant ν D' M [↓] U i e r) (fun i=> ώ M i.i):=by
    let y:= wallY X (b:=b) (n:=0); unfold remnant
    apply Tin.less (aureole K H' hp r|>.here) (over_s (Wall.plusOne X) (fun i hi u r=>?_) (fun i=>K.firs _|>.toBoards) (fun i b he=>offs K H' (by omega) _)) (Wall.plusOne X)
 
    have hv:= (cashIn K (le_trans hi hp) u r).move (Wall.world (b:=b) (n:=0)); exact ⟨_,(Wall.invested X).sway (Wall.plusOne X) hv.serves.choose_spec.1,hv.serves.choose_spec.2⟩
end YM.RG08.Lyt
