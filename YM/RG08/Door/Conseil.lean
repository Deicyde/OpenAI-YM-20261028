import YM.RG08.Door.Wane
/-!
# Canonical summit mark Y obeys neighbor equation, every announced grade.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit
open PertExtension.Series.Tested PertExtension.Series.Radial Scores
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
variable {I:Type}{u:I→Windows}
variable (he:Tights T S ν D' u)
include he
local notation "Ⓨ" => menu X
local notation "Δ" => chop X (1/4)
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Γ" => heights (u:=u) X ν D'
local notation "◆" => (zPlay X Ω ν D' H h hD)
local notation "◇" => (wPlay X Ω ν D' H h hD)
local notation "♣" => didn ν D' X
lemma twinUp (hk:e≤E)(b:Letter F) r: Twill Ⓨ Δ (fun i:Wings u 1=> Υ i.up b e r) (fun i=> dryE (◆ (i.i+1) b) E e r) (fun i=>ώ T (i.i+1)) := by
    have hp:= frozenY he hk b r; have hx:=hp.two.move Wings.up; have hv:= (Tights.hc he).M.crop
    simp only [dryE,if_pos hk]; refine ⟨cashUp he b hk r,?_,hp.goes.lapP hv (by norm_num)⟩
    obtain ⟨B,hB,hV⟩:= hx.serves; exact ⟨_, (aged_up X hv).sway (sh X) hB,hV⟩
lemma outlay (hk:e≤E)(b:Letter F)(r) :
    Twill Ⓨ Δ (fun i:Wings u 1=> juice (Γ i) (slot b) d (Υ i.up b) e r) (fun i=> juice (♣ i.i E) (slot b) d (dryE (◆ (i.i+1) b) E) e r) (fun i=>ώ T i.i) := by
   let MU i:= Γ i; let V (i:Wings u 1):= ♣ i.i E
   let G' j k i:= Refrain (veiled (V i).cv) (V i).song none j k
   let a(i:Wings u 1):= dryE (◆ (i.i+1) b) E; let g i:= Υ (Wings.up i) b
   let v(i:Wings u 1):= ticketW Q (X.J i.i); let σ(i:Wings u 1):= T.vi (X.J i.i)
   let B:= he.operator
   have hT i : T.vi (X.J (i:Wings u 1).i) ≤ v i:=(tick_t T _).2
   have hh := (Summit.polishes he.hc he.hv); have he' := Summit.smooth he.hc he.hv; let A i:= veiled (MU i).cv; let Q i:= veiled (V i).cv
   have hz:=scanned_contract (η:=fun i=>ώ T i.i) hh (le_trans (bucks_v B) (show σ ≤ v from hT)) (sh X) B.hs
   have hJ i: Fits (slot b) (a i) ∧ ∀ j k,Tidy (a i j k):= dayCap (peakY he (i.up.toLaunch) b)
   have hA i:= creamy d _ ((he.firs (i:Wings u 1).up).rank b).cap (fun j k=> (he.firs i.up|>.rank b|>.hem j k).pens) h (X.S.block_odd i.i)
   have hB i:= creamy d _ (hJ (i:Wings u 1)).1 (fun j k=>(hJ i|>.2 j k).pens) h (X.S.block_odd i.i)
   have hP:= veil_contract he' B.hs
   have hv:RowBoth (menu X) Δ A Q σ:= ⟨hP.fresh.soften hT,hP.again.soften hT,hP.moves.soften hT⟩
   have hE(i:Wings u 1): Gets (V i).song:= Gets_awake (X.patch _) D' X.kernel ν (successor (i.toLaunch) he.hc he.hv he.hz he.hs)
   unfold juice filop; apply tw_both B.env hz B.ht _ B.hs (Weighed.constant (menu X) (Nat.cast_nonneg (Fintype.card (Loc G 1))))
   unfold washed; apply Twill.sums _ B.env; intro j hj
   have hu : slot b≤τ:= (slot_le _).trans he.hh; have hf : j≤ windows τ E:= by have hh:= mem_range_succ_iff.mp hj; unfold windows at *; omega
   have hx i := B.ht i|>.trans_le (bucks_v B i)
   refine murmur_f B.env hx B.hs hv (fun i=>(he.fair i).lived) (fun i=>(hE i).1) (fun i=>(hA i).2) (fun i=>(hB i).2) (fun i=>(he.fair i).tune) (fun i j k=> (hE i).2 j k|>.1) (fun i=>(hA i).1) (fun i=>(hB i).1) (fun j hj k hl p=>stampE he (hl.trans hk) j (hj.trans hf) p) (fun i=>(B.ht i).le) ((smul_le_smul_of_nonneg_right (snug_every hu hk hf) (show 0≤_ from (fun i=>(B.ht i).le) : (0:Wings u 1→ℝ) ≤ _)).trans B.money) fun i k hb=>cake_pair (F:=g) (twinUp he (by unfold awaits at hb; omega) b k) h (fun i=> (he.fair _).odds) (fun i=> (hx i).le) B.hv B.hh B.hn B.crop B.env -- F issue
lemma snowfall (hk:e≤E)(b:Letter F)(r) : Twill Ⓨ Δ (fun i:Wings u 1=> Ξ i b e r) (fun i=> Needle.push (♣ i.i E) (slot b) d (dryE (◆ (i.i+1) b) E) e r) (fun i=>ώ T i.i):= by
   unfold Xe uprise Needle.push Tall.hill; refine Twill.sums (range (e+1)) (sh X) fun i hi=>?_
   have hA(i:Wings u 1) : PowerSeries.constantCoeff (♣ i.i E).scale=1:= by unfold didn don afternoons; simp [mat_zero] -- afternoon
   have ho (i:Wings u 1): PowerSeries.constantCoeff (Γ i).scale=1:= (he.fair i).once
   exact (outlay he ((mem_range_succ_iff.mp hi).trans hk) b r).scales (rehearseT (sh X) (fun i hi=> lane_here he (hi.trans (le_trans (Nat.sub_le ..) hk))) ho hA r i) (sh X)
lemma snowfall_steps (x:Launch u)(hk:e≤E)(b:Letter F): ◇ x.i b e=uprise (don ν D' X x.i) (◆ (x.i+1)) b e:= by
    ext1 r; unfold uprise; rw [←daylight hk]; refine tendsto_nhds_unique (hurled_t (irons he x hk b r)) ?_; apply hurled_t; exact Twill.stint (w:=ώ T x.i) (C:=x.farY X) ((snowfall he hk b r).move (escalates x)) (bye X x) (fun _=> (gain_pos ..).le) (T.pos _|>.le)
end YM.RG08.Door
