import YM.RG08.Lyt.Hatch
/-! # Stable transport in full EXP norm on projection-null
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Lyt
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff Classical
open Wings Summit
variable {X:Chain}{G:Gauge}{D d k t n τ s E e i j r:ℕ}{w':ℝ}{T:Labels.Frame G d}{H:SectionData T}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{hp:1/2≤w'}{hD:d+1 ≤ D}{h:Hol G}{M:Signals P Q E τ h H hp hD}{ν:G.ColorIndex}{D':ChartRatio G}{S:Prism G X.kernel g Q E}
variable {I J:Type}{u:I→Windows}{b:J→ShoreP u}{v:Wall b 1→ Wings u 1}
local notation "Ⓨ"=> wallY X
variable (K:Tights M S ν D' u)
variable (hv:∀ i,(v i).toLaunch=i.world.toLaunch)
variable {A:Wall b 0→ BoardU D w' G}{p:J→ℝ}
-- expo width
structure Stems (M:Signals P Q E τ h H hp hD)(p:J→ℝ)(A:Wall b 0→ BoardU D w' G)(U:Wall b 1→BoardU D w' G)(e r:ℕ):Prop where
  here : Tin (wallY X) (strideP X b p) (fun i=> A i e r) (fun i=> ώ M i.i)
  paths : Tin (wallY X) (strideP X b p) (fun i=> U i e r) (fun i=> ώ M i.i)
  paid (k: Letter T): slot k=r→ Dig (wallY X) (strideP X b p) (fun i=> coeff e (call h T (U i) k))

local notation "Γ" => Run.route A X ν D' v t d
local notation "Δ" => strideP X b p
local notation "σ" => fun i:Wall b 1=> ώ M i.i
-- positive input scales (exponential point ask). Unrestricted Width table already by Tights (new smaller).
private lemma past_m (hv:t+e<r)(he:∀ i,Crop t (A i) h T){B:Wall b 1→BoardU D w' G}(hU:∀ i,Marvel t (B i)): Stems M p A B e r:= by
   constructor
   · simp_rw [show ∀ i,A i e r=0 from fun i=>not_ne_iff.mp (mt ((he i).hU.cap e r) (by omega))]; exact Tin.zero
   · simp_rw [show ∀ i,B i e r=0 from fun i=>not_ne_iff.mp (mt ((hU i).cap e r) (by omega))]; exact Tin.zero
   intro j hj; simp_rw [call, coeff_mk,fun i=>audit_cap h (hU i).cap j (e:=e) (by omega)]; exact Dig.zero
include K
private lemma harvest_s (he:Keeps A M ν D' v t)(hz:e≤E)(h1: Tin (fun i=>wallY X (Wall.tip b i)) p (fun i=> A (Wall.tip b i) e r) (fun i=> ώ M (Wall.tip b i).i))(hh:∀ i,0<p i)
    (ht:∀ j k,awaits 1 e r j k → Stems M p A Γ j k): Stems M p A Γ e r:= by
   let U:= Γ
   have hg i : Marvel t (U i):= crest_u (K.fair _) hp (he.zone i.roof|>.hU); have hy i: Lank (U i):= crest_l (K.fair _) hp ((he.zone _).hU) ((he.zone _).paid)
   by_cases hC:r≤t+e; swap; · exact past_m (by omega) he.zone hg
   let y:Wall b 1→ℝ:=wallY X; have hE := anchor_v K he.wake; have hP i:(v i).i=i.i:= congr_arg Launch.i (he.wake i)
   have hQ : ∀ j k, awaits 1 e r j k→ Tin y (strideP X b p) (fun i: Wall b 1=> A i.roof j k) (fun i:Wall b 1=>ώ M ((v i).i+1)):= by
      intro l j hx; simp_rw [hP]; exact ascendM (fun i=>(hh i).le) (crops_w K he.wake) (ht l j hx|>.here)
   let Q i:= fetchU (heights X ν D' (v i)) t d (A i.roof) e r; let B i:= aboard d (babyQ G X (v i)) (A i.roof e r)
   let Y i:= aboard d (heights X ν D' (v i)).tree (A i.roof e r); let D1(i:Wall b 1):= strideP X b p i
   have hV i:0 < D1 i:= mul_pos (hh _) (gain_pos ..)
   have hd (g:∀ i:Wall b 1,EnvelopeU D w' G r)(P:Tin y D1 g (fun i=>ώ M (v i).i)): Tin y D1 g (fun i=>ώ M i.i):= by simp_rw [hP] at P; exact P
   have hv' : Tin y D1 Q σ:= hd _ (fetching_p hE hp he.caps hz hV (t:=t) (fun i=>he.zone i.roof|>.hU) hQ)
   have hu : Tin y D1 (Y-B) σ:= hd _ (ward_p K he.wake _ (t:=t) (fun i=> he.zone i.roof|>.hU) he.caps hz hC (fun j hj r=> hQ j r (Or.inl hj)))
   have hU i: U i e r=Y i+Q i:= formula_bucks (K.fair _) (he.zone i.roof|>.hU) hp d e r
   have hK : Tin y D1 (fun i=> U i e r-B i) σ:= by convert hu.plus hv' hE.env using 1; funext i; simp only [hU,Pi.add_apply,Pi.sub_apply]; abel
   -- Π: expo investments. reserve
   have hS' (i:Wall b 1): ώ M i.i ≤ 1:= ((tick_t M _|>.1).trans (tick_t M _|>.2)).trans (min_le_right ..)
   have hc': Weighed y (fun i:Wall b 1=> (ώ M i.i)⁻¹):= (Wall.invested X).sway hE.env (K.he.costs.transfer (fun i:Wall b 1=> i.world.toLaunch))
   have pay (b: Letter T)(hj:slot b=r): Dig y D1 (fun i=> coeff e (call h T (U i) b)):= by
     simp_rw [call,coeff_mk,auditT]; rw [hj]; refine Dig.sums _ hE.env (fun n hn=> ?_)
     split_ifs with hB; swap; exact Dig.zero -- shadow
     by_cases hz:n=r
     · subst n; rw [Nat.add_sub_cancel]; rw [show (fun i=> invest h (U i e r) b)=(fun i=>invest h (U i e r-B i) b) from funext fun i=>?_]; · exact digs _ hK (fun _=>M.pos _) hS' hc' _
       obtain ⟨hx,hg',hz'⟩:=pollen (e:=e) (v i) (he.zone i.roof|>.hU) (he.zone _|>.paid) (he.zone _|>.spine) K.he b hj; rw [invest_less _ b (seat_made (hg _)) hx (hy _ _ _) hg',show invest _ (B i) b=0 from hz',sub_zero]
     have hv: n< r:= lt_of_le_of_ne (mem_range_succ_iff.mp hn) hz; exact digs _ ((ht _ _ (Or.inl (by omega:e+n-r<e))).paths) (fun _=> M.pos _) hS' hc' b
   have hm {b:Letter T}(hk:r≤slot b) : Dig y D1 (fun i=>coeff e (call h T (U i) b)):= by
      rcases hk.eq_or_lt with hak|hak; exact pay b hak.symm; exact (ht e _ (Or.inr ⟨rfl,by simp only [one_ne_zero,↓reduceIte]; exact hak⟩)).paid b rfl -- hak Lean conditional
   have ht': Tin y D1 (fun i=> A i.low e r - U i e r) σ:= by
      have hT (i):= he.rise i
      rw [show (fun i:Wall b 1=> A i.low e r- U i e r)= -(fun i:Wall b 1=> edgeBook (Ye X ν D' M (v i|>.low)) (call h T (U i)) e r) from funext fun i=>?_]; swap; · rw [hT]; unfold eject; exact sub_sub_cancel_left .. -- verify
      apply Tin.neg; refine over_s hE.env (fun i hi j r=>?_) (fun i=>K.firs _|>.toBoards) (fun j b hj=>?_)
      · let w:Wall b 1→ℝ:= fun i=> ώ M (v i).i; have hx := cashIn K (hi.trans hz) j r; have hv :=hx.move (fun i=> (v i).low); rw [show σ=w from funext fun i=>congr_arg (ώ M) (hP i).symm]; exact ⟨_, (arms_w K he.wake).sway hE.env hv.serves.choose_spec.1,hv.serves.choose_spec.2⟩
      rcases hj with hj|⟨rfl,hj⟩; exact (ht _ _ (Or.inl hj)).paid _ rfl; exact hm hj
   have hh': Tin (wallY X) (strideP X b p) (fun i=>A i e r) (fun i:Wall b 0=> ώ M i.i):= by
     have hv:= ht'.plus hK hE.env
     have hA: Tin y D1 (fun i=> A i.low e r-B i) σ:= by convert hv using 1; funext i; exact (sub_add_sub_cancel ..).symm
     have hg : r ≤ τ+E:= by have hl:=he.caps; omega
     exact hatch (fun i=>(hh i).le) h1 (fun i C H=>edge_path K he.wake i (he.zone i.roof|>.paid e r) (held h ((he.zone i.roof).hU) (he.zone _|>.paid) (he.zone _|>.spine) e r) hg H) hA
   refine ⟨hh',?_,pay⟩
   have hh' := ascendM (show 0≤p from fun i=>(hh i).le) (crops_w K he.wake) hh'
   change Tin y D1 (fun i=> U i e r) σ; rw [show (fun i=>U i e r)=Y+Q from funext hU]; refine (hd Y (boarding_c hE hp hz hV (fun i=>he.zone i.roof|>.hU) ?_)).plus hv' hE.env
   simp_rw [hP]; exact hh'
lemma tribal_pay (he:Keeps A M ν D' v t)(h:∀ i,0<p i)(hE:e≤E)(hz:∀ i≤ E,∀ j,Tin (fun i=>wallY X (Wall.tip b i)) p (fun k=> A (Wall.tip b k) i j) (fun i=> ώ M (Wall.tip b i).i)): Stems M p A Γ e r:=by
    refine tribes_ind (k:=t) hE _ (fun i hi r hx=> harvest_s K he hi (hz _ hi r) h hx) (fun i hi r hx=>past_m hx he.zone ?_)
    exact fun i=> crest_u (K.fair _) (by assumption) (he.zone i.roof|>.hU) -- shadow
end YM.RG08.Lyt
