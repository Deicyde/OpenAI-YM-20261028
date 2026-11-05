import YM.MergeProof.West.Vroom
import YM.TraceExtension.Prom.Front.West.Canvas
import YM.TraceExtension.Prom.Front.West.Cassia
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.Fix
import YM.TraceExtension.Prom.Front.West.Flight
import YM.TraceExtension.Prom.Front.West.Jenn
import YM.TraceExtension.Prom.Front.West.Melt
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Prince
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition Filter
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{X:Points n} {B:Purse} {R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s:ℝ}{Ψ:AtlasData G C.S p}

set_option quotPrecheck false
local notation "AX"=> C.path.levels
local notation "w"=> middleSky AX B.band k
local notation "γ"=> clim AX k
variable {F:Fin n→poly (Chamber G C.S k p)} (Xg:CeremonySky B c P R Ψ) (hv:Kith (A:=C.path.levels) F X B)
    (hq:Caff (G:=G) B (clim C.path.levels k) (k-middleSky C.path.levels B.band k) u n)
local notation "T"=> Ship.yardSky C B.band c.allow p
local notation "ι'"=> (Ship.yardSky C B.band c.allow p).Cell × Fin n
local notation "Z"=> torque γ
local notation "M"=> sheen B γ n+1
local notation "r"=> loot B γ u
include Xg hq hv
lemma greenfeeSky (h:w ≤ i)(hi:i<k) (a:BaleSky C k B.band p B.horizon X hi.le) (U) (x:modes (Fin n)) (E: StageNowSky c R X B.band hi h B.era.coast.Q a (P (i+1)).p.threshold U (B.sends γ)) (ht:Healthy (P i).p.threshold (d_olmSky X B.band B.era.coast.Q (walls (clim AX i)) c.allow hi.le a.1 a.2.val) U)
    (hx:x.val ⊆ a.2.val.val.val): ‖text (vantageSky E) (heads R F hi.le x)‖ ≤ sheen B γ n:=by
    obtain ⟨hy,hP⟩:= metopiaSky hv hq h hi.le (R:=R) (fun i hi hi'=> (Xg.probes.steps i (h.trans hi) hi').pay) x; let V:=F
    let A':= Xg.grant.spend.calm
    apply (view_v _ (heads R F hi.le x) hP A' ?_).trans (le_trans (mul_le_mul_of_nonneg_right hy ?_) ?_)
    rotate_left
    · exact zero_le_one.trans (priced_up _ A')
    · exact mul_le_mul_of_nonneg_right (quota_ge _ _ n) (zero_le_one.trans (priced_up _ A'))
    intro j hj; let S:= basisFtSky c X B.band i c.allow hi.le h a.1 a.2.val U
    obtain ⟨-,z,hz,H⟩:=mem_filter.mp (travelsSky hi.le R F h Xg.sens.canvas Xg.sens.withers hv.regions x hj)
    refine (rigidHelm S j).trans ((i_nsuredSky Xg.sens.canvas h hi.le a.1 j U ?_ ht).trans ((Xg.birth i h hi.le).2.2.trans (Xg.grant.spend.lots _ (Xg.grant.court i ((Station.widerSky ..).trans h) hi.le))))
    exact (separation_triangle ..).trans ((add_le_add (a.2.property _ (head_member _) z (hx hz)) H).trans_eq (add_mul ..).symm)

lemma fluorSky (h:w ≤ i)(hi:i<k)(a:BaleSky C k B.band p B.horizon X hi.le) (U) (E: StageNowSky c R X B.band hi h B.era.coast.Q a (P (i+1)).p.threshold U (B.sends γ)) (ht:Healthy (P i).p.threshold (d_olmSky X B.band B.era.coast.Q (walls (clim AX i)) c.allow hi.le a.1 a.2.val) U):
    ‖(leadFtSky E (offerNowSky E (vista R F hi))).part a.2.val.val - ((tapestrySky hv hq hi.le h Xg.sens c a).value U)‖ ≤ bracelets B γ n:= by
   have hz := topicaSky hv hq (h.trans (Nat.le_succ _)) hi (R:=R) (fun k hk hk'=> (Xg.probes.steps k ((h.trans (Nat.le_succ _)).trans hk) hk').pay); have hs := (rent_buy B γ n).trans (quota_ge B γ n);have hD:= harnessSky Xg h hi
   let y:=quotaFt B γ n; let e:=B.sends γ; have he:0< e:=Real.exp_pos _
   have hf := Xg.grant.spend; have hh:=hf.calm
   have hy₀:0≤gym B γ n:=Finset.sum_nonneg (s:=Finset.univ) (fun u _=> grantS_nn (sprout _ (primeLog (Fin n)) u) _ _ _ (degrFt B n) hD.grain he.le (zero_le_one.trans hs))
   apply f_inaleSky E F ?_ Xg.sens.canvas hD ht he ((Glimmer.billed _ (neg_nonpos.mpr B.positive)).trans (by simp [bill])) (zero_le_one.trans hs)
     (woven R F hi (fun i hj=> Xg.sens.gauge i (h.trans (by omega))) hv.lofty) (fun i=> (hz i).2) (fun i=> (hz i).1)
     (fun u=> (West.housingSky hv hq (h.trans (Nat.le_succ _)) hi Xg.sens u).2) M
     (le_add_of_nonneg_left (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hs (priced_up _ hh)))) _ le_rfl hy₀ (fun i hh=> add_le_add (greenfeeSky Xg hv hq h hi a _ _ E ht hh) hq.bytes)
   intro v hv'
   by_cases hK : v.val.Nonempty
   · let q : Manner n :=⟨v,hK⟩; let H:= West.housingSky hv hq (h.trans (Nat.le_succ _)) hi Xg.sens q; exact ⟨⟨q,H.1 hv'⟩,rfl⟩
   rw [show v=quiet _ from Subtype.ext (not_nonempty_iff_eq_empty.mp hK),forgotten] at hv'; exact False.elim (hv' rfl)

def leasedSky (hk:i≤k)(hh:w ≤ i) (L :Config G (C.side N p) → veil ((Ship.yardSky C B.band c.allow p).Cell × Fin n)) := let A0:=readersSky (C:=C) (b:=B.band) (p:=p) X c.allow (hk.trans c.allow); let T0:=P i
    ∃ (β α : Type),∃ (_ : Fintype β) (_:Fintype α), ∃(H: β→SourceAt G A0) (K:α → Lifted G A0 T0.p.threshold),
       c.flow L i (hk.trans c.allow)=Value.dust T0 (Sum.elim H (tapestrySky hv hq hk hh Xg.sens c)) K ∧ Background T0 K ∧ Light T0 H K (fun _ => loot B (clim AX k) u) (load B.era) (Purse.epoch B (clim AX k) (k-i)) (Perch.gas B.era.coast (clim AX i))
-- fuel
variable (E:PlesseySky B X c P R u) (hu:2≤u) (hx:FitSky C.path.levels B.band k X)
include E hu hx
lemma galacticSky (h:w ≤ i)(hi:i<k)(L)(hp:leasedSky Xg hv hq hi (h.trans (Nat.le_succ _)) L): leasedSky Xg hv hq hi.le h L:=by
  let hi':i+1≤k:=hi; let hc:= h.trans (Nat.le_succ _); let W:= tapestrySky hv hq hi hc Xg.sens c; let Y:= tapestrySky hv hq hi.le h Xg.sens c
  obtain ⟨α,β,hβ,hα,G',K,H,H₁,H₂⟩:=hp; let a:=Xg.grant; let f:=clim C.path.levels i; let x:= P (i+1); let y:=P i
  let δ:= bill (-1) γ; let Z':=Paint.trib B.era.coast.a f
  have hg:= a.races.pos (show k-(i+1)≤ _ from Nat.sub_le_sub_left hc k); let b:=Purse.epoch B γ (k-(i+1)); have hb : B.demand γ ≤ b:=Purse.profit ..
  have he:0 ≤ b:= (Real.exp_pos _).le.trans hb; have hr:0 < (r) := loaf ..
  obtain ⟨Lr,H'⟩:= E.sparks i hi h
  obtain ⟨A1,K1,T1,hA,hB,hC,H',D,S,h₁,h₂,h₃,h₄,h₅,h₆,hL⟩:= H'.lump W (levySky Xg hv hq hc hi) (divySky Xg hv hq hc hi hu) b he hg.2 _ _ hβ hα G' K H₂ H₁
  obtain ⟨hs₁,hs₂,hm⟩:= Xg.grant.spend.voice f (Xg.grant.court i ((Station.widerSky ..).trans h) hi.le); have hT: y.p.B=walls f:= (Xg.birth i h hi.le).1; have hS:1 ≤ quotaFt B γ n:= (rent_buy ..).trans (quota_ge B γ n); let J:=sheen B γ n
  have hJ:1 ≤ sheen B γ n:=one_le_mul_of_one_le_of_one_le hS (priced_up _ a.spend.calm)
  obtain ⟨_,_,hW,hK,F1,L1,hV,Hf,hζ⟩:= resFtSky y Y H' D S (levySky Xg hv hq h hi.le) hx Xg.grant.heft h Xg.sens.canvas hT h₅ h₁ h₄ (Real.exp_pos _).le hr (one_loot B γ u hu) (show 0≤load B.era from add_nonneg B.spend (by norm_num)) h₂ h₃ (show 0≤δ from (Real.exp_pos _).le) (show 0≤Z' from mul_nonneg B.era.coast.posA.le (sq_nonneg _)) (hq.pastry f (Xg.grant.court i ((Station.widerSky ..).trans h) hi.le)) (hT.symm ▸ hs₂) (y:=bracelets B γ n) (by
    intro j U HH; let h':=levySky Xg hv hq h hi.le j
    rw [show (Y j).fires=_ from h'.2,hL j U HH]
    exact fluorSky Xg hv hq h hi j U (Lr.tag _ _ HH)  (Eq.mp (congr_arg (fun Q => Healthy y.p.threshold (d_olmSky X B.band B.era.coast.Q Q c.allow hi.le (C:=C) j.1 j.2.val) U) hT) HH)) (by
    unfold bracelets grater gym gentility; apply mul_nonneg
    · exact Finset.sum_nonneg (fun u (_:u∈(univ : Finset _))=> West.penny _ _ (le_trans zero_le_one (hJ.trans (le_add_of_nonneg_right zero_le_one))))
    exact Finset.sum_nonneg (fun u _ => grantS_nn (sprout _ (primeLog (Fin n)) u) _ _ _ _ (knock _) (Real.exp_pos _).le (zero_le_one.trans hS)))
  · refine ⟨_,_,hW,hK,F1,L1,?_,Hf,?_⟩
    · rw [Course.flow_step c _ i (lt_of_lt_of_le hi c.allow),H]; exact Eq.trans h₆ hV
    refine ⟨Shine.loose (show Shine _ _ _ _ _ from hζ.bulk) ?_, Stripes.loose (show Stripes _ _ _ _ _ from hζ.forced) ?_⟩
    · have hR : B.epoch γ (k-i)=(B.era.α+2)*b:= by
         unfold Purse.epoch Purse.race b; rw [show k-i=k-(i+1)+1 from by omega,pow_succ]; dsimp only [Purse.epoch,Purse.race];ring
      rw [hR]; have hy:=hq.buys; unfold Purse.demand at hb hy; linarith only [hb,hy]
    have ht: Perch.gas B.era.coast f=Real.exp (-Z'):=by unfold Perch.gas Z' Paint.trib; ring_nf
    exact (mul_le_of_le_one_right (Real.exp_pos _).le hm).trans_eq ht.symm

end YM.Next.Rank.Tapes.West
