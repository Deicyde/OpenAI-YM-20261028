import YM.MergeProof.West.Dink
import YM.TraceExtension.Prom.Front.West.Jenn
import YM.TraceExtension.Prom.Front.West.Melt
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Prince
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.LedgerGate
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.West.Dink for dynamic stops. Pulse extension.
-/
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
structure PlesseySky (B:Purse)(X:Points n)(J:Course C N p k)(P:(i:ℕ)→ Rep G (C.side i p))(R:Lead G C.S p) (u:ℕ): Prop where
  sparks (i:ℕ) (h : i<k)(ht : middleSky C.path.levels B.band k ≤ i):
    let x:=clim C.path.levels k
    ∃ v : IgnFtSky R B.band X J h ht B.era.coast.Q B.horizon (P (i+1)).p (P i).p (B.sends x), PleaFtSky B.era (P (i+1)) (P i) (B.sends x) B.goal v (loot B x u)
  dark i : Station.widthSky C.path.levels B.band k ≤ i → i<middleSky C.path.levels B.band k → NonLeadingSky B.era X (Ship.allowance C.path.levels u k) J i (P (i+1)) (P i) B.band
structure CeremonySky (B:Purse)(J:Course C N p k)(P:(i:ℕ)→ Rep G (C.side i p))(R:Lead G C.S p)(Ψ: AtlasData G C.S p):Prop where
   grant : CorridorSky C.path.levels B.band B k
   sens : ReadyShSky (A:=C.path.levels) B.band Ψ B.horizon B.era.coast.Q k R
   probes : KFlux (C:=C) k (middleSky C.path.levels B.band k) Ψ B R
   birth i (h:middleSky C.path.levels B.band k ≤ i)(hi:i≤k): (P i).p.B=walls (clim C.path.levels i) ∧
       (P i).p.threshold= C.path.levels.clock.hatCoupling i * Perch.hot (clim C.path.levels i) ∧
       (P i).p.threshold/anneals C J i ≤ torque (clim C.path.levels i)
   invariant : invariantAt (C:=C) k (wood C.path.levels k) p Ψ

variable {F:Fin n→poly (Chamber G C.S k p)} (Xg:CeremonySky B c P R Ψ) (hv:Kith (A:=C.path.levels) F X B)
    (hq:Caff (G:=G) B (clim C.path.levels k) (k-middleSky C.path.levels B.band k) u n)
include Xg
lemma harnessSky (hm : middleSky C.path.levels B.band k ≤ j) (hk : j<k) :
    let s:=clim C.path.levels k
    Metal B.band c R hk (B.sends s) (P (j+1)).p.threshold (P j).p.threshold (knox s) (torque s) B.L:= by
  intro s; let u:= hm.trans (Nat.le_succ j); let h:=Xg.grant
  have ht(i : ℕ) (he : middleSky AX B.band k ≤ i) (hv : i ≤ k) : (P i).p.threshold / anneals C c i ≤ torque s := (Xg.birth i he hv).2.2.trans (h.spend.lots _ (h.court _ ((Station.widerSky ..).trans he) hv))
  exact ⟨Xg.sens.withers j hm hk,(Xg.probes.steps j hm hk).pay,Glimmer.costed _ _ zero_le_one,h.spend.calm,(ht _ u hk).trans h.spend.inside, ht _ hm hk.le,h.spend.transverse,h.spend.budget,Xg.probes.realPath _ hm hk⟩
include hq
lemma levySky (H:w ≤ i)(he:i≤k): princFtSky C (P i).p c.allow X B.band he B.era.coast.Q B.horizon p (tapestrySky hv hq he H Xg.sens c) := by
    intro j; rw [(Xg.birth i H he).1]; exact ⟨rfl,rfl⟩
include hv
lemma divySky (hh:w ≤ i) (hi:i ≤ k)(hu:2≤u) :
    Shine (tapestrySky hv hq hi hh Xg.sens c) (P i).p (fun _ => loot B γ u) (load B.era) (bill (-4) γ):=by
   let u':= B.era.coast.Q; let e:=load B.era; let l:=torque γ; let y:= loot B γ u; let a:= rentQ u' e; let V:=proDue B γ u n; let W:= tapestrySky hv hq hi hh Xg.sens c; let L:=(P i).p
   have ht:= Xg.grant.spend; have hx := hi.trans c.allow; have hs:=ht.calm; have he: 0<a:= Real.exp_pos _; let r := quotaFt B γ n
   have hb:0<y:= loaf ..; have hB:y ≤ 1:= one_loot B γ u hu
   have hS:1≤r:=(rent_buy ..).trans (quota_ge B γ n)
   have hT:1 ≤ sheen B γ n:= one_le_mul_of_one_le_of_one_le hS (priced_up (degrFt B n) hs)
   apply perFtSky _ (levySky Xg hv hq hh hi) (show 0≤V from mul_nonneg he.le (mul_nonneg hb.le (zero_le_one.trans hT))) _ _ _ ?_ hq.lit
   intro j; refine ⟨(show 0≤V from mul_nonneg he.le (mul_nonneg hb.le (zero_le_one.trans hT))),fun U hh'=>?_⟩
   have hvP := levySky Xg hv hq hh hi j; let S:= basisFtSky c X B.band i c.allow hi hh j.1 j.2.val U; let v:= (W j).fires; have hv2:0<v.val.card:= Finset.card_pos.mpr (W j).chosen
   let f:= vista R F hi j.2.val.val; have h': Value.charge L e (W j).extent ≤ a:= by rw [hvP.1];exact hall u' L (add_nonneg B.spend (by norm_num))
   change Value.charge L e (W j).extent * Poly.toll (fun _=>y) v * ‖dot _ (text (rigid S) f)‖ ≤ a * (y * _)
   rw [dot_norm,mul_assoc]
   have ht : Poly.toll (fun _=>y) v ≤ y:= by unfold Poly.toll; rw [prod_const]; exact (pow_le_pow_of_le_one hb.le hB (show 1 ≤ _ from hv2)).trans_eq (pow_one y)
   obtain ⟨hY,hD⟩:= topicaSky hv hq hh hi (R:=R) (fun j hj hm=> (Xg.probes.steps j (hh.trans hj) hm).pay) j.2.val.val
   have hz : ‖text (rigid S) f‖ ≤ sheen B γ n:=by
      apply (view_v (rigid S) f hD hs ?_).trans (mul_le_mul_of_nonneg_right hY (zero_le_one.trans (priced_up _ hs)))
      intro i' h; refine (rigidHelm ..).trans ?_
      exact (i_nsuredSky Xg.sens.canvas hh hi j.1 i' U ((West.housingSky hv hq hh hi Xg.sens j.2.val).2 i' h) hh').trans ((Xg.birth i hh hi).2.2.trans (Xg.grant.spend.lots _ (Xg.grant.court i ((Station.widerSky ..).trans hh) hi)))
   exact mul_le_mul h' (mul_le_mul ht hz (norm_nonneg _) hb.le) (mul_nonneg (Poly.worth (fun _=> hb) _).le (norm_nonneg _)) he.le
end YM.Next.Rank.Tapes.West
