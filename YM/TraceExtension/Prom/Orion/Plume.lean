import YM.TraceExtension.Prom.Orion.Eupho
import YM.MergeProof.East.Plume
import YM.TraceExtension.Prom.Front.West.Lys
import YM.TraceExtension.Prom.Front.West.Tael
import YM.TraceExtension.Prom.Hill.Ratchet
/-!
  Variant of YM.MergeProof.East.Plume for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Ribbon Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D:ℕ} {ι:Type}[Fintype ι] {z:ℝ}
variable (P:ι → Panel D) (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels

structure PoisedSky (n:ℕ)(z:ℝ)(k:ℕ)(t:ℕ→ℕ→TableL C D):Prop where
    early : ∀ d,d ≤ D → C.ref d ≤ k
    limit : max (((A).clock.factor ((A).clock.J k)).val:ℝ) (((A).clock.factor ((A).clock.J k-1)).val:ℝ) ≤ (A).clock.monitor k
    charts : ∀ N p, k < N→ Charting D k (t N p) N p
    bank : ∀ N p, k < N → ∀ i:Fin (D+1), InvoiceSky C k N p i (t N p i)
    supply (χ:ι) : ∃ l r,∃ h:LegacyCostSky B J (-3) z ((P χ).bag ((A).clock.J k)) k n D O l r,∀ N p (hx:k<N),∃ V,ActumSky B H O J (P χ) h V hx ∧ ∀ d:Fin (D+1),∃ L:StampDuty C k N p d ((P χ).bag ((A).clock.J k)).taylor V ((P χ).bag ((A).clock.J k)).era.coast.Q (stamp A N p),L.T=t N p d

lemma stagingSky (g:G.Simple)(x:ι)(F:ParadeX C)(w:ℕ)(hw:D ≤ w): ∀ᶠ k in atTop, ∀ (P:ι→ Panel D)(hf:(P x).θ=w)(_hp:∀ i,(P x).θ=(P i).θ ∧ ∀ k:ℕ,((P x).bag k).era.coast.Q=((P i).bag k).era.coast.Q), max (((A).clock.factor ((A).clock.J k)).val:ℝ) (((A).clock.factor ((A).clock.J k-1)).val:ℝ) ≤ (A).clock.monitor k→
    (∀ i,∃ l r,LegacyCostSky B J (-3) z ((P i).bag ((A).clock.J k)) k n D O l r) → ∃ p,PoisedSky P B H O J n z k p:=by
   let I:= Fin (D+1); have hE(d:Fin (D+1)):=(mintingSky B g H F d w (le_trans (Nat.le_of_lt_succ d.isLt) hw))
   filter_upwards [eventually_all.mpr hE,follows_prices H g,eventually_all.mpr (fun d : I=> eventually_ge_atTop (C.ref d.val))] with k he hf hD P hΨ hp hv hx
   have hR (d:Fin (D+1)): C.ref d ≤ k:=hD d
   let m:= (A).clock.J k;let u (i):=(P i).bag m; let c:=u x
   have hm: c.taylor=w:= ((P x).stable _).trans hΨ
   choose l r h using hx
   have hy(i): LegacyCostSky B J (-3) z (u i) k n D O (l i) (r i):=h i
   choose V Ht using fun χ N p (hn:k<N)=> prospectSky B H O J (P χ) (hy χ) hn (hf N p hn.le)
   have hu (N p) (hn:k<N) (d:Fin (D+1)):
       ∃ L:StampDuty C k N p d c.taylor (V x N p hn) c.era.coast.Q (stamp A N p),(∀ s b,L.T (mir (C.labels.level d) s b)=mir (C.labels.level d) s (L.T b)) ∧ InvoiceSky C k N p d L.T:=by
      have hw := (Ht x N p hn).pays;
      rw [show c.taylor=w from hm]
      apply he d (hR d) (hm ▸ (hy x).moves.year) (hm ▸ (hy x).moves.length) N p hn.le (V x N p hn) c.era.coast.Q hw.threshold hw.budget hw.qbar
      have hs :Hail C k p c.taylor (stamp A N p):=hw.birth _ rfl; rw [← hm];exact hs
   choose L hL hT using hu
   let p0 (N p:ℕ):TableL C D:= if h:k<N then (fun d=>(L N p h d).T) else 0
   have hh (N p) (h:k<N)(d): p0 N p d=(L N p h d).T:=by simp [p0,h]
   refine ⟨p0,fun d hd=> hR ⟨_,Nat.lt_succ_of_le hd⟩,hv,fun N p hn d=>by rw [hh N p hn];exact ⟨(L N p hn d).lights.span,hL N p hn d⟩,(fun N p hN d=>by rw [hh N p hN]; exact hT N p hN d),fun i=> ⟨l i,r i,hy i,?_⟩ ⟩
   intro N p hn; refine ⟨V i N p hn,Ht i N p hn,fun d=>?_⟩
   have he:=hp i; let U:= L N p hn d; have hW: c.taylor=(u i).taylor:= (hm.trans hΨ.symm).trans (he.1.trans ((P i).stable m).symm)
   have h1:= (Ht i N p hn).pays; have h2:= (Ht x N p hn).pays; obtain ⟨T,-,hu',-⟩:= reborn hW U (he.2 m) (h2.budget.trans h1.budget.symm) (h2.threshold.trans h1.threshold.symm)
   exact ⟨T,hu'.trans (hh N p hn d).symm⟩
end YM.MergeProof.East
