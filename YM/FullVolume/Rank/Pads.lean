import YM.FullVolume.Rank.Esteem
/-! `ClovenD` readouts Cauchy through the common DownKeeper, in ℓ¹ even if Q varies. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Rank
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune Finset
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι:Type}
local notation "R"=> S.orient
namespace Hue
structure Entails (S:Desk G n) (K:Keeper S.orient.p S.orient.activities) (p : Coefficient F n) (a: F.Coeff) (x: Coin F A S): Prop where
   lead : p.x=a
   paid : ∃ v,p.remBound 0 S.orient S.k v
   trim : Coin.uses x=capture p K
lemma assures {P Q:ℕ→ Coefficient F n}{X Y:ℕ→ Coin F A S}{p q:ℕ→ F.Coeff}(K:Keeper S.orient.p S.orient.activities)(h: Hue P Q A S) (hv:∀ i,Entails S K (P i) (p i) (X i))(ht:∀ i,Entails S K (Q i) (q i) (Y i)) :
     Tendsto (fun n=> p n-q n) atTop (𝓝 0) ∧ Tendsto (fun n=> X n-Y n) atTop (𝓝 0):=by
    refine ⟨h.reads.congr' (Eventually.of_forall fun n=>congr_arg₂ (·-·) (hv n).lead (ht n).lead),Metric.tendsto_nhds.mpr fun ε hε=>?_⟩
    filter_upwards [h.sent _ (half_pos hε)] with n hn; rw [dist_zero_right]; apply lt_of_le_of_lt ((Coin.wealths _).mpr ?_) (half_lt_self hε); rw [map_sub,(hv n).trim,(ht n).trim]; obtain ⟨a,ha⟩:= (hv n).paid; obtain ⟨b,hb⟩:=(ht n).paid; rw [← Matric.collected _ _ _ (h.same n) ha hb]; exact alongPay (show Well S.orient S S.k from ⟨⟨rfl,rfl⟩,rfl⟩) _ _ (h.turns n) hn
variable {H:History G}{N p m:ℕ}
abbrev SiteMarks (f c:Side)(E:Desk G c)(O:∀ m':Extra.Histories.Motion,E.orient.activities.Moves m'.1 0) (U:F.Index→ File G f→ Coefficient F c) (D:Desk G f) (a:ℝ) (T:Gram F A D a) (y:F.Coeff): Coefficient F c:= Extra.Histories.pencil (code _) (fun i:Tally F=>audition (O i.1) (U i.2 (Coin.uses (T.scythe i.2)))) (chips F) y
lemma conforms {D:Desk G (H.S.side (m+1) p)}{E:Desk G (H.S.side m p)} (U: Tool F H N p m){T:Heading F}{S:SectionData F}{Z:Worth}{Q:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{c ζ v W}(hP:Tool.Cap U S A Z Q T c ζ v W)(ha:Well (H.rep N p (m+1)) D (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))(hw:Well (H.rep N p m) E (Real.sqrt (H.levels.clock.forcedAllowance m)))(hp:roomCost H.levels Z)(hf:Bank Z H.levels) (O:∀ m':Extra.Histories.Motion,E.orient.activities.Moves m'.1 0) (T':Gram F A D ((H.levels.params (m+1)).columns))(k:Keeper E.orient.p E.orient.activities)(hk:cart («R»:=H.rep N p m) U.down=cart k)(x:F.Coeff):Entails E k (SiteMarks _ _ E O U.shot D _ T' x) (T'.index U hP ha hp hf x) (T'.recorded U hP ha hw hp hf x):=by
   obtain ⟨hx,hh,h⟩:= Hue.clovenD E D U ha hw hP k hk O T' x; exact ⟨hx,hh,h⟩
lemma pitches {f c: Side}{D: Desk G f} (E:Desk G c)(S:SectionData F)(O:∀ m':Extra.Histories.Motion,E.orient.activities.Moves m'.1 0){a:ℝ} (T:Gram F A D a) (x:F.Coeff) (hS:S.Sound A)(hc:2≤c.val) (P Q:ℕ→F.Index→ File G f→ Coefficient F c)(he:∀ i,Hue (fun n=>P n i (Coin.uses (T.scythe i))) (fun n=>Q n i (Coin.uses (T.scythe i))) A E): Hue (fun n=> SiteMarks f c E O (P n) D a T x) (fun n=> SiteMarks f c E O (Q n) D a T x) A E:= Hue.multiple (chips F) x (fun i=> Hue.rhythm (he i.2) _ (O i.1) S hS hc)
end Hue
end YM.FullVolume.Paint.Rank
#print axioms YM.FullVolume.Paint.Rank.Hue.pitches
#print axioms YM.FullVolume.Paint.Rank.Hue.assures
#print axioms YM.FullVolume.Paint.Rank.Hue.conforms
