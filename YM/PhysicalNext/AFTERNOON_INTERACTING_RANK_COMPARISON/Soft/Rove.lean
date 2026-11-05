import YM.Further.QUANTUM_RATES_PORT.Waves
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Legate
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Tissue
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Push.LOOP_COEFFICIENT.Resolution

/-!
# Incoming auxiliary E perturbation on the actual chart

Produce a Plate and exposure by way of the E-blank calculation
on the same physical inputs, no change to fields or to loading. Pay
E cost separately from K and path. Not assuming E regularity is obtained
in these powers on soft stretch. Still with all field/mask tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst Pump Ac
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum
     Tree PhysicalGuard7f546.Curved Next.SectorChange AnalyticNext.ConnectedActivity AnalyticNext.ConnectedActivity.Cab Push.SectorMeasure.Oriented
     AnalyticBridge.LocalGaussianLaws Exterior Dictionary Push.Local Push.AbsoluteSums
     RecursiveSecants079.BothSides
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {v : Dyed G S}
    {P : Teller G} {W L t x a b y q w d : ℝ}

def neutral (v : Dyed G S) : Dyed G S:= {v with source:=white v.source}
local notation "Ψ"=> neutral v
lemma costume (p : Pilot G S x) : v.Playing W p ↔ (Ψ).Playing W p:= Iff.rfl
lemma upgrade (p : Pilot G S x) : v.spoolLift p=(Ψ).spoolLift p+Ancestor.gen v p:= by
  unfold Dyed.spoolLift apart Ancestor.gen
  rw [show (neutral v).source=white v.source from rfl,show (neutral v).top p=v.top p from rfl]
  rw [show (white v.source).p=v.source.p from rfl]; dsimp only; rw [show (white v.source).activities.additive v.source.p (v.top p)=0 from whiteAdd ..];
  rw [show averaged (fun s=> Presented.reduced (white v.source) (Stores.till x) (pull s 0 (v.top p)))=_ from (rfl : _ = averaged (fun s=> Presented.reduced v.source (Stores.till x) (pull s 0 (v.top p))))]
  rw [show (neutral v).keptEarly p=v.keptEarly p from rfl]; simp only [neutral,white]; ring

variable (h : Petals v.source y) (ht : Chips (neutral v) P W x)

def payment (d a t u : ℝ) (L : Side) (B : ℕ) := Footprint.payment (L.val^4) (Footprint.extentCost 1 B) 0 t u d a (Footprint.preCost 1)
include h ht in
lemma offers_bits (hp : 25*radiusB x+30≤ v.bp.B)
    (hv : Footprint.reserve v.source.p.supportExponent a (Footprint.conversion S.ratio 1) t) (hx : v.source.p.B≤2*v.bp.B): Petty v W v.bp.B a (payment y a t 1 S.patch.L v.bp.B) (Ancestor.gen v (x:=x)):= by
  obtain ⟨w,hw,hA⟩:=h.price; let R:=v.source; let r:= R.activities; let B:=R.p; let f i p:=(r.regularOccurrence B i (v.top (x:=x) p)); let X i:=(r.reg i).support; let Y i:= wings S v.bp.B (X i)
  have hY i: Pulled (fun p=> -f i p) (Y i):= by
    refine ⟨fun A F k=> Ancestor.issueTop ht (Measurable.neg (h.live i)) A F k,fun p q ho he hy=>?_⟩
    apply congr_arg Neg.neg; apply UsesFinal.allReads _ _ _ (h.look i)
    intro j hj _; exact (neutral v).peak_record hy j ht.boost.ready ((direct_beam (S:=S) hp (Next.Rank.Thirst.inspect (X i) hj)).shrink (by omega))
  have hg i := (hw i).1; have hX : Footprint.Anchored (fun i=> (r.reg i).site) w (fun i=> coverNumber B.B (X i)) B.supportExponent y:= by intro x; convert! hA x using 1; ext i; simp [BudgetPoint.mass,X,B,r,R,mul_comm]
  have hh : Ac.Hit Y v.bp.B w a (payment y a t 1 S.patch.L v.bp.B):=
    Footprint.coarsen S.ratio 1 v.bp.B B.B X _ (fun i=> (r.reg i).anchor) w hg hX Y (fun i=> by simp [Y,Footprint.enlargement,wings]) v.bp.B_pos hx zero_le_one hv 0 w hg (fun _=>by simp)
  exact (Petty.accepts hY (fun i=> ⟨_, involved _ _ (r.reg i).anchor⟩) hg hh hv.1 (fun i p hp=> by rw [abs_neg]; exact (hw i).2 _)).traded fun _ _ _=> (tsum_neg ..).symm

include h ht in
lemma spins_g (H : ∀ a b,Nonempty (v.source.activities.Moves a b)) (p : Pilot G S x) (hp : Matched p) (e : Wheel c) (w : Site c→G.El) : Ancestor.gen v (burnish w (spires e p))= Ancestor.gen v p:= by
  let i:= spires e p
  have hi := hp.signed e; unfold Ancestor.gen
  rw [v.top_steam ht.boost i hi];
  let s:=S.ratio.embed e.2
  let k:=(H e.1 s).some
  let F := fun V : Config G f=> - v.source.activities.additive v.source.p V
  have hx (k : Site f→G.El) (U : Config G f) : F (Lattice.gauge k U)=F U:= Real.exp_injective (paint_gauge _ h k U)
  change F _= F _; rw [hx,show v.top i = _ from v.top_ship e ht.boost.funded p]
  let U:=v.top p
  have hv :(white v.source).exponent (pull e.1 s U)=(white v.source).exponent U:= Push.Local.exponent_pull (whiteTurns _ _ _ k) U
  have hh:= Push.Local.exponent_pull k U (R:=v.source)
  rw [whiteExp v.source _,whiteExp v.source U, hv] at hh
  exact congr_arg (Neg.neg : ℝ→ℝ) (sub_right_inj.mp hh)


variable {h}
include ht
lemma facing (hp : Petty v W v.bp.B a d (Ancestor.gen v (x:=x))) (h : Petals v.source y) (H : ∀ a b,Nonempty (v.source.activities.Moves a b)) :
    ∃ (f : Glade c→Pilot G S x→ℝ) (w : Glade c→ℝ), Ac.Hit (fun i:Glade c=>i.val) v.bp.B w a d ∧ (∀ i,0≤w i) ∧ (∀ i, Pulled (f i) i.val) ∧ (∀ i,Tinted (f i)) ∧
      (∀ (i : Glade c) p e, f (garden (orient e) i) p=f i (spires e p)) ∧
      (∀ i p,Matched p → |f i p| ≤ w i) ∧ ∀ p,Matched p→ v.Playing W p→Ancestor.gen v p=∑ i,f i p:= by
  obtain ⟨g,b,hg,hb,hc,hd,hp⟩:=hp
  let T:= routes c; refine ⟨fill T g,_,liquidate T hb,fun i=> sum_nonneg fun j _=> mul_nonneg (cash_pos c).le (hc _), fun i=>(fill_price T g hg i).1,fun i=>(fill_price T g hg i).2.1, fun i p e=> (fill_price T g hg _).2.2 e p,fun i p H'=> bill_saving T g hg hd p H' i,fun p he hA=>?_⟩
  rw [full T g hg (fun i=> ⟨_,hd i⟩) _ p he]
  have hx (i : Wheel c) (f : Site c→G.El) :
      let q:= burnish f (spires i p)
      (∑ j∈univ.map (T.dial i).symm.toEmbedding, g j q)=Ancestor.gen v p:= by
    intro q; have hv : Matched q:= (he.signed i).bright f
    rw [show (univ.map ((T.dial i).symm).toEmbedding)=univ from Finset.ext fun _=>by simp, ←hp q hv]
    · exact spins_g h ht H p he i f
    exact (neutral v).starlet W ht.boost p he f i ((costume _).mp hA)
  simp_rw [hx]; simp only [MeasureTheory.integral_const,Measure.real,IsProbabilityMeasure.measure_univ,ENNReal.toReal_one,one_smul]; rw [← sum_mul,cash_one,one_mul]
end YM.PhysicalNext.InteractingRank.Soft
