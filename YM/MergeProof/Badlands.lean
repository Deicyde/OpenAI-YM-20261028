import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.SpringT
import YM.Next.RANK.Insiders
import YM.Next.RANK.Scars
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris


/-! path witness tied to SPEC family. Presentation-and-value. aligned at arbitrary coarse k. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent Menu Motion Extra.Multi Next.Rank Next.Rank.Spindle
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
variable (C:Family G) (d N k p:ℕ)
set_option quotPrecheck false
local notation "H"=> C.path
local notation "Ω" => C.labels.level d
local notation "T"=> C.localSection d
local notation "P"=> C.path.levels.budget
variable (v:C.label d) (o:∀ m:ℕ,Site (C.side m p))(a:Motion) (w:ℝ)
local notation "Rv"=>C.factory d N p
local notation "B!"=> C.path.rep N p

def indexX (k):= radiant (alto C.path k d) a (o k) ((parcel C d k N p v).exponentialEntry 0 (C.localSection d) (C.path.rep N p k))
def Ktone (k):= sunny (B! k) (parcel C d k N p v).forced a (o k) (alto C.path k d)
def item : Config G (C.side N p)→ℂ:= stepUp a (o N) (C.O N p v 0)
-- same d entries (not M equivalence required to align seq).Pack pledge hung to family.
variable (W: Bid.Worth) (u ψ φ δ: ℕ→ℝ)(ζ:ℕ→ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
-- some delimiters required
structure Freightage (d N p:ℕ):Prop where
    lyrics : let H':= C.path; ∃ Z:Extra.Histories.Music (C.labels.level d) C.path N p,
      (C.factory d N p).entries=(Z.draft C.path).inits∧Sung (C.localSection d) C.path N p C.params W (C.ref d) Z∧
         (∀ m:ℕ,C.ref d ≤ m →∀ hm:m<N, Carol (C.localSection d) C.path N p m (D N p m hm) (Z.tone (m+1)) (Z.tone m) (ψ m))∧ ∀ v,profile (C.path.rep N p N).activities ((Z.tone N).plays v).forced=hook (C.path.rep N p N).activities (C.path.rep N p N).p.threshold (booster (C.localSection d) (C.path.rep N p N) 0 v)
structure Geyser : Prop where
   night : Moonlit C.path r δ u D
   cost : roomCost C.path.levels W
   back : Bank W C.path.levels
   stay : Brine C.path 0 δ φ
   mom : Monotone r
   heights d k N p : C.ref d ≤ k → k≤N → ∃ X,
        Fiesta C.path (C.labels.level d) (ζ d) ψ k ∧ Cherry d k C.path φ (ζ d) ∧ Banks C.path (C.labels.level d) X u (ζ d) N ∧ coverNumber (C.path.levels.budget N).B ((C.localSection d).footprint (0:Site (C.side N p))) ≤ 1 ∧ (∀ (i:(C.labels.level d).Index)(U:Config G (C.side N p)), ‖(C.localSection d).places (Size.axis (C.labels.level d) i) 0 U‖ ≤ X)
   aim d N p : C.ref d ≤ N → Freightage C W ψ D d N p
variable (s:V → C.label d) (f:∀ m:ℕ,V→ Site (C.side m p)) (g:V→Motion)(purse: V→ℝ)
   {q:∀ m:ℕ,m≤N→ Config G (C.side m p)→Poly B} -- fix notation
local notation "Z"=> (fun i=> item C d N p (s i) (fun j=>f j i) (g i))
local notation "k!"=> (fun m i=> Ktone C d N p (s i) (fun j=> f j i) (g i) m)
local notation "f!"=> (fun m i=> indexX C d N p (s i) (fun j=> f j i) (g i) m)
lemma Geyser.at (hh : Geyser C W u ψ φ δ ζ r D)(h:C.Makes)(he:C.ref d ≤ k)(hk:k≤N)(hm:Occupancy (f k) (r k))(hx:Migrating C.path k p N f)(hz:Drake B (P k).B (f k))
    (hM:∀ i,purse i*paid C d k N p (s i) ≤ ζ d k)(hw:∀ i,0<purse i)(ht:∀ i:ℕ,k ≤ i →∀ hi:i<N,q i hi.le=(C.path.levels.clock.op i p).push ((C.path.rep N p (i+1)).beta) (q (i+1) hi))
    (hv:q N le_rfl=birth B (C.path.rep N p N) Z) (hP: Integrable (q N le_rfl) (prior G (C.side N p))) : ∀ i:ℕ,k ≤ i→∀ hN:i≤N, Served (B! i) (f! i) (k! i) (q i hN) (f i) (march purse φ k i) (topPitch C.path N i) 1:=by
    obtain ⟨M,hI,hS,hK,hY⟩:= (hh.aim d N p (he.trans hk)).lyrics
    obtain ⟨v,hF,hX,hB,hb,hH⟩:= hh.heights d k N p he hk
    let Y:= (C.factory d N p).terminal.symm ∘ s
    have hp(m j):parcel C d m N p (s j)=(M.tone m).plays (Y j):=by unfold parcel; rw [hI];rfl
    have hf:Brine C.path k δ φ:=⟨fun i _=> hh.stay.water _ (Nat.zero_le i),fun i _=> hh.stay.mint _ (Nat.zero_le i),fun i _=> hh.stay.split _ (Nat.zero_le i),fun i _=> hh.stay.support _ (Nat.zero_le i)⟩
    have hZ: Sung T H N p C.params W k M:= ⟨hS.head,hk,fun j hi=> hS.earned _ (he.trans hi),fun j hi=> hS.step _ (he.trans hi)⟩
    have hM'(i:V): purse i*bond H N p M k (Y i) ≤ ζ d k:=by
       refine le_trans (le_of_eq (congr_arg (purse i* ·) ?_)) (hM i)
       unfold Next.Rank.Spindle.paid Price.awake Price.columns -- inspect
       rw [Size.smul]; unfold bond; congr 1;rw [← (hS.earned k he hk).currents (Y i)] -- hint
       exact congr_arg (C.labels.level d).coeffSize (congr_arg Coefficient.x (hp k i).symm) -- maybe simplify
    have ht:= pollinate C.path C.params W φ ψ (ζ d) u δ r D p N k (C.localSection d) M g Y f purse h.wilson hh.cost hh.back hk hw (h.sections d) hZ hf hX hh.mom hm hx hz hh.night hF hB hM' hb hH (fun i hi ht=> hK i (he.trans hi) ht) hY ht hv hP
    intro i hi hN; simp_rw [Ktone,indexX,hp]; exact ht i hi hN
end YM.MergeProof
