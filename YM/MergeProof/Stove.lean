import YM.MergeProof.Groom
import YM.MergeProof.Kettle
import YM.MergeProof.SpringT
import YM.MergeProof.Wax

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Push
open Mallow Lotus
open YM.MergeProof MergeProof.Accent MergeProof.Menu
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}
section
variable {Q:ℕ→ℕ} {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
variable (h : Steam Q A.delay)
local notation "α"=>A.B.a
set_option quotPrecheck false
local notation "ℓ"=>A.B.a.clock
local notation "P!"=> A.B.a.budget
local notation "J"=> A.B.a.clock.J
local notation "x!"=> A.B.a.clock.hatBeta
-- attach schedule.clout
local notation "H"=> Issue.trail Y
include h
lemma stamina (m:ℕ) : let x:= x! m; let y:=x! (m+1);8≤(P! m).B ∧ y^3 ≤ mintK (P! m).B∧ (let p:=Q (J (m+1)); let t:ℝ:= A.B.a.clock.forcedAllowance m + p*Extra.Multi.siteFactor (P! m).B*stub x
                        (((P! m).B+(P! m).B+1:ℕ):ℝ)^4*t≤3 ∧ Real.exp t-1≤1)∧ ∀ d,d≤ J m→ creek G (A.B.a.params m) (A.B.a.params (m+1)) d x y (tableCost G (A.B.a.params (m+1))) (A.B.a.S.block m) := by
   intro x y; have hh:= h (J (m+1)) (J m) x (step_paid A.B.a m) (A.B.valid.pays m); have he:= Extra.Iteration.block_beta (a:=α) m
   unfold y; rw [he, params_eq A.B.valid, params_eq A.B.valid,Extra.Iteration.block_eq A.B.valid]; exact hh

def renal (p:Levels G) (m:ℕ):ℝ:= probe (p.clock.hatBeta (m+1))
def fly (p:Levels G) (d m:ℕ):ℝ:= fog G d (p.clock.hatBeta m)
def near (p:Levels G) (m:ℕ):ℝ:= sap (p.clock.hatBeta (m+1))
def far (p:Levels G)(m:ℕ):ℝ:= stub (p.clock.hatBeta m)
def mutt (p:Levels G)(Q:ℕ→ℕ) (m:ℕ):= Q (p.clock.J (m+1))
lemma evaporates {k:ℕ} : Brine (Issue.trail Y) k (renal A.B.a) (near A.B.a):=by
   refine ⟨fun m _=>?_,fun m hm=> ?_,fun m hm=>?_,fun m _=> (stamina h m).1⟩
   · have hp := (show 0 < x! (m+1) from zero_lt_one.trans (A.B.a.fits.delayed _)); exact ⟨inv_pos.mpr hp,Real.rpow_pos_of_pos hp _⟩
   · have hp := (show 0 < x! (m+1) from zero_lt_one.trans (A.B.a.fits.delayed _)); change 1 ≤ _*_*mintK (P! m).B
     unfold renal near Mallow.probe sap; rw [Real.rpow_neg hp.le, Real.rpow_ofNat]; field_simp; have hh:=stamina h m|>.2.1; linarith only [hh]
   have hx := Stock.consumes A.B.valid A.prices|>.grows m
   have ht := A.B.a.S.block_large m; exact le_trans hx (Nat.mul_le_mul_right _ (show 2 ≤ (A.B.a.S.block m).val by omega))

lemma resides {d k:ℕ} (hp : d ≤ J k) : let L:= (Labels.frames G).level d
     (Fiesta H L (fly α d) (waybill α) k ∧ Cherry d k H (near α) (fly α d)) ∧
       ∀ m:ℕ,k ≤ m → Banks H L (Doors.cameras G d) (far α) (fly α d) m ∧ minSide G d ≤ (P! m).B:=by
   intro L; have hx(m)(hm:k ≤ m): creek G (α|>.params m) (α|>.params (m+1)) d (x! m) (x! (m+1)) (tableCost G (α|>.params (m+1))) (A.B.a.S.block m):=(stamina h m).2.2.2 d (hp.trans (A.B.a.fits.mono hm))
   refine ⟨⟨⟨fun m hm=>(hx m hm).1,fun m hm=> (hx m hm).2.1,fun m _=> mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (title_one ..)))⟩,⟨fun m hm=> (hx m hm).2.2.2.1, fun m hm=> (hx m hm).2.2.2.2.1⟩⟩,fun m hm=> ⟨⟨Doors.cameras_ge G d,?_⟩,(hx m hm).2.2.2.2.2⟩⟩
   let x:= x! m; let T:= Doors.cameras G d; let C:= P! m
   have he:1 ≤ x:= (α|>.fits.delayed _).le; have hg:0 < fog G d x:= by have hp:0<x:=zero_lt_one.trans_le he; exact inv_pos.mpr (pow_pos hp _)
   refine le_trans (mul_le_mul_of_nonneg_right (b:= (_:ℝ)) (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hg.le) ((hx m hm).2.2.1)
   exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr C.threshold_pos).le (show C.threshold⁻¹ ≤ x from Doors.temp_cheap he) _) (zero_le_one.trans (Doors.cameras_ge G d)) -- potential implicit

include b
lemma escape (hG : G.Simple) (hN:Nest X Y) (hp:Minty X.shape Q A.delay)(ht:∀ m:ℕ,100 ≤ (P! m).supportExponent)(D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m))
     (he:∀ N p m (hm:m<N), Climbs X Y N m p (D N p m hm)) : Moonlit H (mutt α Q) (renal α) (far α) D := by
   constructor
   · intro N p k hk; have he:= Bandage.paneer hG b Y hk Q hN (he N p k hk) hp.hold (hp.word _ _ (A.B.valid.pays k) _ (step_paid _ _)) (ht _) (ht k); exact ⟨_,_,he⟩
   intro k x; have ht:=ht k; refine ⟨div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by norm_num), show 0≤ (P! k).supportExponent-3 from by linarith only [ht],?_⟩; exact (stamina h k).2.2.1
end
end YM.PhysicalNext.Repeat.Legato.Bandage
