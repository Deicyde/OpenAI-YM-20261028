import YM.MergeProof.Summit
import YM.Extension.UV.Shoot
import YM.Extension.UV.VacDemand
import YM.Extension.UV.FloorD
/-! Same producer path as Legato.noel. Retain the Bolt Program and tuning witnesses of the actual
construction before extraction, not an implication on an arbitrary pair of choices. Does not claim
the nearby solutions unique.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent Extension.UV

structure UVBuild (G : Gauge) where
  grid : Metals G
  rolls : Rolls grid.p
  prices : Alloy grid rolls
  works : Factor prices
  stages : ℕ→ℝ
  worth : Bid.Worth
  b : Bandage works stages worth
  engine : Bolt prices
  Q : ℕ→ℕ
  ref : ℕ→ℕ
  manufactured (d N i : ℕ) : TransferData ((Labels.frames G).level d) (Issue.trail engine) N i
  room (N p m : ℕ) (hi:m < N) : GaugeDoor ((Issue.trail engine).rep N p (m+1)) ((Issue.trail engine).rep N p m)

namespace UVBuild
variable (X : UVBuild G)
def C : Family G := ⟨Issue.trail X.engine,hol G,Labels.frames G,localSection G,X.ref,X.manufactured⟩
abbrev tower := X.prices.B
structure Shared : Prop where
  same : Chateau X.b X.Q X.engine X.ref X.manufactured X.room
  built : X.C.Makes
  cal : Spec.Calibrated X.C
  root : Extraction.Wcmain X.C
  scent : Acme.Aroma X.C
  plate f : Cells.CellHyp X.C f→ Grill X.C f ∧ East.CompleteWeak X.C f
  finish (g:Extraction.Order) : ∃ (f:Extraction.Order) (A:Table X.C.book) (L:ℕ→Table X.C.book) (R:Bin A) (T:Table X.C.book) (E:DiffPlan T), Next.Extract.Base X.C (g.refine f) A L R T E ∧∃ s:Spec.Seed X.C (g.refine f) T,Maxwell.Ranks T s.kernel.spin

section
variable (hG:G.Simple)(h:Shared X)
include hG h
-- derived from Shared (in particular h.same etc), not asserting any calibration suffices
lemma final_at : ∃ f : Extraction.Order, ∃ S : Table X.C.book, Nonempty (Spec.Final X.C f S):=by
  let F:= Extraction.Order.full
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:=h.finish F
  obtain ⟨hs,hZ⟩:= h.plate (F.refine g) s.copies
  obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E) h.scent hG hs hZ s hA.clean.ready hA.clean.tilt
  exact ⟨F.refine g,T,Acme.glistens h.cal hA.clean.ready hA.clean.tilt p⟩
end

lemma histories (hG:G.Simple) (t : ℝ) (ht:NearTarget X.tower.a t) : ∃ H : RG.History G, neighboring X.tower t H ∧ SelectedAt t H := all_nearby X.tower X.engine.program hG ht
lemma current : neighboring X.tower X.tower.a.clock.bar X.C.path ∧ ∀ N m p (_hm:m < N),X.tower.Move N m p (X.C.path.rep N p m) (X.C.path.rep N p (m+1)):= ⟨⟨X.engine.history,rfl,X.engine.sticks,X.engine.choice.reaches,X.engine.moves⟩,X.engine.moves⟩
-- Caution latter fields defeq due C built path; if elaboration issues rewrite.
end UVBuild

def residual (X : UVBuild G) (n p i:ℕ):=(X.engine.history n p i).beta - ((X.engine.history n p (i+1)).beta + X.tower.kin.alpha n i)
structure Secure (X : UVBuild G) : Prop where
   numeric : NumericAdmission X.tower.a X.tower.bake X.engine.history
   budget n p i (hi:i<n) : |residual X n p i| ≤ capacity (X.tower.a.clock.hatBeta (i+1))
namespace UVBuild
lemma reserved (X:UVBuild G) (hG:G.Simple) (h:X.Shared) (hm:NumericAdmission X.tower.a X.tower.bake X.engine.history) (hp : (waitAbove X.grid.p).choose ≤ X.prices.delay.betaEntry) : Secure X := by
  refine ⟨hm,fun n p i hi=> ?_⟩
  obtain ⟨l,t,Q,H,x,hx,e₁,e₂⟩:= (h.same.nest.held n i p hi).1
  have hg i := demand_credits X.tower.valid hp i
  apply real_budget_capacity hm (hg _)
  unfold residual
  rw [e₁,e₂]
  exact ((H.moves hG hi).2 x hx).2.2.1
end UVBuild

variable (hG:G.Simple)


lemma blockFloor {s:Metals G} {D:Rolls s.p} (A:Alloy s D) (k:ℝ) (f:ℕ→ℕ) (hv:s.p.floorL=f) (h:∀ j,Linear.Dcost k j ≤ f j): Linear.SizeFloor k A.B.a := by
  intro i
  let a:= A.B.a
  have ht := A.B.valid.lengths
  have hh := a.fits.sameFactor i
  have hp := (D.large (a.clock.J (i+1))).need
  exact (h _).trans (by rw [← ht,hh] at hp; exact_mod_cast hv ▸ hp)

include hG
theorem uv_delivery_secure {b:ℝ} (h:0<b) : ∃ X:UVBuild G, X.prices.B.a.clock.kernel.penalty=b ∧ X.Shared ∧ Linear.SizeFloor b X.tower.a ∧ Secure X := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= himalayas hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let F := fun j=> max (l j) ⌈Linear.Dcost b j⌉₊
  have hLF : l ≤ F := fun j=> le_max_left ..
  let M:=ThroughLaunch.currency s T F
  obtain ⟨⟨P⟩,H⟩:= hK F hLF

  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  let H₂ := H P
  obtain ⟨w,h⟩:= H₂
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  let V' : Delays θ := { V with betaEntry:=fun i=> max (max (V.betaEntry i) ((waitAbove M.p).choose i)) (demand G P i) }
  have hV : DelayLe V V' := ⟨fun _=> (le_max_left ..).trans (le_max_left ..),le_rfl,le_rfl,le_rfl⟩
  obtain ⟨D,hD⟩:= Bar.exists_above V' ((sum_cap_target G hG).choose); let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V' hV D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hq,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ (∀ f:Extraction.Order,MergeProof.East.CompleteWeak Z f) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩ -- fix argument order
  let W : UVBuild G:= ⟨M,P,Alloy.mk F θ V' D Y X B,R,_,_,c,T,fun _=>1,t,S,D'⟩
  have hsFloor : Linear.SizeFloor b W.tower.a := @blockFloor _ M P W.prices b (fun j=> max (l j) ⌈Linear.Dcost b j⌉₊) rfl (fun j=> (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (l j) ⌈Linear.Dcost b j⌉₊)))
  have hZ : W.C = Z:= rfl
  have h₉ : W.Shared := by
    exact ⟨hT,hF,hc,hW,hπ,fun f hf=>⟨grilled Z hF hU hq hf,hu.2 f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  refine ⟨W,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,h₉,hsFloor,W.reserved hG h₉ (numerical_admission hG W.tower.valid (fun i=>le_max_right ..) hD W.engine.sticks W.engine.choice) (fun i=> (le_max_right ..).trans (le_max_left ..))⟩ -- uses defeq

theorem uv_delivery_floor {b:ℝ} (h:0<b) : ∃ X:UVBuild G, X.prices.B.a.clock.kernel.penalty=b ∧ X.Shared ∧ Linear.SizeFloor b X.tower.a := by
   obtain ⟨X,hx,hX,hY,hZ⟩:=uv_delivery_secure hG h
   exact ⟨X,hx,hX,hY⟩

theorem uv_deliver {b:ℝ} (h:0<b) : ∃ X:UVBuild G, X.prices.B.a.clock.kernel.penalty=b ∧ X.Shared:=by
  obtain ⟨X,hQ,hs,hL⟩:=uv_delivery_floor hG h
  exact ⟨X,hQ,hs⟩
end YM.PhysicalNext.Repeat.Legato
