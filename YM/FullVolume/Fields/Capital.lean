import YM.FullVolume.Fields.Ivy
import YM.FullVolume.Gables.Vendee
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}(hG:G.Simple){M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:Bolt A}{C:ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K)
open YM.MergeProof MergeProof.Matric Guard
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Sever
variable {q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p}{f:ℕ→ℕ}{p m k:ℕ}
structure Rising (X:Factor A) (q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p)(f:ℕ→ℕ)(p:ℕ)(k:ℕ) where
    branch :∀ n, Branch X (q n) (f n) p k
    paths n m : k ≤ m → m ≤ f n → (q n (f n) p m).path=A.B.kin.path (f n) m
    helmet : Helmet A p f q k
variable (J:Rising X q f p k)
namespace Rising
set_option quotPrecheck false
local notation "V'"=>fun m i=> q i (f i) p m
local notation "P'"=> A.B.a
local notation "S"=>Pass.stageP
section
include J
lemma flooded {m}(hm:k ≤ m): Flux (V' m) (S P' m p) (P'|>.params m|>.clip) (P'|>.params m|>.width) (P'|>.params m|>.paths) (P'|>.clock.loopCap m) (P'|>.clock.allowance m) (P'|>.clock.forcedAllowance m):=by
    let H:= J.helmet; obtain ⟨v,hv,hX⟩:= H.earns _ hm
    have hg:= H.sails.eventually (eventually_ge_atTop m)
    refine ⟨hg.mono fun n hn=> ((J.branch n|>.choice).represents (f n) p m hn).good,hg.mono fun n hn=> ⟨((J.branch n|>.choice).represents (f n) p m hn).vac,((J.branch n|>.choice).represents (f n) p m hn).clip⟩,⟨v,hv,hg.mono fun i hi=> hX _ hi⟩,H.costa m hm,?_⟩
    obtain ⟨r,v,hp,hA,h⟩:= Stationary.Artes.nativity H.cfront m; refine ⟨r,v,hp, hp.width.trans hA,fun g hg'=>?_⟩; filter_upwards [H.sails.eventually (h g hg'),hg] with i h H; rw [J.paths i m hm H]; exact h
end
variable {ψ:ℕ→ℕ} (T:∀ n d N p,TransferData ((Labels.frames G).level d) (A.B.bake.make (q n)) N p)
-- Σ galleries per q.N
abbrev wen (q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p)(ψ:ℕ→ℕ)(S':∀ n d N p,TransferData ((Labels.frames G).level d) (A.B.bake.make (q n)) N p) (n:ℕ):= Family.mk (A.B.bake.make (q n)) (hol G) (Labels.frames G) (localSection G) ψ (S' n)
local notation "Lx!"=>wen (A:=A) q ψ T
local notation "D"=> Boutique.attire Y
variable (hx:Jams.Wild X.shape A.delay)
variable (hz:Nest X Y) (d:ℕ)
structure Tenable (d':ℕ) (ψ:ℕ→ℕ):Prop where
   height : k ≤ ψ d'
   label : d'+3 ≤ A.B.a.clock.J (ψ d')
   firsts : ∀ n:ℕ,∀ h:ψ d' ≤ f n, Branch.Piano b (J.branch n) (fun i=> Boutique.brochure Y i p hz) height label (T n d' (f n) p) h
   second : ∀ n:ℕ, ψ d' ≤ f n → (T n d' (f n) p).Based (hol G) (localSection G d') (ψ d')
local notation "Ξ"=> (Labels.frames G).level d
variable (he:Tenable b J T hz d ψ)(y: (Labels.frames G|>.level d|>.Coeff))
open Next.Rank
local notation "U"=>fun k n=> Spindle.parcel (Lx! n) d k (f n) p y
section curves
include he hz hx hG J y
lemma grow (m:ℕ)(h:ψ d ≤ m):CauchySeq (fun n=>(show ((Labels.frames G).level d).Coeff from (U m n).x)) ∧
    ∃ c:ℕ→ Coin ((Labels.frames G).level d) (hol G) (D m p), CauchySeq c∧ ∀ n:ℕ,∀ hm: m≤ f n, Coin.uses (c n)= capture (U m n) (Keeper.sufficient (J.branch n|>.slots _ (he.height.trans h) hm)):= Branch.stays hG b hz (fun i=> Boutique.brochure Y i p hz) he.height he.label J.branch J.helmet hx (fun i=> T i d (f i) p) he.firsts he.second y m h
lemma hail (m:ℕ)(hr:ψ d≤ m) (t:Motion)(x:∀ i,Site (A.B.a.S.side i p)): Confluence (fun n=> (show Config G (A.B.a.S.side m p)→ℂ from indexX (Lx! n) d (f n) p y x t m)) ∧ ∀ i:Box (A.B.a.S.side m p),Confluence (fun n=> (show Config G (A.B.a.S.side m p)→ℂ from Ktone (Lx! n) d (f n) p y x t m i)):=by
    let u:= U m; let H:=V' m; let ξ:ℂ:= alto (Lx! 0).path m d; obtain ⟨h,c,hc,hM⟩:= J.grow hG b T hx hz d he y m hr
    have he' :∀ᶠ n in atTop, ∃ K: Keeper (H n).p (H n).activities, Along (H n) (D m p).orient ∧ (u n).Format 0 (hol G) (H n)∧ Coin.uses (c n)=capture (u n) K:= (J.helmet.sails.eventually (eventually_ge_atTop m)).mono (fun n hn=> ⟨_, ((J.branch n).notices (fun i=> Boutique.brochure Y i p hz) (he.height.trans hr) hn).alongside.sym, (he.second n (hr.trans hn)|>.format _ hr hn _),hM n hn⟩)
    let T:=localSection G d
    exact ⟨revive t (x m) (recto T H he' hc h) ξ,fun i=> revive t (x m) (towers H he' hc ((puff t (x m)).symm i)) ξ⟩
lemma creditP (m:ℕ)(hm:ψ d≤ m): ∃ B:ℝ,∀ n, Next.Rank.Spindle.paid (Lx! n) d m (f n) p y≤ B:=by
    obtain ⟨a,h,hB⟩:= Matric.Gear.allowance ((J.grow hG b T hx hz d he y m hm).1); let t:= alto (A.B.bake.make (q 0)) m d; exact ⟨‖t‖ * a, fun n=> by unfold Next.Rank.Spindle.paid Price.awake Price.columns; rw [Size.smul]; exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)⟩
end curves
lemma boreal {d:ℕ} {F:Labels.Frame G d}{n:Side}(R:Rep G n)(A:Hol G)(T:SectionData F)(t:Motion)(x:Site n)(y:ℂ){f:Coefficient F n}(h:f.Format 0 A R): Measurable (radiant y t x (f.exponentialEntry 0 T R))∧ ∀ i,Measurable (sunny R f.forced t x y i):=by
   have hv:Measurable (f.exponentialEntry 0 T R):=(measurable_const.add (masked_measurable _ _ _ (T.continuous_places ..).measurable)).add (Measurable.tsum (fun i=> masked_measurable _ _ _ (h.smooth i).borel))
   have ht(i:Box n):Measurable (profile R.activities f.forced i):= Measurable.tsum (fun i=> h.borel i.val)
   have hc(f:Config G n→ℂ)(hp:Measurable f): Measurable (radiant y t x f):=by
      let m:ℂ→ℂ:=Motion.scalar t; have he:Measurable m:= by unfold m Motion.scalar; split; exact continuous_star.measurable; exact measurable_id
      exact (he.comp (hp.comp (continuous_pull ..).measurable)).const_smul _
   exact ⟨hc _ hv, fun i=> hc _ (ht _)⟩
include he y
lemma markets (m:ℕ)(hm:ψ d≤ m) (t:Motion)(x:∀ i,Site (A.B.a.S.side i p)): ∀ᶠ n in atTop, Measurable (indexX (Lx! n) d (f n) p y x t m) ∧ ∀ i:Box (A.B.a.S.side m p),Measurable (Ktone (Lx! n) d (f n) p y x t m i):=(J.helmet.sails.eventually (eventually_ge_atTop m)).mono fun n hn=> boreal (V' m n) (hol G) (localSection G d) _ _ _ (f:=U m n) ((he.second n (hm.trans hn)).format _ hm hn _)
end Rising
end YM.PhysicalNext.Repeat.Legato.Bandage
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Rising.flooded
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Rising.hail
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Rising.creditP
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Rising.markets
