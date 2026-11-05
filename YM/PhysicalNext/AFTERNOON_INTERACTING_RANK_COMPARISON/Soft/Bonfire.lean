import YM.Extra.MULTISOURCE_TRAJECTORIES.Adjoint
import YM.Extra.MULTISOURCE_TRAJECTORIES.Prepared
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Forestage
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Funds
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Postsale
import YM.Progress.CLASSICAL_KIN_RECURSION.Maple

/-!
# Step at frozen beta

The Kinesis premise is not required on this branch. The unmarked
budget carries all the way into the output E-supports. Top has still
come from true calibration (and the input to comparison retains path
from B). Modifying R on this Course trajectory only below k; not
an assertion of getting any of the primary calibration pieces. Moreover
a different mask, as when comparing in stage 1. No replacement in
Spec target.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis
     Pump Display.Sew Vale PhysicalGuard7f546.Curved Tree Push.SectorMeasure Oriented Function Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
section load_
open Next.Fluctuations.Sector
variable {c f : Side} {S : StepData c f} (x : ℝ) (v : Dyed G S) (R' : Rep G c)
private lemma scalar_base (ht : v.bp=R'.p) (hf : v.source.beta=R'.beta) (hU : R'.clip=v.things.low) (hD : R'.path=v.things.down) (h :∀ V,0<v.loading x V):
    ∃ b : ℝ,∀ V,v.loading x V= Real.exp (b*Fintype.card (Site c)-R'.beta*basis R' V):=by
  let C:=prefactor S G v.source.beta * Real.exp (v.source.v* Fintype.card (Site f)) *
    spare v.ratio v.source.beta ^ Fintype.card v.mode.Free * (Real.sqrt (Native.kinetic v.things v.mode v.token x).det)⁻¹
  have he(V): v.loading x V= banker v.things v.bp V v.source.beta*C:=by unfold Dyed.loading C; ring
  have hg:= h (1:Config G c); rw [he] at hg
  have hV:0<C:= pos_of_mul_pos_right hg (Real.exp_pos _).le
  refine ⟨Real.log C/Fintype.card (Site c),fun V=>?_⟩
  have hp:0<(Fintype.card (Site c):ℝ):=Nat.cast_pos.mpr Fintype.card_pos
  rw [he, mul_comm,div_mul_cancel₀ _ hp.ne',sub_eq_add_neg,Real.exp_add,Real.exp_log hV,ht,hf,banker,basis,hD,hU,neg_mul]; rfl
end load_
variable {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) (J : ChartRatio G) (ξ : Purse)
local notation "Λ"=> C.path.levels
local notation "s"=> Atlas.clim C.path.levels k
local notation "Υ"=> C.path.levels.params k
local notation "b"=> C.path.levels.clock.J k
local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "St"=> C.path.levels.clock.op i p
local notation "H₀"=> ξ.band
local notation "K0"=> Station.width C.path.levels ξ.band k
local notation "t"=> tunnel B N i p
local notation "X"=> Atlas.clim C.path.levels i
local notation "y"=> Atlas.clim C.path.levels (i+1)
variable (H : ShowHours J B ξ k w l r) (Z : Vents B ξ J l r k) (O : Corridor C.path.levels ξ.band ξ k) (hN : k ≤ N)
-- no P.Lawful at softer budget
structure Buoyant (R : Rep G (C.side i p)) (hi : i≤k) (hl : K0≤ i) : Prop where
  warm : Bush B J ξ (N:=N) H (white R) hi hl
  pets : Tissue R (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (rollup (clim C.path.levels k) (k-i)) (gas ξ.era.coast (Atlas.clim C.path.levels i))

section lift
variable {P : Rep G (C.side (i+1) p)} (hi : i<k)(hl : Station.width C.path.levels ξ.band k ≤ i) (hP : Buoyant B J ξ (N:=N) H P hi (hl.trans (Nat.le_succ i)))
local notation "Ψ"=> tabloid B J ξ H hi hl P (N:=N)
local notation "Ω"=> (C.path.levels.params i)
include Z O hl hi in
lemma elongation (hb : 0≤ ξ.band) : Escalates ξ (C.S.block i) s ∧ k-(i+1)≤ stretch (St).patch.L.val ξ.band s:=by
  have ht : C.S.block i=ℓ:= (sizes_at ξ O hl hi p).1
  constructor
  · rw [ht]; exact Z.great.specs hb (ht ▸ (show 1 < ((C.S.block i).val:ℝ) by exact_mod_cast (le_trans (by norm_num:2≤3) (C.S.block_large i))))
  change _ ≤ stretch (C.S.block i).val ξ.band s; rw [ht]; change _≤ height C.path.levels H₀ k+ surplus C.path.levels k
  rw [← O.heft.full,← O.heft.shift]; have hx := (wider (C.path.levels) H₀ k).trans (before ..); have hv:=wider (C.path.levels) H₀ k; have ht := before (C.path.levels) H₀ k; omega
-- Stand take exports param Q (supports recalibration of E)
structure Stock where
  commitment : Draft (tabloid B J ξ H hi hl (N:=N) P) (tell B i) (retime X) l
  exhibit : Plate (tabloid B J ξ H hi hl P (N:=N)) (retime X) l
  heated : 0<l
  lives : 0<fiery G (retime X) (St).patch.L
  loadng : ∀ V, 0<(Ψ).loading (retime X) V
  paid (Q : Rep G (C.side i p)) (hp : Q.p=(tabloid B J ξ H hi hl P (N:=N)).bp) (hs : 25*radiusB (retime X)+30 ≤ Q.p.B) :
    let p' := fun j=> shiftZ (Orchard.canopy St) hp.symm (sprouting commitment exhibit (Orchard.canopy St) j)
    Veins (white P) Q p' (L:=foliage commitment) commitment.enrolled hs hP.pets.status
         (load ξ.era) (acres ξ X y) (Line ξ.era ξ.goal 0 s) (sailboat s (k-(i+1))) ∧
     BodyGrant t P (foliage commitment) ((tabloid B J ξ H hi hl P (N:=N)).chi.profiles G St (retime X) l heated lives) J Q.p.threshold p' (fun V=> (((tabloid B J ξ H hi hl P (N:=N)).loading (retime X) V:ℝ):ℂ))
include M O Z hN in
lemma lifted (hb: 0≤ ξ.band) : Nonempty (Stock B J ξ H hi hl hP):= by
  have hL:=(sizes_at ξ O hl hi p)
  let j:= b; let F:= (Λ).clock; let V:= initials B.prices F.stage F.kernel j j (G:=G)
  have hk:tell B i=V:=by unfold tell V F j;rw [O.heft.plateau i hl hi.le,O.heft.plateau (i+1) (hl.trans (Nat.le_succ i)) hi]
  have hx := Z.great.kraft (St).patch hL.2 hL.1 (C.path.levels.blocks i p).branches;change Kraft J ξ V _ l r s at hx; rw [←hk] at hx
  have hp : Seeks (neutral (Ψ)) (tell B i) r X:= fitPost B M J ξ H ⟨Z.great.onRoad⟩ O hN hi hl hP.warm
  obtain ⟨he,hZ⟩:=elongation (p:=p) B J ξ Z O hi hl hb
  obtain ⟨H,M,he,h,hv,hQ⟩:=hx.prescribes he (O.court i hl hi.le) (St) (Ψ) _ hZ _ _ _ _ hP.pets rfl rfl hp
  refine ⟨H,M,he,h,hv,fun Q he hs=>?_⟩
  intro p'; refine ⟨?_,(hQ Q he hs).2⟩
  rw [show acres ξ X y=_ from congr_arg (acres ξ X) (calendar_warm ..)]; exact (hQ Q he hs).1
-- align Q record at unchanged temperature, allow new vacuum.E nucleus
structure Nucleated (Q : Rep G (C.side i p)) (A : Stock B J ξ H hi hl hP) : Prop where
  beta : Q.beta=P.beta
  params : Q.p=(tabloid B J ξ H hi hl P (N:=N)).bp
  tree : Q.path=(C.path.rep N p i).path
  clip : Q.clip=(C.path.levels.params i).clip
  hm : Q.path.Bounds Q.clip (Ω).width (Ω).paths (C.path.levels.clock.loopCap i)
  hk x b' : Nonempty (Q.activities.Moves x b')
  pets : Petals Q (rollup s (k-i))
  funds : ∀ hS : 25*radiusB (retime X)+30 ≤ Q.p.B,
    let p' := fun j=> shiftZ (Orchard.canopy St) params.symm (sprouting A.commitment A.exhibit (Orchard.canopy St) j)
    let E:Empty→ Rim Q.p.threshold G (C.side i p):=Empty.elim
    Resin (white P) Q p' (L:=foliage A.commitment) A.commitment.enrolled hS hP.pets.status ((tabloid B J ξ H hi hl P (N:=N)).loading (retime X)) E (load ξ.era) (kinetics s)
include Z O hN M
lemma fury (A : Stock B J ξ H hi hl hP) (hb:0≤ ξ.band): ∃ Q, Nucleated B J ξ H hi hl hP Q A:= by
  obtain ⟨Y,-,T,W,Q,hU,h⟩:= Paint.parser C (hi.le.trans hN) M (H.oldPrices i hi.le hl) p
  have hc := hU.precise.2.1.trans ((M.wilson.represents N p i (hi.le.trans hN)).clip)
  have hD := hU.precise.1; let v:= Ψ; have hp : Y.p=v.bp:= hU.precise.2.2.2.2.1
  let G₀: Rep G (C.side i p):={Y with beta:=P.beta}
  obtain ⟨c,hx⟩:= scalar_base (retime X) v G₀ hp.symm rfl hc hD A.loadng
  let F: Rep G (C.side i p):= {G₀ with v:=c}
  have hF : F.path.Bounds F.clip (Ω).width (Ω).paths (C.path.levels.clock.loopCap i):= T.paths
  let z:= fun j=> shiftZ (Orchard.canopy St) hp.symm (sprouting A.commitment A.exhibit (Orchard.canopy St) j)
  let L:= foliage A.commitment
  have h':F.p.B=walls X:= hp ▸ rfl
  obtain ⟨h₁,h₂⟩:= coast_lease B J ξ H hi hl hP.warm O F hp
  have h'': Lease (St).patch.L (white P).p F.p (load ξ.era) (acres ξ X y) (Line ξ.era ξ.goal 0 s) (sailboat s (k-(i+1))) (kinetics s) (gas ξ.era.coast y):=by
    obtain ⟨hX,hB⟩:= elongation (p:=p) B J ξ Z O hi hl hb
    exact hX.books (k-(i+1)) X y _ _ hB (O.court _ hl hi.le) (O.court _ (hl.trans (Nat.le_succ i)) hi) h' h₂
  let N':= pyro (L:=L) (white P) F z A.commitment.enrolled h₁ hP.pets.status hF
  have he := common_era ξ O hl hi.le; have ht:= (A.paid F hp h₁).1
  have hF':0 < P.beta:= bush_pos B J ξ O (P:=white P) hP.warm
  have hβ : P.beta ≤4*X:= by
    have hr : P.beta ≤2*y:= (bush_prices B J ξ O hP.warm).2; have hz:=O.court i hl hi.le
    linarith only [hr,hz.1, (O.court _ (hl.trans (Nat.le_succ i)) hi).2]
  obtain ⟨hY,hX⟩:= Z.great.costs.prices Λ i (O.court _ hl hi.le) P.beta hF' hβ Y.p h' (hp ▸ (show _ from congr_arg Stage.supportExponent he)) (hp ▸ rfl)
  change boxesCost Y.p P.beta (Υ).paths _ ≤ spray s at hY; change _≤ (Υ).width at hX; rw [←he] at hY hX
  obtain ⟨hZ,hm,hχ⟩:= pyro_gen (L:=L) (white P) F z A.commitment.enrolled h₁ hP.pets.status ht h'' hF hX T.labels.moves
  refine ⟨N', rfl,hp,hD,hc,hF,hm, thin N' hZ _ ?_,fun hs=>?_⟩
  · rw [show k-i=k-(i+1)+1 by omega];exact (add_le_add_left hY _).trans ((elongation (p:=p) B J ξ Z O hi hl hb).1.accept _)
  intro p' E; refine ⟨fun V=>?_, ⟨(fun i=>i.elim),(fun i=> i.elim),(fun i=>i.elim),fun i=>?_⟩,fun i j=>?_⟩
  · rw [Fintype.prod_empty,mul_one]; refine Eq.trans ?_ (hχ V); change v.loading (retime X) V * _=_; rw [hx V]; rfl
  · unfold Flux.strike; rw [show (Finset.univ : Finset Empty)=∅ by rfl,filter_empty,sum_empty]; exact (Real.exp_pos _).le
  exact ⟨Equiv.refl Empty,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim⟩
end lift
end YM.PhysicalNext.InteractingRank.Soft
