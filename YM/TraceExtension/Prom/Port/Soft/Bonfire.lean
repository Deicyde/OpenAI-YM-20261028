import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Bonfire
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Endow
import YM.TraceExtension.Prom.Port.Leashes
import YM.TraceExtension.Prom.Port.Opacity.Forestage
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Postsale
import YM.TraceExtension.Prom.Port.Stagecraft
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Bonfire for dynamic stops. Pulse extension.
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
private lemma scalar_baseSky (ht : v.bp=R'.p) (hf : v.source.beta=R'.beta) (hU : R'.clip=v.things.low) (hD : R'.path=v.things.down) (h :∀ V,0<v.loading x V):
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

local notation "Υ"=> C.path.levels.params k
local notation "b"=> C.path.levels.clock.J (i+1)
local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J (i+1))
local notation "St"=> C.path.levels.clock.op i p
local notation "H₀"=> ξ.band

local notation "t"=> tunnel B N i p
local notation "s"=> Atlas.clim C.path.levels k
local notation "X"=> Atlas.clim C.path.levels i
local notation "y"=> Atlas.clim C.path.levels (i+1)
local notation "K0"=> Station.widthSky C.path.levels ξ.band k
variable (H : ShowHoursSky J B ξ k w l r) (Z : VentsSky B ξ J l r k) (O : CorridorSky C.path.levels ξ.band ξ k) (hN : k ≤ N)
-- no P.Lawful at softer budget
structure BuoyantSky (R : Rep G (C.side i p)) (hi : i≤k) (hl : K0≤ i) : Prop where
  warm : BushSky B J ξ (N:=N) H (white R) hi hl
  pets : Tissue R (C.path.levels.params i).width (C.path.levels.params i).paths (C.path.levels.clock.loopCap i) (rollup (clim C.path.levels k) (k-i)) (gas ξ.era.coast (Atlas.clim C.path.levels i))

section lift
variable {P : Rep G (C.side (i+1) p)} (hi : i<k)(hl : Station.widthSky C.path.levels ξ.band k ≤ i) (hP : BuoyantSky B J ξ (N:=N) H P hi (hl.trans (Nat.le_succ i)))

local notation "Ω"=> (C.path.levels.params i)
include Z O hl hi in
lemma elongationSky : ∃ z : ℝ, Kraft J (vent ξ z) (tell B i) (St).patch l r s ∧ Escalates (vent ξ z) (St).patch.L s ∧ k-i ≤ stretch (St).patch.L.val (vent ξ z).band s:=by
  have ht : C.S.block i=ℓ:= (sizes_atSky ξ O hl hi p).1
  obtain ⟨z,he,hb,hv⟩:=Z.great i hl hi
  refine ⟨z,hv.kraft (St).patch rfl ht (C.path.levels.blocks ..).branches,?_,?_⟩
  · rw [show (St).patch.L=_ from ht]; exact hv.specs he (ht ▸ (show 1 < ((C.S.block i).val:ℝ) by exact_mod_cast (le_trans (by norm_num:2≤3) (C.S.block_large i))))
  rw [show (St).patch.L=_ from ht]; exact hb
local notation "Ψ"=> tabloidSky B J ξ H hi hl P (N:=N)
-- Stand take exports param Q (supports recalibration of E)
structure StockSky where
  commitment : Draft (tabloidSky B J ξ H hi hl (N:=N) P) (tell B i) (retime X) l
  exhibit : Plate (tabloidSky B J ξ H hi hl P (N:=N)) (retime X) l
  heated : 0<l
  lives : 0<fiery G (retime X) (St).patch.L
  loadng : ∀ V, 0<(Ψ).loading (retime X) V
  paid (Q : Rep G (C.side i p)) (hp : Q.p=(tabloidSky B J ξ H hi hl P (N:=N)).bp) (hs : 25*radiusB (retime X)+30 ≤ Q.p.B) :
    let p' := fun j=> shiftZ (Orchard.canopy St) hp.symm (sprouting commitment exhibit (Orchard.canopy St) j)
    Veins (white P) Q p' (L:=foliage commitment) commitment.enrolled hs hP.pets.status
         (load ξ.era) (acres ξ X y) (Line ξ.era ξ.goal 0 s) (sailboat s (k-(i+1))) ∧
     BodyGrant t P (foliage commitment) ((tabloidSky B J ξ H hi hl P (N:=N)).chi.profiles G St (retime X) l heated lives) J Q.p.threshold p' (fun V=> (((tabloidSky B J ξ H hi hl P (N:=N)).loading (retime X) V:ℝ):ℂ))
include M O Z hN in
lemma liftedSky (hb: 0≤ ξ.band) : Nonempty (StockSky B J ξ H hi hl hP):= by
  have hL:=(sizes_atSky ξ O hl hi p)
  have hp : Seeks (neutral (Ψ)) (tell B i) r X:= fitPostSky B M J ξ H Z O hN hi hl hP.warm
  obtain ⟨z,hx,he,hZ⟩:=elongationSky (p:=p) B J ξ Z O hi hl
  obtain ⟨H,M,he,h,hv,hQ⟩:=hx.prescribes he (O.court i hl hi.le) (St) (Ψ) (k-(i+1)) (le_trans (Nat.sub_le_sub_left (Nat.le_succ _) k) hZ) _ _ _ _ hP.pets rfl rfl hp
  refine ⟨H,M,he,h,hv,fun Q he hs=>?_⟩
  intro p'; refine ⟨?_,(hQ Q he hs).2⟩
  rw [show acres ξ X y=_ from congr_arg (acres ξ X) (calendar_warm ..)]; exact (hQ Q he hs).1
-- align Q record at unchanged temperature, allow new vacuum.E nucleus
structure NucleatedSky (Q : Rep G (C.side i p)) (A : StockSky B J ξ H hi hl hP) : Prop where
  beta : Q.beta=P.beta
  params : Q.p=(tabloidSky B J ξ H hi hl P (N:=N)).bp
  tree : Q.path=(C.path.rep N p i).path
  clip : Q.clip=(C.path.levels.params i).clip
  hm : Q.path.Bounds Q.clip (Ω).width (Ω).paths (C.path.levels.clock.loopCap i)
  hk x b' : Nonempty (Q.activities.Moves x b')
  pets : Petals Q (rollup s (k-i))
  funds : ∀ hS : 25*radiusB (retime X)+30 ≤ Q.p.B,
    let p' := fun j=> shiftZ (Orchard.canopy St) params.symm (sprouting A.commitment A.exhibit (Orchard.canopy St) j)
    let E:Empty→ Rim Q.p.threshold G (C.side i p):=Empty.elim
    Resin (white P) Q p' (L:=foliage A.commitment) A.commitment.enrolled hS hP.pets.status ((tabloidSky B J ξ H hi hl P (N:=N)).loading (retime X)) E (load ξ.era) (kinetics s)
include Z O hN M
lemma furySky (A : StockSky B J ξ H hi hl hP) (hb:0≤ ξ.band): ∃ Q, NucleatedSky B J ξ H hi hl hP Q A:= by
  obtain ⟨Y,-,T,W,Q,hU,h⟩:= Paint.parser C (hi.le.trans hN) M (H.oldPrices i hi.le hl) p
  have hc := hU.precise.2.1.trans ((M.wilson.represents N p i (hi.le.trans hN)).clip)
  have hD := hU.precise.1; let v:= Ψ; have hp : Y.p=v.bp:= hU.precise.2.2.2.2.1
  let G₀: Rep G (C.side i p):={Y with beta:=P.beta}
  obtain ⟨c,hx⟩:= scalar_baseSky (retime X) v G₀ hp.symm rfl hc hD A.loadng
  let F: Rep G (C.side i p):= {G₀ with v:=c}
  have hF : F.path.Bounds F.clip (Ω).width (Ω).paths (C.path.levels.clock.loopCap i):= T.paths
  let z:= fun j=> shiftZ (Orchard.canopy St) hp.symm (sprouting A.commitment A.exhibit (Orchard.canopy St) j)
  let L:= foliage A.commitment
  have h':F.p.B=walls X:= hp ▸ rfl
  obtain ⟨h₁,h₂⟩:= coast_leaseSky B J ξ H hi hl hP.warm O F hp
  obtain ⟨α,-,hX',hB⟩:= elongationSky (p:=p) B J ξ Z O hi hl
  have h'': Lease (St).patch.L (white P).p F.p (load ξ.era) (acres ξ X y) (Line ξ.era ξ.goal 0 s) (sailboat s (k-(i+1))) (kinetics s) (gas ξ.era.coast y):=by
    exact hX'.books (k-(i+1)) X y _ _ (le_trans (Nat.sub_le_sub_left (Nat.le_succ _) k) hB) (O.court _ hl hi.le) (O.court _ (hl.trans (Nat.le_succ i)) hi) h' h₂
  let N':= pyro (L:=L) (white P) F z A.commitment.enrolled h₁ hP.pets.status hF
  have ht:= (A.paid F hp h₁).1
  have hF':0 < P.beta:= bush_posSky B J ξ O (P:=white P) hP.warm
  have hβ : P.beta ≤4*X:= by
    have hr : P.beta ≤2*y:= (bush_pricesSky B J ξ O hP.warm).2; have hz:=O.court i hl hi.le
    linarith only [hr,hz.1, (O.court _ (hl.trans (Nat.le_succ i)) hi).2]
  obtain ⟨hY,hX⟩:= (Z.rate i hl hi.le).prices Λ i (O.court _ hl hi.le) P.beta hF' hβ Y.p h' (hp ▸ rfl) (hp ▸ rfl)
  change boxesCost Y.p P.beta (Ω).paths _ ≤ spray s at hY; change _≤ (Ω).width at hX
  obtain ⟨hZ,hm,hχ⟩:= pyro_gen (L:=L) (white P) F z A.commitment.enrolled h₁ hP.pets.status ht h'' hF hX T.labels.moves
  refine ⟨N', rfl,hp,hD,hc,hF,hm, thin N' hZ _ ?_,fun hs=>?_⟩
  · rw [show k-i=k-(i+1)+1 by omega];exact (add_le_add_left hY _).trans (hX'.accept _)
  intro p' E; refine ⟨fun V=>?_, ⟨(fun i=>i.elim),(fun i=> i.elim),(fun i=>i.elim),fun i=>?_⟩,fun i j=>?_⟩
  · rw [Fintype.prod_empty,mul_one]; refine Eq.trans ?_ (hχ V); change v.loading (retime X) V * _=_; rw [hx V]; rfl
  · unfold Flux.strike; rw [show (Finset.univ : Finset Empty)=∅ by rfl,filter_empty,sum_empty]; exact (Real.exp_pos _).le
  exact ⟨Equiv.refl Empty,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim⟩
end lift
end YM.PhysicalNext.InteractingRank.Soft
