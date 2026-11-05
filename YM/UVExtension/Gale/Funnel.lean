import YM.UVExtension.Gale.Reef
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{s:Levels G}{n N r k:ℕ}
variable (L:∀ i:ℕ,ℂ→ Lacing.Banner s F A n i)
local notation "O'"=> s.clock
local notation "D"=> F.Coeff
local notation "H"=> Lacing.Card s F A n
local notation "X₀"=> s.params
local notation "l'"=> s.S.block
local notation "κ"=> s.clock.forcedAllowance
local notation "S"=> s.S
local notation "g₀"=> fun i=> Lacing.glaring s i n
variable (i N:ℕ)
variable (U:ℂ→ Card s F A n N)
local notation "U₀"=>fire L N U
noncomputable def tether (r i:ℕ)(h:r ≤ i)(z:ℂ): F.Coeff≃ₗ[ℂ]F.Coeff:= Nat.leRecOn (C:=fun _=> F.Coeff ≃ₗ[ℂ] F.Coeff) h (fun {j} t=> t.trans (turn L N U j z).symm) (LinearEquiv.refl _ _)
lemma flipI (r:ℕ) (z:ℂ): tether L N U r r le_rfl z= LinearEquiv.refl _ _:=by unfold tether; rw [Nat.leRecOn_self]
lemma mirror (r i:ℕ)(hi:r ≤ i)(z:ℂ): tether L N U r (i+1) (hi.trans i.le_succ) z = (tether L N U r i hi z).trans (turn L N U i z).symm:=by unfold tether; rw [Nat.leRecOn_succ hi]
abbrev CaseA (s:Levels G)(F:Labels.Frame G d)(A:Hol G)(n i:ℕ):= Bucket F (s.budget i) A (s.S.side i n)
local notation "t#"=> s.params
local notation "Ω"=> F.Index
noncomputable def cuff (j:ℕ) (z:ℂ)(i:F.Index) : CaseA s F A n j:= spool F A ((S).side j n) (s.budget j) (U₀ j z) (Size.axis F i,0)
-- state = (photo Q, local horizontal payer)
local notation "Υ"=> CaseA s F A n
noncomputable def raftS (i:ℕ)(z:ℂ)(X : (Υ (i+1)) × F.Coeff) : (Υ i) × F.Coeff:=
    let v:= L i z|>.rain X.1.2 none
    (spool F A ((S).side i n) (s.budget i) (fire L N U i z) v, turn L N U i z X.2 + v.1)
noncomputable def shuttle (k:ℕ)(z:ℂ)(x:F.Index)(i:ℕ)(h:i ≤ k): (CaseA s F A n i)×D:= Nat.decreasingInduction (motive:=fun i _=> Υ i × F.Coeff) (fun i _=> raftS L N U i z) (cuff L N U k z x,Size.axis F x) h
lemma shuttles(k:ℕ)(z:ℂ)(x:F.Index): shuttle L N U k z x k le_rfl=(cuff L N U k z x,Size.axis F x):=by simp [shuttle]
lemma wheels (x:F.Index)(k i:ℕ)(hk:i< k) (z:ℂ): shuttle L N U k z x i hk.le= raftS L N U i z (shuttle L N U k z x (i+1) hk):=by unfold shuttle; exact Nat.decreasingInduction_succ_left ..
variable (v c q w:ℕ→ℝ){a:ℝ}
local notation "Z"=> ball (0:ℂ) a
structure Booked (R:Rotor s F A n N r a L v c q w): Prop where
    dims : ∀ z:ℂ,z∈ Metric.ball 0 a→Length F (U z) (w N)
    hulls : ∀ x,DifferentiableOn ℂ (fun z=> U z x) (ball (0:ℂ) a)
variable {L N U v c q w}
variable (R:Rotor s F A n N r a L v c q w) (P:Booked L N U v c q w R) -- N arg inspect
local notation "Φ"=> fire L N U
include P
set_option synthInstance.maxHeartbeats 80000
lemma helix (i:ℕ)(h0:r≤ i)(hi:i≤ N)(x:ℂ→ F.Coeff)(hx:DifferentiableOn ℂ x (ball 0 a)): DifferentiableOn ℂ (fun z=> tether L N U r i h0 z (x z)) Z:=by
   induction h0 with
   | refl=> simp_rw [flipI]; exact hx
   | step h IH=> rename_i k; simp_rw [mirror _ _ _ _ _ h]; exact (arcs U R P.dims P.hulls k h hi _ (IH ((Nat.le_succ ..).trans hi))).2
lemma spiral (i:ℕ)(h0:r≤ i)(hi:i≤ N)(x:ℂ→ F.Coeff)(hx:DifferentiableOn ℂ x (ball 0 a)): DifferentiableOn ℂ (fun z=> (tether L N U r i h0 z).symm (x z)) Z:=by
    let M(z):=(tether L N U r i h0 z).toLinearMap.toContinuousLinearMap; have hg: DifferentiableOn ℂ M Z:= curtains _ (fun y=> helix R P i h0 hi (fun _=>y) (differentiableOn_const _)); have hV z: Bijective (M z):=(tether L N U r i h0 z).bijective
    apply (keel M Metric.isOpen_ball hg (fun i _=> hV i) x hx).congr; intro z hz; rw [show steers (M z)= tether L N U r i h0 z from ?_]; exact LinearEquiv.ext (fun i=> steers_eq _ (hV z) i)
lemma iris (i:ℕ)(he:r ≤ i)(hp:i≤N)(Y:ℂ→ CaseA s F A n i)(hY:DifferentiableOn ℂ Y (ball 0 a)): DifferentiableOn ℂ (fun z=> spool F A ((S).side i n) (s.budget i) (Φ i z) (Y z)) Z:=by
    have hx:DifferentiableOn ℂ (fun z=> (- (Y z).1, fire L N U i z (-(Y z).1))) Z:= DifferentiableOn.prodMk (hY.fst.neg) ((framed U R P.dims P.hulls i he hp).2 _ (hY.fst.neg)); unfold spool; apply DifferentiableOn.fun_sum; intro x _; apply (rooms ((S).side i n) F A (s.budget i) (aisleN (code Bool) x)).differentiable.comp_differentiableOn; cases x; exact hx; exact hY -- op composition
lemma pumps (k i:ℕ)(hk:i ≤ k)(hi:r ≤ i)(hN:k ≤ N)(x:F.Index): DifferentiableOn ℂ (fun z=> shuttle L N U k z x i hk) Z:=by
    induction hk using Nat.decreasingInduction with
    | self=> simp_rw [shuttles]; exact (iris R P k hi hN _ (differentiableOn_const _)|>.prodMk (differentiableOn_const _)) -- choose y
    | of_succ i he IH=>
      have hh:= hi.trans i.le_succ; let V z:= shuttle L N U k z x (i+1) he; have hV : DifferentiableOn ℂ V Z:= IH hh; let f(z):= L i z|>.rain ((V z).1.2) none
      have hg := he.trans_le hN
      obtain ⟨T,hT,hS⟩:=R.busy i hi hg
      have hf:DifferentiableOn ℂ f Z:=raft R.opens (R.wheels i hi hg) (fun i hi=> (hT i hi).counts) _ hV.fst.snd _
      simp_rw [wheels L N U x k i he]; exact (iris R P i hi hg.le f hf).prodMk (((arcs U R P.dims P.hulls i hi hg _ hV.snd).1).add hf.fst)
end YM.UVExtension.Gale
