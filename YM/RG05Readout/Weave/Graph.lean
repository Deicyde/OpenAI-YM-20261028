import YM.RG05Readout.Weave.Ice
/-!
# Physical addressed graph on all centers and intervals

Simultaneous linear output reps on the same path. Confirms real inverse on each
admitted tail with actual label stencils. Weighted graph estimate itself on true
`V` representatives at this germ projection. Not yet our data for analytic
models, which await reclosure and their own prices. Costs may be ample.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical Offsets OPE Copper
open Push Local MergeProof
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}
variable (p m N d:ℕ)
-- step uses THIS vertex set
set_option quotPrecheck false
local notation "Φ"=> C.path
local notation "M"=> C.path.rep N p
abbrev billStart (C:Family G)(p m N:ℕ):= ∀ i:Address.Bud C p m,(C.path.rep N p (m+1)).activities.Moves (1: Signed) (child C p m i)
abbrev Rail (C:Family G):=∀ N p m,m<N→ GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)
noncomputable def keys0 {N p m:ℕ}(h:C.Makes)(hm:m<N):billStart C p m N:= fun i=> Classical.choice ((h.wilson.represents N p (m+1) hm).good.labels.moves 1 (child C p m i))
abbrev Sight (C:Family G)(d p:ℕ):=∀ m:ℕ,Palette C d→ₗ[ℂ]Tape G (C.side m p)
abbrev Emblems (C:Family G)(d:ℕ):=ℕ→(Palette C d≃ₗ[ℂ] Palette C d)

variable {p m N d} (D: Rail C)(B:ℕ→ℕ→ℝ) (h:C.Makes)
structure Awake (b:ℕ) (d:ℕ):Prop where
   post i:i ≤ d → C.ref i ≤ b
   cash i:b ≤ i → (C.path.levels.params i).columns ≤ B d i
   toll p i N (_:b ≤ i)(hi:i<N):SignedPrice C i p d N (D N p i hi) (B d (i+1)) (B d i)
-- Spine predicate. implicit B checked. Recommend match creation proof downstream. Support E input.
structure Spine (b p d N:ℕ) (V:Sight C d p)(r:Emblems C d):Prop where
    starts : V N=basisTop C d N p
    legal m : b ≤ m → m ≤ N → Group C N m p d (V m) (B d m)
    follows m : b ≤ m→ ∀ hM:m<N,Wager (D:=D N p m hM) (u:=keys0 (p:=p) h hM) (V (m+1)) (V m) (r m)

section assembler
variable {B D}
include h
lemma erect {b:ℕ} (hw:Awake D B b d)(hl:b≤N) : ∃ (V:Sight C d p)(r:Emblems C d), Spine D B h b p d N V r :=by
   induction hl using Nat.decreasingInduction with
   | self=>
       let v:Sight C d p:=update (fun _=>0) N (basisTop C d N p)
       refine ⟨v,(fun _=>LinearEquiv.refl _ _),update_self ..,fun i hi hv=>?_,fun i hi he=> by omega⟩
       obtain rfl:i=N:= le_antisymm hv hi; unfold v; rw [update_self]; have hA:=basis_paid (d:=d) (p:=p) h hw.post
       exact ⟨fun i=> let ⟨v,hv⟩:=hA.capacity0 i; ⟨v,hv.grow (mul_le_mul_of_nonneg_right (hw.cash _ le_rfl) (size_ge _))⟩,hA.pos.trans (hw.cash i le_rfl)⟩
   | of_succ k hk ih=>
       obtain ⟨V,r,hS⟩:= ih (show Awake D B _ _ from ⟨fun i hi=>(hw.post i hi).trans k.le_succ, fun i hi=>hw.cash i (k.le_succ.trans hi),fun p i N hi=> hw.toll p i N (k.le_succ.trans hi)⟩)
       obtain ⟨W,z,hB,hT⟩:= lit_step (u:=keys0 h hk) h hk (hw.toll p k N le_rfl hk) (hS.legal (k+1) le_rfl hk)
       refine ⟨update V k W,update r k z,?_,?_,?_⟩
       · rw [update_of_ne hk.ne']; exact hS.starts
       · intro i hi he; by_cases hx:i=k; subst i; rw [update_self]; exact hB
         rw [update_of_ne hx]; exact hS.legal i (by omega) he
       intro i hi hN; rw [update_of_ne (show i+1≠ k by omega)]; by_cases hx:i=k; subst i; rw [update_self,update_self]; exact hT
       rw [update_of_ne hx,update_of_ne hx]; exact hS.follows i (by omega) hN
omit h in
lemma held (hp: UV.Lacquer C D):∃ B:ℕ→ℕ→ℝ,∀ d,∀ᶠ m in atTop,Awake D B m d:=by
    obtain ⟨B,hB,h⟩:=hp.currency; refine ⟨B,fun d=>?_⟩
    obtain ⟨t,ht⟩:= eventually_atTop.mp (h d)
    filter_upwards [eventually_ge_atTop t, ((eventually_all_finset (Finset.range (d+1))).mpr (fun i _=> eventually_ge_atTop (C.ref i)))
    ] with k hk H
    exact ⟨fun i hi=> H i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)),fun i _=> hB .., fun p i N h=> ht i (hk.trans h) p N⟩
end assembler
end YM.RG05Readout.Address
