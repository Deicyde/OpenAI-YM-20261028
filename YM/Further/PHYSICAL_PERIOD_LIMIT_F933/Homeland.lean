import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Sectioning
import YM.Next.UV_STRESS.Union
import YM.Next.WARD_BIN.Spin
import YM.Next.WARD_BIN.Wallet
import YM.Progress.JOINT_CALENDAR.Branches
import YM.Push.RELAY_DIFFERENCE.Attaching

/-!
# Common Ward.Console orientation antecedents without Invoice.about outputs

Don't ask equality between each combined forced output name before operation
 (unnecessary and unlikely on the true dormant maps unless taking more
 preparation of `Pads`). Can use Wall aggregation invariance; designs not
 spending against publications with incompatible alphabets. On separate steps,
 orientations & active sets over the genuine unmarked labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Homeland
open Function Set Filter MeasureTheory Wilson Lattice RG Labels Source Push.Local WardBin WardBin.Gas
    WardBin.Wheels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {n : Side} {ι : Type*} {D : Activities G n} {s : Signed} {q : Site n}
section
variable (σ : D.Moves s q) (e : Equiv.Perm ι) (X : ι → Support n) (Y : ι → Support n)
    (h : ∀ i, Y (e i)=(X i).image (affine s q)) (S : Slots D X) (S' : Slots D Y)
include h



 -- f g infer?

variable {f g : ι → Config G n→ ℂ} {u : Bool}

include h -- δ real or complex rotation


omit σ h in
private lemma collected (t : ℝ) (j : Shape n) (U : Config G n) (f : ι → Config G n→ℂ) :
    bucket D (fun i => S.pack t f i U) j = ∑' i : Letters D X,if shape D (S.label i) = j then S.payload t i f U else 0 := by
  unfold bucket; let F :=fun i : ℕ=> if shape D i=j then S.pack t f i U else 0
  change tsum F=_
  have he : Function.support F ⊆ Set.range S.label := by
    intro x hx; by_contra h
    unfold Function.support at hx
    apply hx; dsimp only [F]; split
    · rw [Slots.pack_none S t f x h]; rfl
    rfl
  rw [← (S.label.injective.tsum_eq he)]; simp [F]

include σ

end

-- for rotation & star (setting s=1). capture output quality BEFORE building sigma bills. Use even when selecting echo estimators on combined cone.
section align
variable {d : ℕ} (F : Labels.Frame G d) (c : Bool) (s : Signed)
def emit (v : F.Coeff) : F.Coeff := turn c ∘ (F.act s.ortho v)
abbrev shoot (U : Config G n→ℂ) := turn c ∘ U ∘ pull s 0

variable (K : Activities G n) (i : Equiv.Perm ℕ)

def buckets (f g : ℕ → Config G n → ℂ) := ∀ (U : Config G n) (v : Shape n),
    bucket K (fun j=> g j U) (bay (aerial s 0) v)=turn c (bucket K (fun j=>f j (pull s 0 U)) v)

structure callback (f g : Push.Local.Raw F n) : Prop where
  initial : g.seed=emit F c s f.seed
  regular j : g.bulk (i j)= shoot c s (f.bulk j)
  old : buckets c s K f.forced g.forced
structure cardBound (f g : Baton F n) : Prop where
  initial : g.1=emit F c s f.1
  regular j : g.2.1 (i j)=shoot c s (f.2.1 j)
  old : buckets c s K f.2.2 g.2.2

variable {F} {σ : ℝ}











end align

section origins
open Sectioning
open Bid
variable {d N p : ℕ} {F : Labels.Frame G d} (u : Bool) (s : Signed) {C : History G} (S : SectionData F)
  {A : Hol G} (h : S.Sound A) (E : Sectioning.Ink C N p) (Z : Finset Cover)
  (he : Z.image s.act=Z) {w : ℝ}

include h he
-- Need G receipts only on H.rep N p N.


variable {l : ℕ} {H0 : History G} (D : Ink H0 N p) (P : Goods D S A l)
-- spin premat, can instantiate with any ℓ flow and stencils matching after expansion. Require κ.Q.Bundle bucket *not* any difference cost or spin/kernel identity
-- on junk records.
structure Earning (s : Signed) (u : Bool) (W : Worth) (w : ℕ→ℝ) : Prop where
  fees : RawBills D S A P w (W:=W)
  transforms : ∃ e : ℕ→Equiv.Perm ℕ, e N 0=0 ∧
    ∀ i, ∀ hl : l ≤ i, ∀ hi : i<N, (∀ j, D.raw i (e i j)=(D.raw i j).image (affine s 0)) ∧
    ∀ x y : Users D S A (i+1), cardBound F u s (H0.rep N p (i+1)).activities (e (i+1)) x.val y.val →
      callback F u s (H0.rep N p i).activities (e i) (P.yields i hl hi x) (P.yields i hl hi y)

omit h he in
private lemma home (m p : ℕ) : (H0.levels.clock.op m p).ratio.parent 0 = 0 := by
  let r := (H0.levels.clock.op m p).ratio; exact (show r.embed 0 = 0 from r.root.map_zero) ▸ r.embed_parent 0
variable (b : Worth) (W : ℕ→ℝ) (g : Earning S D P s u b W)

-- exact trace of recursion on eligible data, not making ANY assumptions on posterior projection outputs and all printed display costs
include b W g

end origins

-- can use signed-invariant Gallery.cover with identical bookings. Important **do this choice
-- BEFORE** requesting `Preowed`, replacing `foundationG` (specialize actual `plans`
-- to this choice, oe gifts prove accordingly; post β holds with Quay) if using `fronts` for spins.
namespace Canvas

lemma atlas (U : Finset Cover) : ∃ T : Finset Cover,U⊆T ∧ ∀ s : Signed,T.image s.act=T := by
  let T:= Finset.univ.biUnion fun s : Signed=> U.image s.act
  refine ⟨T,fun i hi=> Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, Finset.mem_image.mpr ⟨i,hi,Signed.act_one _⟩⟩,?_⟩
  have ha s (i:Cover) : i∈T → (s : Signed).act i∈T := by
    intro he
    obtain ⟨t,-,j⟩:=Finset.mem_biUnion.mp he
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp j
    rw [← Signed.act_mul]; exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,Finset.mem_image.mpr ⟨_,hk,rfl⟩⟩
  intro s
  ext i; constructor
  · intro h; obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp h; exact ha _ _ hk
  exact fun h=>Finset.mem_image.mpr ⟨s⁻¹.act i,ha _ _ h,by simp⟩
open Next.Foundations Sectioning Bid



variable {d N p l : ℕ} {A : Bay.Roads G} {H : History G} (P : Ink H N p) (B : Goods P (localSection G d) (hol G) l)
  (Z : Worth) (w : ℕ→ℝ) (hp : ∀ s u, Earning (localSection G d) P B s u Z w)

structure Payroll (i : ℕ→ℝ) : Prop where
  receipt : ∀ s u, Earning (localSection G d) P B s u Z i
  tack : P.raw N 0= footprint (A.art d).cover (0:Site (H.S.side N p))
  angle s : (A.art d).cover.image (s : Signed).act=(A.art d).cover
  shelf : Offsets.OffsetPrice (Bay.earlier A H d) (N:=N) (p:=p) (spot (Bay.dummy H) N p)
  active : H.Selected






end Canvas
end YM.Further.PhysicalPeriodLimitF933.Homeland
