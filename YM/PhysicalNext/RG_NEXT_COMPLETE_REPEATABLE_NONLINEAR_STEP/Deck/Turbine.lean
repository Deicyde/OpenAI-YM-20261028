import YM.MultiNext.VACUUM_STABILITY.Localized.Deriv
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Primer
/-!
 # discrete marginals. Applies on tag arrays including uneven volumes.
 Rig.member: same pc columns even if there are unused assignments. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter  Shingle 
open Poll Pond MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} 
variable {E J I S : Type}
section ray
structure Matchup (f : E→J) where
  put : E→J→E
  put_get x y : f (put x y)=y
  birth x : put x (f x)=x
  back x y z : put (put x y) z=put x z
namespace Matchup
variable {f : E→J} {g:I→S} (K:Matchup f)
include K
def times (Z:Matchup g) : Matchup (Prod.map f g) where
  put x y:=(K.put x.1 y.1,Z.put x.2 y.2)
  put_get _x _y:=Prod.ext (K.put_get _ _) (Z.put_get _ _)
  birth _x:=Prod.ext (K.birth _) (Z.birth _)
  back _x _y _z:=Prod.ext (K.back ..) (Z.back ..)
def expands (i : I→ S) (he:Injective i): Matchup (fun y:S→E=> f ∘ y ∘ i) where
  put x y:= Function.extend i (fun j=> K.put (x (i j)) (y j)) x
  put_get x y:= funext fun j=> by dsimp only [Function.comp]; rw [he.extend_apply,K.put_get]
  birth x:=funext fun j=>by
    by_cases h:j∈ Set.range i
    · obtain ⟨j,rfl⟩:=h; rw [he.extend_apply]; exact K.birth _
    exact extend_apply' _ _ _ h
  back x y z:=funext fun j=>by
    by_cases h:j∈Set.range i
    · obtain ⟨j,rfl⟩:=h; rw [he.extend_apply,he.extend_apply,he.extend_apply,K.back]
    rw [extend_apply' _ _ _ h,extend_apply' _ _ _ h, extend_apply' _ _ _ h] -- rw occurrence
lemma folded [Fintype E] [Nonempty E] : ∃ m, 0 < m ∧ Fold f m:= by
  let x:= Classical.arbitrary E; let n:= (parcel f (f x)).card; have he j: (parcel f j).card=n:= by
    let v:=K.put; let Y:= parcel f j; let Z:= parcel f (f x)
    apply Finset.card_bij (fun a (_:a∈Y) => v a (f x)) (fun a ha=> (Shingle.posted ..).2 (K.put_get ..)) ?_ ?_
    · intro a ha b hb h; apply_fun (fun t=> K.put t j) at h; dsimp only [v] at h; rw [K.back,K.back,show K.put a j=a from ((Shingle.posted ..).mp ha) ▸ K.birth a, show K.put b j=b from ((Shingle.posted ..).mp hb) ▸ K.birth b] at h; exact h
    intro a ha; exact ⟨v a j, (Shingle.posted ..).2 (K.put_get ..),(K.back ..).trans (((Shingle.posted ..).mp ha) ▸ K.birth a)⟩
  exact ⟨n,Finset.card_pos.mpr ⟨x,by simp⟩,he⟩
lemma cashout [Fintype E] [Nonempty E] [Fintype J] (g:J→ ℝ) : Pond.likely (g ∘ f)= Pond.likely g:= by
  letI: Nonempty J:=⟨f (Classical.arbitrary _)⟩; obtain ⟨m,hm,h⟩:= K.folded; unfold likely; dsimp only [Function.comp_apply]; rw [multiplied f h g,nsmul_eq_mul,received f h]; push_cast; field_simp
end Matchup
def reads (E:Type):Matchup (id:E→E):=⟨fun _ x=>x,fun _ _=>rfl,fun _=>rfl,fun _ _ _=>rfl⟩
end ray

-- picker in Near. use for choices and Forest replication.
variable (hC : C.val=c.val*M) (x : Site C)
local notation "p" => Macrame.splitter (Deck.divides hC)
def reverts := Deck.rise (Deck.divides hC) x
lemma reverted (y: Site c) : p (reverts hC x y)=y:= Deck.dawns ..
lemma irrevocable : Injective (reverts hC x):= LeftInverse.injective (reverted hC x)
lemma same_site (W : Support C) {m:ℕ} (hm:2*m < c.val) (he: W⊆neighbors m x) (y:Site C) (hy:y∈W): reverts hC x (p y)=y:= Deck.boost _ _ _ (lt_of_le_of_lt (Nat.mul_le_mul_left 2 ((neighbors_mem ..).1 (he hy))) hm)
end YM.PhysicalNext.Repeat.Deck
