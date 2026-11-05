import YM.UVExtension.Lacing.Reprise
/-! # analytic operator grammar. quantitative per entry, α absorption
 vintage real cases derive.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing.RoutesF
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet InputColumn Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge} {n n':Side} {d :ℕ} {F:Frame G d} {H: Hol G} {p P : BudgetPoint} {ι:Type}
variable (L:RoutesF F n n' p P H)
local notation "Bc" => Cow G n' p d H
local notation "Lc" => Bucket F P H n
set_option quotPrecheck false
local notation "tc"=>turnCost P.order P.power

structure Counts (M:RoutesF F n n' p P H) (u:ℝ) : Prop where
   calm : 0≤u
   glass i v: orbitCost F * F.coeffSize (M.glass i v).1 ≤ u*‖v‖ ∧ turnCost P.order P.power* ‖(M.glass i v).2.1‖ ≤ u*‖v‖ ∧ ‖(M.glass i v).2.2‖ ≤ u*‖v‖
   wing i v: orbitCost F * F.coeffSize (M.wing i v).1 ≤ u*‖v‖ ∧ turnCost P.order P.power *‖(M.wing i v).2.1‖ ≤ u*‖v‖ ∧ ‖(M.wing i v).2.2‖ ≤ u*‖v‖
structure Tips (M:RoutesF F n n' p P H) (r:Side)(T:Heading F)(u v:ℝ): Prop where
    counts: Counts M u
    wing : 0≤ v
    hush: M.vane none=0
    speed i:
       let x:=Size.axis F i; let w:=v*F.coeffSize (vowel F r (F.core x)); let P':= M.vane (some i)
       orbitCost F*F.coeffSize (P'.1-T.leads r x) ≤ u * F.coeffSize (F.core x) ∧ turnCost P.order P.power* ‖P'.2.1‖ ≤ w ∧ ‖P'.2.2‖ ≤ w
-- Estimates before audition. 

def roof (v:Bc): Listing → Lc:= consist 0 (fun j=> L.glass (key n' j) (v.1 (key n' j))) (extend L.route (fun j=> L.wing j (v.2 j)) 0)

def asset (v:Bc) : Listing→ ℝ := consist 0 (fun i=> ‖v.1 (key n' i)‖) (extend L.route (fun j=> ‖v.2 j‖) 0)

lemma shelter (v:Bc): HasSum (asset L v) (‖v.1‖+ ‖v.2‖):=by
   let f:=extend L.route (fun j=>‖v.2 j‖) (0:ℕ→ℝ); have ht : HasSum f ‖v.2‖:=by
      refine (L.route.injective.hasSum_iff (f:=f) ?_).mp ?_
      · intro i hi; exact extend_apply' _ (0:ℕ→ℝ) _ hi
      exact (castL v.2).congr_fun (fun i=> (L.route.injective.extend_apply (fun j=>‖v.2 j‖) 0 i))
   refine Eq.mp ?_ (added (f:=asset L v) (((key n').hasSum_iff (f:=fun i=>‖v.1 i‖)).2 (castL v.1)) ht)
   rw [show asset L v (.inl ())=0 from rfl,zero_add]

variable {u a c:ℝ} {L}
namespace Counts
variable (h: Counts L u) (v:Cow G n' p d H)
include h
lemma debit (w: Listing): let X:= rooms n F H P (aisleN (code _) w) (roof L v w); orbitCost F* F.coeffSize X.1 ≤ u*asset L v w ∧ tc *‖X.2.1‖ ≤ u*asset L v w ∧ ‖X.2.2‖ ≤ u*asset L v w := by
   intro X; have hh :∀ (w: Listing), let X:= roof L v w; let r:=u * asset L v w; orbitCost F * F.coeffSize X.1 ≤ r ∧ tc * ‖X.2.1‖≤r∧ ‖X.2.2‖ ≤ r:=by
      intro w; rcases w with (_|i|i)
      · change orbitCost F*F.coeffSize 0 ≤u*0∧ tc*‖(0:Roc d H n P)‖ ≤u*0 ∧ ‖(0:Coil G n P)‖ ≤u*0; simp [Frame.coeffSize]
      · exact h.glass ..
      by_cases hi:i∈ Set.range L.route
      · obtain ⟨j,rfl⟩:= hi; dsimp only [roof,consist,asset,Sum.elim]; rw [L.route.injective.extend_apply,L.route.injective.extend_apply]; exact h.wing j _
      dsimp only [roof,consist,asset,Sum.elim]; rw [extend_apply' _ _ _ hi,extend_apply' _ _ _ hi]; simp [Frame.coeffSize]
   exact ⟨(hh w).1, le_trans (mul_le_mul_of_nonneg_left (duck d H P (aisleN (code _) w) _) (by unfold turnCost; positivity)) (hh w).2.1,(hh w).2.2⟩

end Counts
end YM.UVExtension.Lacing.RoutesF
