import YM.OPE.Splitting.Needle

/-!
# Shared prescription over all horizons
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prescription
open Function Table Finset
open scoped Topology BigOperators Classical ContDiff
variable {G: Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}{m n : ℕ}
variable {U V W : Prescription P} (h:S.Symmetric)(hp:P.Inclusions S)
lemma shrink (h:Extends m U V)(he:n ≤ m): Extends n U V := by
    have hp i (hi:i∈ bands P n):i∈ bands P m:= (full_bands ..).2 (((full_bands ..).1 hi).trans he); exact ⟨fun i hi=>h.needle i (hp i hi),fun i hi=>h.sheet i (hp i hi)⟩
lemma Extends.symmetric (h: Extends n U V) : Extends n V U := ⟨fun i hi=> (h.needle i hi).symm, fun i hi=> (h.sheet i hi).symm⟩
lemma Extends.travels (h:Extends n U V)(hp:Extends n V W): Extends n U W :=⟨fun i hi=> (h.needle i hi).trans (hp.needle i hi),fun i hi=>(h.sheet i hi).trans (hp.sheet i hi)⟩
include h hp
private abbrev Trail (P:DiffPlan S)(n:ℕ):= {x:Prescription P//SignedOff n x}
private lemma staircase (n) (x:Trail P n):∃ y:Trail P (n+1),Extends n x.val y.val:=by obtain ⟨v,hv,hs⟩:= nextRows h hp _ x.property; exact ⟨⟨v,hs⟩,hv⟩
theorem chosen : ∃ V: Prescription P, Coherent V:=by
    obtain ⟨x,hx⟩:= startRows h hp
    let u: (n:ℕ) → Trail P n := fun n=> Nat.rec (motive:=fun n=> Trail P n) ⟨x,hx⟩ (fun i v=> (staircase h hp i v).choose) n
    have hv i : Extends i (u i).val (u (i+1)).val:=(staircase h hp i (u i)).choose_spec
    have he (i j:ℕ)(hi:i ≤ j): Extends i (u i).val (u j).val:=by
       induction hi with
       | refl=> exact ⟨fun i _=> rfl,fun i _=> rfl⟩
       | step hi ih=> exact ih.travels (shrink (hv _) hi)
    let L:Prescription P := ⟨fun i=>(u i.fst).val.needle i,fun i=> (u i.fst).val.sheet i⟩
    refine ⟨L,fun i=>?_⟩; apply SignedOff.of_extends (u i).property; refine Extends.symmetric ⟨fun a ha=> ?_, fun a ha=>?_⟩
    exacts [(he a.fst i ((full_bands ..).1 ha)).needle _ ((full_bands ..).mpr le_rfl),
       (he a.fst i ((full_bands ..).1 ha)).sheet _ ((full_bands ..).mpr le_rfl)]
lemma highVan (hU:Coherent U) (x:Mode P)(he:n<x.fst) (a:S.Field n): U.test x n a=0:=by
    let f:=x.fst; let R:=P.rise he.le
    rw [← (hU n).rebuilds a,map_sum]
    refine sum_eq_zero fun i hi=> ?_; have hx:= (full_bands ..).1 hi; simp only [map_smul]; rw [← U.affinity h hp x _ he.le, ← U.load_next h hp i hi he.le, (hU f).bothWays x i ((full_bands ..).2 le_rfl) ((full_bands ..).2 (hx.trans he.le)), if_neg (show x≠i from fun ht=> by rw [← ht] at hx; omega), smul_zero]
omit h hp in
/-- Actual filtration basis equivalence at all horizons. -/
def asBasis (n:ℕ) (hU:Coherent U): S.Field n ≃ₗ[ℂ] ((↑(bands P n):Type)→ℂ) :=
    { LinearMap.pi (fun i:(↑(bands P n):Type)=> U.test i.val n) with
      invFun := fun f => ∑ i: (↑(bands P n):Type), f i • U.loaded i.val n
      left_inv := fun x=> by exact (sum_attach (bands P n) (fun i=> U.test i n x • U.loaded i n)).trans ((hU n).rebuilds x)
      right_inv := fun f=> funext fun i=> by
         change U.test (↑i) n (∑ j:(↑(bands P n):Type), f j • U.loaded j.val n)=_; simp only [map_sum,map_smul]; rw [sum_eq_single i]; simp [-cost,(hU n).bothWays i.val i.val i.property i.property]
         · intro j _ h; simp [-cost,(hU n).bothWays i.val j.val i.property j.property,show i.val ≠ j.val from Subtype.val_injective.ne h.symm]
         simp }
end YM.OPE.Prescription
