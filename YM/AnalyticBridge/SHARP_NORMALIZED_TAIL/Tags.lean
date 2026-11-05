import YM.SectorNext.VACUUM_NORMALIZATION.Relative

/-!
# No volume loss from irrelevant k's

Likelihoods and flags will remain in the actual integrand. This is just the
localization in its tag **reference** measure. We group one frame tag with
the positive-address bonds at the same physical site. This is sufficient for
the compression identity (can include both endpoints, full halo, every
fallback decision site etc in `X` in applications).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Tags
open Filter Function Lattice RG Wilson Pressure Tree MeasureTheory Finset
open Push.SectorMeasure
open scoped Topology BigOperators Classical YM.Push.SectorMeasure

section table
variable {J I X N R : Type*} [Fintype I] [Fintype X] [Fintype J] [Fintype N] [Fintype R]
  [Nonempty X] [DecidableEq I]

def average (g : X → ℝ) := (Fintype.card X:ℝ)⁻¹ * ∑ i,g i

lemma pos : 0 < (Fintype.card X:ℝ) := by exact_mod_cast Fintype.card_pos
lemma same (r : ℝ) : average (fun _ : X => r) = r := by simp [average,(pos (X:=X)).ne']


lemma average_comp (f : N ≃ X) (g : X → ℝ) :
    average (g ∘ f) = average g := by
  unfold average; rw [Fintype.card_congr f,show ∑ i,(g ∘ f) i = _ from Equiv.sum_comp f g]

private lemma squares {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (u : A → ℝ) (v : B → ℝ) : average (fun y : A×B => u y.1*v y.2) = average u*average v := by
  unfold average; simp_rw [Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp; ring

private def Uses (V : Set I) (g : (I → X) → ℝ) := ∀ r s : I → X, Set.EqOn r s V → g r=g s
private lemma splits (V : Set I) (g h : (I → X) → ℝ) (hv : Uses V g) (hb : Uses Vᶜ h) :
    average (g*h)=average g*average h := by
  let E := Equiv.piEquivPiSubtypeProd (fun x => x∈V) (fun _ => X)
  let a := fun x => g (E.symm (x,Classical.ofNonempty))
  let b := fun y => h (E.symm (Classical.ofNonempty,y))
  let T := (Subtype (fun x => x∈V) → X) × (Subtype (fun x => x∉V) → X)
  have hg x (y : Subtype (fun x => x∉V) → X) : g (E.symm (x,y))=a x := hv _ _ (fun i hi => by
    simp [E,hi,Equiv.piEquivPiSubtypeProd_symm_apply])
  have hh (x : Subtype (fun x => x∈V) → X) y : h (E.symm (x,y))=b y := hb _ _ (fun i hi => by
    change i∉V at hi; simp [E,hi,Equiv.piEquivPiSubtypeProd_symm_apply])
  rw [← average_comp E.symm, ← average_comp E.symm g,← average_comp E.symm h,
    show ((g*h) ∘ E.symm) = fun (x : T) => a x.1*b x.2 from funext fun x => by
      obtain ⟨x,y⟩:=x; rw [Function.comp_apply,Pi.mul_apply,hg,hh],
    show g ∘ E.symm = fun x => a x.1*(1:ℝ) from funext fun x => by rw [mul_one]; exact hg _ _,
    show h ∘ E.symm = fun x => (1:ℝ)* b x.2 from funext fun x => by rw [one_mul]; exact hh _ _,
    squares a b,squares a (fun _ => 1),squares (fun _ => 1) b,same,same,one_mul,mul_one]

private lemma once (A : Finset N) (V : N → Set I) (g : N → (I → X) → ℝ)
    (h : ∀ i∈A, Uses (V i) (g i)) (hh : (A : Set N).PairwiseDisjoint V) :
    average (fun a => ∏ i∈A,g i a) = ∏ i∈A,average (g i) := by
  induction A using Finset.induction_on with
  | empty => simp [same (X:=I→X)]
  | @insert i A hi ih =>
    have h' (j : N) (hx : j∈A) := h j (mem_insert_of_mem hx)
    have he : Uses (V i)ᶜ (fun a => ∏ i∈A,g i a) := by
      intro k l hf
      refine prod_congr rfl fun j hj => h' j hj k l (hf.mono ?_)
      intro x hx hh'
      exact Set.disjoint_left.mp (hh (mem_insert_of_mem hj) (mem_insert_self ..)
        (ne_of_mem_of_not_mem hj hi)) hx hh'
    have hM : ((A:Set N)).PairwiseDisjoint V := by
      intro a ha b hb hab; exact hh (mem_insert_of_mem ha) (mem_insert_of_mem hb) hab
    simp_rw [prod_insert hi]; exact (splits _ _ _ (h i (mem_insert_self ..)) he).trans
      (congr_arg (average (g i) * ·) (ih h' hM))
end table

section physical
variable {c f : Side} {S : StepData c f}
def Synchronized (X : Support c) (k l : S.Choices) :=
    (∀ i ∈ X,k.1 i=l.1 i) ∧ ∀ (e : Edge (Site c)),
      e.1 ∈ X → e.1+Lattice.step e.2 ∈ X → k.2 e=l.2 e

private def group (S : StepData c f) : (Site c → S.patch.FrameTag × (Axis→ S.patch.Points)) ≃ S.Choices where
  toFun k := (fun i => (k i).1, fun e => (k e.1).2 e.2)
  invFun k := fun i => (k.1 i,fun b => k.2 (i,b))
  left_inv _ := rfl
  right_inv _ := rfl

variable {G : Gauge}
lemma populated (hm : S.patch.Branches S.kernel G) : Nonempty S.Choices := by
  obtain ⟨t,_⟩ := exists_alive hm (1:Config G f); exact ⟨t⟩

/-- Uniform (not likelihood-weighted) identity. Never replace by iid outcomes
in a function of `prediction`. Use on reads depending on the indicated sets of
tags ONLY, after marginalizing Y and Z. `X` includes e.g. negative reads in
protector lists whenever they affect these values. -/
theorem uses {R : Type} [Fintype R] (hm : S.patch.Branches S.kernel G)
    (X : R → Support c) (g : R → S.Choices → ℝ)
    (h : ∀ i k l, Synchronized (X i) k l → g i k=g i l)
    (hx : Pairwise (fun i j => Disjoint (X i) (X j))) :
    average (fun k => ∏ i,g i k) = ∏ i,average (g i) := by
  obtain ⟨u⟩ := populated hm
  let T := S.patch.FrameTag × (Axis → S.patch.Points)
  let E := group S
  letI : Nonempty T := ⟨E.symm u 0⟩
  rw [← average_comp E (fun k => ∏ i,g i k)]
  simp_rw [← average_comp E (g _)]
  apply once Finset.univ (fun i : R => (X i : Set (Site c))) (fun i a => g i (E a))
  · intro i _ k l hz
    refine h _ _ _ ⟨fun j hj => congr_arg Prod.fst (hz hj),fun e ht _ => ?_⟩
    exact congr_arg (fun x : T => x.2 e.2) (hz ht)
  intro i _ j _ he; exact Finset.disjoint_coe.mpr (hx he)

lemma vacuum (g : S.Choices → ℝ) : average g = ∑ k,SectorNext.Vacuum.tagRef k*g k := by
  unfold average SectorNext.Vacuum.tagRef; rw [Finset.mul_sum]
end physical
end YM.AnalyticBridge.Sharp.Tags
