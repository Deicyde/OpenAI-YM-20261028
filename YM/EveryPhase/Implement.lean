import YM.EveryPhase.Charge
import YM.EveryPhase.Polynomials

/-!
# `T` on the reconstructed systems, all phases
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table Spec
open Next.BOUNDARY.Descent
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {S U : Table C.book} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {F : Waves S} {H : S.RealSpin} {Q : Wightman S}

/-- Represent all classes, for expanding the RHS. Formula will hold whichever
of these representative sections is used. -/
def Modes (S : Table C.book) (p : S.Union → S.Tag) : Prop := ∀ x, S.pin (p x).1 (p x).2=x
lemma reps (P : DiffPlan S) (h : S.Symmetric) (hh : P.Inclusions S) : ∃ p, Modes S p := by
  choose p v hv using P.covered h hh
  exact ⟨fun x => ⟨p x,v x⟩,hv⟩

def involved (X : Set E4) (v : Sentence S) : Prop := ∀ t∈v, tsupport t.2 ⊆ X

def repertoire (X : Set E4) (v : SumOfWords S) : Prop := ∀ i∈v, involved X i.2

lemma localized (v : SumOfWords S) (h : finite v) : ∃ X, IsCompact X ∧ repertoire X v := by
  classical
  let p := v.flatMap (fun i => i.2)
  let F := p.toFinset
  have hp : ∀ x∈p, IsCompact (tsupport ⇑x.2) := by
    intro i hi; obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp hi; exact h _ hj _ he
  refine ⟨⋃ i∈F, tsupport i.2,(Finset.finite_toSet F).isCompact_biUnion (fun i hi => hp i (List.mem_toFinset.mp hi)),?_⟩
  intro i hi p hp
  exact subset_iUnion₂_of_subset p (show p ∈ F from List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨i,hi,hp⟩)) subset_rfl

/-- derivation rule on fields and composition (all pin, domain and operator choices fixed). -/
def wordAct (Q : Wightman S) (K : Killing) (R : S.Rotation) (p : S.Union → S.Tag) : Sentence S → Q.operators.domain →ₗ[ℂ] Q.operators.domain
  | [] => 0
  | x::xs => (action Q K R (p x.1) x.2).comp (monomial Q.operators xs) +
      (Q.operators.field x.1 x.2).comp (wordAct Q K R p xs)
def sumAct (Q : Wightman S) (K : Killing) (R : S.Rotation) (p : S.Union → S.Tag) : SumOfWords S → Q.operators.domain →ₗ[ℂ] Q.operators.domain
  | [] => 0
  | x::xs => x.1 • wordAct Q K R p x.2+sumAct Q K R p xs

lemma derivation (q a b : Q.operators.domain →ₗ[ℂ] Q.operators.domain) : adjAction (Q:=Q) q (a.comp b)=
    (adjAction (Q:=Q) q a).comp b+a.comp (adjAction (Q:=Q) q b) := by
  ext1 x; simp only [adjAction,LinearMap.comp_apply, LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,
    map_smul,map_sub, ← smul_add]; apply congrArg; abel
lemma linearity (q a b : Q.operators.domain →ₗ[ℂ] Q.operators.domain) (z : ℂ) : adjAction (Q:=Q) q (z • a+b)=
    z • adjAction (Q:=Q) q a+adjAction (Q:=Q) q b := by
  ext1 x; simp only [adjAction,LinearMap.comp_apply, LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,
    map_smul,map_add]; rw [smul_comm z I, ← smul_add]; apply congrArg; rw [smul_sub]; abel

def Generates (Q : Wightman S) (T : S.Stress) (R : S.Rotation) := ∀ (X : Set E4), IsCompact X →
  ∀ (f : Probe ℝ), Season f → ∀ c, Reservation X f c → ∀ B : S.Tag, ∀ m : Test4, tsupport m ⊆ X →
  ∀ K : Killing, adjAction (Q:=Q) (Charge Q K T f c) (Q.operators.field (S.pin B.1 B.2) m) = action Q K R B m

def Derives (Q : Wightman S) (T : S.Stress) (R : S.Rotation) := ∀ p : S.Union → S.Tag, Modes S p →
    ∀ (X : Set E4), IsCompact X → ∀ (f : Probe ℝ), Season f → ∀ c, Reservation X f c →
    ∀ v : SumOfWords S, repertoire X v → ∀ K, adjAction (Q:=Q) (Charge Q K T f c) (operator Q.operators v) = sumAct Q K R p v

lemma Generated {T : S.Stress} {R : S.Rotation} (g : Generates Q T R) : Derives Q T R := by
  intro p hp X hX f hf c hc v hv K
  let Z := Charge Q K T f c
  have he w (h : involved (S:=S) X w) : adjAction (Q:=Q) Z (monomial Q.operators w) = wordAct Q K R p w := by
    induction w with
    | nil => ext1 x; simp [monomial,adjAction,wordAct]
    | cons x xs ih =>
      have hm := ih (fun t ht => h t (by simp [ht]))
      have hz := g X hX f hf c hc (p x.1) x.2 (h x (by simp)) K
      rw [hp x.1] at hz
      rw [monomial,derivation,hm,show adjAction (Q:=Q) Z (Q.operators.field x.1 x.2)=_ from hz]; rfl
  change adjAction (Q:=Q) Z _=_
  induction v with
  | nil => ext x; simp [adjAction, operator,sumAct]
  | cons y ys ih => rw [operator,linearity, ih (fun p hp => hv p (by simp [hp])),he y.2 (hv y (by simp)),sumAct]

-- record all at the actual surface, also open continuation and access to partial and joint flux test identities
structure Force (S : Table C.book) (U : Table C.book) (F : Contour S) (R : S.Rotation) (P : DiffPlan S)
    (H : S.RealSpin) (Q : Wightman S) (T : S.Stress) : Prop where
  appointment : ∃ (D : ∀ n, Blanket n) (Z : F.world.Aurora D), Prospect F.waves Z U P H T ∧ Gallery F.world Z
  orbital : ∀ (p : Poincare) (f : Test4) (a b : Axis) (x : Q.operators.domain), ∃ y : Q.operators.domain,
    Q.action.V p x.val=y.val ∧ Q.action.V p (fieldM Q T a b f x).val =
      ((∑ i : Axis, ∑ j : Axis, (((mat p.Λ i a * mat p.Λ j b : ℝ) : ℂ)) • fieldM Q T i j (Joint.push p f)) y).val
  symmetric : ∀ a b, fieldM Q T a b = fieldM Q T b a
  hermitian : ∀ (f : Test4) (a b : Axis) (u v : Q.operators.domain),
    inner ℂ (fieldM Q T a b f u).val v.val=inner ℂ u.val (fieldM Q T a b (Probe.bar f) v).val
  conserve : ∀ (b : Axis) (f : Test4), (∑ a : Axis, (eta a : ℂ) • fieldM Q T a b (partialProbe a f))=0
  commutator : Generates Q T R
  rule : Derives Q T R

lemma force {f : Extraction.Order} {F : Final C f S} (L : Almanac F) (p : F.α.space.X) :
    Force S (F.α.ensemble p) (L.contours p) F.sector.turns F.sector.derivatives F.room.kernel.spin (L.actors p) F.sector.energy := by
  obtain ⟨Y,hY,hy⟩ := (L.cards p).reveals
  have h := L.cores p
  let H := L.pantries p
  have hr := (hy _ h.induced).1
  obtain ⟨D,Z,hD⟩ := hr.visible
  have ht := F.phase.transport.conserved
  have hu := F.phase.transport.spots
  have hb := F.phase.transport.spin
  have hp : Prospect (L.contours p).waves Z _ _ _ _ := ⟨ht,H.adopted,F.room.kernel.laws.toSymmetric,H.rises,
    H.Der,(L.cards p).fromPhase.heat,hY ▸ hD.2⟩
  have hz : Gallery (L.contours p).world Z := by
    refine ⟨blankets _,spectra hr.I, fun n i => ?_⟩
    obtain ⟨y,hy,hh⟩ := windows H hr.I F.realization.qt.letters _ (pair i)
    refine ⟨y,hy, fun j x => ?_⟩; obtain ⟨⟨E⟩,hE⟩ := hh j D Z x; exact ⟨E,(hE E).1⟩
  have hg : Generates (L.actors p) F.sector.energy F.sector.turns := by
    intro X hX k hk c hc B t ht r
    exact local_action r _ B _ hp (F.phase.phase.flux p) hz h t hX ht k hk c hc
  refine ⟨⟨D,Z,hp,hz⟩, fun b f a g x =>
    ⟨⟨_,h.covariance.domain b x.property⟩,rfl,tensor_lorentz h hu _ hb b f a g x⟩,
    fun a b => ?_,tensor_herm h hu _ ht hb,tensor_conserved h hp.hu hp.hs hp.hi hp.hd hp.hF hp.hZ hz.spectra _ ht,hg, Generated hg⟩
  unfold fieldM; rw [M_symmetric F.sector.energy ht]
end YM.EveryPhase.Stress
