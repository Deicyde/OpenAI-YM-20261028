import YM.Integrated
import YM.Org.Theatre
import YM.Push.RELAY_MARK.Gauge

/-!
# Linear lifting

Combine the equation and other labels in one infinitesimal universal
purchase (before actual schedule L,all stages). Do not require the
kernel to be the EXACT polynomials of the Maxwell equation ideal at
bare scale. It is OK to take an injective image (of equal dimension
and also respecting the real and H data). Here get a near-diagonal
(in a *filtration*, not yet norms) automorphism on whole label space,
to deliver an actual calibrated-section candidate beside the marked
image. Gives a way to discharge one of the RBin physics obligations
by reaching agreement already at RAuthors, without changing the
endpoint semantics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} {p q : Label G d} {f : Pre G} {m : ℕ × ℕ}

abbrev Bill (G : Gauge) (d : ℕ) := Label G d × Pre G
abbrev Switch (G : Gauge) (d : ℕ) := Label G d →ₗ[ℂ] Bill G d
abbrev code (d : ℕ) : Finset (ℕ × ℕ) := (Finset.range (d+1)) ×ˢ (Finset.range (d+1))

lemma fees (p : Label G d) : (∑ m∈code d,gradePart m p)=p := by
  rw [code,Finset.sum_product]; exact decompose _

structure Offered (H : Hol G) (d : ℕ) (m : ℕ × ℕ) (p : Label G d) (v : Bill G d) : Prop where
  grade : p∈Grade m
  gauge : GaugeInvariant v.2
  grow : v.1.val-p.val∈above m
  glyph : Forms H d v.2 v.1.val
  cost : v.2∈powered G m.2

namespace Offered
variable {u v : Bill G d}

lemma add (h : Offered H d m p v) (ha : Offered H d m q u) : Offered H d m (p+q) (v+u) :=
    ⟨Submodule.add_mem _ h.grade ha.grade, fun T V => congr_arg₂ (·+·) (h.gauge T V) (ha.gauge T V),
      by change v.1.val+u.1.val-(p.val+q.val)∈_; rw [add_sub_add_comm]; exact Submodule.add_mem _ h.grow ha.grow,
      h.glyph.add ha.glyph,Submodule.add_mem _ h.cost ha.cost⟩

lemma scale (c : ℂ) (h : Offered H d m p v) : Offered H d m (c • p) (c • v) :=
    ⟨Submodule.smul_mem _ _ h.grade, fun T V => congr_arg (c • ·) (h.gauge T V),
      by change c • v.1.val-c • p.val∈_; rw [← smul_sub]; exact Submodule.smul_mem _ _ h.grow,
      h.glyph.scale _, Submodule.smul_mem _ _ h.cost⟩
lemma zero (G : Gauge) (H : Hol G) (d : ℕ) (m : ℕ × ℕ) : Offered H d m 0 0 :=
    ⟨Submodule.zero_mem _,fun _ _=>rfl,by simp,Forms.zero ..,Submodule.zero_mem _⟩

lemma sum {α : Type*} (s : Finset α) (P : α→Label G d) (V : α→Bill G d)
    (h : ∀ i∈s, Offered H d m (P i) (V i)) : Offered H d m (∑ i∈s,P i) (∑ i∈s,V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty,Finset.sum_empty]; exact zero ..
  | insert i s hi ih=>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add
      (ih (fun i hh=> h i (Finset.mem_insert_of_mem hh)))
end Offered

structure Payment (H : Hol G) (d : ℕ) (m : ℕ × ℕ) (p : Label G d) (v : Bill G d) : Prop where
  takes : Offered H d m p v
  exacts : p ∈ Maxwell.equationIdeal G d → Micro v.2

structure Campaign (H : Hol G) (d : ℕ) (F : Switch G d) : Prop where
  each (m : ℕ × ℕ) : m∈code d → ∀ p : Label G d, p∈Grade m → Payment H d m p (F p)
  start : F (unit G d) = (unit G d,1)

section One

private lemma basis_offer (H : Hol G) (d : ℕ) (F : Labels.Frame G d) (T : SectionData F)
    (ht : T.Sound H) (hv : Bid.pop T) : ∃ x : Switch G d,
      (x (unit G d))=(unit G d,1) ∧ ∀ (m : ℕ × ℕ) p, p∈Grade m → Offered H d m p (x p) := by
  let e : Label G d→ₗ[ℂ] Pre G := ((T.eval_linear).mk' _).comp F.coords.toLinearMap
  let x : Switch G d := LinearMap.id.prod e
  have hX p : x p = (p,T.evaluate (F.coords p)) := rfl
  refine ⟨x,by rw [hX,F.coords_unit,ht.unit], fun m p hp=>?_⟩
  refine ⟨hp,ht.gaugeInvariant _,?_,(Forms.seats (H:=H) p (x p).2).2 ?_, ?_⟩
  · rw [hX]; simp
  · have hu := ht.projects (F.coords p)
    rw [LinearEquiv.symm_apply_apply] at hu
    exact hu
  change e p∈powered G m.2
  rw [← F.basis.sum_repr p,map_sum]
  refine Submodule.sum_mem _ fun i hi=> ?_
  by_cases h : F.grades i=m
  · obtain ⟨b,B,hr,P,hP,hs⟩ := hv i
    have hc : e (F.basis i)=spelledPose B P := by
      change T.evaluate (F.coords (F.basis i))=_; rw [F.coords_basis]; exact hP
    rw [map_smul,hc,← h]; exact Submodule.smul_mem _ _ (pose_power B P hs)
  rw [show F.basis.repr p i=0 from F.power_coefficient i (Ne.symm h) hp,zero_smul,map_zero]
  exact Submodule.zero_mem _

-- On an arbitrary auxiliary frame used to generate “other” directions.
lemma shelf (H : Hol G) (d : ℕ) : ∃ x : Switch G d,
    x (unit G d)=(unit G d,1) ∧ ∀ (m : ℕ × ℕ) p,p∈Grade m → Offered H d m p (x p) := by
  obtain ⟨T,ht,hv,h⟩ := (Integrated.source_sections G H (frames G)).builds
  exact basis_offer H d ((frames G).level d) (T d) (ht _) (hv _)

private abbrev bay (G : Gauge) (d : ℕ) (m : ℕ × ℕ) : Submodule ℂ (Label G d) := Grade m ⊓ Maxwell.equationIdeal G d

private lemma marked_shelf (H : Hol G) (d : ℕ) (m : ℕ × ℕ) (h : m.1 ≤ d) :
    ∃ f : bay G d m →ₗ[ℂ] Bill G d, ∀ v : bay G d m, Payment H d m v.val (f v) := by
  classical
  have simple {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (P : Submodule ℂ V) : Module.Free ℂ P ∧ Module.Finite ℂ P := ⟨inferInstance,inferInstance⟩
  haveI h0 := (simple (bay G d m)).1; haveI h1 := (simple (bay G d m)).2
  let B := Module.finBasis ℂ (bay G d m)
  choose F Q hg hc using fun i => positioned H (B i).val m h (B i).property.1 (B i).property.2
  let f := B.constr ℂ fun i => (Q i,F i)
  have ht (i) : Offered H d m (B i).val (f (B i)) := by
    rw [show f (B i)=(Q i,F i) from Module.Basis.constr_basis ..]
    exact ⟨(B i).property.1,hg i,(hc i).head,(hc i).maps,(hc i).size⟩
  have hx i : Micro (f (B i)).2 := by rw [show f (B i)=_ from Module.Basis.constr_basis ..]; exact (hc i).mark
  refine ⟨f,fun v=>?_⟩
  rw [← B.sum_repr v,map_sum,Submodule.coe_sum]; constructor
  · apply Offered.sum _ _ _ (fun i _=>?_)
    rw [map_smul]; exact (ht i).scale _
  intro he; rw [Prod.snd_sum]; change _∈micros G
  refine Submodule.sum_mem _ fun i _=> ?_
  rw [map_smul, Prod.smul_snd]; exact Submodule.smul_mem _ _ (hx _)

/-- Extend along any algebraic projection onto the equation-grade piece. -/
private lemma one_floor (H : Hol G) (d : ℕ) (m : ℕ × ℕ) (h : m.1 ≤ d) :
    ∃ X : Switch G d, (∀ p : Label G d,p∈Grade m → Payment H d m p (X p)) ∧
      (m=(0,0) → X (unit G d) = (unit G d,1)) := by
  classical
  obtain ⟨x,hx,hT⟩ := shelf H d
  obtain ⟨f,hf⟩ := marked_shelf H d m h
  let P := bay G d m
  have hl {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) :
      ∃ L : V→ₗ[ℂ] P,∀ p:P, L (P.subtype p)=p := ⟨P.subtype.leftInverse,LinearMap.leftInverse_apply_of_inj P.ker_subtype⟩
  obtain ⟨L,hh⟩ := hl P
  let X := f ∘ₗ L + x ∘ₗ (LinearMap.id - P.subtype ∘ₗ L)
  have hu p : X p=f (L p) + x (p-(L p).val) := by simp [X]
  refine ⟨X,fun p hp=>?_,fun hm=>?_⟩
  · rw [hu p]
    refine ⟨?_,fun he=>?_⟩
    · have ha := (hf (L p)).takes.add (hT m (p-(L p).val) (Submodule.sub_mem _ hp (L p).property.1))
      simpa only [add_sub_cancel] using ha
    have hk : L p= (⟨p,hp,he⟩ : P) := hh ⟨p,hp,he⟩
    rw [hk]; simp only [sub_self,map_zero,add_zero]; exact (hf ⟨p,hp,he⟩).exacts he
  have hl (p) : L p=0 := by
    let u := L p
    apply Subtype.ext
    have hQ : u.val∈Maxwell.equationIdeal G d := u.property.2
    have hb : u.val∈Grade m := u.property.1
    rw [hm] at hb; exact no_unit _ hQ 0 hb
  rw [hu,hl]; simp only [ZeroMemClass.coe_zero,sub_zero,map_zero, zero_add,hx]
end One

lemma unsym (H : Hol G) (d : ℕ) : ∃ F : Switch G d, Campaign H d F := by
  classical
  let I := code d
  choose F hF ha using fun i : I => one_floor H d i.val (Nat.le_of_lt_succ
    (Finset.mem_range.mp (Finset.mem_product.mp i.property).1))
  let X : Switch G d := ∑ i:I,(F i).comp (gradePart i.val)
  have ht (m) (hm : m∈I) (p:Label G d) (hp:p∈Grade m) : X p=F ⟨m,hm⟩ p := by
    rw [show X p=∑ i : I,F i (gradePart i.val p) by simp [X], Finset.sum_eq_single ⟨m,hm⟩]
    · rw [gradePart_self _ _ hp]
    · intro b _ hb; rw [gradePart_zero _ _ m (fun h=>hb (Subtype.ext h)) hp,map_zero]
    simp
  have he : (0,0)∈I := by simp [I]
  refine ⟨X,fun m hm p hp=> (ht m hm p hp).symm ▸ hF ⟨m,hm⟩ p hp,?_⟩
  rw [ht _ he _ (unit_grade d)]; exact ha ⟨(0,0),he⟩ rfl
end YM.Push.Mark
