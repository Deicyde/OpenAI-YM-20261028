import YM.Fields.System
import YM.OS.Dynamics
import YM.Shift.Swap



/-!
# Concrete left multiplication on ONE field domain using Gram

Squared null tested at all word probes; no each-single field completion.
Actual rule even if representing b with relations. Expose test ports to
Shape. Tests operate on sentence, no 'one plus map'. -/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Function Set Filter Complex Analysis Kernel Mink MeasureTheory Distribution Probe
open scoped Topology BigOperators InnerProductSpace ComplexOrder ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L}

abbrev Soil (W : Surface S) (J : StarOp S) := Kernel.Gram (W.kernel J)
abbrev Scroll (S : Table L) := Sentence S →₀ ℂ

namespace Surface
/-- these ports will come from W's actual tested values + limits, differ
from S point permutation. -/
def Symbol (W : Surface S) := ∀ a b : Sentence S,
    ∃ U : S.Union →ₗ[ℂ] Test4 →ₗ[ℂ] ℂ, ∀ (x : S.Union) (f : Test4), W.expect (a++((x,f)::b)) = U x f

def Cam (W : Surface S) (J : StarOp S) := ∀ a b : Sentence S, ∀ x y : S.Union,
    Continuous fun p : Test4 × Test4 => W.kernel J ((x,p.1)::a) ((y,p.2)::b)

/-- exposed when writing polynomial locality proof, not assumed at T. -/
def Regional (W : Surface S) := ∀ a b : Sentence S, ∀ x y : S.Union, ∀ f g : Test4,
    Fields.causal f g → W.expect (a ++ ((x,f)::(y,g)::b)) = W.expect (a ++ ((y,g)::(x,f)::b))

def Marker (W : Surface S) (x : S.Union) := ∀ a b : Sentence S, ∀ f : Test4, W.expect (a++((x,f)::b))=0

def Persists (W : Surface S) := ∀ x, W.Marker x → x=0
end Surface

namespace Soil
variable {W : Surface S} {J : StarOp S} (Z : Soil W J)
abbrev land : Submodule ℂ Z.H := LinearMap.range Z.stems
abbrev WordOp := Z.land→ₗ[ℂ] Z.land

def variety : Scroll S→ₗ[ℂ] Z.land := Z.stems.rangeRestrict

def seed (v : Sentence S) : Z.land := ⟨Z.plant v,⟨_,Z.one v⟩⟩

@[simp] lemma one_pack (v) : Z.variety (Finsupp.single v 1)=Z.seed v := Subtype.ext (Z.one _)
lemma rich : Surjective Z.variety := LinearMap.surjective_rangeRestrict _

/-- lift left concatenation with honest pair proof. -/
def machine (x : Letter S) : Scroll S →ₗ[ℂ] Z.land := Finsupp.linearCombination ℂ fun i => Z.seed (x::i)
@[simp] lemma shoot (x : Letter S) (i) (a : ℂ) : Z.machine x (Finsupp.single i a) = a • Z.seed (x::i) := by simp [machine]
lemma folds (x : Letter S) (i k) : W.kernel J (x::i) k = W.kernel J i ((Letter.op J x)::k) := by simp [Surface.kernel,Sentence.rev]

lemma they (x : Letter S) (p q : Scroll S) : inner ℂ (Z.machine x p) (Z.variety q) = inner ℂ (Z.variety p) (Z.machine (Letter.op J x) q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hP hQ => simp only [map_add,inner_add_left,hP,hQ]
  | single i a =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add p q hP hQ => simp only [map_add,inner_add_right,hP,hQ]
    | single j b =>
      have he (p : Letter S) k c : (Z.machine p (Finsupp.single k c)).val = c • Z.plant (p::k) := by
        rw [shoot];rfl
      change inner ℂ (Z.machine _ _).val (Z.stems _) = inner ℂ (Z.stems _) (Z.machine _ _).val
      rw [he,he]; simp [Kernel.Gram.stems,inner_smul_left,inner_smul_right,Z.measure,folds]

lemma compactor (x : Letter S) : LinearMap.ker Z.variety ≤ LinearMap.ker (Z.machine x) := by
  intro u H; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  obtain ⟨v,hv⟩ := Z.rich (Z.machine x u)
  change Z.variety u=0 at H
  nth_rw 2 [← hv]
  rw [Z.they,H]; simp

def beginsOp (x : Letter S) : Z.WordOp := ((LinearMap.ker Z.variety).liftQ (Z.machine x) (Z.compactor x)).comp
    (LinearMap.quotKerEquivOfSurjective Z.variety Z.rich).symm.toLinearMap

@[simp] lemma press (x : Letter S) (i : Scroll S) : Z.beginsOp x (Z.variety i)=Z.machine x i := by
  unfold beginsOp; rw [LinearMap.comp_apply]
  rw [show (LinearMap.quotKerEquivOfSurjective _ Z.rich).symm.toLinearMap (Z.variety i)=
      Submodule.Quotient.mk (p:=LinearMap.ker Z.variety) i from ?_]; rfl
  exact Z.variety.quotKerEquivOfSurjective_symm_apply Z.rich i
@[simp] lemma actual (x i) : Z.beginsOp x (Z.seed i)=Z.seed (x::i) := by
  rw [← one_pack,press,shoot,one_smul]

lemma flipped (x : Letter S) (u v : Z.land) : inner ℂ (Z.beginsOp x u) v= inner ℂ u (Z.beginsOp (Letter.op J x) v) := by
  obtain ⟨i,rfl⟩ := Z.rich u; obtain ⟨j,rfl⟩ := Z.rich v; rw [press,press, Z.they]
lemma splits (x y : Z.land) (h : ∀ i : Sentence S, inner ℂ (Z.seed i) x = inner ℂ (Z.seed i) y) : x=y := by
  apply ext_inner_left ℂ
  intro f
  obtain ⟨g,rfl⟩ := Z.rich f
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add p q hP hQ => simp only [map_add, inner_add_left, hP, hQ]
  | single i c =>
    rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)]; rw [map_smul, inner_smul_left,inner_smul_left,one_pack,h]

lemma buds (f g : Z.WordOp) (h : ∀ i : Sentence S,f (Z.seed i)=g (Z.seed i)) : f=g := by
  ext1 i; obtain ⟨x,rfl⟩ := Z.rich i
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hP hQ => simp only [map_add,hP,hQ]
  | single i c => rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)];simp only [map_smul,one_pack,h]
lemma bearings (i j) : inner ℂ (Z.seed i) (Z.seed j)=W.expect (Sentence.rev J i ++ j) := Z.measure i j
lemma adds_test (h : W.Symbol) (x : S.Union) (f g : Test4) : Z.beginsOp (x,f+g) = Z.beginsOp (x,f)+Z.beginsOp (x,g) := by
  apply Z.buds; intro i; apply Z.splits; intro j
  obtain ⟨U,hU⟩ := h (Sentence.rev J j) i
  simp only [LinearMap.add_apply,Z.actual,inner_add_right,Z.bearings,hU,map_add]
lemma scale_test (h : W.Symbol) (x : S.Union) (f : Test4) (a : ℂ) : Z.beginsOp (x,a•f) = a • Z.beginsOp (x,f) := by
  apply Z.buds; intro i; apply Z.splits; intro j
  obtain ⟨U,hU⟩ := h (Sentence.rev J j) i
  simp only [LinearMap.smul_apply,Z.actual,inner_smul_right,Z.bearings,hU,map_smul,smul_eq_mul]

def beginTest (h : W.Symbol) (x : S.Union) : Test4→ₗ[ℂ] Z.WordOp := ⟨⟨Z.beginsOp ∘ fun f => (x,f),Z.adds_test h x⟩,fun a f => Z.scale_test h x f a⟩

def starter (h : W.Symbol) : Fields S where
  H := Z.H
  domain := Z.land
  omega := Z.seed []
  field := {
    toFun := Z.beginTest h
    map_add' := by
      intro x y; ext1 f; apply Z.buds; intro i
      apply Z.splits; intro j
      obtain ⟨U,hU⟩ := h (Sentence.rev J j) i
      change inner ℂ _ (Z.beginsOp _ _) = inner ℂ _ (Z.beginsOp (x,f) _ + Z.beginsOp (y,f) _)
      simp only [Z.actual, inner_add_right,Z.bearings,hU,map_add,LinearMap.add_apply]
    map_smul' := by
      intro a x; ext1 f; apply Z.buds; intro i
      apply Z.splits; intro j
      obtain ⟨U,hU⟩ := h (Sentence.rev J j) i
      change inner ℂ _ (Z.beginsOp _ _) = inner ℂ _ (a • Z.beginsOp (x,f) _)
      simp only [Z.actual, inner_smul_right,Z.bearings,hU,map_smul,LinearMap.smul_apply,smul_eq_mul] }

@[simp] lemma sp (h : W.Symbol) (x : S.Union) (f) : (Z.starter h).field x f=Z.beginsOp (x,f) := rfl
lemma forms (h : W.Symbol) (v : Sentence S) : (Z.starter h).evaluates v=Z.seed v := by
  induction v with
  | nil => rfl
  | cons i v IH =>
    change Z.beginsOp i ((Z.starter h).evaluates v)=_
    rw [IH,actual]
lemma bears (h : W.Symbol) (v : Sentence S) : (Z.starter h).vector v=Z.plant v := by
  unfold Fields.vector;rw [Z.forms];rfl
lemma sharp (h : W.Symbol) : (Z.starter h).sharpPair J := fun x f a b => Z.flipped (x,f) a b
lemma relishes (h : W.Symbol) : (Z.starter h).realizes W := by
  intro v; rw [Z.bears]
  change inner ℂ (Z.plant []) (Z.plant v)=_
  rw [Z.measure]; rfl

lemma varies (x : S.Union) (i) (h : W.Cam J) : Continuous (fun f : Test4 => Z.plant ((x,f)::i)) := by
  apply continuous_iff_continuousAt.mpr; intro f
  apply OS.ketC
  · simp_rw [Z.measure]; exact ((h i i x x).comp (continuous_id.prodMk continuous_id)).continuousAt
  simp_rw [Z.measure]; exact ((h i i x x).comp (continuous_const.prodMk continuous_id)).continuousAt

lemma usable (h : W.Symbol) (p : W.Cam J) (he : W.expect []=1) : (Z.starter h).Total := by
  refine ⟨?_,?_,?_,?_⟩
  · have he : inner ℂ (Z.plant []) (Z.plant []) =1 := (Z.measure [] []).trans he
    change ‖Z.plant []‖=1
    rw [@norm_eq_sqrt_re_inner ℂ,he]; simp
  · exact Z.whole
  · simp_rw [← Finsupp.range_linearCombination, show (Z.starter h).vector=Z.plant from funext (Z.bears h)]
    rfl
  intro x v; obtain ⟨g,hg⟩ := Z.rich v
  subst v; change Continuous (fun f => (Z.beginsOp (x,f) (Z.variety g)).val)
  induction g using Finsupp.induction_linear with
  | zero => simp;exact continuous_const
  | add a b H W =>
    simp_rw [map_add]
    exact H.add W
  | single i c =>
    rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)]
    simp_rw [map_smul,one_pack,actual]
    change Continuous (fun f : Test4 => c • Z.plant ((x,f)::i)); exact continuous_const.smul (Z.varies x i p)

lemma regional (h : W.Symbol) (p : W.Regional) : (Z.starter h).commutes := by
  intro x y f g H v
  have he : (Z.beginsOp (x,f)).comp (Z.beginsOp (y,g))=(Z.beginsOp (y,g)).comp (Z.beginsOp (x,f)) := by
    apply Z.buds; intro i; apply Z.splits; intro j
    simp only [LinearMap.comp_apply,actual,Z.bearings,p _ _ x y _ _ H]
  exact LinearMap.congr_fun he v

lemma sees (h : W.Symbol) (ht : Involutive J) (p : W.Persists) : (Z.starter h).notLost := by
  intro x hx; by_contra! he
  refine hx (p x ?_); intro a b f
  have h1 : Z.beginsOp (x,f)=0 := he _
  have hm := Z.bearings (Sentence.rev J a) ((x,f)::b)
  rw [Sentence.rev_rev J ht] at hm; rw [← hm, ← actual Z, h1, LinearMap.zero_apply, inner_zero_right]
end Soil
end YM.Boundary
