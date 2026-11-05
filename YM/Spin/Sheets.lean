import YM.Euclid.Comparator
import YM.Euclid.Stress
import YM.Spin.Shape


/-!
# Scope weak cap identification. ANY weight independently at continuum point,
exact equivalence of rotation action.

Useful repairs vs : no appeal to unchecked finite-dim Lie theory.
Give exact Casimir ports incl limiting polynomial; no assumption weak reps already integrate.
Orientation adapters commute finite H and reality. Unit not required of Θ,
(τ intertwines, generators kill unit; infer SO invariance later). PVM proofs live outside.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spin
open Function Set Filter Ward Table Analysis Maxwell
open scoped Topology BigOperators ContDiff ComplexOrder Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}

abbrev Ind := Axis × Axis
abbrev K (p : Ind) := Ortho.plane p.1 p.2

abbrev pick (p : Ind) : Axis := if p.1≠0 ∧ p.2≠0 then 0 else if p.1≠1 ∧ p.2≠1 then 1 else 2

def fle (p : Ind) := (p.1,pick p)
def fox (p : Ind) := (pick p,p.2)

variable (D : SpinRows S)

def leaf (d : ℕ) (i : Ind) : Mat (S.Field d) := LinearMap.toContinuousLinearMap (D d (K i))

/-- Scales only for final Lie case at cap d: stronger joint low-rank inputs at IR. -/
def rel := ∀ d, Relations (leaf D d) fle fox

section atCap
abbrev comparator (L : Register G) := freeTable L.grid

variable {D} (P : Rotation (comparator L))

def attach (d : ℕ) := leaf P.lie d

abbrev change (S : Table L) (d : ℕ) := (comparator L).Field d≃ₗ[ℂ] S.Field d

/-- Conjugate scaled Γ matrices. Need converge for this cap. -/
def transport (D : SpinRows S) {d} (U : change S d) (p : Ind) : Mat ((comparator L).Field d) :=
    LinearMap.toContinuousLinearMap (U.symm.toLinearMap.comp ((D d (K p)).comp U.toLinearMap))

def realH (A : S.RealSpin) (a : (comparator L).RealSpin) {d : ℕ} (U : change S d) :=
    (∀ h x, U ((comparator L).mirror a d h x) = S.mirror A d h (U x)) ∧
    ∀ x, U ((comparator L).conj a d x) = S.conj A d (U x)

/-- admissible matrices on source. -/
def fine (a : S.RealSpin) (d : ℕ) : AddSubgroup (Mat (S.Field d)) where
  carrier := {f | (∀ h x, f (S.mirror a d h x)= S.mirror a d h (f x)) ∧
    ∀ x, f (S.conj a d x) = S.conj a d (f x)}
  add_mem' := by
    intro x y hx hy
    obtain ⟨A,B⟩ := hx; obtain ⟨T,W⟩ := hy
    constructor <;> simp [A,B,T,W]
  neg_mem' := by
    intro x hx; obtain ⟨A,B⟩ := hx; constructor <;> simp [A,B]
  zero_mem' := by constructor <;> simp

lemma cont_conj (a : S.RealSpin) (d : ℕ) : Continuous (S.conj a d) :=
  let f : S.Field d →ₗ[ℝ] S.Field d := ⟨⟨S.conj a d,map_add _⟩, fun c x => by
    change S.conj a d (c • x)=c • S.conj a d x
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smulₛₗ]; change (starRingEnd ℂ (Complex.ofReal c)) • _=c • S.conj a d x; rw [Complex.conj_ofReal]; exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c _).symm ⟩
  f.continuous_of_finiteDimensional
lemma fine_close (a : S.RealSpin) (d : ℕ) : IsClosed (fine a d: Set (Mat (S.Field d))) := by
  suffices he : (fine a d:Set _)=(⋂ (h : Signed) (i : S.Field d),
      {f : Mat (S.Field d) | f (S.mirror a d h i)=S.mirror a d h (f i)}) ∩ (⋂ i : S.Field d,
      {f : Mat (S.Field d) | f (S.conj a d i) = S.conj a d (f i)}) by
    rw [he]
    have hv (x : S.Field d) : Continuous (fun f : Mat (S.Field d) => f x) := (ContinuousLinearMap.apply ℂ (S.Field d) x).continuous
    exact (isClosed_iInter fun x => isClosed_iInter fun i => isClosed_eq (hv _) ((S.mirror a d x).continuous_of_finiteDimensional.comp (hv i))).inter
      (isClosed_iInter fun i => isClosed_eq (hv _) ((cont_conj a d).comp (hv _)))
  ext x; simp; rfl

lemma intact (D : SpinRows S) (h : rel D) (d) (U : change S d) : Relations (transport D U) fle fox := by
  intro i; ext1 x; apply U.injective
  have hu (i : Ind) (x) : U (transport D U i x)=leaf D d i (U x) := U.apply_symm_apply _
  have he := h d i
  rw [hu]
  change leaf D d i (U x)=U ((transport D U (fle i)) ((transport D U (fox i)) x)- (transport D U (fox i)) ((transport D U (fle i)) x))
  rw [map_sub,hu,hu,hu,hu]
  conv_lhs => rw [he]
  rfl

/-- Need equality for all Ω, not just generating planes. No unnoticed constants. -/
lemma spans : Submodule.span ℝ (Set.range K) = ⊤ := by
  -- express any matrix Ω as half sum over all ordered
  rw [eq_top_iff]; intro x hx; change Ortho.Skew at x
  have hb : ((2:ℝ) • x) = ∑ i : Axis, ∑ j : Axis, (x.val i j) • K (i,j) := by
    apply Subtype.ext; ext i j
    simp only [SetLike.val_smul, Submodule.coe_sum,K]
    have he : star x.val= -x.val := x.property
    have hz : x.val j i= -x.val i j := by
      have hm := congr_arg (fun z : M4 => z i j) he
      simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial, Matrix.neg_apply] using hm
    simp [Ortho.plane,Matrix.sum_apply,Matrix.single_apply,mul_sub,mul_ite, Finset.sum_sub_distrib,ite_and] -- hz
    rw [hz]
    ring
  rw [show x=(2:ℝ)⁻¹ • ∑ i : Axis, ∑ j:Axis,(x.val i j) • K (i,j) from by rw [← hb,inv_smul_smul₀ two_ne_zero]] -- dependant occurrences!
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_)
  exact (Submodule.span ..).smul_mem _ (Submodule.subset_span (mem_range_self _))

lemma extendsE {A : Type*} [AddCommGroup A] [Module ℝ A]
    (f g : Ortho.Skew →ₗ[ℝ] A) (h : ∀ i, f (K i) = g (K i)) : f=g := by
  -- ext by spanning
  apply sub_eq_zero.mp
  suffices he : LinearMap.ker (f-g)=⊤ from LinearMap.ker_eq_top.mp he
  rw [eq_top_iff,← spans,Submodule.span_le]; rintro _ ⟨i,rfl⟩; apply LinearMap.mem_ker.mpr; simp [h i]

structure Tilt (A : S.RealSpin) (a : (comparator L).RealSpin) (D : SpinRows S) (d : ℕ) (U : ℕ → change S d) (z : List ℝ) : Prop where
  preserves (n : ℕ) : realH A a (U n)
  converges (i : Ind) : Tendsto (fun n => transport D (U n) i) atTop (𝓝 (attach P d i))
  infinitesimal : rel D
  optic : rel P.lie
  marks : Works z (attach P d)
  tracks : ∀ᶠ n : ℕ in atTop, Tracks (fine a d) z (attach P d) (transport D (U n))

lemma unit_shape {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] (V : A→L[ℂ] A) (h : IsUnit V) :
    ∃ W : A≃ₗ[ℂ] A, W.toLinearMap=V.toLinearMap := by
  obtain ⟨p,hp⟩ := h
  subst V
  refine ⟨LinearEquiv.ofBijective (p.val).toLinearMap ⟨fun i j hi => ?_,fun i => ?_⟩, rfl⟩
  · have he v : p.inv (p.val v)=v := congr_arg (fun x : Mat A => x v) p.inv_val
    rw [← he i,← he j]
    exact congr_arg _ hi
  exact ⟨p.inv i, congr_arg (fun x : Mat A => x i) p.val_inv⟩

theorem meet (D : SpinRows S) {A a d U z} (h : Tilt P A a D d U z) : ∃ V : change S d,
    realH A a V ∧ ∀ k x, D d k (V x) = V (P.lie d k x) := by
  have he := realize (fun n => transport D (U n)) (attach P d) fle fox h.converges
    (Eventually.of_forall fun i => intact D h.infinitesimal d _) (h.optic d) z h.marks
    (fine a d) (show _ from And.intro (fun _ _ => rfl) (fun _ => rfl)) (fine_close a d) h.tracks
  obtain ⟨n,η,hA,hη,H⟩ := he.exists
  obtain ⟨L',hp⟩ := unit_shape η hA
  let V := L'.trans (U n)
  obtain ⟨hc,hr⟩ := h.preserves n
  have hy (p) : V p=U n (η p) := congr_arg (U n) (LinearMap.congr_fun hp p)
  obtain ⟨hw,hW⟩ := hη
  refine ⟨V,⟨fun x p => ?_,fun x => ?_⟩,?_⟩
  · rw [hy,hw,hc,← hy]
  · rw [hy,hW,hr,← hy]
  intro k x
  let f : Ortho.Skew→ₗ[ℝ] S.Field d := ⟨⟨(fun k => D d k (V x)), by simp⟩, by simp⟩ -- core
  let g : Ortho.Skew→ₗ[ℝ] S.Field d := ⟨⟨(fun k => (V.toLinearMap.restrictScalars ℝ) (P.lie d k x)), by simp⟩, by simp⟩
  change f k=g k; congr 1; apply extendsE _ _
  intro i
  change D d _ _=V _; rw [hy,hy]
  let W := U n
  apply W.symm.injective
  rw [W.symm_apply_apply]
  exact congr_arg (fun c : Mat _ => c x) (H i)
end atCap
end YM.Spin
