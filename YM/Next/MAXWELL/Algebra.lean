import YM.Euclid.Comparator
import YM.Next.MAXWELL.Paint


/-!
# Polynomial observables on the invariant free sector

Color equivariant projection and a section give the *exact* description
in terms of weight-restricted invariant polynomials; weight and length
projections remain inside. `decompose` uses the two gradings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis
open MvPolynomial hiding monomial
open scoped ContDiff Topology BigOperators
variable {G : Gauge} {d j l : ℕ}

def scaleW (v : Slot G) : ℕ := v.1 + 2



def degree (b : Slot G →₀ ℕ) := Finsupp.weight scaleW b

def lowerCap (G : Gauge) (d : ℕ) : Submodule ℂ (WickPol G) := restrictSupport ℂ {b | degree b ≤ d}

lemma bounded_grade {σ τ : Type*} {m : Type*} [AddCommMonoid m] (a : σ → m) (b : τ → m)
    (L : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (H : ∀ i, IsWeightedHomogeneous b (L (X i)) (a i))
    (p : σ →₀ ℕ) (c : ℂ) : IsWeightedHomogeneous b (L (MvPolynomial.monomial p c)) (Finsupp.weight a p) := by
  rw [MvPolynomial.monomial_eq]; rw [map_mul,algHom_C]; apply IsWeightedHomogeneous.C_mul
  rw [Finsupp.weight_apply]; unfold Finsupp.sum Finsupp.prod; rw [map_prod]; simp_rw [map_pow];
  exact IsWeightedHomogeneous.prod _ _ _ (fun i hi => (H i).pow (p i))

lemma transfers {σ τ : Type*} (a : σ → ℕ) (b : τ → ℕ)
    (L : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (H : ∀ i, IsWeightedHomogeneous b (L (X i)) (a i))
    (p : MvPolynomial σ ℂ) (hp : p ∈ MvPolynomial.restrictSupport ℂ {s|Finsupp.weight a s ≤ d}) :
    L p ∈ MvPolynomial.restrictSupport ℂ {s|Finsupp.weight b s ≤ d} := by
  rw [restrictSupport_eq_span] at hp
  refine Submodule.span_induction (p := fun p _ => L p ∈ _) ?_ ?_ ?_ ?_ hp
  · rintro f ⟨x,hx,rfl⟩
    rw [mem_restrictSupport_iff]
    intro s hs; change Finsupp.weight b s ≤ d
    rw [bounded_grade a b L H x 1 (MvPolynomial.mem_support_iff.mp hs)]; exact hx
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ h k; rw [map_add]; exact Submodule.add_mem _ h k
  intro t y _ k; rw [map_smul]; exact Submodule.smul_mem _ _ k

lemma symbol_hom {M : Type*} [AddCommMonoid M] (p : Probe G j) (m : ℕ → M) :
    IsWeightedHomogeneous (fun k : Slot G => m k.1) (symbol j p) (m j) := by
  unfold symbol; apply IsWeightedHomogeneous.sum; intro i hi; apply IsWeightedHomogeneous.C_mul
  exact isWeightedHomogeneous_X ..

lemma reduce_grade {M : Type*} [AddCommMonoid M] (m : ℕ → M) (i : Labels.Key G) :
    IsWeightedHomogeneous (fun k : Slot G => m k.1) (reduceEq (X i)) (m i.1) := by
  rw [reduceEq,MvPolynomial.aeval_X]; apply IsWeightedHomogeneous.sum
  intro j _; apply IsWeightedHomogeneous.C_mul; exact isWeightedHomogeneous_X ..

lemma reduces {p : Labels.Pol G} (hp : p ∈ Labels.limited G d) : reduceEq p ∈ lowerCap G d :=
  transfers _ _ reduceEq (reduce_grade (fun i => i+2)) p hp

/-- Pull color on actual shell jets. -/
def shade (u : G.El) (A : TaylorTower G) : TaylorTower G := fun i => castFace u i (A i)

def pigment (u : G.El) : WickPol G →ₐ[ℂ] WickPol G := MvPolynomial.aeval fun i : Slot G =>
  symbol i.1 ((coordinateLeg i).comp (castFace u i.1))

lemma pigment_action (u : G.El) (A : TaylorTower G) (p : WickPol G) :
    probe A (pigment u p) = probe (shade u A) p := by
  suffices he : (probe A).comp (pigment u) = probe (shade u A) from DFunLike.congr_fun he p
  ext i; rw [AlgHom.comp_apply,pigment, MvPolynomial.aeval_X,symbol_test,probe,MvPolynomial.aeval_X]; rfl

lemma symbol_pigment (u : G.El) (p : Probe G j) : pigment u (symbol j p) = symbol j (p.comp (castFace u j)) := by
  apply equalPol; intro A; rw [pigment_action,symbol_test,symbol_test]; rfl

lemma pivot_observable (v : Labels.Label G d) (u : G.El) : pigment u (observable G d v)=observable G d v := by
  apply equalPol
  intro A; rw [pigment_action]; change probe _ (reduceEq _) = probe _ (reduceEq _)
  rw [jet_value,jet_value];
  simpa only [shade,equiv_curl] using! (show Labels.read (Labels.colored u (fun i => gaugeJet (A i))) v.val = _ from v.property.2 (fun i => gaugeJet (A i)) u)

/-- A section, capitalizing that `assign` is already color equivariant.
No need to Haar average this section. -/
def protoLift (G : Gauge) : WickPol G →ₐ[ℂ] Labels.Pol G := MvPolynomial.aeval fun i : Slot G =>
    ∑ j : Fin (Labels.dim G i.1), C (σ:= Labels.Key G) (coordinateLeg i (assign G i.1 (Labels.axes G i.1 j)) : ℂ) *
      X (R:=ℂ) (⟨i.1,j⟩ : Labels.Key G)

lemma lifts_value (p : WickPol G) (A : Labels.Jet G) : Labels.read A (protoLift G p)=probe (fun i => assign G i (A i)) p := by
  suffices H : (Labels.read A).comp (protoLift G)=probe (fun i => assign G i (A i)) from DFunLike.congr_fun H p
  ext i
  simp only [AlgHom.comp_apply,protoLift, MvPolynomial.aeval_X,map_sum,map_mul,Labels.read, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply,probe]
  rcases i with ⟨j,i⟩
  change ∑ k : Fin (Labels.dim G j), _ * (↑(((Labels.axes G j).repr (A j) k):ℝ):ℂ) =
    (↑(coordinateLeg (⟨j,i⟩ : Slot G) (assign G j (A j))) : ℂ)
  conv_rhs => rw [← (Labels.axes G j).sum_repr (A j)]
  simp only [map_sum,map_smul,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm ..

lemma section_eq (p : WickPol G) : reduceEq (protoLift G p) = p := by
  apply equalPol; intro A; rw [jet_value,lifts_value]; simp only [retrieve]

lemma lift_lim {p : WickPol G} (hp : p ∈ lowerCap G d) : protoLift G p ∈ Labels.limited G d := by
  apply transfers (a:=scaleW) Labels.generation _ ?_ p hp
  intro i; rw [protoLift,MvPolynomial.aeval_X]; apply IsWeightedHomogeneous.sum; intro j hj
  apply IsWeightedHomogeneous.C_mul; exact isWeightedHomogeneous_X ..

lemma sector {p : WickPol G} : p ∈ shellSector G d ↔ p ∈ lowerCap G d ∧ ∀ i : G.El, pigment i p=p := by
  constructor
  · rintro ⟨v,rfl⟩; exact ⟨reduces v.property.1,pivot_observable v⟩
  rintro ⟨hv,h⟩
  refine ⟨⟨protoLift G p,lift_lim hv,?_⟩, section_eq p⟩
  intro A u
  rw [lifts_value,lifts_value]
  change probe (fun i => assign G i (Labels.Taylor.paint u (A i))) _ = _
  simp_rw [fit_paint]; exact (pigment_action u _ p).symm.trans (congr_arg _ (h u))

lemma chain (h : d ≤ l) : shellSector G d ≤ shellSector G l := fun _ hp => sector.mpr
  ⟨restrictSupport_mono ℂ (show {b | degree (G:=G) b ≤ d} ⊆ {b| degree b ≤ l} from fun _ ht => le_trans ht h)
    (sector.mp hp).1,(sector.mp hp).2⟩

/- Convenient homogeneous component results for later Ward tests. -/


lemma commuting {σ τ M : Type*} [AddCommMonoid M] (a : σ → M) (b : τ → M)
    (L : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ) (H : ∀ i, IsWeightedHomogeneous b (L (X i)) (a i))
    (p : MvPolynomial σ ℂ) (k : M) : weightedHomogeneousComponent b k (L p) = L (weightedHomogeneousComponent a k p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial s c =>
    have ht := bounded_grade a b L H s c
    have hp := isWeightedHomogeneous_monomial a s c (m := Finsupp.weight a s) rfl
    by_cases hx : k=Finsupp.weight a s
    · subst k; rw [ht.weightedHomogeneousComponent_same,hp.weightedHomogeneousComponent_same]
    rw [ht.weightedHomogeneousComponent_ne k hx,hp.weightedHomogeneousComponent_ne k hx,map_zero]


end YM.Maxwell.Free
