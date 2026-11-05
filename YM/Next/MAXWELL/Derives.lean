import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import YM.Next.MAXWELL.Algebra
import YM.Next.MAXWELL.Angular
import YM.Next.MAXWELL.Recurse



/-!
# Wick derivations of the three Ward charges (normalized)

As actual derivations of unbounded Wick polynomials; restrict to
bounded sectors before using in the axioms. Use Euler later for the
free-vector tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open MvPolynomial hiding monomial
open WaveOn
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l d : ℕ}

abbrev Engine (G : Gauge) (l : ℕ) := (j : ℕ) → Probe G j →ₗ[ℝ] Probe G (j+l)

def rewired (T : Engine G l) : Derivation ℂ (WickPol G) (WickPol G) :=
  MvPolynomial.mkDerivation ℂ fun i : Slot G => symbol _ (T _ (coordinateLeg i))

lemma symbol_linear (j : ℕ) : ∃ L : Probe G j →ₗ[ℝ] WickPol G, (fun p => L p) = symbol j := by
  refine ⟨{ toFun := symbol j
            map_add' := ?_
            map_smul' := ?_ },rfl⟩
  · intro p q; apply equalPol; intro A; simp only [symbol_test,map_add,LinearMap.add_apply,Complex.ofReal_add]
  intro t p; apply equalPol; intro A; rw [symbol_test]
  change ((↑(t*p _) : ℂ)) = probe A (t • symbol _ p)
  have ht := map_smul ((probe A).toLinearMap.restrictScalars ℝ) t (symbol j p)
  change probe A _ = t • probe A _ at ht
  rw [ht,symbol_test]; simp

lemma rewired_symbol (T : Engine G l) (p : Probe G j) :
    rewired T (symbol j p)=symbol (j+l) (T j p) := by
  classical
  obtain ⟨L,hL⟩ := symbol_linear (G:=G) j
  obtain ⟨Q,hQ⟩ := symbol_linear (G:=G) (j+l)
  let D : WickPol G →ₗ[ℝ] WickPol G := (rewired T).toLinearMap.restrictScalars ℝ
  change D (symbol j p) = _
  rw [← hL, ← hQ]
  change D (L p) = Q _
  rw [probe_expansion p]; simp_rw [map_sum,map_smul]
  apply Finset.sum_congr rfl; intro i _; congr 1
  have hs := symbol_coordinate (G:=G) ⟨j,i⟩
  change symbol j ((frame G j).coord i)= _ at hs
  change D (L ((frame G j).coord i))= Q _
  rw [congr_fun hL,hs,congr_fun hQ]; exact MvPolynomial.mkDerivation_X ..

lemma rewire_pure (T : Engine G l) (p : Slot G →₀ ℕ) (c : ℂ) :
    IsWeightedHomogeneous scaleW (rewired T (MvPolynomial.monomial p c)) (degree p+l) := by
  classical
  rw [rewired,mkDerivation_monomial,← C_mul']; apply IsWeightedHomogeneous.C_mul
  unfold Finsupp.sum
  apply IsWeightedHomogeneous.sum; intro i hi
  change IsWeightedHomogeneous _ (MvPolynomial.monomial _ _ * _) _
  have hu (q : Probe G (i.1+l)) : IsWeightedHomogeneous scaleW (symbol _ q) (i.1+l+2) :=
    symbol_hom _ (fun i => i+2)
  have hp : Finsupp.single i 1 ≤ p := by
    intro j; by_cases he : j=i
    · subst j; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    simp [Ne.symm he]
  have he : degree p+l=degree (p - Finsupp.single i 1)+(i.1+l+2) := by
    have ht := congr_arg (Finsupp.weight scaleW) (tsub_add_cancel_of_le hp)
    rw [map_add,Finsupp.weight_single] at ht
    simp only [scaleW, one_smul] at ht
    change degree _ + (i.1+2) = degree p at ht; omega
  rw [he]; exact (isWeightedHomogeneous_monomial scaleW _ _ rfl).mul (hu _)

lemma rewire_bound (T : Engine G l) (p : WickPol G) (hp : p ∈ lowerCap G d) :
    rewired T p ∈ lowerCap G (d+l) := by
  rw [lowerCap,MvPolynomial.restrictSupport_eq_span] at hp
  refine Submodule.span_induction (p := fun p _ => rewired T p ∈ _) ?_ ?_ ?_ ?_ hp
  · rintro f ⟨x,hx,rfl⟩
    rw [lowerCap,mem_restrictSupport_iff]; intro i hi; change degree i ≤ d+l
    rw [show degree i=degree x+l from rewire_pure T x 1 (MvPolynomial.mem_support_iff.mp hi)]
    exact Nat.add_le_add_right hx _
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ h k; rw [map_add]; exact Submodule.add_mem _ h k
  intro t y _ k; rw [Derivation.map_smul]; exact Submodule.smul_mem _ _ k

lemma morph_wire (L Q : Engine G l) (u : WickPol G →+* WickPol G) (P : ∀ j, Probe G j → Probe G j)
    (H : ∀ x : ℂ, ∃ q : ℂ, u (C x)=C q) (hp : ∀ j (p : Probe G j), u (symbol j p)=symbol j (P j p))
    (he : ∀ j (p : Probe G j), Q j (P j p)=P (j+l) (L j p)) (p : WickPol G) :
    rewired Q (u p) = u (rewired L p) := by
  induction p using MvPolynomial.induction_on with
  | C a => obtain ⟨q,hq⟩ := H a; simp [hq]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i ih =>
    rw [← symbol_coordinate (G:=G) i]; simp_rw [map_mul, hp, Derivation.leibniz, smul_eq_mul,rewired_symbol,
      map_add,map_mul,hp,he,ih]

lemma preserve_sectors (T : Engine G l) (H : ∀ (u : G.El) (j : ℕ) (p : Probe G j),
    T j (p.comp (castFace u j))=(T j p).comp (castFace u (j+l))) (p : WickPol G) (h : p ∈ shellSector G d) :
    rewired T p ∈ shellSector G (d+l) := by
  rw [sector] at h ⊢
  refine ⟨rewire_bound T p h.1,fun u => ?_⟩
  have he := morph_wire T T (pigment u).toRingHom (fun i p => p.comp (castFace u _))
    (fun x => ⟨x,MvPolynomial.algHom_C ..⟩) (fun _ v => symbol_pigment u v) (H u) p
  change rewired T (pigment u p) = _ at he; rw [h.2] at he; exact he.symm



def glide (G : Gauge) (x : E4) : Engine G 1 := fun _ => raiseLeg x

def wheel (G : Gauge) (s : Ortho.Skew) : Engine G 0 := fun j => angularLeg G j s

def metric (G : Gauge) : Engine G 0 := fun j => ((j:ℝ)+2) • LinearMap.id

lemma glide_holds (x : E4) {p : WickPol G} (h : p ∈ shellSector G d) :
    rewired (glide G x) p ∈ shellSector G (d+1) := by
  refine preserve_sectors _ ?_ p h; intro u j p; ext1 A
  exact congr_arg p (color_lower _ _ _).symm

lemma wheel_holds (s : Ortho.Skew) {p : WickPol G} (h : p ∈ shellSector G d) :
    rewired (wheel G s) p ∈ shellSector G d := by
  refine preserve_sectors (l:=0) (wheel G s) ?_ p h; intro u j p; ext1 A
  change p (castFace u j (derivativeTurn s A))=p (derivativeTurn s (castFace u j A))
  let v := fun t : ℝ => solutionTurn (Ortho.oneParameter s t)⁻¹ A
  let q := p.comp (castFace u j)
  have hh := turn_has s A q
  have ht := turn_has s (castFace u j A) p
  apply hh.unique
  have he (t) : solutionTurn (Ortho.oneParameter s t)⁻¹ (castFace u j A) = castFace u j (v t) := by
    apply Subtype.ext; funext a b; ext1 w
    change turnJ _ _ a b w = G.adjoint u (turnJ _ _ a b w)
    simp_rw [turns_apply,map_sum,map_smul]; rfl
  simp_rw [he] at ht
  exact ht

lemma metric_holds {p : WickPol G} (h : p ∈ shellSector G d) : rewired (metric G) p ∈ shellSector G d := by
  refine preserve_sectors (l:=0) _ ?_ p h; intro u j p; ext1 A; rfl

end YM.Maxwell.Free
