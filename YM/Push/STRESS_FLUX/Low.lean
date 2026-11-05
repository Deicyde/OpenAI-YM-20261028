import YM.Next.FOUNDATIONS.SU2
import YM.Push.STRESS_FLUX.Color

/-!
Elementary low-weight representation on actual radial jets, including all covariance
rules on the bilinear terms. No assumption about free equations or separated detection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Labels Function Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge}

structure Low (G : Gauge) where
  c : ℂ
  l : Jet G →ₗ[ℝ] ℂ
  sq : Taylor G 0 →ₗ[ℝ] Taylor G 0 →ₗ[ℝ] ℂ
  mix : Taylor G 0 →ₗ[ℝ] Taylor G 1 →ₗ[ℝ] ℂ

def Low.eval (A : Low G) (J : Jet G) := A.c + A.l J + A.sq (J 0) (J 0) + A.mix (J 0) (J 1)
def Low.Sym (A : Low G) := ∀ x y, A.sq x y = A.sq y x

lemma peel_weight {M : Key G →₀ ℕ} (h : M ≠ 0) :
    ∃ i : Key G, ∃ N : Key G →₀ ℕ, M = Finsupp.single i 1 + N ∧ height M = generation i + height N := by
  obtain ⟨i,hi⟩ : ∃ i : Key G, 1 ≤ M i := by
    by_contra! hh
    exact h (Finsupp.ext fun i => (Nat.lt_one_iff.mp (hh i) :))
  obtain ⟨N,hN⟩ := exists_add_of_le (Finsupp.single_le_iff.mpr hi)
  exact ⟨i,N,hN,by simp [hN,height, Finsupp.weight_single]⟩

private def atom (i : Key G) : Taylor G i.1 →ₗ[ℝ] ℂ := Complex.ofRealAm.toLinearMap.comp ((axes G i.1).coord i.2)
private def molecule (i j : Key G) : Taylor G i.1 →ₗ[ℝ] Taylor G j.1 →ₗ[ℝ] ℂ :=
  (LinearMap.mul ℝ ℂ).compl₁₂ (atom i) (atom j)

private lemma monomial_low {d : ℕ} (hd : d ≤ 5) (M : Key G →₀ ℕ) (h : height M ≤ d) :
    ∃ A : Low G, (d ≤ 4 → A.mix = 0) ∧ ∀ J, read J (MvPolynomial.monomial M 1) = A.eval J := by
  rcases eq_or_ne M 0 with rfl|h0
  · exact ⟨⟨1,0,0,0⟩,fun _ => rfl,fun J => by simp [Low.eval, Labels.read]⟩
  obtain ⟨i,N,hN,hi⟩ := peel_weight h0
  rcases eq_or_ne N 0 with ht|ht
  · rw [ht,add_zero] at hN
    refine ⟨⟨0,(atom i).comp (LinearMap.proj i.1),0,0⟩,fun _ => rfl,fun J => ?_⟩
    rw [hN]
    change read J (MvPolynomial.X i) = _
    simp only [Low.eval,Labels.read, MvPolynomial.aeval_X, LinearMap.zero_apply, add_zero,zero_add]; rfl
  obtain ⟨j,K,hK,hj⟩ := peel_weight ht
  have he : K=0 := by
    by_contra! he; obtain ⟨a,b,-,hb⟩ := peel_weight he; unfold generation at *; omega
  rw [he,add_zero] at hK
  rw [hN,hK,show MvPolynomial.monomial _ 1 = (MvPolynomial.X i : Pol G)*MvPolynomial.X j by
    simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
  simp only [Labels.read,map_mul,MvPolynomial.aeval_X]
  unfold generation at hi hj
  obtain ⟨ni,i⟩ := i; obtain ⟨nj,j⟩ := j
  change height M = ni+2+height N at hi; change height N=nj+2+_ at hj
  have hc : ni+nj=0 ∨ (ni=0 ∧ nj=1 ∧ d=5) ∨ (ni=1 ∧ nj=0 ∧ d=5) := by omega
  rcases hc with hh|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · have := Nat.eq_zero_of_add_eq_zero_right hh
    have := Nat.eq_zero_of_add_eq_zero_left hh
    subst ni nj
    refine ⟨⟨0,0,molecule ⟨0,i⟩ ⟨0,j⟩,0⟩,fun _ => rfl,fun J => ?_⟩
    simp only [Low.eval, LinearMap.zero_apply, zero_add,add_zero]; rfl
  · refine ⟨⟨0,0,0,molecule ⟨0,i⟩ ⟨1,j⟩⟩,by omega,fun J => ?_⟩
    simp only [Low.eval, LinearMap.zero_apply,zero_add]; rfl
  refine ⟨⟨0,0,0,molecule ⟨0,j⟩ ⟨1,i⟩⟩,by omega,fun J => ?_⟩
  simp only [Low.eval, LinearMap.zero_apply,zero_add]; rw [mul_comm]; rfl

private lemma has_low {d : ℕ} (hd : d≤5) (p : Pol G) (h : p ∈ limited G d) :
    ∃ A : Low G, (d ≤ 4 → A.mix = 0) ∧ ∀ J, read J p = A.eval J := by
  rw [limited, MvPolynomial.restrictSupport_eq_span] at h
  induction h using Submodule.span_induction with
  | mem _ h => obtain ⟨M,hM,rfl⟩ := h; exact monomial_low hd M hM
  | zero => exact ⟨⟨0,0,0,0⟩,fun _ => rfl,fun J => by simp [Low.eval]⟩
  | add p q _ _ hp hq =>
    obtain ⟨x,hx,H⟩ := hp; obtain ⟨y,hy,L⟩ := hq
    refine ⟨⟨x.c+y.c,x.l+y.l,x.sq+y.sq,x.mix+y.mix⟩,fun he => by simp [hx he,hy he],fun J => ?_⟩
    simp [Low.eval,map_add,H,L]; abel
  | smul a p _ hp =>
    obtain ⟨x,hx,H⟩ := hp
    refine ⟨⟨a*x.c,a • x.l,a • x.sq,a • x.mix⟩,fun he => by simp [hx he],fun J => ?_⟩
    simp [Low.eval,H,mul_add]

theorem low {d : ℕ} (hd : d ≤ 5) (p : Label G d) :
    ∃ A : Low G, A.Sym ∧ (d ≤ 4 → A.mix=0) ∧ ∀ J, read J p.val = A.eval J := by
  obtain ⟨x,hx,H⟩ := has_low hd p.val p.property.1
  refine ⟨{ x with sq := (2:ℂ)⁻¹ • (x.sq+x.sq.flip) }, (fun a b => by
    change (2:ℂ)⁻¹ * (_ + _) = (2:ℂ)⁻¹ * (_ + _); rw [add_comm]; rfl),hx,fun J => ?_⟩
  simp [H,Low.eval]; ring

def axesMove (e : ∀ i, Module.End ℝ (Taylor G i)) : Jet G →ₗ[ℝ] Jet G :=
  LinearMap.pi fun i => (e i).comp (LinearMap.proj i)

def Low.comp (A : Low G) (L : ℂ →ₗ[ℝ] ℂ) (e : ∀ i, Module.End ℝ (Taylor G i)) : Low G where
  c := L A.c
  l := L ∘ₗ A.l ∘ₗ axesMove e
  sq := (A.sq.compr₂ L).compl₁₂ (e 0) (e 0)
  mix := (A.mix.compr₂ L).compl₁₂ (e 0) (e 1)

theorem Low.comp_sym {A : Low G} (h : A.Sym) (L e) : (A.comp L e).Sym := fun x y => congr_arg L (h (e 0 x) (e 0 y))
theorem Low.comp_eval (A : Low G) (L e) (J) : (A.comp L e).eval J = L (A.eval (axesMove e J)) := by
  unfold eval; simp only [map_add]; rfl

private lemma unique_sq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hA : ∀ x y, A x y = A y x) (hB : ∀ x y, B x y = B y x)
    (H : ∀ v, A v v = B v v) : A=B := by
  apply LinearMap.ext₂
  intro x y
  have h := H (x+y)
  simp only [map_add,LinearMap.add_apply, H x,H y, hA y x,hB y x] at h
  linear_combination h / 2

lemma Low.ext (A B : Low G) (hA : A.Sym) (hB : B.Sym) (h : ∀ J, A.eval J = B.eval J) : A=B := by
  have hc : A.c=B.c := by simpa [Low.eval] using h 0
  have hL : A.l=B.l := by
    ext1 J; have he := h (-J)
    simp only [Low.eval,hc, map_neg, Pi.neg_apply, LinearMap.neg_apply, neg_neg] at h he
    linear_combination ((h J) - he) / 2
  have hq (J : Jet G) := h J
  simp only [Low.eval,hc,hL,add_assoc,add_right_inj] at hq
  have hS : A.sq=B.sq := unique_sq _ _ hA hB (fun v => by simpa using hq (Pi.single 0 v))
  have hM : A.mix=B.mix := LinearMap.ext₂ fun x y => by
    simpa [hS] using hq (Pi.single 0 x + Pi.single 1 y)
  cases A; cases B; congr

lemma Low.covariance {d : ℕ} {p : Label G d} {A : Low G} (hs : A.Sym) (he : ∀ J, read J p.val = A.eval J) (g : G.El) :
    A.comp LinearMap.id (fun _ => Taylor.paint g) = A := by
  apply Low.ext _ _ (A.comp_sym hs _ _) hs
  exact fun J => (A.comp_eval ..).trans (by
    change A.eval (colored g J)=A.eval J; rw [← he, ← he, p.property.2])

/-- A rank-one operator in color applied to a Taylor column stays radial. -/
private def paintOne (j : ℕ) (c : G.ColorIndex) (J : Jet G) (x : G.Color) : Taylor G j :=
  let L := (EuclideanSpace.proj c).smulRight x
  ⟨fun i => L.compContinuousMultilinearMap ((J j).val i), by
    refine ⟨fun i u s => congr_arg L ((J j).property.1 i u s),fun z => ?_⟩
    change ∑ i, z i • L ((J j).value i z) = 0
    rw [← map_zero L, ← Taylor.radial_value (J j) z,map_sum]; simp only [map_smul] ⟩

private def paintColumn (c : G.ColorIndex) (J : Jet G) : G.Color →ₗ[ℝ] Jet G where
  toFun x j := paintOne j c J x
  map_add' x y := by
    funext j; apply Taylor.value_ext; funext i z
    exact smul_add (((J j).value i z) c) x y
  map_smul' a x := by
    funext j; apply Taylor.value_ext; funext i z
    exact smul_comm (((J j).value i z) c) a x

lemma Low.linear_invariant {A : Low G} (H : G.Simple)
    (h : ∀ g, A.comp LinearMap.id (fun _ => Taylor.paint g) = A) : A.l=0 := by
  have he (c : G.ColorIndex) (J : Jet G) : A.l ∘ₗ paintColumn c J = 0 := by
    refine StressFlux.linear_invariant H _ fun g x => ?_
    have hf : paintColumn c J (G.adjoint g x) = axesMove (fun _ => Taylor.paint g) (paintColumn c J x) := by
      funext j; apply Taylor.value_ext; funext i z
      exact (map_smul (G.adjoint g) _ x).symm
    exact (congr_arg A.l hf).trans (congr_arg (fun B => Low.l B (paintColumn c J x)) (h g))
  apply LinearMap.ext
  intro J
  let b := EuclideanSpace.basisFun G.ColorIndex ℝ
  suffices ht : (∑ i, paintColumn i J (b i)) = J by
    change A.l J=0; rw [← ht,map_sum]
    exact Finset.sum_eq_zero (fun i _ => LinearMap.congr_fun (he i J) (b i))
  funext j; apply Taylor.value_ext; funext i z
  simp only [Finset.sum_apply,Taylor.value,AddSubmonoidClass.coe_finsetSum, Tensor.diagonal, _root_.sum_apply]
  exact b.sum_repr ((J j).value i z)

end YM.StressFlux
