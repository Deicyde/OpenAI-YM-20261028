import YM.Next.FOUNDATIONS.LinkBounds
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Filters

/-! # Polarization of labels on Snap and the two scalings -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Labels Work Function Filter Tensor Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {d : ℕ}

def stretch (t : ℝ) : Module.End ℝ (Snap G d) := LinearMap.pi fun i : Level d =>
    t^(i.val+2) • LinearMap.proj (R:=ℝ) i

lemma dilated (t : ℝ) (A : Snap G d) : expand d (stretch t A) = scaleJet (expand d A) t := by
  funext i; unfold expand scaleJet
  split <;> rename_i h <;> simp [stretch,h]

lemma read_weight {m : ℕ × ℕ} {p : Label G d} (hp : p ∈ Grade m) (J : Jet G) (t : ℝ) :
    read (scaleJet J t) p.val = t^m.1 • read J p.val := by
  classical
  have hv : MvPolynomial.IsWeightedHomogeneous generation p.val m.1 := by
    intro q hq
    change height q = _
    apply (congrArg Prod.fst (weight_slot q)).symm.trans
    exact congr_arg Prod.fst (show Finsupp.weight bidegree q = m from (pure_grade _ _).1 hp hq) -- weight_slot
  have he (n : Key G →₀ ℕ) (c : ℂ) : read (scaleJet J t) (MvPolynomial.monomial n c) =
      t^(height n) • read J (MvPolynomial.monomial n c) := by
    simp only [Labels.read, MvPolynomial.aeval_monomial, Algebra.algebraMap_self,RingHom.id_apply,
      Complex.real_smul, Complex.ofReal_pow,Finsupp.prod,coord_scales,mul_pow,← pow_mul]
    simp_rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
    unfold height; rw [Finsupp.weight_apply]; simp only [Finsupp.sum, smul_eq_mul]
    simp_rw [mul_comm (generation (G:=G) _) (n _)]; ring
  have hs := p.val.as_sum
  rw [hs,map_sum,map_sum,Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [he,height,hv (MvPolynomial.mem_support_iff.mp hi)]

/-- Actual label evaluated on the Snap space (as real variables; ℂ output). -/
def tally (p : Label G d) (A : Snap G d) := Labels.read (expand d A) p.val

lemma tally_smooth (p : Label G d) (n : WithTop ℕ∞) : ContDiff ℝ n (tally p) := by
  suffices h : ∀ r : Pol G, ContDiff ℝ n (fun A : Snap G d => read (expand d A) r) from h _
  intro r
  induction r using MvPolynomial.induction_on with
  | C a => simp only [Labels.read,MvPolynomial.aeval_C]; exact contDiff_const
  | add u v hu hv => simp only [map_add]; exact hu.add hv
  | mul_X v i hv =>
    simp only [map_mul,Labels.read,MvPolynomial.aeval_X]
    apply hv.mul
    by_cases h : i.1 < d-1
    · let L : Snap G d →ₗ[ℝ] ℝ := ((axes G i.1).coord i.2).comp (LinearMap.proj (φ:=fun k : Level d => Taylor G k.val) (R:=ℝ) ⟨i.1,h⟩)
      simp_rw [Labels.coord,expand,dif_pos h]
      change ContDiff ℝ n (Complex.ofRealCLM ∘ L.toContinuousLinearMap)
      exact Complex.ofRealCLM.contDiff.comp L.toContinuousLinearMap.contDiff
    simp_rw [Labels.coord,expand,dif_neg h]; exact contDiff_const

lemma tally_slot {m : ℕ × ℕ} {p : Label G d} (hp : p ∈ Grade m) (A : Snap G d) (t : ℝ) :
    tally p (t • A) = t^m.2 • tally p A := by
  unfold tally
  rw [← read_pure (expand d A) hp]
  refine congr_arg (fun J : Jet G => read J p.val) (funext fun i => ?_)
  unfold expand; split <;> rename_i h <;> simp [h]

lemma tally_stretch {m : ℕ × ℕ} {p : Label G d} (hp : p ∈ Grade m) (A : Snap G d) (t : ℝ) :
    tally p (stretch t A) = t^m.1 • tally p A := by rw [tally,dilated,read_weight hp]; rfl

lemma tally_invariant (p : Label G d) (A : Snap G d) (u : G.El) : tally p (Cast u A) = tally p A := by
  have hx : expand d (Cast u A) = colored u (expand d A) := by
    funext i; unfold expand colored; split <;> rename_i h <;> simp [Cast,h]
  unfold tally; rw [hx,p.property.2 (expand d A) u] -- A should expand

/-- Taylor coefficient of order l for p of homogeneous slot degree l. -/
def palette (l : ℕ) (p : Label G d) := Tensor.coeff (tally p) l 0

lemma palette_sym (l : ℕ) (p : Label G d) : Sym (palette l p) := coeff_symm (tally_smooth p _).contDiffAt

set_option synthInstance.maxHeartbeats 50000 in
set_option maxHeartbeats 300000 in
lemma label_leg {m : ℕ × ℕ} {p : Label G d} (hp : p ∈ Grade m) (A : Snap G d) :
    Tensor.diagonal (palette m.2 p) A = tally p A := by
  have hl := iteratedDeriv_on_line (k:=m.2) (tally_smooth p _).contDiffAt A
  rw [Tensor.diagonal, palette, coeff,smul_apply]
  change ((m.2.factorial:ℝ)⁻¹) • Tensor.diagonal _ A = _
  rw [← hl, funext (tally_slot hp A)]
  rw [iteratedDeriv_smul_const (contDiffAt_id.pow m.2), iteratedDeriv_fun_pow_zero, if_pos rfl, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

section Transport
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {l : ℕ}

lemma covariant_pol (B : Tensor.T X ℂ l) (h : Sym B) (T : X →L[ℝ] X) (t : ℝ)
    (hh : ∀ x : X, Tensor.diagonal B (T x) = t • Tensor.diagonal B x) (x : Fin l → X) :
    B (fun i => T (x i)) = t • B x := by
  let C := B.compContinuousLinearMap fun _ => T
  have hc : Sym C := fun v s => h (T ∘ v) s
  have hs : Sym (t • B) := by intro v s; rw [smul_apply,h,smul_apply]
  have he : C = t • B := ext_diag _ _ hc hs (funext fun y => hh y)
  exact congr_arg (fun V : Tensor.T X ℂ l => V x) he -- x
end Transport

lemma painting (l : ℕ) {p : Label G d} {n} (hp : p ∈ Grade (n,l)) (u : G.El) (x : Fin l → Snap G d) :
    palette l p (fun i => Cast u (x i)) = palette l p x := by
  let T : Snap G d →L[ℝ] Snap G d := LinearMap.toContinuousLinearMap (castAction u)
  trans (1:ℝ) • palette l p x
  · refine covariant_pol (palette l p) (palette_sym l p) T _ ?_ x
    intro a
    have hh (a : Snap G d) : Tensor.diagonal (palette l p) a=tally p a := label_leg hp a
    rw [hh,hh,one_smul]; exact tally_invariant p a u
  exact one_smul ..

lemma exposed {m : ℕ × ℕ} {p : Label G d} (hp : p ∈ Grade m) (t : ℝ) (x : Fin m.2 → Snap G d) :
    palette m.2 p (fun i => stretch t (x i)) = t^m.1 • palette m.2 p x := by
  refine covariant_pol (palette m.2 p) (palette_sym _ p) (LinearMap.toContinuousLinearMap (stretch (G:=G) (d:=d) t)) _ ?_ x
  intro a; rw [label_leg hp,label_leg hp]; exact tally_stretch hp a t
end YM.ProjectorNext.Calibration
