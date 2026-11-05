import YM.Next.MAXWELL.Algebra
import YM.Next.MAXWELL.Simple


/-!
# Color Reynolds operator on free labels

Averages are finite polynomials; Haar from the Gauge itself. Use for
obtaining invariant testers and classifying low weights. Do not assume
connectedness of G.El. No norm instance choice needed on the polynomial
algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder

variable {G : Gauge} {j : ℕ}

lemma orient_shade (u v : G.El) (A : TaylorTower G) : shade u (shade v A)=shade (u*v) A := by
  funext i; apply Subtype.ext; funext a b; ext1 x
  exact (G.adjoint_mul u v _).symm

lemma paints_comp (u v : G.El) (p : WickPol G) : pigment v (pigment u p)=pigment (u*v) p := by
  apply equalPol; intro A; rw [pigment_action,pigment_action, pigment_action,orient_shade]

lemma continuous_paint (A : Shell G j) (p : Probe G j) : Continuous fun u => p (castFace u j A) := by
  induction p using leg_probe_induction with
  | vars v c i l => exact (EuclideanSpace.proj c : G.Color →L[ℝ] ℝ).continuous.comp (adj_cont (G:=G) _)
  | zero => exact continuous_const
  | add p q hp hq => exact hp.add hq
  | smul t p hp => exact hp.const_mul _

section Orbit
private def Orbit (u : G.El → WickPol G) := ∃ (ι : Type) (_ : Fintype ι) (p : ι → WickPol G) (c : ι → G.El → ℂ),
    (∀ i, Continuous (c i)) ∧ ∀ x, u x=∑ i, c i x • p i

private lemma orbit_const (p : WickPol G) : Orbit (fun _ => p) := ⟨Unit,inferInstance,fun _ => p, fun _ _ => 1,
  fun _ => continuous_const, fun _ => by simp⟩
private lemma orbit_add {u v : G.El→ WickPol G} (H : Orbit u) (K : Orbit v) : Orbit (u+v) := by
  classical
  obtain ⟨ι,I,p,c,h,ht⟩ := H
  obtain ⟨σ,S,q,d,w,hv⟩ := K
  refine ⟨ι⊕σ,inferInstance,Sum.elim p q,Sum.elim c d,fun i => ?_,fun x => ?_⟩
  · cases i <;> simp [h,w]
  rw [Fintype.sum_sum_type]; exact congr_arg₂ (·+·) (ht x) (hv x)
private lemma orbit_mul {u v : G.El→ WickPol G} (H : Orbit u) (K : Orbit v) : Orbit (u*v) := by
  classical
  obtain ⟨ι,I,p,c,h,ht⟩ := H
  obtain ⟨σ,S,q,d,w,hv⟩ := K
  refine ⟨ι×σ,inferInstance,fun i => p i.1*q i.2, fun i => c i.1 * d i.2,fun i => (h _).mul (w _),fun x => ?_⟩
  rw [Fintype.sum_prod_type]; simp_rw [Pi.mul_apply,ht,hv,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm, smul_smul]

private theorem orbit (p : WickPol G) : Orbit fun u : G.El => pigment u p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp_rw [pigment,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq]; exact orbit_const _
  | add p q hp hq => simp_rw [map_add]; exact orbit_add hp hq
  | mul_X p i hp =>
    simp_rw [map_mul]; apply orbit_mul hp
    let e (j : Fin (legDim G i.1)) : Slot G := ⟨i.1,j⟩
    refine ⟨Fin _,inferInstance,fun j => MvPolynomial.X (e j),fun j u => (coordinateLeg i (castFace u _ (frame G _ j)) : ℂ),
      fun i => Complex.continuous_ofReal.comp (continuous_paint _ _),fun x => ?_⟩
    dsimp only; rw [pigment,MvPolynomial.aeval_X,symbol]; refine Finset.sum_congr rfl fun j _ => MvPolynomial.C_mul' ..

lemma hue_continuous (p : WickPol G) (f : WickPol G →ₗ[ℂ] ℂ) : Continuous fun u => f (pigment u p) := by
  obtain ⟨ι,I,q,g,hg,ht⟩ := orbit p
  simp_rw [ht, map_sum,map_smul]; exact continuous_finsetSum _ fun i _ => (hg i).mul continuous_const

lemma tone_integrable (p : WickPol G) (f : WickPol G →ₗ[ℂ] ℂ) :
    Integrable (fun u => f (pigment u p)) G.probHaar := (hue_continuous p f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma blend (p : WickPol G) : ∃ q, ∀ f : WickPol G →ₗ[ℂ] ℂ, f q=∫ u, f (pigment u p) ∂G.probHaar := by
  obtain ⟨ι,I,q,c,hc,ht⟩ := orbit p
  refine ⟨∑ i,(∫ u,c i u ∂G.probHaar) • q i,fun f => ?_⟩
  simp_rw [ht,map_sum,map_smul,smul_eq_mul];
  rw [integral_finsetSum _]; simp_rw [integral_mul_const]
  exact fun i _ => ((hc i).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def moyenne (G : Gauge) : Module.End ℂ (WickPol G) where
  toFun p := (blend p).choose
  map_add' p q := by
    apply equalPol; intro A; rw [map_add]
    let f := (probe A).toLinearMap
    change f _=f _ + f _
    simp_rw [(blend _).choose_spec f,map_add]; rw [integral_add (tone_integrable p f) (tone_integrable q f)]
  map_smul' c p := by
    apply equalPol; intro A; rw [map_smul]
    let f := (probe A).toLinearMap
    change f _=c • f _
    simp_rw [(blend _).choose_spec f,map_smul,integral_smul]

lemma blended (p : WickPol G) (f : WickPol G →ₗ[ℂ] ℂ) :
    f (moyenne G p) = ∫ u, f (pigment u p) ∂G.probHaar := (blend p).choose_spec _

def Painted (p : WickPol G) := ∀ u : G.El, pigment u p=p

theorem paints_self {p : WickPol G} (H : Painted p) : moyenne G p=p := by
  apply equalPol; intro A
  let f := (probe A).toLinearMap
  change f _ = f _; rw [blended]; simp_rw [show ∀ u, pigment u p=p from H]; simp

theorem painted_moy (p : WickPol G) : Painted (moyenne G p) := by
  intro v; apply equalPol; intro A
  rw [pigment_action]
  let f := (probe A).toLinearMap
  let L := (probe (shade v A)).toLinearMap
  change L _=f _; rw [blended,blended]
  simp_rw [show ∀ u, L (pigment u p) = f (pigment (u*v) p) from fun u =>
    (pigment_action v _ _).symm.trans (congr_arg _ (paints_comp ..))]
  exact integral_mul_right_eq_self (μ:=G.probHaar) (fun u => f (pigment u p)) v

theorem paints_fact {p : WickPol G} (H : Painted p) (q : WickPol G) : moyenne G (q*p) = moyenne G q*p := by
  apply equalPol; intro A; rw [map_mul (probe A)]
  let f := (probe A).toLinearMap
  change f _=f _ * f _; rw [blended,blended]
  simp_rw [map_mul,show ∀ u, pigment u p=p from H,show ∀ p q, f (p*q)=f p*f q from fun p q => map_mul (probe A) p q, integral_mul_const]
end Orbit
end YM.Maxwell.Free
