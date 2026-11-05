import YM.Bid.Source
import YM.Work.G06.TurnSlot

/-!
# G06: projection through Reynolds averaging

On functions, `pull` acts here by precomposition. It includes the change of
oriented bonds with inverse on a negative direction, and the origin remains
fixed. Match it with the inverse action on the input to the section. This
file proves the laws as identities of functions. Still need to package the
result by polynomial expressions with stencil/support and lower degree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.G06
open Lattice Labels RG Wilson Source Drops Bid Function
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {d : ℕ} {H : Hol G}

section calculus
variable {f : CoverConfig G → ℂ} {p : Label G d}

lemma projects_smul (h : Projects H p f) (c : ℂ) : Projects H (c • p) (c • f) := by
  intro J
  obtain ⟨ha,hb,he⟩ := h J
  dsimp only
  simp only [Pi.smul_apply,SetLike.val_smul,map_smul]
  refine ⟨ha.const_smul c,hb.const_smul c, fun k hk => ?_⟩
  simp only [iteratedDeriv_fun_const_smul_field, he k hk]

lemma projects_sum {ι : Type*} (p : ι → Label G d) (f : ι → CoverConfig G → ℂ) (S : Finset ι)
    (h : ∀ i ∈ S, Projects H (p i) (f i)) : Projects H (∑ i ∈ S,p i) (∑ i ∈ S, f i) := by
  intro J
  let a := fun (i : ι) t => f i (H.links d J t)
  let b := fun (i : ι) t => read (scaleJet J t) (p i).val
  have ha : ∀ i ∈ S, ContDiffAt ℝ d (a i) 0 := fun i hi => (h i hi J).1
  have hb : ∀ i ∈ S, ContDiffAt ℝ d (b i) 0 := fun i hi => (h i hi J).2.1
  dsimp only
  simp only [Finset.sum_apply,Submodule.coe_sum,map_sum]
  change ContDiffAt ℝ d (fun t => ∑ i ∈ S,a i t) 0 ∧ ContDiffAt ℝ d (fun t => ∑ i ∈ S,b i t) 0 ∧ _
  refine ⟨ContDiffAt.sum ha,ContDiffAt.sum hb,fun k hk => ?_⟩
  have hkd : (k : WithTop ℕ∞) ≤ d := by exact_mod_cast hk
  change iteratedDeriv k (fun t => ∑ i ∈ S, a i t) 0 = iteratedDeriv k (fun t => ∑ i ∈ S, b i t) 0
  rw [iteratedDeriv_fun_sum (fun i hi => (ha i hi).of_le hkd),
      iteratedDeriv_fun_sum (fun i hi => (hb i hi).of_le hkd)]
  exact Finset.sum_congr rfl fun i hi => (h i hi J).2.2 k hk

lemma projects_pull (a : swirls H) (h : Projects H p f) (s : Signed) :
    Projects H (tensor s.ortho p) (f ∘ pull s 0) := by
  intro J
  let M : Jet G := changedJet (fun _ => Taylor.turn s.ortho⁻¹) J
  have hg (t : ℝ) : read (scaleJet J t) (tensor s.ortho p).val =
      read (scaleJet M t) p.val := by
    change read (scaleJet J t) (changed _ p.val)=_
    rw [eval_changed]; apply congr_arg (fun Z => read Z p.val)
    funext i; simp [M,scaleJet,changedJet]
  dsimp only
  simp only [Function.comp_apply,a s,hg]
  exact h M
end calculus

/-- Linear extension in the given reference coordinates. -/
def assemble {m : ℕ} {F : Frame G d} (P : F.Index → Pose G m) : F.Coeff →ₗ[ℂ] Pose G m where
  toFun x := ∑ i,x i • P i
  map_add' x y := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z x := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_assoc]

variable {F : Frame G d} {m : ℕ} (B : Fin m → Slot) (P : F.Index → Pose G m)

def beforeTurn (c : F.Coeff) : CoverConfig G → ℂ := lumin (assemble (F:=F) P c) ∘ mapped B

lemma before_eq (c : F.Coeff) : beforeTurn B P c =
    ∑ i : F.Index, c i • (lumin (P i) ∘ mapped B) := by
  funext U
  simp only [beforeTurn,Function.comp_apply,lumin,assemble,LinearMap.coe_mk,
    AddHom.coe_mk,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply]

lemma before_projects (h : Cumuli H d F B P) (c : F.Coeff) :
    Projects H (F.coords.symm c) (beforeTurn B P c) := by
  rw [before_eq]
  have hl : (∑ i,c i • F.basis i) = F.coords.symm c := by
    have he := F.basis.sum_repr (F.coords.symm c)
    change (∑ i,F.coords (F.coords.symm c) i • F.basis i) = _ at he
    simpa using he
  rw [← hl]
  exact projects_sum _ _ _ fun i _ => projects_smul (h.2.2.2.1 i) _

def term (c : F.Coeff) (s : Signed) :=
    beforeTurn B P (F.act s.ortho⁻¹ c) ∘ pull s 0

lemma term_projects (a : swirls H) (h : Cumuli H d F B P) (c : F.Coeff) (s : Signed) :
    Projects H (F.coords.symm c) (term B P c s) := by
  have ht := projects_pull a (before_projects B P h (F.act s.ortho⁻¹ c)) s
  have hs : tensor s.ortho (F.coords.symm (F.act s.ortho⁻¹ c))=F.coords.symm c := by
    simp only [Frame.act, LinearEquiv.coe_coe,LinearMap.comp_apply,LinearEquiv.symm_apply_apply]
    rw [← tensor_mul,mul_inv_cancel,tensor_one]
  rwa [hs] at ht

/-- Share factor fixed independent of stage, degree, U. -/
def share : ℂ := (Fintype.card Signed : ℂ)⁻¹

lemma share_sum {M : Type*} [AddCommGroup M] [Module ℂ M] (x : M) :
    share • (∑ _s : Signed, x) = x := by
  have hp : (Fintype.card Signed : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  simp only [share,inv_mul_cancel₀ hp,one_smul]

def averaged (c : F.Coeff) : CoverConfig G → ℂ := share • ∑ s : Signed, term B P c s

theorem averaged_projects (a : swirls H) (h : Cumuli H d F B P) (c : F.Coeff) :
    Projects H (F.coords.symm c) (averaged B P c) := by
  have he := projects_smul (projects_sum (fun _ : Signed => F.coords.symm c) (term B P c) Finset.univ fun s _ => term_projects B P a h c s) share
  simpa only [share_sum, averaged] using he

theorem averaged_unit (h : Cumuli H d F B P) : averaged B P F.e0 = 1 := by
  have he (s : Signed) : F.act s.ortho⁻¹ F.e0 = F.e0 := by
    rw [← F.coords_unit,F.act_coords]; congr 1
    apply Subtype.ext; exact (rotated (G := G) _).map_one
  have ht (s : Signed) : term B P F.e0 s = 1 := by
    unfold term
    rw [he,before_eq]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _)]
    · funext U
      simp [Frame.e0, h.1, lumin]
    intro b _ hb; simp [Frame.e0,Pi.single_eq_of_ne hb]
  simp only [averaged,ht,share_sum]

theorem averaged_gauge (h : Cumuli H d F B P) (c : F.Coeff) : GaugeInvariant (averaged B P c) := by
  have hb (x : F.Coeff) : GaugeInvariant (beforeTurn B P x) := by
    intro t U
    have hx : mapped B (Lattice.gauge t U) = rotates (t 0) (mapped B U) :=
      funext fun i => slot_gauge (B i) t U
    rw [before_eq]; simp only [Finset.sum_apply,Pi.smul_apply,comp_apply,hx,h.2.1]
  intro t U
  simp only [averaged,Pi.smul_apply,Finset.sum_apply,term,Function.comp_apply,
    pull_gauge_zero]
  apply congr_arg (fun z : ℂ => share • z)
  exact Finset.sum_congr rfl fun _ _ => hb _ _ _

theorem averaged_Hpart (s : Signed) (c : F.Coeff) (U : CoverConfig G) :
    averaged B P c (pull s 0 U) = averaged B P (F.act s.ortho c) U := by
  have he (t : Signed) : term B P c t (pull s 0 U) = term B P (F.act s.ortho c) (s*t) U := by
    simp only [term, comp_apply,pull_pull,affine,Signed.act_zero,add_zero]
    rw [← Frame.act_mul,show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..]
    rw [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  simp only [averaged,Pi.smul_apply, Finset.sum_apply,he]
  have hh := Equiv.sum_comp (Equiv.mulLeft s) (fun t => term B P (F.act s.ortho c) t U)
  exact congr_arg (fun x : ℂ => share • x) hh

private lemma share_real : star share = share := by simp [share]

theorem averaged_bar (h : Cumuli H d F B P) (c : F.Coeff) (U : CoverConfig G) :
    averaged B P (star c) U = star (averaged B P c U) := by
  have hv (x : F.Coeff) : F.coords (realBar (F.coords.symm x)) = star x :=
    funext fun _ => F.conj_basis ..
  have ht (s : Ortho) : F.act s (star c) = star (F.act s c) := by
    rw [← hv c, ← hv (F.act s c)]; simp [Frame.act]
  have hb (s : Signed) : term B P (star c) s U = star (term B P c s U) := by
    simp only [term, before_eq, ht, Function.comp_apply,Finset.sum_apply,Pi.smul_apply,
      Pi.star_apply,star_sum,star_smul,h.2.2.1]
  simp only [averaged,Pi.smul_apply, Finset.sum_apply, hb,star_smul,share_real,star_sum]
end YM.Work.G06
