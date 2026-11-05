import YM.Pert.Lattice.Geometry
/-! Dimensions and linear inverses: site FP inverse and full inverted link precision. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice Function
open scoped InnerProductSpace
variable {G : Gauge} {n : Side}
lemma sumM (a : ↥(Mean G n)) : ∑ x : Site n, a.val x = 0 := by
  have ht : (∑ x : Site n, LinearMap.proj (R:=ℝ) x) a.val = 0 := (show _ ∧ _ from a.property).2
  simpa only [LinearMap.sum_apply,LinearMap.proj_apply] using ht
lemma atZ (a : ↥(Orb.Zero G n)) : a.val 0 = 0 := (show _ ∧ _ from a.property).2

def gLin : ↥(EvenSite G n) →ₗ[ℝ] ↥(LinkP G n) where
  toFun f := ⟨grad f.val, fun l => show f.val (-l.1-step l.2) - f.val ((-l.1-step l.2)+ step l.2)=-_ by
    rw [sub_add_cancel, show -l.1-step l.2= -(l.1+step l.2) by abel, f.property _,f.property l.1]; simp [grad]⟩
  map_add' a b := Subtype.ext (funext (fun _ => by dsimp [grad]; abel))
  map_smul' r a := Subtype.ext (funext (fun l => by dsimp; unfold grad; rw [smul_sub]; rfl))

def gZ : ↥(Orb.Zero G n) →ₗ[ℝ] ↥(LinkP G n) := gLin.comp (Submodule.inclusion (show Orb.Zero G n ≤ EvenSite G n from inf_le_left))
def gM : ↥(Mean G n) →ₗ[ℝ] ↥(LinkP G n) := gLin.comp (Submodule.inclusion (show Mean G n ≤ EvenSite G n from inf_le_left))

def dLin : ↥(LinkP G n) →ₗ[ℝ] ↥(Mean G n) where
  toFun a := ⟨divB a.val, ⟨div_even a.val a.property,by simp [LinearMap.mem_ker,LinearMap.sum_apply,sum_div]⟩⟩
  map_add' a b := Subtype.ext (funext (fun _ => by simp [divB,add_sub_add_comm, Finset.sum_add_distrib]))
  map_smul' r a := Subtype.ext (funext (fun _ => by simp [divB,Finset.smul_sum,smul_sub]))

def bridge (G : Gauge) (n : Side) : ↥(Orb.Zero G n) →ₗ[ℝ] ↥(Mean G n) := dLin.comp gZ

lemma div_grad_eq_zero (f : Site n → G.Color) (h : divB (grad f) = 0) (x y) : f x = f y := by
  ext i; apply harmonic_const (fun z => f z i) _ x y; intro a
  have eq : lap f a = -divB (grad f) a := by
    unfold lap divB; rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _
    simp only [grad,sub_add_cancel]; abel
  have ht := congrArg (fun z : G.Color => z i) (eq.trans (by rw [h,Pi.zero_apply,neg_zero]))
  simpa only [lap,WithLp.ofLp_sum,Finset.sum_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,nsmul_eq_mul,Nat.cast_ofNat] using ht

lemma mem_ker_const {a b : ↥(EvenSite G n)} (h : dLin (gLin (n:=n) a) = dLin (gLin b)) : ∃ z : G.Color, ∀ x, (a-b).val x = z := by
  refine ⟨(a-b).val 0,fun x => div_grad_eq_zero (a-b).val ?_ x 0⟩
  apply funext; intro l;
  simpa [dLin,gLin] using congrFun (congrArg Subtype.val (show dLin (gLin (a-b)) = (0:↥(Mean G n)) by simp [h])) l

lemma mean_inj : Injective ((dLin ∘ₗ gM) : ↥(Mean G n) →ₗ[ℝ] ↥(Mean G n)) := by
  intro a b h; have he := mem_ker_const (G:=G) h
  simp only [LinearMap.coe_comp,comp_def,gM] at h
  obtain ⟨z,hz⟩ := mem_ker_const h
  have hv (x : Site n) : (a-b).val x = z := hz x
  obtain rfl : z = 0 := by
    have ht : (Fintype.card (Site n)) • z = 0 := by simpa only [hv,Finset.sum_const,Finset.card_univ] using sumM (a-b)
    have hpos : ((Fintype.card (Site n) : ℝ)) ≠ 0 := by positivity
    rw [← Nat.cast_smul_eq_nsmul ℝ (Fintype.card (Site n)) z] at ht
    exact (smul_eq_zero.mp ht).resolve_left hpos
  exact sub_eq_zero.mp (Subtype.ext (funext hv))

lemma bridge_inj : Injective (bridge G n) := by
  intro a b h
  dsimp only [gZ,bridge,LinearMap.coe_comp,comp_def] at h
  obtain ⟨z,hz⟩ := mem_ker_const h
  have hv (x : Site n) : (a-b).val x = z := hz x
  obtain rfl := (hv 0).symm.trans (atZ (a-b))
  exact sub_eq_zero.mp (Subtype.ext (funext hv))
lemma bridge_surj : Surjective (bridge G n) := by
  intro y
  obtain ⟨x,rfl⟩ := LinearMap.surjective_of_injective mean_inj y
  let a (u : Site n) := x.val u - x.val 0
  let z : ↥(Orb.Zero G n) := ⟨a,⟨fun v => congrArg (·-x.val 0) ((show _ ∧ _ from x.property).1 v),by simp [LinearMap.mem_ker,a]⟩⟩
  refine ⟨z,(congrArg (fun t => dLin t) ?_)⟩
  apply Subtype.ext; funext l; dsimp [gLin,gZ,gM]; change grad a l = grad x.val l; unfold grad a; abel
def bridgeEquiv (G : Gauge) (n : Side) := LinearEquiv.ofBijective (bridge G n) ⟨bridge_inj,bridge_surj⟩

def curL (x : Site n) (i j : Axis) : ↥(LinkP G n) →ₗ[ℝ] G.Color where
  toFun A := cur A.val x i j
  map_add' A B := by dsimp [cur]; abel
  map_smul' r A := by dsimp [cur]; simp [smul_add,smul_sub]

def form (A B : ↥(LinkP G n)) : ℝ :=
  ((∑ x : Site n, ∑ i : Axis, ∑ j : Axis, if i<j then inner ℝ (curL x i j A) (curL x i j B) else 0) +
    ∑ x : Site n, inner ℝ ((dLin A).val x) ((dLin B).val x)) / 2
lemma form_add (A B C : ↥(LinkP G n)) : form (A+B) C = form A C + form B C := by
  unfold form
  simp only [map_add,Submodule.coe_add,inner_add_left,Pi.add_apply]
  have he (p : Prop) [Decidable p] (x y : ℝ) : (if p then x+y else 0) = (if p then x else 0)+(if p then y else 0) := by by_cases hp : p <;> simp [hp]
  simp only [he,Finset.sum_add_distrib]; ring
lemma form_smul (r : ℝ) (A B : ↥(LinkP G n)) : form (r • A) B = r * form A B := by
  unfold form
  simp only [map_smul,Submodule.coe_smul_of_tower,Pi.smul_apply,real_inner_smul_left]
  have he (p : Prop) [Decidable p] (x : ℝ) : (if p then r*x else 0) = r*(if p then x else 0) := by by_cases hp : p <;> simp [hp]
  simp_rw [he]; simp only [← Finset.mul_sum]; ring
lemma form_symm (A B : ↥(LinkP G n)) : form A B = form B A := by
  unfold form; simp only [show ∀ i j k, inner ℝ (curL k i j A) (curL k i j B)=_ from fun i j k => real_inner_comm .., show ∀ x, inner ℝ ((dLin A).val x) ((dLin B).val x)=_ from fun x => real_inner_comm ..]
def formL (G : Gauge) (n : Side) : ↥(LinkP G n) →ₗ[ℝ] Module.Dual ℝ ↥(LinkP G n) :=
  LinearMap.mk₂ ℝ form form_add form_smul (fun A _ _ => by rw [form_symm A,form_add,form_symm _ A,form_symm _ A])
    fun r A B => by rw [form_symm A,form_smul,form_symm B A]; rfl

lemma nonneg_curL (A : ↥(LinkP G n)) (x : Site n) (i j : Axis) : 0 ≤ if i<j then inner ℝ (curL x i j A) (curL x i j A) else 0 := by
  split; · exact real_inner_self_nonneg
  rfl
lemma nonneg_divB (A : ↥(LinkP G n)) (x : Site n) : 0 ≤ inner ℝ ((dLin A).val x) ((dLin A).val x) := real_inner_self_nonneg

lemma form_pos {A : ↥(LinkP G n)} (hA : A≠0) : 0 < form A A := by
  have hf (x : Site n) (i : Axis) := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => nonneg_curL A x i j)
  have hs (x : Site n) := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hf x i))
  have hv := Finset.sum_nonneg (fun x (_ : x ∈ Finset.univ) => hs x)
  have hz := Finset.sum_nonneg (fun x (_ : x ∈ Finset.univ) => nonneg_divB A x)
  by_contra ht; rw [not_lt,form] at ht
  apply hA
  have hzero := add_eq_zero_iff_of_nonneg hv hz |>.1 (le_antisymm (by linarith only [ht]) (add_nonneg hv hz))
  have e1 := Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hs i) |>.1 hzero.1
  have eq (x : Site n) (i j : Axis) (ht : i < j) : curL x i j A=0 := by
    have ex := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hf x i)).1 (e1 x (Finset.mem_univ _)) i (Finset.mem_univ _)
    have ey := (Finset.sum_eq_zero_iff_of_nonneg (fun j hi => nonneg_curL A x i j)).1 ex j (Finset.mem_univ _)
    rw [if_pos ht] at ey; exact inner_self_eq_zero.mp ey
  have he' (x : Site n) (i j : Axis) : cur A.val x i j=0 := by
    rcases lt_trichotomy i j with h|h|h
    · exact eq x i j h
    · subst h; unfold cur; abel
    have hv : cur A.val x i j = -cur A.val x j i := by unfold cur; abel
    rw [hv]; change -(curL x j i A)=0; simp [eq x j i h]
  exact Subtype.ext (kernel A.val A.property he' (fun x => inner_self_eq_zero.mp
       ((Finset.sum_eq_zero_iff_of_nonneg (fun x _ => nonneg_divB A x)).1 hzero.2 _ (Finset.mem_univ x))))
lemma form_nonneg (A : ↥(LinkP G n)) : 0≤ form A A := by
  by_cases ht : A=0; · show 0 ≤ formL G n A A; simp [ht]
  exact (form_pos ht).le
lemma formL_inj : Injective (formL G n) := by
  rw [← LinearMap.ker_eq_bot]; apply bot_unique; rintro v hv
  have he : form v v=0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) v
  by_contra ht; exact (form_pos (show v ≠ 0 from ht)).ne' he

def kernelEquiv (G : Gauge) (n : Side) : ↥(LinkP G n) ≃ₗ[ℝ] Module.Dual ℝ ↥(LinkP G n) :=
  LinearEquiv.ofBijective (formL G n) ⟨formL_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 formL_inj⟩ where finally
  simp

def covar (a b : Module.Dual ℝ ↥(LinkP G n)) : ℝ := b ((kernelEquiv G n).symm a)
lemma covar_formula (a b : Module.Dual ℝ ↥(LinkP G n)) : covar a b = form ((kernelEquiv G n).symm a) ((kernelEquiv G n).symm b) := by
  rw [form_symm]; change _ = (kernelEquiv G n) _ _; simp [covar]
end YM.Pert.Orb
