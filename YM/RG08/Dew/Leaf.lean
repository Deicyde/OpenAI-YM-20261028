import YM.RG08.Germ.Mass
import YM.RG08.Origin.Axe
import YM.PertExtension.GaussianIBP

/-!
# Finite Gaussian evaluation for polynomial fields

Auxiliary actual-real calculus for *formal* covariance. No mask integrals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG PertExtension PertExtension.Series GaussianScore Stationary Tensor
open Lattice Wilson Filter Asymptotics Analysis Function Finset
open scoped Topology ContDiff Classical
variable {X Y ι : Type} {k n : ℕ}
section any
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
def Hemi (k : ℕ) (f : E→ℝ) : Prop := ∃ A : Tensor.T E ℝ k, Tensor.Sym A ∧ f= Tensor.diagonal A
lemma Hemi.pos (A : Tensor.T E ℝ k) : Hemi k (Tensor.diagonal A) :=
  ⟨Tensor.symmetrize A,Tensor.symmetrize_sym A, Eq.symm (funext (Tensor.symmetrize_diagonal A))⟩
lemma Hemi.smooth (h : Hemi k f) : ContDiff ℝ ω f := by obtain ⟨A,h,rfl⟩:=h; exact diag_smooth ..
lemma start_hemi (h : AnalyticAt ℝ f 0) (hp : ∀ x (t:ℝ), f (t • x)= t^k*f x) : Hemi k f := by
  have hx (x:E) : Tendsto (fun t : ℝ => (t^k)⁻¹ • f (t • x)) cutRay (𝓝 (f x)) := by
    refine EventuallyEq.tendsto ?_
    filter_upwards [self_mem_nhdsWithin (s:={t : ℝ|t ≠ 0})] with t (ht : t≠0)
    rw [hp, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ ht)]
  exact ⟨Tensor.coeff f k 0,Tensor.coeff_symm h.contDiffAt,funext fun x=> tendsto_nhds_unique (hx x) (ray_limit h (ray_origin fun x=> ⟨_,hx x⟩) x)⟩
lemma Hemi.times (h : Hemi k f) (H : Hemi n g) : Hemi (k+n) (f*g) := by
  apply start_hemi ((h.smooth.mul H.smooth).contDiffAt.analyticAt); intro x v
  obtain ⟨A,h,rfl⟩:=h; obtain ⟨B,g,rfl⟩:=H; simp only [Tensor.homogeneous,smul_eq_mul]; rw [pow_add]; ring
lemma Hemi.scale (h : Hemi k f) (t : ℝ) : Hemi k (t • f) := by obtain ⟨A,h,rfl⟩:=h; exact Hemi.pos (t • A)
lemma Hemi.const (t : ℝ) : Hemi 0 (fun _ : E => t) := start_hemi analyticAt_const (fun _ _=> by rw [pow_zero,one_mul])
lemma Hemi.plus (h : Hemi k f) (p : Hemi k g) : Hemi k (f+g) := by obtain ⟨A,h,rfl⟩:=h; obtain ⟨B,p,rfl⟩:=p; exact Hemi.pos (A+B)
lemma Hemi.zero (k : ℕ) : Hemi k (fun _ : E => (0:ℝ)) := Hemi.pos (0:Tensor.T E ℝ k)
lemma Hemi.list {F : ι→ E→ℝ} (s : Finset ι) (h : ∀ i∈s,Hemi k (F i)) : Hemi k (∑ i∈s,F i) := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Hemi.zero k
  | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma Hemi.invoiced (h : Hemi k f) : PertExtension.Series.Zone.Invoice PertExtension.Series.Radial.zone f := by
  obtain ⟨A,h,rfl⟩:=h; refine ⟨‖A‖,k,norm_nonneg _,fun x=> ((A.le_opNorm (fun _=>x))).trans ?_⟩
  simp only [prod_const,card_univ,Fintype.card_fin]; gcongr; unfold Series.Radial.zone; simp
lemma Hemi.lower (u : E) (h : Hemi (n+1) f) : Hemi n (D u f) := by
  obtain ⟨A,h,rfl⟩:=h; rw [Dfade _ _ h]; exact (Hemi.pos _).scale _
lemma Hemi.dry_zero (u : E) (h : Hemi 0 f) : D u f=0 := by obtain ⟨A,h,rfl⟩:=h; exact Dhush ..
inductive Grass {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] : (E → ℝ) → Prop where
 | base {k : ℕ} {f : E→ℝ} : Hemi k f → Grass f
 | sum {f g : E→ℝ} : Grass f → Grass g → Grass (f+g)
lemma Grass.scale (h : Grass f) (t : ℝ) : Grass (t • f) := by
  induction h with
  | base h => exact Grass.base (h.scale t)
  | sum _ _ hx hy => rw [smul_add]; exact hx.sum hy
lemma Grass.times (h : Grass f) (hv : Grass g) : Grass (f*g) := by
  induction h with
  | @base k f h =>
    induction hv with
    | base p => exact Grass.base (h.times p)
    | sum _ _ hx hy => rw [mul_add]; exact hx.sum hy
  | sum _ _ hx hy => rw [add_mul]; exact hx.sum hy
lemma Grass.smooth (h : Grass f) : ContDiff ℝ ω f := by induction h with | base h=> exact h.smooth | sum _ _ hx hy => exact hx.add hy
lemma Grass.invoiced (h : Grass f) : PertExtension.Series.Zone.Invoice PertExtension.Series.Radial.zone f := by induction h with | base h=> exact h.invoiced | sum _ _ hx hy => exact hx.add hy
lemma Grass.const (t : ℝ) : Grass (fun _:E=> t) := Grass.base (Hemi.const t)
lemma Grass.list {F : ι→ E→ ℝ} {s : Finset ι} (h : ∀ i∈s,Grass (F i)) : Grass (∑ i∈s,F i) := by
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Grass.const 0
  | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).sum (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma Grass.prod {F : ι→E→ℝ} {s : Finset ι} (h : ∀ i∈s,Grass (F i)) : Grass (∏ i∈s,F i) := by
  induction s using Finset.induction_on with
  | empty => rw [prod_empty]; exact Grass.const 1
  | insert i s hi ih => rw [prod_insert hi]; exact (h i (mem_insert_self ..)).times (ih fun j hj=> h j (mem_insert_of_mem hj))
end any

variable [Fintype X]
lemma grass_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Psalm X} {M : E→(X→ℝ)}
    (h : Grass f) (hv : ∀ i,Grass (fun x=> M x i)) : Grass (f ∘ M) := by
  induction h with
  | @base k f h =>
    obtain ⟨A,h,rfl⟩:=h
    let p (u : Fin k→X) := (∏ i, (fun x:E=> M x (u i))) * (fun _ : E=> A (fun i=> Pi.single (u i) 1))
    rw [show Tensor.diagonal A∘ M=∑ i,p i from funext fun i=> by rw [Finset.sum_apply]; have ht := expand_coord A.toMultilinearMap (fun _=>M i); rw [recording_apply] at ht; unfold p; simp only [Pi.mul_apply,Finset.prod_apply]; exact ht.symm]
    exact Grass.list (fun i _=> (Grass.prod (fun j _=>hv (i j))).times (Grass.const _))
  | sum _ _ hx hy=> exact hx.sum hy
section
variable [DecidableEq X] (M : Matrix X X ℝ) {F : Psalm X}
lemma Hemi.soaks (h : Hemi (n+2) F) : Hemi n (lap M F) := by
  let U i j := M i j • Analysis.D (zpk j) (Analysis.D (zpk i) F)
  rw [show lap M F=(1/2:ℝ) • (∑ i,∑ j,U i j) from funext fun x=> by simp only [Pi.smul_apply,Finset.sum_apply]; rfl]; exact (Hemi.list _ (fun i _=> Hemi.list _ (fun j _=> ((h.lower _).lower _).scale _ ) ) ).scale _
lemma Hemi.soak1 (h : Hemi 1 F) : lap M F=0 := by funext x; simp_rw [lap, (h.lower (n:=0) _).dry_zero]; simp
lemma Hemi.soak0 (h : Hemi 0 F) : lap M F=0 := by funext x; simp_rw [lap,h.dry_zero ]; simp [D]
lemma soak_iter (F : Psalm X) (n : ℕ) (h : ContDiff ℝ ω F) : ContDiff ℝ ω ((lap M)^[n] F) := by induction n with | zero => exact h | succ n ih => rw [iterate_succ_apply']; exact lap_prime M ih
lemma Grass.soaks (h : Grass F) : Grass (lap M F) := by
  induction h with
  | @base k F h =>
    match k with
    | 0=> rw [h.soak0]; exact Grass.const 0
    | 1=> rw [h.soak1]; exact Grass.const 0
    | k+2=> exact Grass.base (h.soaks M)
  | sum h v hx hy => rw [lap_total _ h.smooth v.smooth]; exact hx.sum hy
lemma Grass.iter (h : Grass F) : Grass ((lap M)^[n] F) := by induction n with| zero=> exact h| succ n ih=>rw [iterate_succ_apply']; exact ih.soaks M
lemma Grass.wick (h : Grass F) (n) : Grass (wickLayer M n F) := (h.iter M).scale _
end
end YM.RG08
