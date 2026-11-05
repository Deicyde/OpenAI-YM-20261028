import YM.Next.FREE_KERNELS.Dispatch
import YM.Progress.STATIONARY_SCENES.Green
import YM.Progress.STATIONARY_SCENES.Response


/-!
# Post-L exponential Schur estimates needed for the tree-slice Hessian

Real torus mat, full-metric K alone is NOT Hessian: use `probe` too.
Locality of patch, torus fine-native units (costs post-L, so can afford).
Include rows AND columns. No claims here of pre-L inverse costs as in
some other (e.g. joint gap) arguments in E.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes.Green
open Filter Lattice RG Wilson Precision Bid Function Matrix Exterior Bloch
open YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {f c : Side}

/-- `t` after fixing L. Fine-lattice. -/
def radius (r L : ℕ) := L + 12*r

def fee (r L : ℕ) : ℝ := L + 32*(r:ℝ)

def sideCount (r L : ℕ) (η : ℝ) := let t:= radius r L
  ((box t).card * (Fintype.card (TypeFace 1):ℝ))*(Real.exp (η*t)*fee r L)

section visit
variable (S : StepData c f)
local notation "L" => S.patch.L.val
local notation "t" => radius S.patch.radius L
local notation "ε" => fee S.patch.radius L

lemma probe_here (y : Body 1 c) (v : form 1 f) (B : ℝ) (hB : 0 ≤ B)
    (hh : ∀ z : Body 1 f, separation (S.ratio.embed y.1) z.1 ≤ t → |v z| ≤ B) :
    |(probe S *ᵥ v) y| ≤ ε*B := by
  obtain ⟨x,i⟩ := y
  obtain ⟨i,rfl⟩ := axisEquiv.surjective i
  let z := S.ratio.embed x
  have hs (b : S.patch.Points) : |integralLink (atPoint S x b) (S.repath i) v| ≤ L*B := by
    have he := Response.at_point S x b
    have hg : (S.repath i).length=L := List.length_replicate
    have hu : separation z (atPoint S x b)+(S.repath i).length ≤ t := by unfold z radius; omega
    simpa only [hg] using Response.integral_near v z (atPoint S x b) _ _ B hh hu
  have hz : |(mean S *ᵥ v) (x, coord i)| ≤ L*B := by
    simp only [mean, LinearMap.toMatrix'_mulVec, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, show axisEquiv.symm (coord i) = i from axisEquiv.symm_apply_apply i,
      smul_eq_mul]
    apply le_trans (Finset.abs_sum_le_sum_abs ..)
    calc
      _ ≤ ∑ b : S.patch.Points, S.patch.weight b * (L*B) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (S.patch.weight_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hs b) (S.patch.weight_nonneg _)
      _ = _ := by rw [← Finset.sum_mul,S.patch.weight_sum,one_mul]
  have hf : separation z (S.ratio.embed (x+step i)) ≤ L := by
    apply (scaled_root S.ratio x (x+step i)).trans
    have hv : separation x (x+step i) ≤ 1 := (Response.by_one x (posDir i)).1
    calc
      _ ≤ L*1 := Nat.mul_le_mul_left _ hv
      _ = _ := Nat.mul_one _
  have hu := Response.psi S v z (x+step i) _ B hB hh (Nat.add_le_add_right hf (12*S.patch.radius))
  have hw := Response.psi S v z x t B hB hh (by simp [z,radius])
  rw [probe,Matrix.add_mulVec, Pi.add_apply, ← Matrix.mulVec_mulVec]
  change |(mean S *ᵥ v) (x, coord i) + (d 0 c *ᵥ (fixRoot S *ᵥ v)) (x,coord i)| ≤ _
  rw [d_sites]
  refine le_trans ((abs_add_le ..).trans (add_le_add hz ((abs_sub ..).trans (add_le_add hu hw)))) (le_of_eq ?_)
  unfold fee; ring

lemma probe_range (x : Body 1 c) (y : Body 1 f) : |probe S x y| ≤ ε ∧
    (¬ separation (S.ratio.embed x.1) y.1 ≤ t → probe S x y=0) := by
  let v : form 1 f := Pi.single y 1
  have he : probe S x y = (probe S *ᵥ v) x := by unfold v; rw [Matrix.mulVec_single_one]; rfl
  rw [he]; constructor
  · have hh (z : Body 1 f) : |v z| ≤ (1:ℝ) := by by_cases h : z=y <;> simp [v,h]
    exact (probe_here S _ v 1 (by norm_num) fun z _ => hh z).trans_eq (mul_one _)
  intro H
  have hh (z : Body 1 f) (hz : separation (S.ratio.embed x.1) z.1 ≤ t) : v z=0 := by
    by_cases h : z=y
    · rw [h] at hz; exact False.elim (H hz)
    simp [v,Pi.single_eq_of_ne h]
  have h := probe_here S _ v 0 le_rfl (fun z hz => by rw [hh z hz,abs_zero])
  rwa [mul_zero, abs_nonpos_iff] at h
end visit

private lemma within_rows {ι χ Y : Type*} [Fintype χ] [Fintype ι] [Fintype Y] [DecidableEq χ] [DecidableEq ι]
    (a : Y → Site f) (b : χ → Site f) (P : Matrix Y (χ × ι) ℝ) (hb : Injective b)
    (t : ℕ) (η C : ℝ) (h : 0 ≤ η) (hC : 0 ≤ C)
    (hp : ∀ y z, |P y z| ≤ C ∧ (¬ separation (a y) (b z.1) ≤ t → P y z=0)) :
    Rows a (b ∘ Prod.fst) P η (((box t).card * (Fintype.card ι:ℝ))*(Real.exp (η*t)*C)) := by
  intro y
  let Z := Finset.univ.filter (fun z : χ × ι => separation (a y) (b z.1) ≤ t)
  have he : Z.card ≤ (box t).card * Fintype.card ι := by
    let J (x : Z) : ↥(box t) × ι := (⟨lift (b x.val.1 - a y),
      Work.E08.lift_mem_box (Finset.mem_filter.mp x.property).2⟩, x.val.2)
    have hh : Injective J := by
      intro p q H; apply Subtype.ext
      have Hq := congr_arg Prod.snd H
      refine Prod.ext ?_ (show p.val.2=q.val.2 from Hq)
      have he := congr_arg (wrap f) (congr_arg Subtype.val (congr_arg Prod.fst H))
      unfold J at he; dsimp only at he; rw [wrap_lift,wrap_lift] at he
      exact hb (sub_left_injective he)
    simpa only [Fintype.card_prod,Fintype.card_coe] using Fintype.card_le_of_injective J hh
  have hv : 0 ≤ Real.exp (η*t)*C := mul_nonneg (Real.exp_pos _).le hC
  calc
    _ = ∑ i ∈ Z, wt η (a y) (b i.1)* |P y i| := by
      symm; refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      have hg := hp y i |>.2 (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      simp [hg]
    _ ≤ ∑ _i ∈ Z, Real.exp (η*t)*C := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hu : separation (a y) (b i.1) ≤ t := (Finset.mem_filter.mp hi).2
      refine mul_le_mul (Real.exp_monotone ?_) (hp y i).1 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hu) h
    _ ≤ _ := by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) hv

theorem probe_budget (S : StepData c f) (η : ℝ) (h : 0 ≤ η) :
    let C := sideCount S.patch.radius S.patch.L.val η
    Both (S.ratio.embed ∘ Prod.fst) Prod.fst (probe S) η C C := by
  intro C
  have hp : 0 ≤ fee S.patch.radius S.patch.L.val := by unfold fee; positivity
  constructor
  · exact within_rows _ id (probe S) (fun _ _ hh => hh) _ η _ h hp (probe_range S)
  refine within_rows Prod.fst S.ratio.embed (probe S).transpose S.ratio.embed_injective _ η _ h hp ?_
  rintro y ⟨x,i⟩
  constructor
  · exact (probe_range S (x,i) y).1
  rw [separation_comm]; exact (probe_range S (x,i) y).2

theorem periodic {m n : Type*} [Fintype n] [Fintype m] (R : Row m n) (f : Side) {η C : ℝ}
    (he : 0 ≤ η) (h : R.strip η C) : Both Prod.fst Prod.fst (R.acts f) η (Fintype.card n*C) (Fintype.card m*C) := by
  constructor
  · exact row_sprawl he h f
  intro j
  simp only [wt,transpose_apply]
  simpa only [separation_comm j.1] using! col_sprawl he h f j

/-- Price kernel on 1-forms with full (non-diagonal!) metric. -/
def differential (η : ℝ) := max 1 (Work.F08.stencilCost 1 η)

def kinetic (η C : ℝ) := Fintype.card (TypeFace 2)*differential η*(Fintype.card (TypeFace 2)*max C 1)*
    (Fintype.card (TypeFace 1)*differential η)

lemma kinetic_price {η C : ℝ} (f : Side) (D : Bed) (h : D.metric.strip η C) (he : 0 ≤ η) :
    Rows Prod.fst Prod.fst (K (D.metric.acts f)) η (kinetic η C) := by
  have hh := periodic (cobound 1) f he (Work.F08.strip_mono (Work.F08.strip_stencil 1 η) le_rfl
    (show Work.F08.stencilCost 1 η ≤ differential η from le_max_right ..))
  have hp : 0 ≤ differential η := le_max_of_le_left zero_le_one
  have hv : 0 ≤ max C 1 := le_max_of_le_right zero_le_one
  have hu := periodic _ f he (Work.F08.strip_mono h le_rfl (le_max_left C 1))
  exact Rows.multiply he (Rows.multiply he hh.2 (show Rows _ _ (D.metric.acts f) η (Fintype.card (TypeFace 2)*max C 1) from hu.1) (by positivity)) hh.1 (by positivity)
end YM.Progress.StationaryScenes.Green
