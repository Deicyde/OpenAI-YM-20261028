import YM.Primitives.TWO_WAVE_TRACE_DENSITY.C12

/-!
# Laurent vertices

Fine residues stay in TYPES (including colors). Cover exponent is on
independent incoming displacements in coarse cells relative to output.
Application might for example use all chart slot types = sum of coarse
and free tangent types, filling other types with zero when substituting a
particular bond wave. `drive` allows indistinguishable locations; Fintype
products count repetitions. Scalar periods in Clusters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Matrix Complex RG
open scoped BigOperators Topology

abbrev Leaf (n : Side) (α : Type*) := Site n × α
abbrev Arm (k : ℕ) := Fin k × Axis
abbrev Fan (α β : Type*) (k : ℕ) := α → (Fin k → β) → On (Arm k) ℝ
variable {α β : Type*} {n : Side} {k : ℕ}

/-- right displacements, hold output location (same sign convention as Row). -/
def point (w : Shift (Arm k)) (i : Fin k) : Cover := fun a=> w (i,a)
def joint (p : Fin k → Momentum) : Phase (Arm k) := fun i=> p i.1 i.2

def floated (x : Site n) (j : Fin k→β) (w : Shift (Arm k)) : Fin k → Leaf n β :=
    fun s => (x+wrap n (point w s),j s)

abbrev FrameCoeffs (ι τ : Type*) (k : ℕ) (R : Type*) := ι → (Fin k → τ) → R

open scoped Classical
/-- Period assembly, no `/k!` or volume factors. -/
def pieces (F : Fan α β k) (n : Side) : FrameCoeffs (Leaf n α) (Leaf n β) k ℝ :=
    fun i t=> ∑' w, if t=floated i.1 (Prod.snd ∘ t) w then F i.2 (Prod.snd ∘ t) w else 0

def Cap (F : Fan α β k) (η C : ℝ) := ∀ i t,Laurent.Width η C (F i t)

lemma Cap.prom {F : Fan α β k} {η C : ℝ} (h : Cap F η C) (i) (t) : Laurent.Width η C (fun w=> (F i t w:ℂ)) := by
  simpa only [Width,norm_real] using h i t

lemma Cap.pencils {F : Fan α β k} {η C : ℝ} (h : Cap F η C) (he : 0≤η) (i : Leaf n α) (t : Fin k → Leaf n β) : HasSum
    (fun w:Shift (Arm k)=> if t=floated i.1 (Prod.snd ∘ t) w then F i.2 (Prod.snd ∘ t) w else 0) (pieces F n i t) := by
  let A : Set (Shift (Arm k)) := {w|t=floated i.1 (Prod.snd ∘ t) w}
  classical
  refine (Summable.hasSum ?_)
  exact (((h i.2 (Prod.snd ∘ t)).summable he).indicator A).congr (fun w=> by simp [A, Set.indicator])

def colors (F : Fan α β k) (p : Fin k → Momentum) : FrameCoeffs α β k ℂ :=
    fun i j=> Laurent.read (fun w => (F i j w:ℂ)) (joint p)
lemma tile_mode (w : Shift (Arm k)) (p : Fin k → Momentum) : mode (joint p) w= ∏ i,mode (p i) (point w i) := by simp [mode,Fintype.sum_prod_type,Complex.exp_sum, Finset.mul_sum,point,joint]

section finite
variable {ι τ R : Type*} [Fintype τ] [CommSemiring R]

/-- Moment/coeff contraction, unweighted. -/
def drive (P : FrameCoeffs ι τ k R) (v : Fin k → τ → R) : ι→R := fun i => ∑ j : Fin k→τ, P i j*∏ s, v s (j s)

lemma drive_cons (P : FrameCoeffs ι τ (k+1) R) (b : τ → R) (v : Fin k→τ→R) (i : ι) :
    drive P (Fin.cons b v) i = ∑ a : τ, (∑ j : Fin k → τ, P i (Fin.cons a j) * ∏ s,v s (j s))*b a := by
  unfold drive
  let e := (Fin.consEquiv (fun _ : Fin (k+1) => τ))
  rw [← Equiv.sum_comp e,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _
  change P i (Fin.cons a j)*(∏ l:Fin (k+1),Fin.cons (α:=fun _=>τ→R) b v l (Fin.cons (α:=fun _=>τ) a j l))=_
  rw [Fin.prod_univ_succ]; simp; ring

def injectMatrix (P : FrameCoeffs ι τ (k+1) R) (v : Fin k→τ→R) : Matrix ι τ R :=
    of fun i a=> ∑ j : Fin k → τ, P i (Fin.cons a j) * ∏ s,v s (j s)

lemma injectMatrix_mulVec (P : FrameCoeffs ι τ (k+1) R) (v : Fin k→τ→R) (b : τ→R) :
    injectMatrix P v *ᵥ b = drive P (Fin.cons b v) := by ext1 i; exact (drive_cons ..).symm
end finite

variable [Fintype β]

def darken {ι τ : Type*} (P : FrameCoeffs ι τ k ℝ) : FrameCoeffs ι τ k ℂ := fun i t=>(P i t:ℂ)

/-- Test periodized coefficients on arbitrary periodic fields. -/
lemma covered_action {F : Fan α β k} {η C : ℝ} (h : Cap F η C) (he : 0 ≤ η)
    (i : Leaf n α) (v : Fin k → Leaf n β → ℂ) :
    drive (darken (pieces F n)) v i =
      ∑' w : Shift (Arm k), ∑ j : Fin k→β,(F i.2 j w:ℂ)*∏ s,v s (floated i.1 j w s) := by
  let T t w:= if t=floated i.1 (Prod.snd ∘ t) w then F i.2 (Prod.snd ∘ t) w else 0
  let u (t : Fin k→Leaf n β) := ∏ s,v s (t s)
  have hS (t : Fin k→Leaf n β) : HasSum (fun w:Shift (Arm k)=> (T t w:ℂ)*u t)
      ((pieces F n i t:ℂ)*u t) := ((Complex.ofRealCLM.hasSum (h.pencils he i t))).mul_right _
  have hm := (hasSum_sum (s:=Finset.univ) (fun i _=>hS i)).tsum_eq
  unfold drive darken
  change (∑ t : Fin k→Leaf n β,(pieces F n i t:ℂ)*u t)=_
  rw [← hm]; apply tsum_congr; intro w
  classical
  let W := fun j : Fin k → β => floated i.1 j w
  have hi : Function.Injective W := fun a b ha=> funext fun l=>congr_arg (fun j=> ((j:Fin k → Leaf n β) l).2) ha
  calc
    _ = ∑ t∈ Finset.univ.image W,(T t w:ℂ)*u t := by
      symm; apply Finset.sum_subset (Finset.subset_univ _); intro x hx h'
      rw [show T x w=0 by unfold T; rw [if_neg]; rintro ha; exact h' (ha.symm ▸ Finset.mem_image_of_mem W (Finset.mem_univ _))]; simp
    _ = _ := by
      rw [Finset.sum_image hi.injOn]; refine Finset.sum_congr rfl fun j _=>?_
      have hj : Prod.snd ∘ W j=j := rfl
      unfold T; rw [hj,if_pos rfl]

lemma cell_sum (p : Fin k→Site n) (x : Site n) : cell (∑ i,p i) x=∏ i,cell (p i) x := by
  classical
  have hh (s : Finset (Fin k)) : cell (∑ i∈s,p i) x=∏ i∈s,cell (p i) x := by
    induction s using Finset.induction_on with
    | empty => simp [cell_duality (0 : Site n)]
    | insert i s he ih => rw [Finset.sum_insert he,Finset.prod_insert he,cell_duality (_+_), cell_add,cell_duality x,cell_duality x,ih]
  exact hh _

/-- Exact Laurent/Bloch representation for all insertion placements. -/
theorem fan_route {F : Fan α β k} {η C : ℝ} (h : Cap F η C) (he : 0 ≤ η)
    (p : Fin k → Site n) (v : Fin k → β → ℂ) :
    drive (darken (pieces F n)) (fun s => ray (p s) (v s)) =
      ray (∑ s,p s) (drive (colors F (mon ∘ p)) v) := by
  ext1 i
  rw [covered_action h he]
  let u (j : Fin k → β) := ∏ s,v s (j s)
  have hx : Within η (joint (mon ∘ p)) := by
    intro a
    have he' := congr_fun (real_frequency (p a.1)) a.2
    change star (mon (p a.1) a.2)=_ at he'; rw [Complex.star_def, Complex.conj_eq_iff_im] at he'
    simpa only [joint,Function.comp_apply, he',abs_zero] using he
  unfold ray drive; rw [Finset.mul_sum]
  simp_rw [colors,Laurent.read,← tsum_mul_right,← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]; swap
  · intro j _
    exact ((((h.prom i.2 j).series _ hx).2.1.of_norm.mul_right _).mul_left _)
  apply tsum_congr; intro w; refine Finset.sum_congr rfl fun j _=>?_
  rw [tile_mode,cell_sum,smul_eq_mul]
  simp_rw [floated,cell_add,cell_wrap,Function.comp_apply,Finset.prod_mul_distrib]; ring

/-- Insert all but INTERNAL first incoming leg. Multiple variations,
contact term uses k=2, the distinct-segment term k=1 twice. All entries
unrestricted. No `[p+t=0]` branch needed for the routing. -/
def badge (F : Fan α β (k+1)) (p : Fin k → Momentum) (v : Fin k → β → ℂ) : Symbol α β := fun q=>
    injectMatrix (colors F (Fin.cons q p)) v




def badgeFare (β : Type*) [Fintype β] (C R : ℝ) (k : ℕ) := (Fintype.card β)^k * (C*R^k)

omit [Fintype β] in
lemma coloring {F : Fan α β k} {η C : ℝ} (h : Cap F η C) {p : Fin k→Momentum} (hp : Within η (joint p)) :
    ∀ i j,‖colors F p i j‖ ≤ C := fun i j=> (h.prom i j).estimate _ hp


end YM.Primitives.TwoWave
