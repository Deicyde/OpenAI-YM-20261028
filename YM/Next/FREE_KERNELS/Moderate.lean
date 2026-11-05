import Mathlib.Analysis.Complex.Schwarz
import YM.CellFourier.Mesh
import YM.Work.F07.Read



/-!
# Cube calculus for the free kernels

Radian momenta, unscaled axis coordinates. `Moderate w f` is a *uniform*
statement: it budgets a strictly positive cube thickness before any specialization
of the index; scale powers etc must be made explicit in `w`. We need to use it
with both history and block length included in that index. It makes **no**
assertion of periodicity (the regular pole splits on the cube will not all glue).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

def physical (p : Momentum) : Prop := star p = p

def baseCube : Set Momentum := {p | physical p ∧ ∀ i, |(p i).re| ≤ Real.pi}

/-- Real tests in a slightly enlarged cube (for real overlap identities). -/
def realCube (η : ℝ) : Set Momentum := {p | physical p ∧ ∀ i, |(p i).re| < Real.pi+η}

def rpart (p : Momentum) : Momentum := fun i => ((p i).re:ℂ)

@[simp] lemma physical_rpart (p : Momentum) : physical (rpart p) := by
  unfold physical rpart; ext i; simp

lemma physical_iff (p : Momentum) : physical p ↔ ∀ i, (p i).im = 0 := by
  unfold physical
  rw [funext_iff]
  exact forall_congr' fun i => Complex.conj_eq_iff_im

lemma cube_mono {a b : ℝ} (h : a ≤ b) : cube (α:=Axis) a ⊆ cube b :=
  fun _ hp => ⟨fun i => lt_of_lt_of_le (hp.1 i) h,
    fun i => lt_of_lt_of_le (hp.2 i) (add_le_add_right h _)⟩

lemma cube_neg (p : Momentum) {a : ℝ} (h : p ∈ cube a) : -p ∈ cube a := by
  constructor <;> intro i <;> simp only [Pi.neg_apply, Complex.neg_im, Complex.neg_re, abs_neg]
  · exact h.1 i
  · exact h.2 i

lemma realCube_neg {p : Momentum} {a : ℝ} (h : p ∈ realCube a) : -p ∈ realCube a := by
  obtain ⟨hx,hy⟩ := h
  refine ⟨star_neg p |>.trans (congr_arg Neg.neg hx), fun i => ?_⟩
  simpa only [Pi.neg_apply, Complex.neg_re, abs_neg] using hy i

lemma mem_cube_real {p : Momentum} {a : ℝ} (h : p ∈ realCube a) (ha : 0<a) : p ∈ cube a :=
  ⟨Work.F07.realStrip a ha h.1,h.2⟩

lemma base_subset_realCube {a : ℝ} (ha : 0<a) : baseCube ⊆ realCube a := fun _ h =>
  ⟨h.1,fun i => (h.2 i).trans_lt (by linarith)⟩

lemma rpart_mem_realCube {p : Momentum} {a : ℝ} (h : p ∈ cube a) : rpart p ∈ realCube a :=
  ⟨physical_rpart _, fun i => h.2 i⟩

lemma cube_open (η : ℝ) : IsOpen (cube (α:=Axis) η) := by
  apply (Work.F07.stripOpen _).inter
  rw [show {p : Momentum | ∀ i, |(p i).re| < Real.pi+η} =
      ⋂ i : Axis, {p : Momentum | |(p i).re| < Real.pi+η} by ext; simp]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const

lemma cube_zero (η : ℝ) (hη : 0 < η) : (0 : Momentum) ∈ cube η := by
  constructor
  · intro i; simpa only [Pi.zero_apply, Complex.zero_im, abs_zero] using hη
  intro i
  simp only [Pi.zero_apply, Complex.zero_re, abs_zero]
  positivity

lemma ball_inside_cube {p : Momentum} {η θ : ℝ} (hp : p ∈ cube θ) : ball p (η-θ) ⊆ cube η := by
  intro q hq
  rw [mem_ball, dist_eq_norm] at hq
  have h (i : Axis) : ‖q i - p i‖ < η-θ := (norm_le_pi_norm (q-p) i).trans_lt hq
  constructor
  · intro i
    have hx : |(q i).im - (p i).im| < η-θ := (Complex.abs_im_le_norm (q i - p i)).trans_lt (h i)
    have hy := hp.1 i
    grind
  intro i
  have hx : |(q i).re - (p i).re| < η-θ := (Complex.abs_re_le_norm (q i - p i)).trans_lt (h i)
  have hy := hp.2 i
  grind

lemma thin_dist {p : Momentum} {η : ℝ} (hη : 0<η) (hp : p ∈ cube η) : dist p (rpart p) ≤ η := by
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hη.le]
  intro i
  have h : p i - (((p i).re:ℝ):ℂ)=((p i).im:ℂ)*Complex.I := by apply Complex.ext <;> simp
  change ‖p i - (((p i).re:ℝ):ℂ)‖ ≤ η
  rw [h,norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  exact (hp.1 i).le

variable {ι κ : Type*}

/-- Absolute holomorphic cube budget (not same as Laurent coefficient budget `Width`). -/
structure SafeCube (η C : ℝ) (f : Momentum → ℂ) : Prop where
  hol p : p ∈ cube η → DifferentiableAt ℂ f p
  bound p : p ∈ cube η → ‖f p‖ ≤ C

def Moderate (w : ι → ℝ) (f : ι → Momentum → ℂ) :=
  ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ i, SafeCube η (C*w i) (f i)

def Firm (w : ι → ℝ) (f : ι → Momentum → ℂ) :=
  ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ i, ∀ p ∈ realCube η, c*w i ≤ ‖f i p‖

lemma SafeCube.mono {η θ C B : ℝ} {f : Momentum → ℂ} (h : SafeCube η C f) (ht : θ ≤ η) (hb : C ≤ B) :
    SafeCube θ B f := ⟨fun p hp => h.hol p (cube_mono ht hp),fun p hp => (h.bound p (cube_mono ht hp)).trans hb⟩

lemma SafeCube.nonneg {η C : ℝ} {f : Momentum → ℂ} (h : SafeCube η C f) (hp : 0 < η) : 0 ≤ C :=
  (norm_nonneg _).trans (h.bound _ (cube_zero _ hp))

namespace Moderate
variable {f g : ι → Momentum → ℂ} {w u v : ι → ℝ}

lemma nonneg (h : Moderate w f) (i : ι) : 0 ≤ w i := by
  obtain ⟨η,C,hp,hc,h⟩ := h
  exact nonneg_of_mul_nonneg_right ((h i).nonneg hp) hc

lemma index (h : Moderate w f) (i : κ → ι) : Moderate (fun a => w (i a)) (fun a => f (i a)) := by
  obtain ⟨η,C,hp,hc,h⟩ := h
  exact ⟨η,C,hp,hc,fun j => h (i j)⟩

lemma raise_price (h : Moderate w f) (hu : w ≤ u) : Moderate u f := by
  obtain ⟨η,C,hp,hc,h⟩ := h
  exact ⟨η,C,hp,hc,fun i => (h i).mono le_rfl (mul_le_mul_of_nonneg_left (hu i) hc.le)⟩

lemma bounded_const (f : ι → ℂ) (C : ℝ) (hC : 0<C) (hc : ∀ i, ‖f i‖ ≤ C*w i) :
    Moderate w (fun i _ => f i) :=
  ⟨1,C,one_pos,hC,fun i => ⟨fun _ _ => differentiableAt_const _, fun _ _ => hc i⟩⟩

lemma const (x : ℂ) : Moderate (fun _ : ι => 1) (fun _ _ => x) :=
  bounded_const _ (‖x‖+1) (by positivity) (fun _ => by simp)

lemma zero (hw : ∀ i, 0 ≤ w i) : Moderate w (fun _ _ => 0) := bounded_const _ 1 one_pos (fun i => by simp [hw])

lemma add (hf : Moderate w f) (hg : Moderate w g) : Moderate w fun i p => f i p + g i p := by
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  obtain ⟨θ,B,hq,hb,hg⟩ := hg
  refine ⟨min η θ,C+B, lt_min hp hq, by linarith, fun i => ?_⟩
  have hF := (hf i).mono (min_le_left η θ) le_rfl
  have hG := (hg i).mono (min_le_right η θ) le_rfl
  refine ⟨fun p hm => (hF.hol p hm).add (hG.hol p hm), fun p hm => ?_⟩
  exact (norm_add_le ..).trans ((add_le_add (hF.bound p hm) (hG.bound p hm)).trans_eq (add_mul ..).symm)

lemma neg (hf : Moderate w f) : Moderate w fun i p => -f i p := by
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  refine ⟨η,C,hp,hc, fun i => ⟨fun p hm => ((hf i).hol p hm).neg, fun p hm => ?_⟩⟩
  rw [norm_neg]; exact (hf i).bound p hm

lemma sub (hf : Moderate w f) (hg : Moderate w g) : Moderate w fun i p => f i p - g i p := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma mul (hf : Moderate w f) (hg : Moderate u g) : Moderate (fun i => w i * u i) fun i p => f i p * g i p := by
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  obtain ⟨θ,B,hq,hb,hg⟩ := hg
  refine ⟨min η θ,C*B, lt_min hp hq, by positivity, fun i => ?_⟩
  have hF := (hf i).mono (min_le_left η θ) le_rfl
  have hG := (hg i).mono (min_le_right η θ) le_rfl
  refine ⟨fun p hm => (hF.hol p hm).mul (hG.hol p hm), fun p hm => ?_⟩
  rw [norm_mul, mul_mul_mul_comm]
  exact mul_le_mul (hF.bound p hm) (hG.bound p hm) (norm_nonneg _) ((hf i).nonneg hp)

lemma pow (hf : Moderate w f) (m : ℕ) : Moderate (fun i => w i ^ m) fun i p => f i p ^ m := by
  induction m with
  | zero => simpa only [pow_zero] using const (ι:=ι) 1
  | succ m ih => simpa only [pow_succ] using ih.mul hf

/-- Real separation suffices for spending the complex cubewise reciprocal. -/
lemma kept (hf : Moderate w f) (hg : Firm w f) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ i, ∀ p ∈ cube η, c*w i ≤ ‖f i p‖ := by
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  obtain ⟨θ,c,hq,hb,hg⟩ := hg
  let r := min (η/4) (min θ (c*η/(8*C)))
  have hr : 0 < r := lt_min (by positivity) (lt_min hq (by positivity))
  have hr1 : r ≤ η/4 := min_le_left ..
  have hr2 : r ≤ θ := (min_le_right ..).trans (min_le_left ..)
  have hr3 : r ≤ c*η/(8*C) := (min_le_right ..).trans (min_le_right ..)
  refine ⟨r,c/2,hr,by linarith,fun i p hx => ?_⟩
  have hw : 0 ≤ w i := nonneg_of_mul_nonneg_right ((hf i).nonneg hp) hc
  let y := rpart p
  have hy : y ∈ cube r := mem_cube_real (rpart_mem_realCube hx) hr
  have hy' : y ∈ cube η := cube_mono (by linarith) hy
  have hyθ : y ∈ cube θ := cube_mono hr2 hy
  have hl := hg i y ⟨physical_rpart p,hyθ.2⟩
  have hxy : dist p y ≤ r := thin_dist hr hx
  have hz : p ∈ ball y (η/2) := by rw [mem_ball]; linarith
  have hwit : ball y (η/2) ⊆ cube η := (ball_subset_ball (show η/2≤η-r by linarith)).trans (ball_inside_cube hy)
  have hh : MapsTo (f i) (ball y (η/2)) (closedBall (f i y) (2*(C*w i))) := by
    intro z h
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le ..).trans ((add_le_add ((hf i).bound z (hwit h)) ((hf i).bound y hy')).trans_eq (two_mul ..).symm)
  have hds := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (fun z he => ((hf i).hol z (hwit he)).differentiableWithinAt) hh hz
  have ht : dist (f i p) (f i y) ≤ c/2*w i := hds.trans (calc
    _ ≤ 2*(C*w i)/(η/2)*(c*η/(8*C)) := mul_le_mul_of_nonneg_left (hxy.trans hr3) (by positivity)
    _ = _ := by field_simp; ring)
  have hn := norm_sub_norm_le (f i y) (f i p)
  rw [dist_comm, dist_eq_norm] at ht
  linarith

lemma inv (hf : Moderate w f) (hg : Firm w f) (hw : ∀ i, 0 < w i) : Moderate (fun i => (w i)⁻¹) fun i p => (f i p)⁻¹ := by
  obtain ⟨θ,c,hq,hb,hg⟩ := hf.kept hg
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  refine ⟨min θ η,c⁻¹,lt_min hq hp, by positivity,fun i => ⟨fun p h => ?_,fun p h => ?_⟩⟩
  · apply ((hf i).hol p (cube_mono (min_le_right ..) h)).inv
    exact norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hb (hw i)) (hg i p (cube_mono (min_le_left ..) h)))
  have he := hg i p (cube_mono (min_le_left ..) h)
  rw [norm_inv,← mul_inv]; exact inv_le_inv₀ (lt_of_lt_of_le (mul_pos hb (hw i)) he) (mul_pos hb (hw i)) |>.mpr he



lemma sum (s : Finset κ) (f : κ → ι → Momentum → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i ∈ s, Moderate w (f i)) :
    Moderate w fun i p => ∑ k ∈ s, f k i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero hw
  | @insert a s hs ih =>
    simp only [Finset.sum_insert hs]
    exact (hf a (Finset.mem_insert_self ..)).add (ih fun i h => hf i (Finset.mem_insert_of_mem h))

/-- Alias-sized sums require an actual total weight bound. -/
lemma sum_family {α : ι → Type*} (s : ∀ i, Finset (α i)) (m : ∀ i, α i → ℝ)
    (hm : ∃ M : ℝ, 0<M ∧ ∀ i, ∑ k∈s i, m i k ≤ M*w i) (F : ∀ i, α i → Momentum → ℂ)
    (hf : Moderate (fun x : Σ i, {k // k∈ s i} => m x.1 x.2) (fun x => F x.1 x.2)) :
    Moderate w (fun i p => ∑ k∈s i, F i k p) := by
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  obtain ⟨M,hM,h⟩ := hm
  refine ⟨η,C*M,hp, by positivity,fun i => ⟨fun p ho => ?_,fun p ho => ?_⟩⟩
  · apply DifferentiableAt.fun_sum
    intro k hk; exact (hf ⟨i,k,hk⟩).hol p ho
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ k∈s i, C*m i k := Finset.sum_le_sum fun k hk => (hf ⟨i,k,hk⟩).bound p ho
    _ ≤ _ := by
      rw [← Finset.mul_sum, mul_assoc]; exact mul_le_mul_of_nonneg_left (h i) hc.le

lemma reverse (hf : Moderate w f) : Moderate w fun i p => f i (-p) := by
  obtain ⟨η,C,hp,hc,hf⟩ := hf
  refine ⟨η,C,hp,hc,fun i => ⟨fun p ho => ?_,fun p ho => (hf i).bound _ (cube_neg _ ho)⟩⟩
  exact ((hf i).hol _ (cube_neg _ ho)).comp p differentiableAt_id.neg

end Moderate
end YM.Next.Free
