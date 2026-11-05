import YM.Analysis.Homogeneous
import YM.Laurent.Rune
import YM.Work.F02.Series
import YM.Work.F07.Read






set_option autoImplicit false
/-!
# Vanishing by rays

Real rays suffice throughout: in particular the tests used for Ward on real
meshes will not have hypotheses on an off-mesh analytic interpolation. These
are qualitative (even constants may depend on the ray).
-/
noncomputable section
namespace YM.Stationary
open Finset Function Filter Asymptotics Set
open scoped Topology ContDiff BigOperators
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

abbrev cutRay := 𝓝[≠] (0 : ℝ)

def Rays (s : ℕ) (f : X → Y) := ∀ x,
    (fun t : ℝ => f (t • x)) =O[cutRay] (fun t => t^s)

lemma along (x : X) : Tendsto (fun t : ℝ => t • x) cutRay (𝓝 0) := by
  have ht := (show Continuous (fun t : ℝ => t • x) by fun_prop).tendsto 0
  rw [zero_smul] at ht; exact ht.mono_left nhdsWithin_le_nhds

lemma powers {s t : ℕ} (h : s ≤ t) : (fun x : ℝ => x^t) =O[cutRay] (fun x => x^s) := by
  refine isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [nhdsWithin_le_nhds (α:=ℝ) (a:=0) (s:={0}ᶜ) (Metric.ball_mem_nhds 0 zero_lt_one)] with i hi
  rw [norm_pow, norm_pow, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (by simpa [Metric.mem_ball] using hi)) h

omit [NormedSpace ℝ Y] in
lemma Rays.weaker {f : X → Y} {s t : ℕ} (h : Rays t f) (he : s ≤ t) : Rays s f :=
  fun x => (h x).trans (powers he)
omit [NormedSpace ℝ Y] in
lemma Rays.add {f g : X → Y} {s : ℕ} (h : Rays s f) (he : Rays s g) : Rays s (f+g) :=
    fun x => (h x).add (he x)
omit [NormedSpace ℝ Y] in
lemma Rays.sub {f g : X → Y} {s : ℕ} (h : Rays s f) (he : Rays s g) : Rays s (f-g) :=
    fun x => (h x).sub (he x)
lemma Rays.mul {Z : Type} [NormedRing Z] [NormedAlgebra ℝ Z]
    {f g : X → Z} {s t : ℕ} (h : Rays s f) (he : Rays t g) : Rays (s+t) (f*g) := by
  intro x; simpa only [Rays, Pi.mul_apply,pow_add] using (h x).mul (he x)

-- scaled limit at degree n
lemma scale_limit {f : ℝ → Y} (n : ℕ) (y : Y)
    (h : (fun t : ℝ => f t - (t^n) • y) =O[cutRay] (fun t => t^(n+1))) :
    Tendsto (fun t => (t^n)⁻¹ • f t) cutRay (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨C,h⟩ := isBigO_iff.mp h
  have hm := (tendsto_id (x:=𝓝 (0:ℝ))).norm.const_mul C |>.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
  simp only [id_eq, norm_zero,mul_zero] at hm
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hm
  filter_upwards [h, (self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay, t ≠ 0)] with t ht hi
  have hp : ‖t‖ ≠ 0 := (norm_pos_iff.mpr hi).ne'
  rw [norm_pow] at ht
  rw [show _ - y = (t^n)⁻¹ • (f t - (t^n) • y) by rw [smul_sub,inv_smul_smul₀ (pow_ne_zero _ hi)], norm_smul, norm_inv,norm_pow]
  exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (by rw [pow_succ]; field_simp)

section analytics
variable {p : FormalMultilinearSeries ℝ X Y} {f : X → Y} (h : HasFPowerSeriesAt f p 0)
include h

private lemma approx (t : ℕ) (x : X) :
    (fun b : ℝ => f (b • x) - p.partialSum t (b • x)) =O[cutRay] (fun b => b^t) := by
  have he := (h.isBigO_sub_partialSum_pow t).comp_tendsto (along x)
  simp only [comp_def, zero_add,norm_smul] at he
  refine he.trans (isBigO_of_le' (c:=‖x‖^t) _ fun b => ?_)
  rw [norm_pow,norm_pow, Real.norm_of_nonneg (by positivity), mul_pow, mul_comm]

lemma rays_one (t : ℕ) (x : X) :
    (fun b : ℝ => f (b • x)) =O[cutRay] (fun b => b^t) ↔
      ∀ m : ℕ, m<t → Tensor.diagonal (p m) x=0 := by
  induction t with
  | zero =>
    simp; simpa [FormalMultilinearSeries.partialSum] using! (approx h 0 x)
  | succ t ih =>
    have he {y : X} : p.partialSum (t+1) y = p.partialSum t y + Tensor.diagonal (p t) y := sum_range_succ ..
    constructor
    · intro hp
      have hv := ih.mp (hp.trans (powers t.le_succ))
      suffices H : Tensor.diagonal (p t) x = 0 from fun m hm =>
        (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hm)).elim (fun hh => hh.symm ▸ H) (hv m)
      have hh (b : ℝ) : p.partialSum t (b • x) = 0 := Finset.sum_eq_zero (fun i hi => by
        change Tensor.diagonal (p i) (b • x)=_; rw [Tensor.homogeneous,hv i (mem_range.mp hi),smul_zero])
      have hx := approx h (t+1) x
      simp_rw [he,hh,zero_add,Tensor.homogeneous] at hx
      exact tendsto_nhds_unique (scale_limit (f:=fun b => f (b • x)) t _ hx)
        (scale_limit t 0 (by simpa using hp))
    · intro hp
      have hh (b : ℝ) : p.partialSum (t+1) (b • x) = 0 := sum_eq_zero (fun i hi => by
        change Tensor.diagonal (p i) (b • x)=_; rw [Tensor.homogeneous, hp _ (mem_range.mp hi),smul_zero])
      have he := approx h (t+1) x; simpa only [hh,sub_zero] using he

variable [CompleteSpace Y]

lemma diag_derivative (t : ℕ) (x : X) : Tensor.diagonal (iteratedFDeriv ℝ t f 0) x =
    (t.factorial : ℝ) • Tensor.diagonal (p t) x := by
  obtain ⟨r,h⟩ := h
  simpa only [Tensor.diagonal, Fintype.card_perm, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    Nat.cast_smul_eq_nsmul] using h.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin t => x)
end analytics

section use
variable [CompleteSpace Y] {f : X → Y} (h : AnalyticAt ℝ f 0)
include h

omit [CompleteSpace Y] in
lemma rays_zero : Rays 0 f := by
  obtain ⟨p,h⟩ := h
  exact fun i => (rays_one h 0 i).2 (by simp)

lemma rays_jet (n : ℕ) : Rays n f ↔ ∀ i < n, iteratedFDeriv ℝ i f 0=0 := by
  have hh := h.contDiffAt (n:=ω)
  obtain ⟨p,h⟩ := h
  have he (i : ℕ) (x : X) : Tensor.diagonal (iteratedFDeriv ℝ i f 0) x=0 ↔ Tensor.diagonal (p i) x=0 := by
    have hv : (i.factorial:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [diag_derivative h,smul_eq_zero,or_iff_right hv]
  constructor
  · refine fun u i hi => Tensor.ext_diag _ _ (hh.iteratedFDeriv_comp_perm) (fun _ _ => rfl) ?_
    exact funext fun x => (he i x).2 ((rays_one h n x).1 (u x) _ hi)
  exact fun u x => (rays_one h n x).2 fun i hi => (he i x).1 (by rw [u i hi]; rfl)

omit [CompleteSpace Y] in
lemma rays_from_dense (s : Set X) (hs : Dense s) (n : ℕ)
    (he : ∀ x∈s, (fun b : ℝ => f (b • x)) =O[cutRay] (fun b => b^n)) : Rays n f := by
  obtain ⟨p,h⟩ := h
  intro x; refine (rays_one h n x).2 (fun i hi => ?_)
  have hh : Continuous (Tensor.diagonal (p i)) := (Tensor.diag_smooth _ ω).continuous
  exact closure_minimal (fun b hb => (rays_one h n b).1 (he b hb) i hi) (isClosed_eq hh (continuous_const (y:=0))) (hs x)

lemma rays_at_zero : Rays 1 f ↔ f 0=0 := by
  rw [rays_jet h]; simp only [Nat.lt_one_iff,forall_eq]
  constructor
  · intro he; simpa using DFunLike.congr_fun he 0
  intro he; apply ContinuousMultilinearMap.ext; intro x
  simp [he]

lemma ray_limit {s : ℕ} (H : Rays s f) (p : X) :
    Tendsto (fun t : ℝ => (t^s)⁻¹ • f (t • p)) cutRay (𝓝 (Tensor.diagonal (Tensor.coeff f s 0) p)) := by
  obtain ⟨P,hp⟩ := h
  have he := approx hp (s+1) p
  have hh := (rays_one hp s p).1 (H p)
  have hv (b : ℝ) : P.partialSum (s+1) (b • p) = (b^s) • Tensor.diagonal (P s) p := by
    rw [← Tensor.homogeneous]
    apply Finset.sum_eq_single s
    · intro i hi he
      change Tensor.diagonal (P i) _=0
      rw [Tensor.homogeneous, hh _ (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hi)) he), smul_zero]
    simp
  have ht : Tensor.diagonal (Tensor.coeff f s 0) p=Tensor.diagonal (P s) p := by
    unfold Tensor.diagonal Tensor.coeff
    rw [_root_.smul_apply,show iteratedFDeriv ℝ s f 0 (fun _ => p)=_ from diag_derivative hp s p]
    rw [inv_smul_smul₀ (by exact_mod_cast Nat.factorial_ne_zero s)]; rfl
  simp_rw [hv] at he; rw [ht]; exact scale_limit (f:=fun t => f (t • p)) _ _ he

omit h [CompleteSpace Y] in
lemma ray_origin {s : ℕ} (H : ∀ x, ∃ k : Y, Tendsto (fun t : ℝ => (t^s)⁻¹ • f (t • x)) cutRay (𝓝 k)) : Rays s f := by
  intro x
  obtain ⟨k,h⟩ := H x
  refine isBigO_iff.mpr ⟨‖k‖+1,?_⟩
  filter_upwards [h.norm.eventually (ge_mem_nhds (lt_add_one _)),
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in cutRay,t≠0)] with i hi hv
  exact (div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero _ hv))).mp (by simpa only [norm_smul,norm_inv,inv_mul_eq_div] using hi)
end use
end YM.Stationary
end

/-! Analytic strip bookkeeping at a fixed (but arbitrary) pre-L price. -/
noncomputable section
namespace YM.Stationary
open Filter Function Laurent
open scoped Topology BigOperators ContDiff
set_option linter.unusedSectionVars false

variable {α β : Type} [Fintype α] [Fintype β] {p : Phase α} {σ τ A M : ℝ}

def axes (r : Corn α) : Phase α := fun i => ↑(r i)
@[simp] lemma axes_real (p : Corn α) : star (axes p)=axes p := by ext i; simp [axes]
@[simp] lemma axes_origin : axes (0:Corn α)=0 := by ext; simp [axes]
lemma axes_of_real (h : star p=p) : axes (fun i => (p i).re)=p := funext fun i => by
  change ((p i).re:ℂ) = _
  apply Complex.ext
  · simp
  exact (Complex.conj_eq_iff_im.mp (congr_fun h i)).symm

@[fun_prop] lemma axes_maps : ContDiff ℝ ω (axes (α:=α)) := by
  exact contDiff_pi.mpr fun i => Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)

def Firm (σ K : ℝ) (f : Phase α → ℂ) : Prop := Vane f σ ∧ ∀ p∈ Laurent.strip σ, ‖f p‖ ≤ K

namespace Firm
variable {f g : Phase α → ℂ}
lemma width_pos (h : Firm σ A f) : 0 < σ := h.1.side
lemma in_range (h : Firm σ A f) {p : Phase α} (he : star p=p) : p ∈ strip σ := Work.F07.realStrip _ h.width_pos he
lemma budget_nonneg (h : Firm σ A f) : 0 ≤ A := (norm_nonneg _).trans (h.2 0 (h.in_range (by simp)))
lemma mono (h : Firm σ A f) (hp : 0<τ) (he : τ≤σ) (ha : A≤M) : Firm τ M f := by
  let e : strip (α:=α) τ ⊆ strip σ := fun _ v i => (v i).trans_le he
  exact ⟨⟨hp,fun i hi => h.1.hol i (e hi), fun i hi => h.1.reset i (e hi)⟩,fun i hi => (h.2 i (e hi)).trans ha⟩
lemma const (hp : 0 < σ) (z : ℂ) : Firm σ ‖z‖ (fun _ : Phase α => z) :=
  ⟨⟨hp,fun _ _ => differentiableAt_const z,fun _ _ _ => rfl⟩,fun _ _ => le_rfl⟩
lemma zero (hp : 0 < σ) : Firm σ 0 (fun _ : Phase α => 0) := by simpa using const (α:=α) hp 0

variable (h : Firm σ A f)
include h
lemma add (hs : Firm σ M g) : Firm σ (A+M) (fun i => f i + g i) :=
    ⟨⟨h.width_pos,fun i hi => (h.1.hol i hi).add (hs.1.hol i hi), fun i hi u => by rw [h.1.reset i hi u, hs.1.reset i hi u]⟩,
      fun i hi => (norm_add_le ..).trans (add_le_add (h.2 i hi) (hs.2 i hi))⟩
lemma sub (hs : Firm σ M g) : Firm σ (A+M) (fun i => f i - g i) :=
    ⟨⟨h.width_pos,fun i hi => (h.1.hol i hi).sub (hs.1.hol i hi), fun i hi u => by rw [h.1.reset i hi u, hs.1.reset i hi u]⟩,
      fun i hi => (norm_sub_le ..).trans (add_le_add (h.2 i hi) (hs.2 i hi))⟩
lemma neg : Firm σ A (fun i => -f i) := by simpa using (zero (α:=α) h.width_pos).sub h
lemma mul (hs : Firm σ M g) : Firm σ (A*M) (fun i => f i * g i) :=
    ⟨⟨h.width_pos,fun i hi => (h.1.hol i hi).mul (hs.1.hol i hi), fun i hi u => by rw [h.1.reset i hi u, hs.1.reset i hi u]⟩,
      fun i hi => by rw [norm_mul]; exact mul_le_mul (h.2 i hi) (hs.2 i hi) (norm_nonneg _) h.budget_nonneg⟩
omit h in
lemma sum {ι : Type} (s : Finset ι) (f : ι → Phase α → ℂ) (A : ι → ℝ) (hσ : 0 < σ)
    (H : ∀ i ∈ s, Firm σ (A i) (f i)) : Firm σ (∑ i∈s, A i) (fun p => ∑ i ∈ s,f i p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero (α:=α) hσ
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (H i (Finset.mem_insert_self ..)).add (ih fun i hi => H _ (Finset.mem_insert_of_mem hi))

lemma comp (g : Phase β → Phase α) (ht : Differentiable ℂ g) (hp : 0<τ)
    (he : ∀ p : Phase β, p∈ strip τ → g p∈ strip σ)
    (hx : ∀ p : Phase β, ∀ x : Shift β, ∃ y : Shift α, g (p+reciprocal x)=g p+reciprocal y) : Firm τ A (f ∘ g) := by
  refine ⟨⟨hp,fun i hi => (h.1.hol _ (he i hi)).comp _ (ht _),fun i hi u => ?_⟩,fun i hi => h.2 _ (he i hi)⟩
  obtain ⟨k,hk⟩ := hx i u
  simp only [comp_apply, hk,h.1.reset _ (he i hi) k]

lemma analytic {p : Phase α} (hp : p ∈ strip σ) : AnalyticAt ℂ f p := by
  apply PolyDisc.formOf
  filter_upwards [(Work.F07.stripOpen σ).mem_nhds hp] with i hi; exact h.1.hol _ hi
lemma analytic_real (r : Corn α) : AnalyticAt ℝ (f ∘ axes) r := by
  have ht : ContDiffAt ℝ ω f (axes r) := ((h.analytic (h.in_range (axes_real r))).contDiffAt (n:=ω)).restrict_scalars ℝ
  exact (ht.comp _ axes_maps.contDiffAt).analyticAt

omit h in
lemma mode (u : Shift α) (hs : 0<σ) : Firm σ (Real.exp (σ * size u)) (fun p => Laurent.mode p u) :=
    ⟨⟨hs,fun _ _ => by unfold Laurent.mode; fun_prop,fun _ _ _ => by rw [mode_phase, mode_periodic, mul_one]⟩,
      fun i hi => reward i u σ (fun b => (hi b).le)⟩

omit h in
lemma of_series {f : Shift α → ℂ} (hf : Width σ A f) (hσ : 0<σ) : Firm σ A (Laurent.read f) := by
  refine ⟨⟨hσ,fun p hp => ?_, fun p _ u => Laurent.periodic _ _ _⟩,fun p hp => Width.estimate hf p (fun i => (hp i).le)⟩
  obtain ⟨R,hR,hK⟩ := Metric.mem_nhds_iff.mp ((Work.F07.stripOpen σ).mem_nhds hp)
  refine (Work.F02.analytic_series (fun i p => Laurent.mode p i * f i) hR
    (fun i => by unfold Laurent.mode; fun_prop) hf.2.1 (fun i p hp => ?_)).differentiableAt
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (reward p i σ (fun j => (hK hp j).le)) (norm_nonneg _)
end Firm
end YM.Stationary
end

/-! # Polarizing real analytic arrays in independent Fourier slots

`beat` is the derivative, `noteAt` the coefficient (symmetric factorial
normalization); both *ordinary complexification* in their slots, so no Ad /
star even for matrix values on phases. Use pointwise over a finite physical
shape; F02/friend inputs use Color norm or their physical basis explicitly
via coordinate changes in the applications.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Laurent Finset
open scoped Topology BigOperators ContDiff
variable {α β ι : Type} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]

abbrev RecordM (R : Type) [CommSemiring R] (i α : Type) := MultilinearMap R (fun _ : i => α → R) R

variable {R : Type} [CommSemiring R]

def recording (a : (ι → α) → R) : RecordM R ι α := ∑ i : ι → α,
    (MultilinearMap.mkPiRing R ι (a i)).compLinearMap (fun k => LinearMap.proj (i k))
lemma recording_apply (a : (ι → α) → R) (v : ι → α → R) :
    recording a v = ∑ i : ι→α, (∏ k, v k (i k))*a i := by unfold recording; rw [_root_.sum_apply]; rfl

section units
variable [DecidableEq α]

lemma expand_coord (a : RecordM R ι α) (v : ι → α → R) :
    recording (fun i => a (fun k => Pi.single (i k) 1)) v=a v := by
  rw [recording_apply]
  let g (i : ι) (b : α) := v i b • (Pi.single b (1:R))
  have he : (fun i => ∑ b : α, g i b)=v := by
    funext i x; simp [Finset.sum_apply,g,Pi.single_apply,mul_ite]
  rw [← he, a.map_sum]; rw [he]
  refine sum_congr rfl fun b _ => ?_
  rw [show a _ = _ from a.map_smul_univ (fun k => v k (b k)) (fun k => Pi.single (b k) (1:R))]
  rfl

def enlarge (a : RecordM ℝ ι α) : RecordM ℂ ι α := recording (fun i => ((a (fun k => Pi.single (i k) 1)):ℂ))

lemma enlarge_real (a : RecordM ℝ ι α) (v : ι → Corn α) : enlarge a (axes ∘ v)=(a v:ℂ) := by
  classical
  rw [← expand_coord a v]
  unfold enlarge
  rw [recording_apply,recording_apply]; push_cast; rfl
lemma enlarge_inj : Injective (enlarge (α:=α) (ι:=ι)) := by
  intro a b h; ext1 v; apply Complex.ofReal_injective; rw [← enlarge_real,← enlarge_real,h]
lemma enlarge_unique (a b : RecordM ℂ ι α) (he : ∀ v : ι → Corn α, a (axes ∘ v)=b (axes ∘ v)) : a=b := by
  classical
  ext1 v; rw [← expand_coord a v, ← expand_coord b v]; congr 2
  ext1 i
  have H := he (fun k => Pi.single (i k) 1)
  rw [show axes ∘ (fun k => Pi.single (i k) 1) = (fun k => Pi.single (i k) 1) by
    funext a b; simp [axes,Pi.single_apply]; split <;> simp] at H
  exact H
lemma enlarge_bar (a : RecordM ℝ ι α) (v : ι → Phase α) : star (enlarge a v)=enlarge a (star v) := by
  simp only [enlarge,recording_apply,star_sum,star_mul,star_prod, Pi.star_apply]
  apply sum_congr rfl; intro k _; rw [mul_comm,Complex.star_def,Complex.conj_ofReal]
end units

section continuity
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]
lemma wired {f : Y → Z} (L : X →L[ℝ] Y) {x : X} (hf : AnalyticAt ℝ f (L x)) [CompleteSpace Z] (n : ℕ) (v : Fin n → X) :
    iteratedFDeriv ℝ n (f ∘ L) x v = iteratedFDeriv ℝ n f (L x) (L ∘ v) := by
  obtain ⟨s,hO,hs,he⟩ := (hf.contDiffAt (n:=ω)).contDiffOn' (m:=ω) le_rfl (by simp)
  have hy : ContDiffOn ℝ ω f s := by simpa using he
  have H := DFunLike.congr_fun (L.iteratedFDerivWithin_comp_right hy (hO.uniqueDiffOn) ((hO.preimage L.continuous).uniqueDiffOn) hs (show (↑n : WithTop ℕ∞)≤ω from le_top)) v
  rw [iteratedFDerivWithin_of_isOpen n (hO.preimage L.continuous) (show x ∈ L ⁻¹' s from hs), iteratedFDerivWithin_of_isOpen n hO hs] at H
  exact H
end continuity

section jets
variable [DecidableEq α] [DecidableEq β] {n : ℕ} {x : Corn α}

def beat (f : Corn α → ℝ) (x : Corn α) (n : ℕ) : RecordM ℂ (Fin n) α := enlarge (iteratedFDeriv ℝ n f x).toMultilinearMap
def noteAt (f : Corn α → ℝ) (n : ℕ) : RecordM ℂ (Fin n) α := ((n.factorial:ℂ)⁻¹) • beat f 0 n
lemma beat_real (f : Corn α → ℝ) (v : Fin n → Corn α) : beat f x n (axes ∘ v) = ↑((iteratedFDeriv ℝ n f x) v) := enlarge_real ..
lemma note_real (f : Corn α → ℝ) (v : Fin n → Corn α) : noteAt f n (axes ∘ v) = ↑((Tensor.coeff f n 0) v) := by
  rw [noteAt, _root_.smul_apply, beat_real]; simp [Tensor.coeff]
lemma note_map (f : Corn α → ℝ) (n : ℕ) : noteAt f n = enlarge (Tensor.coeff f n 0).toMultilinearMap := enlarge_unique _ _ fun v => (note_real f v).trans (enlarge_real _ v).symm
lemma from_note (f g : Corn α → ℝ) (n : ℕ) (h : noteAt f n=noteAt g n) : iteratedFDeriv ℝ n f 0=iteratedFDeriv ℝ n g 0 := by
  have hf : ((n.factorial:ℂ)⁻¹)≠0 := by exact inv_ne_zero (by exact_mod_cast n.factorial_ne_zero)
  have he := smul_right_injective _ hf h
  exact ContinuousMultilinearMap.toMultilinearMap_injective (enlarge_inj he)

lemma note_fixed (f : Corn α → ℝ) (v : Fin n → Phase α) : star (noteAt f n v)=noteAt f n (star v) := by rw [note_map,enlarge_bar]
lemma note_perm (f : Corn α → ℝ) (h : AnalyticAt ℝ f 0) (v : Fin n→Phase α) (s : Equiv.Perm (Fin n)) : noteAt f n (v ∘ s) = noteAt f n v := by
  suffices he : (noteAt f n).domDomCongr s=noteAt f n from DFunLike.congr_fun he v
  apply enlarge_unique; intro v
  change noteAt f n (axes ∘ (v ∘ s))=noteAt _ _ (axes ∘ v)
  rw [note_real,note_real,Tensor.coeff_symm h.contDiffAt v s]
end jets
end YM.Stationary
end

/-! The head of a Taylor jet after passage along a germ. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset
open scoped Topology BigOperators ContDiff

section atoms
open OrderedFinpartition
lemma atom_left (n) : (atomic n).extendLeft=atomic (n+1) := by
  have hp (i : Fin (n+1)) : ((atomic n).extendLeft).partSize i=1 := by cases i using Fin.cases <;> rfl
  have hh (i : Fin (n+1)) (j) : ((atomic n).extendLeft).emb i j=i := by cases i using Fin.cases <;> rfl
  unfold extendLeft atomic; congr!
  · exact hp _
  · exact hp _
  rename_i H i u e j j' h; exact (hh i j).trans e
lemma allSingle {n : ℕ} (c : OrderedFinpartition n) (hc : c.length = n) : c=atomic n := by
  induction n with
  | zero => exact Subsingleton.elim ..
  | succ i ih =>
    obtain ⟨⟨b,h|k⟩,rfl⟩ := (extendEquiv i).surjective c
    · change b.length+1=i+1 at hc; rw [ih b (Nat.succ.inj hc)]; exact atom_left i
    change b.length=i+1 at hc; have hh := b.length_le; omega
end atoms

variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- first unseen jet, even with a constant. -/
lemma quiet_comp {n : ℕ} {F : X → Y} {G : Y → Z} (x : X) (h : AnalyticAt ℝ F x)
    (hp : AnalyticAt ℝ G (F x)) (hu : ∀ i : ℕ, i<n → 0 < i → iteratedFDeriv ℝ i G (F x)=0)
    (v : Fin n → X) :
    iteratedFDeriv ℝ n (G ∘ F) x v = iteratedFDeriv ℝ n G (F x) (fderiv ℝ F x ∘ v) := by
  cases n with
  | zero => simp
  | succ i =>
    rw [iteratedFDeriv_comp (hp.contDiffAt (n:=ω)) h.contDiffAt le_top]
    unfold FormalMultilinearSeries.taylorComp
    rw [_root_.sum_apply,Finset.sum_eq_single (OrderedFinpartition.atomic (i+1))]
    · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
        OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
      change iteratedFDeriv ℝ (i+1) G (F x) (fun b => iteratedFDeriv ℝ 1 F x (fun _ => v b))=_
      simp only [iteratedFDeriv_one_apply]; rfl
    · intro b _ hb
      have hx : b.length < i+1 := lt_of_le_of_ne b.length_le (fun h => hb (allSingle b h))
      simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hu _ hx (b.length_pos (by omega))]; rfl
    simp
end YM.Stationary
end
