import YM.Next.STATIONARY.Lift.Ward



set_option autoImplicit false
/-! # Dimension-free M-test for local extensions -/
noncomputable section
namespace YM.Stationary
open Function Metric Finset Laurent Filter
open scoped Topology ContDiff BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]
    {n : ℕ} {R A : ℝ}

def circleTax (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => circleTax R n / (R / 2^(n+1))
lemma circleTax_pos (h : 0<R) (n : ℕ) : 0 < circleTax R n := by
  induction n with
  | zero => simp [circleTax]
  | succ k ih => unfold circleTax; positivity

section pass
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (x : X) (hr : 0 < R)
include hr

omit [CompleteSpace Y] in
lemma outline {f : X → Y} (h : ContDiff ℂ ω f) (hf : ∀ y ∈ ball x R, ‖f y‖ ≤ A) (n : ℕ) :
    ∀ y ∈ ball x (R / 2^n), ‖iteratedFDeriv ℂ n f y‖ ≤ A*circleTax R n := by
  induction n with
  | zero => simpa [circleTax,norm_iteratedFDeriv_zero] using hf
  | succ k ih =>
    intro y hy
    have he : 0<R / 2^k := by positivity
    have hh : R / 2^(k+1)= R / 2^k / 2 := by rw [pow_succ]; ring
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.norm_map,circleTax,
      hh, ← mul_div_assoc]
    exact Work.F02.fderiv_bound (h.differentiable_iteratedFDeriv (by simp)) he ih (hh ▸ hy)

omit hr in
private lemma tsum_local {ι : Type} {f : ι → X → Y} {f' : ι → X → X →L[ℂ] Y} {u : ι → ℝ}
    (he : Summable u) {s : Set X} (hs : IsOpen s) (hp : IsPreconnected s) (hx : x∈s)
    (hf : Summable fun i => f i x) (hg : ∀ i z, z∈s → HasFDerivAt (f i) (f' i z) z)
    (hw : ∀ i z, z∈s → ‖f' i z‖ ≤ u i) (g : X → Y) (hM : g =ᶠ[𝓝 x] fun z => ∑' i,f i z) :
    HasSum (fun i => f' i x) (fderiv ℂ g x) := by
  have hH := hasFDerivAt_tsum_of_isPreconnected he hs hp hg hw hx hf hx
  rw [(hH.congr_of_eventuallyEq hM).fderiv]; exact (Summable.of_norm_bounded he (fun i => hw i x hx)).hasSum

set_option maxHeartbeats 600000 in
lemma circles {ι : Type} (f : ι → X → Y) {A : ι → ℝ} (ha : Summable A) (h : ∀ i, ContDiff ℂ ω (f i))
    (hf : ∀ i y, y ∈ ball x R → ‖f i y‖ ≤ A i) (n : ℕ) :
    ∀ y ∈ ball x (R/2^n), HasSum (fun i => iteratedFDeriv ℂ n (f i) y)
      (iteratedFDeriv ℂ n (fun z => ∑' i, f i z) y) := by

  induction n with
  | zero =>
    simp_rw [pow_zero,div_one,iteratedFDeriv_zero_eq_comp, Function.comp_apply]; intro y hy
    let M := (continuousMultilinearCurryFin0 ℂ X Y).symm.toContinuousLinearEquiv
    exact M.toContinuousLinearMap.hasSum ((Summable.of_norm_bounded ha (f:=fun i => f i y) (fun i => hf i y hy)).hasSum)
  | succ k ih =>
    let T := ball x (R/2^(k+1))
    have he : T ⊆ ball x (R/2^k) := by unfold T; apply ball_subset_ball; gcongr <;> [norm_num; omega]
    intro y hy
    let F (i : ι) := iteratedFDeriv ℂ k (f i)
    have hs i : Differentiable ℂ (F i) := (h i).differentiable_iteratedFDeriv (by simp)
    have hx i z (hz : z∈ T) : ‖fderiv ℂ (F i) z‖ ≤ A i*circleTax R (k+1) := by
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,LinearIsometryEquiv.norm_map] using outline x hr (h i) (hf i) _ z hz
    have u := ha.mul_right (circleTax R (k+1))
    have hu : IsPreconnected T := by
      letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
      exact (convex_ball ..).isPreconnected
    have hn : Summable (fun i => F i y) := (ih y (he hy)).summable
    have hE := tsum_local (f:=F) y u isOpen_ball hu hy hn
      (fun i z _ => (hs i z).hasFDerivAt) hx (iteratedFDeriv ℂ k (fun z => ∑' i, f i z))
      ((show ∀ᶠ z in 𝓝 y,z∈T from isOpen_ball.mem_nhds hy).mono
        (fun z hz => (ih z (he hz)).tsum_eq.symm))
    simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k+1) => X) Y).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hE
end pass

section sup
variable {g : Phase α → ℂ} {f : Corn α → ℝ}
    (h : g ∘ axes = Complex.ofRealCLM ∘ f) (he : AnalyticAt ℂ g 0)

def axisCL (α : Type) [Fintype α] : Corn α →L[ℝ] Phase α := ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)
include h he

omit [DecidableEq α] in
lemma earth_cont : AnalyticAt ℝ f 0 := by
  let L := axisCL α
  have hf : f=Complex.reCLM ∘ g ∘ axes := by rw [h]; rfl
  have hh : ContDiffAt ℝ ω g (L 0) := by rw [map_zero]; exact (he.contDiffAt (n:=ω)).restrict_scalars ℝ
  rw [hf]; exact (Complex.reCLM.analyticAt _).comp ((hh.comp 0 L.contDiff.contDiffAt).analyticAt)
lemma mix_extension (b : Fin n → Phase α) : beat f 0 n b = iteratedFDeriv ℂ n g 0 b := by
  have hs : AnalyticAt ℝ f 0 := earth_cont h he
  have hu := (he.contDiffAt (n:=(↑n:WithTop ℕ∞))).restrictScalars_iteratedFDeriv (𝕜:=ℝ)
  apply DFunLike.congr_fun (?_ : beat f 0 n=(iteratedFDeriv ℂ n g 0).toMultilinearMap)
  refine enlarge_unique _ _ fun v => ?_
  rw [beat_real]; let L := axisCL α
  change _=iteratedFDeriv ℂ n g 0 _
  calc
    _ = iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) 0 v := by
      rw [Complex.ofRealCLM.iteratedFDeriv_comp_left (hs.contDiffAt (n:=ω)) le_top]; rfl
    _ = iteratedFDeriv ℝ n g 0 (L ∘ v) := by
      rw [← h]
      change iteratedFDeriv ℝ n (g ∘ L) 0 v=_
      rw [wired L (by rw [map_zero]; exact ((he.contDiffAt (n:=ω)).restrict_scalars ℝ).analyticAt),map_zero]
    _ = _ := by rw [← hu]; rfl
end sup

lemma mixtape {ι : Type} (f : ι → Corn α → ℝ) (g : ι → Phase α → ℂ) {A : ι → ℝ} (hu : 0 < R)
    (hA : Summable A) (hg : ∀ i, ContDiff ℂ ω (g i)) (hv : ∀ i x, x∈ball 0 R → ‖g i x‖≤A i)
    (hx : ∀ i, g i ∘ axes=Complex.ofRealCLM ∘ f i) (n : ℕ) (b : Fin n → Phase α) :
    HasSum (fun i => noteAt (f i) n b) (noteAt (fun x => ∑' i,f i x) n b) := by
  have hh := Work.F02.analytic_series g hu (fun i => (hg i).differentiable (by simp)) hA hv
  have he : (fun x => ∑' i,g i x) ∘ axes=Complex.ofRealCLM ∘ (fun x => ∑' i,f i x) := by
    funext x; dsimp only [Function.comp_apply]; simp_rw [show ∀ i,g i (axes x)=_ from fun i => congr_fun (hx i) x]
    exact (Complex.ofReal_tsum _).symm
  have ht := circles (0:Phase α) hu g hA hg hv n 0 (mem_ball_self (by positivity))
  have hB i := mix_extension (hx i) ((hg i).contDiffAt.analyticAt) b
  unfold noteAt; simp_rw [_root_.smul_apply,mix_extension he hh,hB]
  exact ((ContinuousMultilinearMap.apply ℂ _ ℂ b).hasSum ht).const_smul _

lemma mixtape_cost {f : Corn α → ℝ} {g : Phase α → ℂ} (hr : 0<R)
    (hg : ContDiff ℂ ω g) (hv : ∀ x∈ball 0 R, ‖g x‖≤A)
    (hx : g ∘ axes=Complex.ofRealCLM ∘ f) (n : ℕ) (b : Fin n → Phase α) :
    ‖noteAt f n b‖ ≤ ((n.factorial:ℝ)⁻¹ * (A*circleTax R n))*(∏ i, ‖b i‖) := by
  have ht := outline _ hr hg hv n 0 (mem_ball_self (by positivity))
  rw [noteAt, _root_.smul_apply, mix_extension hx hg.contDiffAt.analyticAt,norm_smul,norm_inv,norm_natCast]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_right ht (by positivity))) (by positivity)
end YM.Stationary
end

/-!
# Reading a local action atom

Each atom gets its own auxiliary torus (contains *whole* stencil). Purely to
extract the symbol. All actual torus reads still use the same atom and the
norms are pre-L. Complexification of any link here occurs only in its Lie log
coordinate, supplies unmasked derivatives. `R` is NOT a radius for the
critical implicit graph.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {m : Side} {σ A R : ℝ} {t n : ℕ}

-- Site radius read on the *Cover*.
def village (d : ℕ) : Side := ⟨2*d+1,by omega⟩
lemma farlift {a} (i : Site (village a)) : lift i∈box a := by
  apply box_test.mpr
  have h (j : Axis) := lift_centers i j
  rw [show (village a).val=2*a+1 from rfl] at h; push_cast at h; constructor <;> intro j <;> specialize h j <;> omega
lemma inclusive {a i} (h : i∈box a) : lift (wrap (village a) i)=i := lift_eq_iff.mpr ⟨rfl,fun j => by
    have hv := (box_test.mp h).1 j; have hh := (box_test.mp h).2 j
    rw [show (village a).val=2*a+1 from rfl]; push_cast; omega⟩
lemma farsum {a} (i : Site (village a)) : size (lift i) ≤ 4*a := by
  have h := box_test.mp (farlift i)
  unfold Laurent.size
  calc
    _ ≤ ∑ _ : Axis,a := sum_le_sum fun j _ => by have hx := h.1 j; have hy := h.2 j; omega
    _ = _ := by simp

def localAtom (F : CoverConfig G → ℝ) (x : Site m) (p : Link G m) := F (expandAt x (input G m p))

section port
variable (d : ℕ) (F : CoverConfig G → ℝ)

def patchCopy {B : Type} [CommRing B] (x : Site m) : (Lines G m 1→B) →ₗ[B] (Lines G (village d) 1→B) := LinearMap.pi fun i => LinearMap.proj (wrap m (lift i.1)+x,i.2)

def VaultOn (G : Gauge) (F : CoverConfig G → ℝ) (R A : ℝ) := ∀ m (x : Site m),
    ∃ g : Phase (Lines G m 1) → ℂ, ContDiff ℂ ω g ∧ (∀ i∈ball 0 R, ‖g i‖ ≤ A) ∧
      g ∘ axes=Complex.ofRealCLM ∘ localAtom F x

theorem VaultOn.native (h : VaultOn G F R A) (p : Site m) : AnalyticAt ℝ (localAtom F p) 0 := by
  obtain ⟨g,hg,_,hv⟩ := h _ p; exact earth_cont hv hg.contDiffAt.analyticAt

variable (hx : LocalOn ↑(box d) F)
include hx

lemma inhabit (x : Site m) : localAtom F x=localAtom F (0 : Site (village d)) ∘ patchCopy (G:=G) d x := by
  funext p; apply hx
  rintro ⟨a,i⟩ ha hb
  unfold expandAt
  simp_rw [add_zero,encode_link]
  congr 1; ext1 j; simp [arm_apply,patchCopy,inclusive (show a∈box d from ha)]
omit hx in
def motif (u : Fin (t+1) → Momentum) (x : Ink G (t+1)) (b : Run (t+1)) : Fin (t+1) → Phase (Lines G (village d) 1) := fun i j => if j.2=(b i,x i) then mode (u i) (lift j.1) else 0

lemma copies (p : Site m) (u : Fin (t+1) → Site m) (w : Fin (t+1) → Momentum) (he : ∀ i, rolls (mon (u i)) (w i)) i b
    (h : VaultOn G F R A) : noteAt (localAtom F p) (t+1) (glyph u i b) =
      cell (∑ j, u j) p * noteAt (localAtom F 0) (t+1) (motif d w i b) := by
  let L := (patchCopy (B:=ℝ) (G:=G) d p).toContinuousLinearMap
  have hh (x) : axes (L x)= patchCopy d p (axes x) := rfl
  rw [inhabit d F hx]
  change noteAt (localAtom F _ ∘ L) _ _=_
  rw [note_comp L _ hh (VaultOn.native F h _) (t+1),MultilinearMap.compLinearMap_apply]
  rw [show (fun i => patchCopy _ _ _)=(fun k => cell (u k) p • motif d w i b k) by
    funext k j; unfold glyph patchCopy relay tune
    simp only [LinearMap.pi_apply,LinearMap.proj_apply,cell_add,cell_wrap,motif,Pi.single_apply,
      Pi.smul_apply,smul_eq_mul]
    split_ifs with heq <;> simp only [mul_zero,mul_one]; rw [(he k).exp, mul_comm],
    (noteAt (localAtom F _) (t+1)).map_smul_univ,smul_eq_mul]
  congr 1
  suffices hv : ∀ s : Finset (Fin (t+1)), (∏ j ∈ s, cell (u j) p) = cell (∑ i ∈ s, u i) p from hv univ
  intro s; induction s using Finset.induction with
  | empty => simp [cell_duality _ p]
  | insert i s hs ih => rw [prod_insert hs, sum_insert hs, ih, cell_duality (_+_),cell_add,cell_duality p,cell_duality p]
end port

section bulletin
variable (F : CoverConfig G→ℝ) (d : ℕ)

def recital (F : CoverConfig G→ℝ) (d t : ℕ) : Picture G t := fun i x p => noteAt (localAtom F 0) _ (motif d (plotted p) i x)

def recitalScale (t d : ℕ) (σ : ℝ) := Real.exp ((t+1)^2*σ*(4*d))

def costNote n R := (n.factorial:ℝ)⁻¹ * circleTax R n

lemma tilted (p : Space t) (hp : p∈strip σ) (hs : 0<σ) j : plotted p j∈strip ((t+1)*σ) := by
  have hA : σ≤(↑t+1)*σ := by nlinarith [show 0 ≤ (t:ℝ) from by positivity]
  refine Fin.cases ?_ (fun j => ?_) j
  · intro i
    simp only [plotted,Fin.cons_zero,missing, Pi.neg_apply,Finset.sum_apply,Complex.neg_im,abs_neg,Complex.im_sum]
    apply (abs_sum_le_sum_abs ..).trans_lt
    calc
      _ ≤ ∑ _ : Fin t,σ := sum_le_sum fun j _ => (hp (j,i)).le
      _ < _ := by simp; linarith
  simp only [plotted,Fin.cons_succ]; exact fun i => (hp _).trans_le hA

lemma platform_diffs (i : Fin (t+1)) : Differentiable ℂ (fun p : Space t => plotted p i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine differentiable_pi.mpr (fun a => ?_); simp only [plotted,Fin.cons_zero, missing, Pi.neg_apply,Finset.sum_apply, Function.comp_def]; fun_prop
  refine differentiable_pi.mpr (fun a => ?_); simp only [plotted,Fin.cons_succ,projected,Function.comp_def]; fun_prop

theorem recital_entire (i : Ink G (t+1)) (x : Run (t+1)) : Differentiable ℂ (recital F d t i x) := by
  unfold recital
  have he j z : Differentiable ℂ (fun p : Space t => motif d (plotted p) i x j z) := by
    unfold motif; split
    next h => exact (show Differentiable ℂ (fun p : Momentum => mode p (lift z.1)) by unfold mode; fun_prop).comp (platform_diffs j)
    exact differentiable_const _
  let f := noteAt (localAtom F (0:Site (village d))) (t+1)
  change Differentiable ℂ (fun p => f (motif d (plotted p) i x))
  have hu : f=recording (fun v => f (fun j => Pi.single (v j) 1)) := MultilinearMap.ext fun v => (expand_coord _ _).symm
  rw [hu]; simp_rw [recording_apply]
  fun_prop

lemma recital_cost (h : VaultOn G F R A) (hs : 0<σ) (hr : 0<R) (i : Ink G (t+1)) (x : Run (t+1)) :
    Firm σ (A*costNote (t+1) R * recitalScale t d σ) (recital F d t i x) := by
  constructor
  · refine ⟨hs, fun a _ => recital_entire F d _ _ a,fun p _ z => ?_⟩
    unfold recital; congr 1
    funext a j; unfold motif; split
    · exact ((projections_roll (show rolls p (p+reciprocal z) from ⟨z,rfl⟩) a).exp _).symm
    rfl
  obtain ⟨f,hf,hG,hx⟩ := h _ (0:Site (village d))
  intro p hp
  let N := Real.exp (((t:ℝ)+1)*σ*(4*d))
  have ht j : ‖motif d (plotted p) i x j‖ ≤ N := by
    apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
    intro k; unfold motif; split
    · have hv := tilted p hp hs j
      apply (reward _ _ _ (fun a => (hv a).le)).trans
      apply Real.exp_monotone; gcongr
      exact_mod_cast (farsum k.1)
    rw [norm_zero]; exact (Real.exp_pos _).le
  unfold recital
  apply (mixtape_cost hr hf hG hx (t+1) (motif _ _ _ _)).trans
  have he : 0 ≤ A := (norm_nonneg _).trans (hG _ (mem_ball_self hr))
  calc
    _ ≤ (( (t+1).factorial : ℝ)⁻¹*(A*circleTax R (t+1)))*(∏ _ : Fin (t+1), N) := by
      have := circleTax_pos hr (t+1); gcongr; exact ht _
    _ = _ := by
      simp only [prod_const,card_univ,Fintype.card_fin,N, ← Real.exp_nat_mul,costNote,recitalScale]
      push_cast; ring_nf
end bulletin
end YM.Stationary
end

/-!
# The radii are pre-L for the unmasked terms

Apply locality on each individual full term. `VaultOn` bound may grow with its
length; here use it to estimate the full Fourier series before moving to a
particular mesh. No Cauchy assertion about masked functions.
-/

noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {m : Side} {σ A R : ℝ}

lemma local_price (F : CoverConfig G→ℝ) (d t : ℕ) (hl : LocalOn ↑(box d) F) (h : VaultOn G F R A)
    (p : Fin (t+1) → Site m) i b :
    ∑ x : Site m,noteAt (localAtom F x) (t+1) (glyph p i b)=collected (recital F d t) p i b := by
  unfold collected; split
  next hp =>
    simp_rw [copies d F hl _ p (plotted _) (fun j => (ties hp j).symm) i b h,hp,cell_duality (0:Site m), cell_origin,one_mul]
    rw [sum_const,card_univ,nsmul_eq_mul]; rfl
  next hp =>
    have he y := copies d F hl y p (fun j => mon (p j)) (fun _ => rolls.refl _) i b h
    simp_rw [he]; rw [← Finset.sum_mul, sum_cell hp,zero_mul]

def chorus {ι : Type} (F : ι → CoverConfig G → ℝ) (m : Side) : Link G m → ℝ := fun v => ∑ x : Site m, ∑' i : ι, localAtom (F i) x v

theorem gathered {ι : Type} (F : ι → CoverConfig G → ℝ) (d : ι → ℕ) (w : ι → ℝ) (ht : Summable w)
    (hs : 0<σ) (hr : 0<R) (h : ∀ i, VaultOn G (F i) R (w i)) (hx : ∀ i, LocalOn ↑(box (d i)) (F i))
    (t : ℕ) (hp : SumBudget (fun i => w i*recitalScale t (d i) σ) A) :
    (∀ m : Side, AnalyticAt ℝ (chorus F m) 0) ∧ ∃ Y : Picture G t, (∀ i j, Firm σ (A*costNote (t+1) R) (Y i j)) ∧
      ∀ m : Side, Recorded Y (chorus F m) 0 := by
  -- use separate contours on the actual real link pull
  choose g hg hv Hg using fun (i : ι) m (x : Site m) => h i m x
  have ho : 0≤costNote (t+1) R := mul_nonneg (by positivity) (circleTax_pos hr _).le
  have hi m (x : Site m) : AnalyticAt ℝ (fun v => ∑' i, localAtom (F i) x v) 0 := by
    have he (i v) : g i m x (axes v)=↑(localAtom (F i) x v) := congr_fun (Hg i m x) v
    apply earth_cont (g:=fun p : Phase (Lines G m 1) => ∑' i,g i m x p)
    · funext v; simp_rw [Function.comp_apply,he]; exact (Complex.ofReal_tsum _).symm
    exact Work.F02.analytic_series (fun i => g i m x) hr (fun i => (hg i m x).differentiable (by simp)) ht (fun i p => hv i m x p)
  let Y i b p := ∑' j, recital (F j) (d j) t i b p
  refine ⟨fun m => ?_,Y,fun i b => ?_,fun m p i b => ?_⟩
  · exact (ContDiffAt.sum (n:=ω) (fun i _ => (hi m i).contDiffAt)).analyticAt
  · let W j := w j * costNote (t+1) R * recitalScale t (d j) σ
    have hm j : W j=w j * recitalScale t (d j) σ * costNote (t+1) R := by unfold W; ring
    have hu j : Firm σ (W j) (recital (F j) (d j) t i b) := recital_cost _ _ (h j) hs hr _ _
    have he : Summable W := by rw [show W=_ from funext hm]; exact hp.2.1.mul_right _
    refine ⟨⟨hs,fun p hx => ?_,fun p hp u => tsum_congr fun j => (hu j).1.reset p hp u⟩,fun p hp' => ?_⟩
    · obtain ⟨δ,hδ,H⟩ := Metric.mem_nhds_iff.mp ((Work.F07.stripOpen σ).mem_nhds hx)
      exact (Work.F02.analytic_series (fun j => recital (F j) _ _ i b) hδ (fun j => recital_entire (F j) (d j) i b) he (fun i z hz => (hu i).2 z (H hz))).differentiableAt
    have hh j := (hu j).2 p hp'
    have ha := (he.of_nonneg_of_le (fun _ => norm_nonneg _) hh)
    refine (norm_tsum_le_tsum_norm ha).trans ((ha.tsum_le_tsum hh he).trans ?_)
    rw [show W=_ from funext hm,tsum_mul_right]; exact mul_le_mul_of_nonneg_right hp.2.2 ho
  · apply norm_le_zero_iff.mpr; apply sub_eq_zero.mpr
    unfold chorus; rw [note_sum _ (hi m), _root_.sum_apply]
    let T (x : Site m) j := noteAt (localAtom (F j) x) (t+1) (glyph p i b)
    have hh (x : Site m) := mixtape (fun j => localAtom (F j) x) (fun j => g j m x) hr ht (fun j => hg j m x)
      (fun j => hv j m x) (fun j => Hg j m x) (t+1) (glyph p i b)
    calc
      _ = ∑ x : Site m, ∑' j, T x j := sum_congr rfl fun i _ => (hh i).tsum_eq.symm
      _ = ∑' j, collected (recital (F j) (d j) t) p i b := by
        rw [← Summable.tsum_finsetSum (f:=T) (fun j _ => (hh j).summable)]; exact tsum_congr fun j => local_price _ _ _ (hx j) (h j) p i b
      _ = _ := by unfold collected Y; split <;> simp [tsum_mul_left]
end YM.Stationary
end

/-!
# The actual orientation orbit on the real mesh

Handle relative phases also at Nyquist. The same statements will be used
when testing symmetries of determinant jets in the period limit.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal
variable {G : Gauge} {t : ℕ} {m : Side} {σ A : ℝ}

variable (s : Signed)
def rotatePhase (p : Space t) : Space t := fun x => s⁻¹.act (projected (strand x.1) p) x.2
lemma rotate_lifts (p : Fin (t+1) → Site m) (x : Space t) (hx : rolls (outphase p) x) :
    rolls (outphase (s⁻¹.act ∘ p)) (rotatePhase s x) := by
  apply rolls_keys; intro i
  have hg := projections_roll hx i.succ
  apply rolls_of_mode; intro b
  let f := p i.succ
  have he : mode (mon (s⁻¹.act f)) b = cell f (wrap m (s.act b)) := by
    rw [← cell_wrap,← wrap_signed,← mirror_cell s⁻¹ f (s.act (wrap m b)),s.inv_act]
  change mode (mon (s⁻¹.act f)) b = mode (s⁻¹.act (projected (strand i) x)) b
  rw [he, ← act_phase s (s⁻¹.act _) b,s.act_inv,cell_wrap]
  have hv : rolls (mon f) (projected (strand i) x) := by simpa only [plotted,Fin.cons_succ] using! hg
  exact hv.exp _

lemma rotation_cont : Continuous (rotatePhase s (t:=t)) := by
  refine continuous_pi fun j => ?_; unfold rotatePhase Signed.act projected; simp only [Function.comp_apply]; split <;> fun_prop
lemma rotation_pays {f : Space t → ℂ} (hf : Firm σ A f) : Firm σ A (f ∘ rotatePhase s) := by
  refine hf.comp (rotatePhase s) (differentiable_pi.mpr (fun j => ?_)) hf.width_pos (fun p hp j => ?_) fun p x => ?_
  · unfold rotatePhase Signed.act projected; simp only [Function.comp_apply]; split <;> fun_prop
  · unfold rotatePhase Signed.act; split
    · rw [Complex.neg_im,abs_neg]; exact hp _
    exact hp _
  refine ⟨fun j => s⁻¹.act (x ∘ strand j.1) j.2, ?_⟩
  funext j; simp only [rotatePhase,projected,Signed.act,Function.comp_apply, Pi.add_apply,reciprocal]; split <;> simp
  abel

lemma rotjet {f : Space t → ℂ} {n : ℕ} (hf : Rays n (f ∘ axes)) : Rays n ((f ∘ rotatePhase s) ∘ axes) := by
  intro p
  let q : Corn (Keys t) := fun i => s⁻¹.act (p ∘ strand i.1) i.2
  apply (hf q).congr_left; intro k
  change f _=f _; congr 1
  ext1 i
  simp only [rotatePhase,axes,q, Pi.smul_apply, Signed.act, projected,Function.comp_apply]; split <;> simp

lemma path_roll (x : Fin (t+1) → Site m) (h : ∑ i,x i=0) (y : Space t) (hy : rolls (outphase x) y) (k : Fin (t+1) → Axis) j :
    reflectFee s (plotted y j) (k j)=reflectFee s (mon (x j)) (k j) := by
  have he := ((projections_roll hy j).symm.trans (ties h _)).exp
  unfold reflectFee; split <;> simp only [he]

variable (F : Link G m → ℝ)

lemma record_exact (L : Picture G t) : Recorded L F 0 ↔ ∀ p i b,
    noteAt F _ (glyph p i b)=collected (m:=m) L p i b := by simp [Recorded,sub_eq_zero]

-- price under pull on THAT drawing
def rotPix (L : Picture G t) : Picture G t := fun i v p =>
    let r := s.perm.symm ∘ axisEquiv.symm ∘ v
    (∏ j, reflectFee s (plotted p j) (r j))* L i (coord ∘ r) (rotatePhase s p)



lemma pix_records {L : Picture G t} (hf : AnalyticAt ℝ F 0) (hp : ∀ i j,Firm σ A (L i j))
    (hz : Recorded L F 0) : Recorded (rotPix s L) (F ∘ orderTurn s) 0 := by
  apply (record_exact _ _).2
  intro p i b
  let r := s.perm.symm ∘ axisEquiv.symm ∘ b
  have hh : (fun j => coord (s.perm (r j)))=b := by
    ext1 j; simp only [r,Function.comp_apply,s.perm.apply_symm_apply]; exact axisEquiv.apply_symm_apply _
  conv_lhs => rw [← hh,priceNote F hf]
  let k := s⁻¹.act ∘ p
  have hK : ∑ j,k j=s⁻¹.act (∑ j,p j) := (map_sum (s⁻¹.actEquiv (R:=Per m)) p univ).symm
  rw [(record_exact F L).1 hz]; change _ * collected L k i _ = collected (rotPix s L) _ _ _; unfold collected
  have hP : (∑ j,k j)=0 ↔ (∑ j,p j)=0 := by
    rw [hK]; conv_lhs => rhs; rw [← show s⁻¹.act 0=(0:Site m) from Signed.act_zero _]
    exact s⁻¹.act_injective.eq_iff
  simp only [hP]
  split <;> rename_i h'
  · have hi := rotate_lifts s p _ (rolls.refl (outphase p))
    let X := hp i (coord ∘ r)
    rw [show L i (fun j => coord (r j)) (outphase k) = L i (coord ∘ r) (rotatePhase s (outphase p)) from hi.apply X
      (X.in_range (out_real k))]
    have hy := path_roll s p h' _ (rolls.refl (outphase p)) r
    unfold rotPix; dsimp only; simp_rw [← hy]; apply mul_left_comm
  rw [mul_zero]
lemma reciprocal_fold (y : Space t) (z : Shift (Keys t)) (i : Fin (t+1)) : rolls (plotted y i) (plotted (y+reciprocal z) i) := projections_roll (by exact ⟨z,rfl⟩) _

lemma reflect_firm (h : 0<σ) (i : Fin (t+1)) (k : Axis) :
    Firm σ (Real.exp (((t:ℝ)+1)*σ)) (fun p : Space t => reflectFee s (plotted p i) k) := by
  unfold reflectFee
  split
  · apply Firm.neg
    refine ⟨⟨h, fun p hp => (DifferentiableAt.comp _ (g:=fun y : Momentum => mode y (-step (s.perm k))) (by unfold mode; fun_prop) (platform_diffs i _)),
      fun p _ z => ((reciprocal_fold p z i).exp _).symm⟩,fun p hp => ?_⟩
    have hy : Laurent.size (step (s.perm k):Cover)=1 := by
      unfold Laurent.size; rw [sum_eq_single (s.perm k)] <;> simp_all
    simpa only [size_neg, hy,Nat.cast_one,mul_one] using reward (plotted p i) (-(step (s.perm k))) (((t:ℝ)+1)*σ) fun j => (tilted p hp h i j).le
  apply (Firm.const h 1).mono h le_rfl; rw [norm_one]; exact Real.one_le_exp (by positivity)

lemma firmProd {α ι : Type} [Fintype α] (l : Finset ι) (f : ι → Phase α→ℂ) (A : ι → ℝ) (hp : 0<σ) (h : ∀ i∈l, Firm σ (A i) (f i)) : Firm σ (∏ i∈l,A i) (fun p => ∏ i∈l,f i p) := by
  classical
  induction l using Finset.induction with
  | empty => simpa using Firm.const (α:=α) hp 1
  | insert a l ha H =>
    simp_rw [Finset.prod_insert ha]; exact (h a (Finset.mem_insert_self ..)).mul (H fun i hi => h i (Finset.mem_insert_of_mem hi))

def reflectBill (t : ℕ) (σ : ℝ) : ℝ := Real.exp (((t:ℝ)+1)*σ)^(t+1)
lemma pix_firm {L : Picture G t} (hp : ∀ i j,Firm σ A (L i j)) (i j) : Firm σ (reflectBill t σ*A) (rotPix s L i j) := by
  let r := s.perm.symm ∘ axisEquiv.symm ∘ j
  have he := hp i (coord ∘ r)
  have hh := firmProd univ _ _ he.width_pos (fun j _ => reflect_firm s he.width_pos j (r j))
  simp only [prod_const,card_univ,Fintype.card_fin] at hh
  exact hh.mul (rotation_pays s he)
end YM.Stationary
end

/-!
Helpers for Taylor receipt *on the orbit*. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal

variable {α : Type} [Fintype α] [DecidableEq α] {G : Gauge} {m : Side} {σ A ε : ℝ} {t n : ℕ}

lemma note_add {F H : Corn α → ℝ} (hf : AnalyticAt ℝ F 0) (hh : AnalyticAt ℝ H 0) (n : ℕ) :
    noteAt (F+H) n=noteAt F n + noteAt H n := by
  apply enlarge_unique; intro v
  simp only [_root_.add_apply, note_real,Tensor.coeff_add (j:=n) hf.contDiffAt hh.contDiffAt,Complex.ofReal_add]
lemma note_sub {F H : Corn α→ℝ} (hf : AnalyticAt ℝ F 0) (hh : AnalyticAt ℝ H 0) (n : ℕ) :
    noteAt (F-H) n=noteAt F n-noteAt H n := by
  rw [eq_sub_iff_add_eq, ← note_add (hf.sub hh) hh n, sub_add_cancel]
lemma note_bill {F : Corn α→ℝ} (a : ℝ) (hf : AnalyticAt ℝ F 0) (n : ℕ) : noteAt (a • F) n=(a:ℂ) • noteAt F n := by
  apply enlarge_unique; intro v
  rw [_root_.smul_apply,note_real,note_real]
  unfold Tensor.coeff; rw [iteratedFDeriv_const_smul_apply hf.contDiffAt]
  simp; ring

variable {F H : Link G m → ℝ} {L K : Picture G t}

lemma labelAdd (p : Fin (t+1) → Site m) (i : Ink G (t+1)) (b) : collected (L+K) p i b=collected L p i b+collected K p i b := by unfold collected; split <;> simp [mul_add]
lemma labelSub (p : Fin (t+1) → Site m) (i : Ink G (t+1)) b : collected (L-K) p i b=collected L p i b-collected K p i b := by unfold collected; split <;> simp [mul_sub]
lemma Recorded.both (hf : AnalyticAt ℝ F 0) (hg : AnalyticAt ℝ H 0) (he : Recorded L F ε) (hk : Recorded K H 0) : Recorded (L+K) (F+H) ε := by intro p i b; rw [note_add hf hg,labelAdd p i b,_root_.add_apply,(record_exact _ _).1 hk, add_sub_add_right_eq_sub]; exact he ..
lemma Recorded.less (hf : AnalyticAt ℝ F 0) (hg : AnalyticAt ℝ H 0) (he : Recorded L F ε) (hk : Recorded K H 0) : Recorded (L-K) (F-H) ε := by intro p i b; rw [note_sub hf hg,labelSub p i b,_root_.sub_apply,(record_exact _ _).1 hk, sub_sub_sub_cancel_right]; exact he ..
lemma Recorded.weigh (a : ℝ) (he : Recorded L F 0) (hf : AnalyticAt ℝ F 0) : Recorded ((a:ℂ) • L) (a • F) 0 := by
  apply (record_exact ..).2; intro p i b
  rw [note_bill _ hf,_root_.smul_apply,(record_exact ..).1 he]; unfold collected; split <;> simp [mul_left_comm]

lemma priceReflect {T : Signed → Picture G t} (hs : 0 < σ) (h : ∀ s i j,Firm σ A (T s i j)) (x j) :
    Firm σ A (fun p => (Fintype.card Signed:ℂ)⁻¹ * ∑ i : Signed,T i x j p) := by
  have he := Firm.sum univ _ _ hs (fun i _ => h i x j)
  have hi : (Fintype.card Signed:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  convert (Firm.const hs (Fintype.card Signed:ℂ)⁻¹).mul he using 1
  simp [hi]

def bleed (L : Picture G t) : Picture G t := fun x j p => (Fintype.card Signed:ℂ)⁻¹ * ∑ i, rotPix i L x j p
lemma bleed_cap (hp : 0<σ) (h : ∀ i j,Firm σ A (L i j)) (x j) : Firm σ (reflectBill t σ*A) (bleed L x j) := priceReflect (T:=fun i => rotPix i L) hp (fun i => pix_firm i h) x j
lemma bleed_record (hf : AnalyticAt ℝ F 0) (h : ∀ i j,Firm σ A (L i j)) (hp : Recorded L F 0) :
    Recorded (bleed L) (fun x => Patch.average (fun s => F (orderTurn s x))) 0 := by
  apply (record_exact _ _).2; intro p i b
  let f (s : Signed) := F ∘ orderTurn (G:=G) (m:=m) s
  have he s : AnalyticAt ℝ (f s) 0 := (show AnalyticAt ℝ F (orderTurn s 0) by rw [map_zero]; exact hf).comp (ContinuousLinearMap.analyticAt _ _)
  change noteAt (fun x => Patch.average (fun s => f s x)) _ _=_; rw [note_mean f he, _root_.smul_apply,_root_.sum_apply]
  have hw s : noteAt (f s) (t+1) (glyph p i b)=_ := (record_exact _ _).1 (pix_records s F hf h hp) p i b
  simp_rw [hw]; unfold collected bleed; split <;> simp [mul_left_comm,Finset.mul_sum]
end YM.Stationary
end
