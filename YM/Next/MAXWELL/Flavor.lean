import Mathlib.Analysis.Normed.Module.Connected
import YM.Next.MAXWELL.Team


/-!
# Real tested flavor leg and rank, across orders

No span assertion from just polarization at one momentum. `ranging`
uses stress/dilation and the actual position derivatives. This suffices
for the kernel across any fixed jet orders (unrestricted partner).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G : Gauge} {j l d : ℕ}

def stay (u : Fin j → E4) (a b : Axis) : Flavor j where
  toFun z := z.val a b u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cell (a b : Axis) := stay (j:=0) (fun _ => 0) a b



lemma flavor_ext {p q : Sheet j} (h : ∀ u a b, stay u a b p = stay u a b q) : p=q :=
  Subtype.ext (funext fun a => funext fun b => ContinuousMultilinearMap.ext fun u => h u a b)

theorem unitStay (j : ℕ) : Submodule.span ℝ {p : Flavor j | ∃ u a b,p=stay u a b}=⊤ := by
  let V := Submodule.span ℝ {p : Flavor j | ∃ u a b,p=stay u a b}
  change V=⊤
  have hp : V.dualCoannihilator=⊥ := by
    apply le_antisymm _ bot_le; intro x hx; apply (Submodule.mem_bot ..).mpr
    apply flavor_ext; intro u a b; rw [map_zero]
    exact (Submodule.mem_dualCoannihilator _).1 hx _ (show stay u a b ∈ V from Submodule.subset_span ⟨u,a,b,rfl⟩)
  apply Submodule.eq_top_of_finrank_eq
  have he := Subspace.finrank_add_finrank_dualCoannihilator_eq V
  rw [hp,finrank_bot,add_zero] at he
  rw [he]; exact (Subspace.dual_finrank_eq ..).symm

lemma cell_price (a b i l : Axis) (u : ℝ) : cell a b (blade i l u)=wedge 1 a b i l * u := blade_eval ..

lemma cell_alive : cell 0 1≠0 := by
  intro h; have he := LinearMap.congr_fun h (blade 0 1 (1:ℝ)); rw [cell_price] at he
  norm_num [wedge,Matrix.one_apply] at he

def actFlavor (s : Ortho) (j : ℕ) : Module.End ℝ (Flavor j) where
  toFun p := p.comp (solutionTurn s⁻¹)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def feed (u : E4) (j : ℕ) : Flavor j →ₗ[ℝ] Flavor (j+1) where
  toFun p := p.comp (lower ℝ j u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma consecutive (u : E4) (p : Flavor j) (i : G.ColorIndex) :
    flavor (j+1) i (feed u j p) = raiseLeg u (flavor j i p) := by
  ext1 x
  exact congr_arg p (color_lower (cp (G:=G) i) _ _)

lemma tasted (p : Flavor j) (i : G.ColorIndex) (u : Sheet j) : flavor j i p (fill j (unitColor G i) u) = p u := by
  change p (faceMap j _ _) = _
  rw [which,unitPaint]; simp
lemma orientFlavor (s : Ortho) (p : Flavor j) (i : G.ColorIndex) :
    probeTurn s (flavor j i p)=flavor j i (actFlavor s j p) := by
  ext1 x; apply congr_arg p; apply Subtype.ext; funext a b; ext1 u
  change cp (G:=G) i (turnJ s⁻¹ x.val a b u)=turnJ s⁻¹ (faceMap _ (cp (G:=G) i) x).val a b u
  simp_rw [turns_apply,map_sum,map_smul]; rfl

lemma orient_team (s : Ortho) (p : Flavor j) (q : Flavor l) : reflectPol s (team G p q)=team G
    (actFlavor s j p) (actFlavor s l q) := by
  simp_rw [team,bit,map_sum,map_mul,reflect_symbol,orientFlavor]

section Pair
variable (c : G.ColorIndex)

def fare (p : Flavor j) (q : Flavor l) (z : E4) := legKernel (flavor (G:=G) j c p) (flavor (G:=G) l c q) z

def assay {z : E4} (hz : z ≠ 0) (j l : ℕ) : Flavor j →ₗ[ℝ] Flavor l →ₗ[ℝ] ℝ where
  toFun p := (pairing (G:=G) (show z ∈ away from hz) (flavor j c p)).comp (flavor l c)
  map_add' p q := by apply LinearMap.ext; intro x; simp [map_add]
  map_smul' p q := by apply LinearMap.ext; intro x; simp

lemma fare_pair (p : Flavor j) (q : Flavor l) {x : E4} (hx : x ≠ 0) :
    assay c hx j l p q=fare c p q x := rfl

lemma any_ink (p : Flavor j) (q : Flavor l) (a b : G.ColorIndex) {x : E4} (hx : x ≠ 0) :
    legKernel (flavor j a p) (flavor l b q) x = (if a=b then 1 else 0) * fare c p q x := by
  let H : Flavor j →ₗ[ℝ] Flavor l →ₗ[ℝ] ℝ :=
    { toFun p := (pairing (G:=G) (show x∈away from hx) (flavor j a p)).comp (flavor l b),
      map_add' p q := by apply LinearMap.ext; intro x; simp
      map_smul' p q := by apply LinearMap.ext; intro x; simp }
  let K := ((if a=b then 1 else 0) : ℝ) • assay c hx j l
  change H p q=K p q
  suffices he : H=K by rw [he]
  refine LinearMap.ext_on (unitStay j) ?_
  rintro p ⟨u,i,m,rfl⟩; refine LinearMap.ext_on (unitStay l) ?_
  rintro q ⟨v,k,t,rfl⟩
  change pairing (G:=G) (show x ∈ away from hx) (leg u a i m) (leg v b k t)=
    (if a=b then 1 else 0) * pairing (G:=G) (show x∈away from hx) (leg u c i m) (leg v c k t)
  rw [leg,leg,leg,leg,raw_mixed _ _ _ _ _ _ a b hx, raw_mixed _ _ _ _ _ _ c c hx]
  split_ifs <;> simp_all

/-- Keep a ray-direction Euler rule for use in other parts. -/
lemma pole_power {r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E4 → V} (H : Pole r f) {x : E4} (hx : x ∈ away) : D x f x = (-(↑r:ℝ)) • f x := by
  have ht : HasDerivAt (fun t : ℝ => t • x) x 1 := by
    refine ((hasDerivAt_id' (1:ℝ)).smul_const x).congr_deriv ?_; rw [one_smul]
  have he : HasDerivAt (fun t : ℝ => f (t • x)) (D x f x) 1 := by
    have h : DifferentiableAt ℝ f ((1:ℝ) • x) := by rw [one_smul]; exact (H.diff x hx).differentiableAt (by simp)
    refine (h.hasFDerivAt.comp_hasDerivAt (1:ℝ) ht).congr_deriv ?_; rw [one_smul]; rfl
  have hs : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 1] fun t => t⁻¹ ^ r • f x := by
    filter_upwards [lt_mem_nhds (by norm_num : (0:ℝ)<1)] with u hu; exact H.degree u hu x hx
  apply he.unique (HasDerivAt.congr_of_eventuallyEq (f:=fun t : ℝ => (t⁻¹ ^ r) • f x) ?_ hs)
  refine ((((hasDerivAt_id' (1:ℝ)).inv one_ne_zero).pow r).smul_const _).congr_deriv ?_
  simp

lemma payment {p : Flavor j} (h : ∀ (z : E4),z≠0 → ∀ q : Flavor 0, fare c p q z=0) : p=0 := by
  let i := flavor j c p
  let V := pulse i 0
  have H (x : E4) (hx : x≠0) (a b : Axis) : V a b x=0 := by
    ext1 u; rw [show V a b x u=K i (omegaLeg u a b) 0 x from (K_observe i _ _ _ (Ne.symm hx)).symm]
    change legKernel _ (flavor 0 u (cell a b)) (0-x)=0; rw [any_ink c p _ c u (sub_ne_zero.mpr (Ne.symm hx)), h _ (sub_ne_zero.mpr (Ne.symm hx)),mul_zero]
  apply LinearMap.ext; intro q
  let A := fill j (unitColor G c) q
  let C : ContDiffBump (0:E4) := ⟨1,2,by norm_num,by norm_num⟩
  have he := radial_flux isOpen_univ (wavePoly A) i (x:=0) (χ:=C) C.contDiff C.hasCompactSupport (subset_univ _) C.eventuallyEq_one
  have ht : singleFlux (fromCenter 1 0) C V (asWave A)=0 := by
    unfold singleFlux exportFlux
    simp only [neg_eq_zero]; apply Finset.sum_eq_zero; intro a _
    rw [show (fun y => grad a (⇑C) y • current (fromCenter 1 0) V (asWave A) a y) = 0 from ?_]
    · exact integral_zero ..
    funext y; by_cases h : y=0
    · subst y; rw [image_eq_zero_of_notMem_tsupport (x:=0) (f:=grad a (⇑C)) fun hw =>
        collar C.eventuallyEq_one (gradient_part C a hw),zero_smul]; rfl
    simp [current,cross,H y h]
  rw [show pulse i 0 = V from rfl, ht, sample_eval i (wavePoly A) isOpen_univ (mem_univ _),
    show i ⟨WaveOn.nth (asWave A) j (0:E4),(wavePoly A).jets isOpen_univ (mem_univ _)⟩=p q from
      (congr_arg i (Subtype.ext (asWave_jet A))).trans (tasted p c q)] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (neg_ne_zero.mpr (by positivity))

lemma ranging (p : Flavor j) (l : ℕ) (H : ∀ (z:E4), z≠0 → ∀ q : Flavor l, fare c p q z=0) : p=0 := by
  induction l with
  | zero => exact payment c H
  | succ l ih =>
    apply ih
    intro x hx q
    let P := flavor j c p
    let Q := flavor l c q
    have he := K_right_D P Q (x := x) (y := 0) hx x
    have hp := kernel_pole P Q
    have hw := pole_power hp hx
    rw [← consecutive x q c, K,sub_zero,show legKernel _ _ x=0 from H _ hx _] at he
    let L := fun y : E4 => x-y
    have hf : HasFDerivAt L (-(ContinuousLinearMap.id ℝ E4)) 0 := by
      convert! ((hasFDerivAt_id (0:E4) (𝕜:=ℝ)).const_sub x) using 1
    have hl : L 0=x := sub_zero _
    have hh : DifferentiableAt ℝ (legKernel P Q) (L 0) := by rw [hl]; exact (kernel_smooth P Q hx).differentiableAt (by simp)
    change fderiv ℝ (legKernel P Q ∘ L) 0 x=0 at he
    rw [fderiv_comp _ hh hf.differentiableAt,hf.fderiv,hl,ContinuousLinearMap.comp_apply] at he
    change fderiv ℝ (legKernel P Q) x (-x)=0 at he; rw [map_neg,neg_eq_zero] at he; change D x _ x=_ at he; rw [hw] at he
    exact (smul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr (by positivity))
end Pair
end YM.Maxwell.Free
