import YM.Maxwell.Leg
import YM.Analysis.Exchange

/-! The one-leg bilinear form matches actual differentiated opposite curls and is symmetric in the endpoints (off the diagonal). -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Function Set Filter Tensor
open WaveOn Submodule
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {j l : ℕ} {z : E4}

theorem responds_add (p q : Probe G j) :
    responded G (extension (p+q)) = responded G (extension p) + responded G (extension q) := by
  funext i m x
  simp [responded, extension, scalarTest,add_smul,Finset.sum_add_distrib]

theorem responds_smul (p : Probe G j) (c : ℝ) : responded G (extension (c • p)) = c • responded G (extension p) := by
  funext i m x
  simp [responded,extension,scalarTest,Finset.smul_sum,smul_smul]

/-- Bilinear on the actual shell legs on the open patch. -/
def pairing (hz : z ∈ away) : Probe G j →ₗ[ℝ] Probe G l →ₗ[ℝ] ℝ where
  toFun p :=
    { toFun q := legKernel p q z
      map_add' q r := by simp [legKernel,contraction,extension]; ring
      map_smul' t q := by simp [legKernel,contraction,extension]; ring }
  map_add' p s := by
    apply LinearMap.ext; intro q
    change contraction G (extension (p+s)) (extension q) z =
      contraction G (extension p) (extension q) z + contraction G (extension s) (extension q) z
    unfold contraction
    rw [responds_add]
    have he : nth (responded G (extension p) + responded G (extension s)) l z =
        nth (responded G (extension p)) l z + nth (responded G (extension s)) l z := funext fun i => funext fun m =>
      coeff_add (((response (G := G) (extension p)).smooth i m z hz).of_le (WithTop.coe_le_coe.mpr le_top))
        (((response (G := G) (extension s)).smooth i m z hz).of_le (WithTop.coe_le_coe.mpr le_top))
    rw [he, map_add,mul_add]
  map_smul' c p := by
    apply LinearMap.ext; intro q
    change contraction G (extension (c • p)) (extension q) z = c * contraction G (extension p) (extension q) z
    unfold contraction
    rw [responds_smul]
    rw [show nth (c • responded G (extension p)) l z = c • nth (responded G (extension p)) l z from
      funext fun i => funext fun m => coeff_smul c (((response (G := G) (extension p)).smooth i m z hz).of_le
        (WithTop.coe_le_coe.mpr le_top)), map_smul]; simp [mul_left_comm]

/-- Coordinate reading of mixed derivatives. -/
def fromF (G : Gauge) {j : ℕ} (u : Fin j → E4) (c : G.ColorIndex) (a b : Axis) : Extended G j where
  toFun Q := Q a b u c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma unitPaint (c d : G.ColorIndex) : unitColor G c d = if d=c then 1 else 0 := by
  simp [unitColor,PiLp.single_apply,eq_comm]

lemma observed (P : Extended G j) (i m : Axis) (z : E4) (c : G.ColorIndex) :
    responded G P i m z c = scalarTest (G := G) P c i m z := by
  simp [responded, unitPaint]

lemma tests_curl (u : Fin j → E4) (c : G.ColorIndex) (a b i m : Axis) (d : G.ColorIndex)
    (h : z ∈ away) :
    responded G (fromF G u c a b) i m z d = if c=d then coeff (bareCurl a b i m) j z u else 0 := by
  rw [observed]
  change coeff (leftF G d i m a b) j z u c = _
  unfold leftF
  rw [coeff_linear (tint (G := G) _) u
    ((Bare.curl_diff h a b i m).of_le (WithTop.coe_le_coe.mpr le_top)), tint_at]
  simp [unitPaint]

lemma raw_mixed (u : Fin j → E4) (v : Fin l → E4) (i m a b : Axis) (c d : G.ColorIndex) (h : z ≠ 0) :
    pairing (G := G) (show z ∈ away from h) (constrain (fromF G u c i m)) (constrain (fromF G v d a b)) =
    if c=d then (-1)^l * coeff (fun z => coeff (bareCurl i m a b) j z u) l z v else 0 := by
  change legKernel _ _ z = _
  rw [concrete (fromF ..) (fromF ..) h]
  let R := responded G (fromF G u c i m)
  let L : G.Color →L[ℝ] ℝ := EuclideanSpace.proj d
  change (-1)^l * L (coeff (R a b) l z v) = _
  rw [← coeff_linear L v (((response (G := G) (fromF ..)).smooth _ _ z h).of_le (WithTop.coe_le_coe.mpr le_top))]
  have he : L ∘ R a b =ᶠ[𝓝 z] fun w => if c=d then coeff (bareCurl i m a b) j w u else 0 := by
    filter_upwards [open_away.mem_nhds (show z ∈ away from h)] with w hw
    exact tests_curl u c i m a b d hw
  rw [GermCoeff l he]
  by_cases hw : c=d
  · subst c; simp
  simp [hw]

/-- Endpoint coordinates, *actual* y derivative (when translated to z includes the chain-rule sign). -/
lemma reads_mixed (u : Fin j → E4) (v : Fin l → E4) (i m a b : Axis) (c d : G.ColorIndex) {x y : E4}
    (h : x ≠ y) :
    legKernel (G := G) (constrain (fromF G u c i m)) (constrain (fromF G v d a b)) (x-y) =
    if c=d then coeff (fun y => coeff (fun x => bareCurl i m a b (x-y)) j x u) l y v else 0 := by
  have hz := sub_ne_zero.mpr h
  change pairing (G := G) (show x-y ∈ away from hz) _ _ = _
  rw [raw_mixed u v i m a b c d hz]
  split_ifs with he
  · rw [show (fun y => coeff (fun x => bareCurl i m a b (x-y)) j x u) =
        (fun y => coeff (bareCurl i m a b) j (x-y) u) by
      funext y; rw [coeff, iteratedFDeriv_comp_sub]; rfl]
    rw [oppositeCoeff (f := fun z => coeff (bareCurl i m a b) j z u)]
    · rfl
    exact (((ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ u).contDiff.contDiffAt.comp (x-y)
      (coeff_smooth (Bare.curl_diff hz i m a b) j)).of_le (WithTop.coe_le_coe.mpr le_top))
  · rfl

theorem raw_exchange (u : Fin j → E4) (v : Fin l → E4) (i m a b : Axis) (c d : G.ColorIndex) (h : z ≠ 0) :
    pairing (G := G) (show z ∈ away from h) (constrain (fromF G u c i m)) (constrain (fromF G v d a b)) =
    pairing (G := G) (show -z ∈ away from neg_ne_zero.mpr h) (constrain (fromF G v d a b)) (constrain (fromF G u c i m)) := by
  have hw := neg_ne_zero.mpr h
  rw [raw_mixed u v i m a b c d h, raw_mixed v u a b i m d c hw]
  rcases eq_or_ne d c with hdc | hdc
  · subst d; rw [if_pos rfl, if_pos rfl]
    let K := bareCurl i m a b
    let T := bareCurl a b i m
    have hs (x) (hx : x ∈ away) : ContDiffAt ℝ ∞ K x := Bare.curl_diff hx i m a b
    have ht (x) (hx : x ∈ away) : ContDiffAt ℝ ∞ T x := Bare.curl_diff hx a b i m
    let f : E4 → ℝ := fun y => coeff K l y v
    have hf : ContDiffAt ℝ j f z :=
      ((ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ v).contDiff.contDiffAt.comp z (coeff_smooth (hs z h) l)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hfn : ContDiffAt ℝ j (fun y => f (-y)) (-z) :=
      (show ContDiffAt ℝ j f (-(-z)) by simpa using hf).comp _ contDiffAt_id.neg
    have hp : (fun y => coeff T l y v) =ᶠ[𝓝 (-z)] ((-1 : ℝ)^l • fun y => f (-y)) := by
      filter_upwards [open_away.mem_nhds (show -z ∈ away from hw)] with y hy
      have HN : -y ∈ away := neg_ne_zero.mpr hy
      have hh : T =ᶠ[𝓝 y] fun w => K (-w) := by
        filter_upwards [open_away.mem_nhds hy] with w h'
        exact (Bare.exchange h' _ _ _ _).trans (Bare.even h' _ _ _ _).symm
      change coeff T l y v = _
      rw [GermCoeff l hh,reflectionJet ((hs _ HN).of_le (WithTop.coe_le_coe.mpr le_top))]
      rfl
    change (-1)^l * coeff (fun y => coeff K j y u) l z v = (-1)^j * coeff (fun y => coeff T l y v) j (-z) u
    rw [exchangeJet open_away hs h, GermCoeff j hp, coeff_smul _ hfn,
      reflectionJet (show ContDiffAt ℝ j f (-(-z)) by simpa using hf), smul_apply, smul_apply, neg_neg]
    change _ = (-1)^j * ((-1)^l * ((-1)^j * coeff (fun y => coeff K l y v) j z u))
    rw [mul_left_comm,← mul_assoc ((-1:ℝ)^j), ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rw [if_neg hdc.symm, if_neg hdc]

/-- Probe-induction holds with actual component derivatives. -/
lemma spans : span ℝ {p : Probe G j | ∃ u c i m, p=constrain (G := G) (fromF G u c i m)} = ⊤ := by
  let A := span ℝ {p : Probe G j | ∃ u c i m, p=constrain (G := G) (fromF G u c i m)}
  change A=⊤
  have h : A.dualCoannihilator = ⊥ := by
    apply le_antisymm _ bot_le; intro x hx
    apply (Submodule.mem_bot ℝ).mpr
    apply Subtype.ext
    funext i m
    apply ContinuousMultilinearMap.ext
    intro u
    ext1 c
    have he : constrain (G := G) (fromF G u c i m) ∈ A := Submodule.subset_span ⟨u,c,i,m,rfl⟩
    exact (Submodule.mem_dualCoannihilator _).1 hx _ he
  apply Submodule.eq_top_of_finrank_eq
  have he := Subspace.finrank_add_finrank_dualCoannihilator_eq A
  rw [h, finrank_bot, add_zero] at he
  rw [he]; exact (Subspace.dual_finrank_eq ..).symm

theorem exchange (p : Probe G j) (q : Probe G l) (h : z ∈ away) : pairing h p q =
    pairing (show -z ∈ away from neg_ne_zero.mpr h) q p := by
  let f : Probe G j →ₗ[ℝ] Probe G l →ₗ[ℝ] ℝ := pairing h
  let g := (pairing (G := G) (l := j) (j := l) (show -z ∈ away from neg_ne_zero.mpr h)).flip
  have he : f=g := by
    refine LinearMap.ext_on (f := f) (g := g) spans ?_
    rintro a ⟨u,c,i,m,rfl⟩
    refine LinearMap.ext_on spans ?_
    rintro b ⟨v,d,a,b,rfl⟩
    exact raw_exchange u v i m a b c d h
  change f p q = g p q; rw [he]
end YM.Maxwell
