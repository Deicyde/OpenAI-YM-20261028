import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube
import YM.UVNext.FREE_STRESS_CERTIFICATE.Diagonal

/-! Exact tangent microphone in the actual two-curl Wick correlation. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Analysis Work.A01 Next.UVStress Function Set Filter
open scoped RealInnerProductSpace Topology ContDiff
variable {G : Gauge} (F : Frames G)

-- derivative of second gradient, at a unit axis, keep kronecker coefficients
-- over integers for ensuing kernel-level finite reduction.
def kr (t i : Axis) : ℤ := if i=t then 1 else 0
lemma basis_cast (t i : Axis) : ((kr t i:ℤ):ℝ)=YM.basis t i := by unfold kr; simp [basis_eq]

def curve (t i j : Axis) : ℤ := -2*kr j i +8*kr t j * kr t i
-- j gradient on i, r tangent; t center
def ray (r t i j : Axis) : ℤ := 8*kr j i * kr t r -48*kr t i * kr t j * kr t r +8*(kr r i * kr t j + kr r j * kr t i)

lemma radial (t i j : Axis) : grad j (grad i Green) (YM.basis t) = normal * ((curve t i j:ℤ):ℝ) := by
  rw [second_Green (by intro h; simpa using congr_arg norm h)]; simp only [basis_norm,one_pow,inv_one,curve]; push_cast;
  simp_rw [basis_cast]; ring

set_option maxHeartbeats 500000 in
lemma tangent_axis (t r i j : Axis) :
    grad r (grad j (grad i Green)) (YM.basis t) = normal * ((ray r t i j:ℤ):ℝ) := by
  let P := YM.basis t
  have hx : P ≠ 0 := fun h => one_ne_zero (α:=ℝ) (by simpa [P] using congr_arg norm h)
  have he : grad j (grad i Green) =ᶠ[𝓝 P] fun x =>
      -2 * normal * (YM.basis j i) * (‖x‖^2)⁻¹^2 + 8 * normal * (x j * x i) * (‖x‖^2)⁻¹^3 := by
    filter_upwards [open_away.mem_nhds (show P∈away from hx)] with x h
    exact second_Green h ..
  have hv := (hasFDerivAt_inv (show ‖P‖^2 ≠ 0 by simp [P])).comp P (hasStrictFDerivAt_norm_sq P).hasFDerivAt
  have hw := (((hv.pow 2).const_mul (-2 * normal * (YM.basis j i))).add
    ((((compAxis j).hasFDerivAt.mul (compAxis i).hasFDerivAt).const_mul (8 * normal)).mul (hv.pow 3))).fderiv
  rw [grad,GermD _ he, Analysis.D, show fderiv ℝ (fun x : E4 => -2*normal*YM.basis j i*(‖x‖^2)⁻¹^2 +
    8*normal*(x j*x i)*(‖x‖^2)⁻¹^3) (YM.basis t) = _ from hw]
  unfold ray
  push_cast
  simp [P,two_smul,-basis_eq,compAxis,basis_cast]
  rw [show YM.basis r t = YM.basis t r by simp [basis_eq,eq_comm]]; ring

def rotate (f : Axis → Axis → ℤ) (a b i k : Axis) :=
  (if i=b then f k a else 0) - (if k=b then f i a else 0) - ((if i=a then f k b else 0)-(if k=a then f i b else 0))

lemma one_view (t a b i k : Axis) : bareCurl a b i k (YM.basis t) = normal * ((rotate (curve t) a b i k : ℤ):ℝ) := by
  have ht : YM.basis t ≠ 0 := by intro h; simpa using congr_arg norm h
  unfold bareCurl
  simp only [Pi.sub_apply,Bare.opp_grad ht,radial,rotate]
  split_ifs <;> push_cast <;> ring

lemma view_ray (t r a b i k : Axis) : grad r (bareCurl a b i k) (YM.basis t) = normal * ((rotate (ray r t) a b i k : ℤ):ℝ) := by
  have ht : YM.basis t ≠ 0 := by intro h; simpa using congr_arg norm h
  let g (a b c d : Axis) : E4 → ℝ := if d=b then grad a (grad c Green) else 0
  have hh (a b c d) : ContDiffAt ℝ ∞ (g a b c d) (YM.basis t) := by unfold g; split <;> first | exact HessSmooth ht a c | exact contDiffAt_const (𝕜:=ℝ) (x:=YM.basis t) (c:= (0:ℝ))
  have he : bareCurl a b i k =ᶠ[𝓝 (YM.basis t)] ((g a b k i-g a b i k)-(g b a k i-g b a i k)) := by
    filter_upwards [open_away.mem_nhds (show _∈away from ht)] with x h
    unfold bareCurl; simp only [Pi.sub_apply,Bare.opp_grad h,g]; split_ifs <;> rfl
  rw [show grad r (bareCurl a b i k) (YM.basis t) = grad r _ (YM.basis t) from GermD _ he,
    Bare.grad_sub (f:=g a b k i-g a b i k) ((hh a b k i).sub (hh a b i k))
      (g:=g b a k i-g b a i k) ((hh b a k i).sub (hh b a i k))]
  simp_rw [Bare.grad_sub (hh _ _ _ _) (hh _ _ _ _)]
  have hx : grad r (0 : E4 → ℝ) (YM.basis t) = 0 := by simp [grad,D]
  unfold g rotate; split_ifs <;> push_cast <;> try simp only [tangent_axis,hx]
  all_goals ring

private lemma grad_product {x} {f g : E4→ℝ} (h : DifferentiableAt ℝ f x) (k : DifferentiableAt ℝ g x) (i : Axis) :
    grad i (f*g) x = grad i f x * g x + f x * grad i g x := by
  unfold grad D; rw [fderiv_mul h k]
  simp [mul_comm,add_comm]

def look (t a b i k c e f m : Axis) : ℤ :=
    rotate (curve t) a b c e * rotate (curve t) i k f m + rotate (curve t) a b f m * rotate (curve t) i k c e

def slide (r t a b i k c e f m : Axis) : ℤ :=
    rotate (ray r t) a b c e * rotate (curve t) i k f m + rotate (curve t) a b c e * rotate (ray r t) i k f m +
    (rotate (ray r t) a b f m * rotate (curve t) i k c e + rotate (curve t) a b f m * rotate (ray r t) i k c e)

lemma still_axis (t a b i k c e f m : Axis) : flash a b i k c e f m (YM.basis t)=normal^2 * ((look t a b i k c e f m:ℤ):ℝ) := by
  unfold flash look
  simp_rw [one_view]; push_cast; ring

lemma grad_flash (t r a b i k c e f m : Axis) : grad r (flash a b i k c e f m) (YM.basis t)=
    normal^2*((slide r t a b i k c e f m:ℤ):ℝ) := by
  have ht : YM.basis t ≠ 0 := by intro h; simpa using congr_arg norm h
  have he (a b i j) := (Bare.curl_diff ht a b i j).differentiableAt (by simp)
  let K := bareCurl
  change fderiv ℝ (K a b c e * K i k f m + K a b f m * K i k c e) (YM.basis t) (YM.basis r) = _
  rw [fderiv_add ((he a b c e).mul (he i k f m)) ((he a b f m).mul (he i k c e)), _root_.add_apply]
  change grad r (K a b c e * K i k f m) _ + grad r (K a b f m * K i k c e) _ = _
  rw [grad_product (he a b c e) (he i k f m), grad_product (he a b f m) (he i k c e)]
  simp_rw [one_view,view_ray]; unfold slide; push_cast; ring

def loud (G : Gauge) := (G.lieDim:ℂ) * (normal^2 : ℝ)
lemma loud_ne (h : G.Simple) : loud G ≠ 0 := by
  have hn : 0 < G.lieDim := by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos
  exact mul_ne_zero (by exact_mod_cast hn.ne') (by exact_mod_cast pow_ne_zero 2 normal_pos.ne')

lemma still_listens (t a b i k c e f m) :
    hearing F (camera t) c e f m 4 (flat F a b i k) = loud G * (↑(look t a b i k c e f m):ℂ) := by
  rw [flat,link,hears F (shutter _),camera_ab,camera_zero,sub_zero,still_axis, Complex.ofReal_mul,loud,mul_assoc, Complex.ofReal_intCast]

private def sight : Points 2 →L[ℝ] E4 := PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 2 => E4) 0 - PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 2 => E4) 1
lemma sight_read (x : Points 2) : sight x=x 0-x 1 := rfl
lemma sight_direction (a : Axis) : sight (Points.direction 0 a)=YM.basis a := by
  rw [sight_read]; simp [Points.direction]

variable (W : DiffPlan (freeTable F)) (hW : W.Derivatives (freeTable F))

include hW in
/-- Tangent sample of W.deriv: via *only its required consumer interface*
on separated positions; no identification with a derivative on representative
polynomials or on an unconstrained space. -/
lemma listens_to (a t i j b g c e f m : Axis) :
    hearing F (camera t) c e f m 5 (W.deriv 4 a (flat F i j b g)) = loud G * (↑(slide a t i j b g c e f m) : ℂ) := by
  let P := camera t
  let l := flash i j b g c e f m
  have h : YM.basis t ≠ 0 := by intro h; simpa using congr_arg norm h
  have ht : sight P=YM.basis t := by simp [P,sight_read]
  have hh (a b c e) : DifferentiableAt ℝ (bareCurl a b c e) (sight P) :=
    (Bare.curl_diff (ht ▸ h) _ _ _ _).differentiableAt (by simp)
  have hl : DifferentiableAt ℝ l (sight P) := ((hh i j c e).mul (hh b g f m)).add ((hh i j f m).mul (hh b g c e))
  let z := flat F i j b g
  let q := negs F c e f m
  rw [listens, hW.kernels 4 a z (shutter _) q]
  let L := Complex.ofRealCLM
  have he : (fun y => (freeTable F).useAt (freeTable F) y (Fin.cons ⟨4,z⟩ q)) =ᶠ[𝓝 P]
      (fun y => (G.lieDim:ℂ) * (L ∘ l ∘ sight) y) := by
    filter_upwards [(conf_open _).mem_nhds (shutter t)] with x hx
    change (freeTable F).useAt (freeTable F) x (Fin.cons ⟨4,link F _ _ _ _ _ _⟩ q) = _
    rw [← listens F]
    exact hears F hx i j b g c e f m
  change D (Points.direction 0 a) _ P = _
  rw [GermD _ he,D,fderiv_const_mul (L.differentiableAt.comp P (hl.comp P sight.differentiableAt)),
    fderiv_comp P L.differentiableAt (hl.comp P sight.differentiableAt),L.fderiv,
    fderiv_comp P hl sight.differentiableAt, sight.fderiv, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,sight_direction,ht]
  change (G.lieDim:ℂ) * (↑(grad a l (YM.basis t)):ℂ) = _
  unfold l; rw [grad_flash,Complex.ofReal_mul,loud,mul_assoc, Complex.ofReal_intCast]

end YM.UVNext.FreeStress
