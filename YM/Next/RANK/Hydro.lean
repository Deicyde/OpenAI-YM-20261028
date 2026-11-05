import YM.Next.RANK.ArcEstimate
import YM.Next.RANK.Stride

/-! Homogeneous curl-jet kernel off zero in E4. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Prayer
open Function Set Lattice Wilson RG Maxwell Maxwell.Wick Labels Normal Beamer Perch Configuration  Filter Tensor
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge}

-- offset version, multi factorial included.
def gleam (L K : Degree G) (z : E4) : ℝ :=
  (L.degree.factorial * (K.degree.factorial:ℝ)) *
    if L.paint = K.paint then (-1)^K.degree * Tensor.coeff (fun x =>
      Tensor.coeff (bareCurl L.a.val.1 L.a.val.2 K.a.val.1 K.a.val.2) L.degree x (basis ∘ L.layout)) K.degree z (basis ∘ K.layout) else 0
lemma glisten (L K : Degree G) (x y : E4) (hx : x ≠ y) : gleam L K (x-y)=light L K x y := by
  unfold gleam light; apply congr_arg (L.degree.factorial * (K.degree.factorial:ℝ) * ·)
  rw [← Maxwell.reads_mixed _ _ _ _ _ _ _ _ hx]; exact (Maxwell.raw_mixed _ _ _ _ _ _ _ _ (sub_ne_zero.mpr hx)).symm

lemma gleam_diff (L K : Degree G) : ContinuousOn (gleam L K) Maxwell.away := by
  intro z hz
  unfold gleam; split
  · let P:= bareCurl L.a.val.1 L.a.val.2 K.a.val.1 K.a.val.2; let T:= Tensor.coeff P L.degree
    have he : ContDiffAt ℝ ∞ T z := Tensor.coeff_smooth (Bare.curl_diff hz _ _ _ _) _
    let R := fun x => T x (YM.basis ∘ L.layout); let Q := fun v => Tensor.coeff R K.degree v
    have hx : ContDiffAt ℝ ∞ R z := (ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ (basis ∘ L.layout)).contDiff.contDiffAt.comp z he
    have hw : ContinuousWithinAt (fun p => Q p (YM.basis ∘ K.layout)) away z := ((ContinuousMultilinearMap.apply ℝ (fun _ => E4) ℝ (basis ∘ K.layout)).cont.continuousAt.comp (Tensor.coeff_smooth hx _).continuousAt).continuousWithinAt
    exact continuousWithinAt_const.mul (continuousWithinAt_const.mul hw)
  exact continuousWithinAt_const

private lemma bare_hom (a b i l) (r : ℝ) (hr : 0 < r) (x : E4) (hx : x ∈ away) :
    bareCurl a b i l (r • x)= (r^4)⁻¹*bareCurl a b i l x := by
  have hx : x ≠ 0 := hx
  have h : r • x ≠ 0 := smul_ne_zero hr.ne' hx
  have he i j : grad i (grad j Green) (r • x)= (r^4)⁻¹ * grad i (grad j Green) x := by rw [second_Green h, second_Green hx]; simp only [PiLp.smul_apply,norm_smul,Real.norm_of_nonneg hr.le,smul_eq_mul]; have hv:= norm_pos_iff.mpr hx; field_simp
  unfold bareCurl; simp only [Pi.sub_apply,Bare.opp_grad hx,Bare.opp_grad h,he, mul_sub,mul_ite,mul_zero]

private lemma magnify {f : E4 → ℝ} (j : ℕ) (r : ℝ) (hr : 0<r) {a : ℝ}
    (h : ∀ z∈ Maxwell.away, f (r • z)=a*f z) (hs : ∀ z∈Maxwell.away,ContDiffAt ℝ ∞ f z) (z : E4) (hz : z∈Maxwell.away)
    (w : Fin j → E4) :
    Tensor.coeff f j (r • z) w=(r^j)⁻¹*a*(Tensor.coeff f j z w) := by
  let L:= r • ContinuousLinearMap.id ℝ E4
  have hi : L z≠0 := smul_ne_zero hr.ne' hz
  have ht : ∀ x : E4,L x=r • x := fun _ => rfl
  have hg : (f ∘ L) =ᶠ[𝓝 z] a • f := by
    filter_upwards [Maxwell.open_away.mem_nhds hz] with x hx
    exact h x hx
  have hc := (hs z hz).of_le (show (↑j : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have he : Tensor.coeff (f ∘ L) j z w=a*Tensor.coeff f j z w := by rw [Tensor.GermCoeff j hg, Tensor.coeff_smul a hc]; rfl
  have hy : Tensor.coeff (f ∘ L) j z w=Tensor.coeff f j (L z) (fun i=> L (w i)) := by
    have hv := (open_away.preimage L.continuous).uniqueDiffOn (𝕜:=ℝ)
    have hu : ∀ x∈away, ContDiffAt ℝ j f x := fun x hx => (hs x hx).of_le (WithTop.coe_le_coe.mpr le_top)
    have hh := hu (L z) hi
    have ht := L.iteratedFDerivWithin_comp_right (s:=away) (fun x hx => (hu x hx).contDiffWithinAt) open_away.uniqueDiffOn hv (show L z∈away from hi) (i:=j) le_rfl
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hv (hh.comp z L.contDiff.contDiffAt) (show z∈_ from hi), iteratedFDerivWithin_eq_iteratedFDeriv open_away.uniqueDiffOn hh hi] at ht; unfold Tensor.coeff
    rw [ht]; rfl
  rw [hy] at he
  simp_rw [ht] at he
  have hT : (Tensor.coeff f j (r • z)) (fun i => r • w i)= r^j*Tensor.coeff f j (r • z) w := by
    simpa using! (Tensor.coeff f j (r • z)).map_smul_univ (fun _ => r) w
  rw [hT] at he; rw [mul_assoc, ← he]; field_simp

lemma grown (L K : Degree G) {r : ℝ} (hr : 0 < r) (z : E4) (hz : z∈away) : amount r L *amount r K * gleam L K (r • z)=gleam L K z := by
  unfold gleam; split
  · let f:= bareCurl L.a.val.1 L.a.val.2 K.a.val.1 K.a.val.2
    let P x := Tensor.coeff f L.degree x (YM.basis ∘ L.layout)
    have he : ∀ x∈away, ContDiffAt ℝ ∞ f x := fun x hx => Bare.curl_diff hx _ _ _ _
    have hp : ∀ x∈away, ContDiffAt ℝ ∞ P x := fun x hx => (ContinuousMultilinearMap.apply ℝ (fun _=> E4) ℝ (basis ∘ L.layout)).contDiff.contDiffAt.comp x (Tensor.coeff_smooth (he x hx) _)
    have hv : ∀ x∈away,P (r • x)=(r^L.degree)⁻¹*(r^4)⁻¹*P x := fun x hx => magnify _ r hr (bare_hom _ _ _ _ r hr) he x hx _
    change r^(L.degree+2)*r^(K.degree+2) *(_ * (_*Tensor.coeff P K.degree (r • z) (basis ∘ K.layout)))=_*(_*Tensor.coeff P K.degree z _)
    rw [magnify K.degree r hr hv hp z hz]; simp only [pow_add]; field_simp
  simp only [mul_zero]
end YM.Next.Rank.Prayer
