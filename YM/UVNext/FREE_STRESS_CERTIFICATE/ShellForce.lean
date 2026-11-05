import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Strands
import YM.Next.ROTATIONS.Switch
import YM.Next.SCHEDULE.Blocks
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression
import YM.Work.A01.Conserve


/-! Optional constructor aid. The canonical stress certificate itself is
independent of the Red shell-input package. Here ask what is *forced* when
that part of the package succeeds: the `StressLaws` fluxes (all windows)
already impose conservation/symmetry off diagonal. Together with the low
classification this can canonize MaxwellData for consumers even if the
initial Lighthouse builder supplied some other J; of course we have to
perform any such choice *before* comparison, on the same C, not change J
in the middle of a common receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Climb Table Work.A01 Work.A15 Next.UVStress Function Set Filter MeasureTheory Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {d n : ℕ}

private def patch (x : Points n) : Set E4 := (range x.ofLp)ᶜ
private lemma patch_open (x : Points n) : IsOpen (patch x) := (finite_range x.ofLp).isClosed.isOpen_compl
private lemma every {x : Points n} {y : E4} (hy : y∈patch x) {i} : y≠x i := by rintro rfl; exact hy (mem_range_self _)

private lemma next {x : Points (n+1)} {χ g : E4 → ℝ} (hw : Window x χ)
    (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (he : tsupport g ⊆ patch x) : Window x (χ-g) := by
  refine ⟨hw.1.sub hs,hw.2.1.sub hc, ?_,fun i => ?_⟩
  · have hz : g =ᶠ[𝓝 (x 0)] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => every (i:=0) (he h) rfl
    filter_upwards [hw.2.2.1,hz] with i hi hx; exact (show χ i - g i = _ from by simp_all)
  intro h
  rcases (tsupport_sub χ g h) with hz|hz
  · exact hw.2.2.2 i hz
  exact every (i:=i.succ) (he hz) rfl

private lemma raw_flux (J : S.Stress) (χ : E4→ℝ) (V : E4→E4) (x : Points (n+1))
    (q : Fin n → S.Tag) (v : S.Field d)
    (pay : ∀ a b : Axis, Integrable (term J χ V x q v a b)) :
    flux J χ V x q v = - ∑ a : Axis, ∫ y : E4, D (basis a) χ y • current J V x (Fin.cons ⟨d,v⟩ q) a y := by
  unfold flux; congr 1
  apply Finset.sum_congr rfl; intro a _
  rw [← integral_finsetSum _ (fun b _ => pay a b)]
  apply integral_congr_ae; filter_upwards with y
  simp [term,current, Finset.smul_sum,Complex.real_smul,mul_assoc]

-- change a window by any compact test in the patch. No boundary regularity
-- of current beyond there asserted.
private theorem drain (HS : S.Smooth) (J : S.Stress) (V : E4→E4) (hV : ∀ i : Axis,ContDiff ℝ ∞ fun y => V y i)
    {x : Points (n+1)} (hx : x∈conf _) (q : Fin (n+1) → S.Tag)
    (h : ∀ χ φ : E4→ℝ, Window x χ → Window x φ →
      flux J χ V x (Fin.tail q) (q 0).2=flux J φ V x (Fin.tail q) (q 0).2)
    {y : E4} (hy : y∈patch x) :
    ∑ a : Axis, D (basis a) (current J V x q a) y = 0 := by
  let M := current J V x q
  let f (z : E4) := ∑ a : Axis, D (basis a) (M a) z
  have he (a : Axis) (z : E4) (ht : z∈patch x) : ContDiffAt ℝ ∞ (M a) z :=
    smooth_current J V q a hV (Work.A01.conf_cons hx (fun i => every ht)) HS
  have hf : ContinuousOn f (patch x) := continuousOn_finsetSum _ fun a _ z hz => ((dSmooth (m:=∞) (he a z hz) _ (by simp)).continuousAt.continuousWithinAt)
  have hw {χ : E4→ℝ} (hχ : Window x χ) := raw_flux J χ V x (Fin.tail q) (q 0).2
    (fun a b => term_integrable _ _ _ _ _ _ HS hx hχ a b (hV b).continuous)
  rw [Sigma.eta, Fin.cons_self_tail] at hw
  have hk {χ : E4→ℝ} (hχ : Window x χ) (a : Axis) :
      Integrable fun y => D (basis a) χ y • M a y := by
    have ht := integrable_finsetSum Finset.univ fun b _ => term_integrable J χ V x (Fin.tail q) (q 0).2 HS hx hχ a b (hV b).continuous
    -- eta
    unfold term at ht; rw [Sigma.eta,Fin.cons_self_tail] at ht
    simpa only [M,current, Finset.smul_sum,Complex.real_smul,Complex.ofReal_mul,mul_assoc] using ht
  have h0 (g : E4→ℝ) (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ha : tsupport g⊆patch x) :
      ∫ z, g z • f z = 0 := by
    obtain ⟨χ,hχ⟩ := exists_window x hx
    have hg := h _ _ hχ (next hχ hs hc ha)
    simp_rw [hw hχ, hw (next hχ hs hc ha), neg_inj] at hg
    have hA (a : Axis) : Integrable fun z => D (basis a) g z • M a z :=
      cutoff_integrable (hc.fderiv_apply ℝ (basis a)) (continuous_iff_continuousAt.mpr fun y =>
        (dSmooth (m:=∞) (hs.contDiffAt (x:=y)) _ (by simp)).continuousAt)
          (fun z h => (he a z (ha (tsupport_fderiv_apply_subset ℝ _ h))).continuousAt)
    have hB (a : Axis) : Integrable fun z => g z • D (basis a) (M a) z :=
      cutoff_integrable hc hs.continuous (fun z h => (dSmooth (m:=∞) (he a z (ha h)) _ (by simp)).continuousAt)
    have hC (a : Axis) (z) : D (basis a) (χ-g) z = D (basis a) χ z - D (basis a) g z := by
      unfold D; rw [fderiv_sub (hχ.1.differentiable (by simp) z) (hs.differentiable (by simp) z)]; rfl
    change (∑ a : Axis, ∫ z, D (basis a) χ z • M a z) = (∑ a : Axis, ∫ z, D (basis a) (χ-g) z • M a z) at hg -- simp_rw neg already removed
    simp_rw [hC,sub_smul, integral_sub (hk hχ _) (hA _), Finset.sum_sub_distrib] at hg
    have hi (a : Axis) : (∫ z, g z • D (basis a) (M a) z) = - ∫ z, D (basis a) g z • M a z :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (hA a) (hB a)
        (cutoff_integrable hc hs.continuous fun z hz => (he a z (ha hz)).continuousAt)
        (fun y _ => hs.differentiable (by simp) y) (fun y hz => (he a y (ha hz)).differentiableAt (by simp))
    simp_rw [f, Finset.smul_sum, integral_finsetSum _ (fun a _ => hB a), hi, Finset.sum_neg_distrib]
    linear_combination (norm:=abel) -hg
  have hu := (patch_open x).ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume)
    (hf.locallyIntegrableOn (patch_open x).measurableSet) h0
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' (patch_open x).measurableSet).mpr hu) (patch_open x) hf continuousOn_const hy

-- Can always use at least one spectator, by adding a distant unit if needed.
private theorem populated (hs : S.Basic) {B C : S.Field d}
    (h : ∀ n (x : Points (n+2)) (q : Fin (n+1) → S.Tag), x∈conf _ →
      S.useAt S x (Fin.cons ⟨d,B⟩ q)=S.useAt S x (Fin.cons ⟨d,C⟩ q)) : B=C := by
  apply S.field_ext hs.toSymmetric; intro n q x hx
  cases n with
  | succ n => exact h n x q hx
  | zero =>
    let y := x 0 + basis 0
    have he : y ≠ x 0 := by
      intro h
      have hq : basis 0 = 0 := by simpa [y] using h
      replace hq := congr_arg norm hq; simp at hq
    have hU : Points.cons y x∈conf _ := Work.A01.conf_cons hx (fun i => by rw [@Subsingleton.elim (Fin 1) _ i 0]; exact he)
    let v := Points.rearrange (exchangeFirst 0) (Points.cons y x)
    have hv : v∈conf _ := Points.rearrange_in _ hU
    have ht (B : S.Field d) : S.useAt S x (Fin.cons ⟨d,B⟩ q) =
        S.useAt S v (Fin.cons ⟨d,B⟩ (Fin.cons ⟨0,S.unit 0⟩ q)) := by
      rw [← exchange_use hs.toSymmetric hU ⟨0,S.unit 0⟩ ⟨d,B⟩ q,S.at_unit hs hU]
      rfl
    rw [ht B,ht C]; exact h 0 _ _ hv

private lemma cleared {x : Points (n+2)} (hx : x ∈ conf _) : x 0 ∈ patch (Points.tail x) := by
  rintro ⟨i, hi⟩; exact Fin.succ_ne_zero i ((show Injective x.ofLp from hx) hi)
private lemma tot (x : Points (n+2)) : Points.cons (x 0) (Points.tail x) = x := by
  ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

variable (HS : S.Hierarchy) (W : DiffPlan S) (hW : W.Derivatives S) (J : S.Stress)
variable {T : Climb.Parts S} {A : Ward.SpinRows S} (h : StressLaws S J T A)
include HS W hW J h

lemma drain_div (b : Axis) : ∑ a, W.deriv 4 a (J a b) = 0 := by
  apply populated HS.laws; intro n x q hx
  have he (χ φ : E4→ℝ) (hχ : Window (Points.tail x) χ) (hφ : Window (Points.tail x) φ) :
      flux J χ (fun _ => basis b) (Points.tail x) (Fin.tail q) (q 0).2 =
        flux J φ (fun _ => basis b) (Points.tail x) (Fin.tail q) (q 0).2 := by
    rw [flux_translation,flux_translation,h.translation (Points.tail_in hx) (Fin.tail q) hχ,h.translation (Points.tail_in hx) (Fin.tail q) hφ]
  have hq := drain HS.smooth J (fun _ => basis b) (fun _ => contDiff_const) (Points.tail_in hx) q he (cleared hx)
  have hA (a : Axis) : current J (fun _ => basis b) (Points.tail x) q a = fun y =>
      S.useAt S (Points.cons y (Points.tail x)) (Fin.cons ⟨4,J a b⟩ q) := by
    funext y; simp [current]
  have hf : Points.cons (x 0) (Points.tail x) ∈ conf _ := (tot x).symm ▸ hx
  simp_rw [hA,D_cons HS.smooth W hW _ q hf,tot x, ← front_eval, ← map_sum] at hq
  rw [← front_eval q x _ (∑ _,_), ← front_eval q x _ 0, map_zero]; exact hq


omit HS W hW J h in
private def twisted (u : Ortho.Skew) (b : Axis) : E4 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun y := M4.move u.val y b
    map_add' y z := congr_arg (fun p : E4 => p b) (map_add (Matrix.toEuclideanLin u.val) y z)
    map_smul' c y := congr_arg (fun p : E4 => p b) (map_smul (Matrix.toEuclideanLin u.val) c y) }
omit HS W hW J h in
private lemma orbital_D (u : Ortho.Skew) (w z : E4) (i j : Axis) :
    D (basis i) (fun y => orbital u w y j) z = u.val j i := by
  rw [show (fun y => orbital u w y j) = fun y => twisted u j y - twisted u j w from funext fun y => map_sub (twisted u j) y w]
  unfold D
  rw [fderiv_fun_sub (twisted u j).differentiableAt (differentiableAt_const _), (twisted u j).fderiv,
    (hasFDerivAt_const ((twisted u j) w) z).fderiv,sub_zero]
  exact M4.move_basis u.val j i

lemma curl_free (u : Ortho.Skew) : ∑ a : Axis, ∑ b : Axis, (u.val b a:ℂ) • J a b = 0 := by
  apply populated HS.laws; intro n x q hx
  let U := Points.tail x
  let V := orbital u (U 0)
  have hv (b : Axis) := smooth_orbital u (U 0) b
  have he (χ φ : E4→ℝ) (hχ : Window U χ) (hφ : Window U φ) :
      flux J χ V U (Fin.tail q) (q 0).2 = flux J φ V U (Fin.tail q) (q 0).2 := by
    unfold V orbital
    rw [flux_spin,flux_spin,h.rotation (Points.tail_in hx) (Fin.tail q) hχ,h.rotation (Points.tail_in hx) (Fin.tail q) hφ]
  have hd := drain HS.smooth J V hv (Points.tail_in hx) q he (cleared hx)
  let z := x 0
  have hsep : Points.cons z U∈conf _ := (tot x).symm ▸ hx
  let f (a b : Axis) (y : E4) := S.useAt S (Points.cons y U) (Fin.cons ⟨4,J a b⟩ q)
  have hf (a b : Axis) : DifferentiableAt ℝ (f a b) z := (smooth_cons S HS.smooth _ q hsep).differentiableAt (by simp)
  have hp (b : Axis) : DifferentiableAt ℝ (fun y => V y b) z := (hv b).differentiable (by simp) _
  let g (a b : Axis) := u.val b a • f a b z + V z b • S.useAt S (Points.cons z U) (Fin.cons ⟨5,W.deriv 4 a (J a b)⟩ q)
  have hA (a b) : D (basis a) (fun y => V y b • f a b y) z = g a b := by
    calc
      _ = D (basis a) (fun y => V y b) z • f a b z + V z b • D (basis a) (f a b) z := by
        unfold D; rw [fderiv_fun_smul (hp b) (hf a b)]; simp [add_comm]
      _ = _ := by rw [orbital_D]; unfold f; rw [D_cons HS.smooth W hW _ q hsep a]
  have hB (a) : D (basis a) (current J V U q a) z = ∑ b, g a b := by
    change fderiv ℝ (fun y => ∑ b : Axis, V y b • f a b y) z _ = _
    rw [fderiv_fun_sum (fun b _ => (show DifferentiableAt ℝ (fun y => V y b • f a b y) z from (hp b).smul (hf a b))), _root_.sum_apply]
    exact Finset.sum_congr rfl fun b _ => hA a b
  change ∑ a : Axis, D (basis a) (current J V U q a) z = 0 at hd; simp_rw [hB,g,Finset.sum_add_distrib] at hd
  have hC : (∑ a : Axis,∑ b : Axis,V z b • S.useAt S (Points.cons z U) (Fin.cons ⟨5,W.deriv 4 a (J a b)⟩ q))=0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro b _
    simp_rw [← front_eval, ← Finset.smul_sum, ← map_sum,drain_div HS W hW J h b,map_zero,smul_zero]
  rw [hC,add_zero] at hd
  dsimp only [z,U,f] at hd; simp_rw [tot x,← front_eval] at hd
  simp_rw [← front_eval q x 4, map_zero,map_sum,map_smul]
  simpa only [Complex.real_smul,smul_eq_mul] using hd

omit HS W hW J h in
private def oneMatrix (i j : Axis) : M4 := Matrix.of fun a b => if a=i then if b=j then 1 else 0 else 0
omit HS W hW J h in
private def shear (i j : Axis) : Ortho.Skew := ⟨oneMatrix i j - star (oneMatrix i j),by
  change star _ = -_
  rw [star_sub,star_star,neg_sub]⟩

lemma symmetry (i j : Axis) : J i j=J j i := by
  have ht := curl_free HS W hW J h (shear j i)
  have he (a b : Axis) : (↑((shear j i).val b a):ℂ) =
      (if a=i then if b=j then 1 else 0 else 0)-(if b=i then if a=j then 1 else 0 else 0) := by
    simp only [shear,oneMatrix,Matrix.sub_apply,Matrix.star_apply,Matrix.of_apply,star_trivial]
    split_ifs <;> norm_num
  simp_rw [he,sub_smul,ite_smul,zero_smul,one_smul,Finset.sum_sub_distrib] at ht
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at ht
  exact sub_eq_zero.mp ht

end YM.UVNext.FreeStress
