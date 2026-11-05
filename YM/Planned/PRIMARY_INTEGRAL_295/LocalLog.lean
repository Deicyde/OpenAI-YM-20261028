import YM.Next.FOUNDATIONS.LinkBounds
import YM.Planned.PRIMARY_INTEGRAL_295.SplitRadial


/-!
# The log-gauge substitution before testing

All Norms in physical B70 coordinates. Local analytic link germ incl its
gauge endpoints, and mixed jets *polynomial* in the initial link position
when fed polynomial gauges and graded radial tests. Positional orders in
the nonlinear differential are checked on the same representation/ODE.
No uniform analytic neighborhood asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Filter Lattice Labels Source Source.Drops RG WardBin MeasureTheory Next.Foundations
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d n : ℕ}

/-- Inputs to one link. The second color is the **difference** of endpoint
gauge logarithms, with initial site logarithm first. -/
abbrev EdgeRead (G : Gauge) (d : ℕ) := G.Color × G.Color × Route G d

def peak (x : EdgeRead G d) := G.lieExp x.1 * flight x.2.2 1 * (G.lieExp (x.1-x.2.1))⁻¹

def logo (x : EdgeRead G d) : G.Color := G.plog (G.mat (peak x))

lemma peak_root (G : Gauge) (d : ℕ) : peak (0 : EdgeRead G d) = 1 := by
  simp [peak,no_flight]

@[simp] lemma logo_zero : logo (0 : EdgeRead G d) = 0 := by simp [logo,peak_root]

lemma peak_smooth (G : Gauge) (d : ℕ) : ContDiffAt ℝ ω (fun x : EdgeRead G d => G.mat (peak x)) 0 := by
  let g (X : Route G d) := G.mat (flight X 1)
  let f (x : G.Color) := G.mat (G.lieExp x)
  have he : ContDiff ℝ ω f := G.exp_jet
  have hx : ContDiffAt ℝ ω g 0 := (arrival G d).1.contDiffAt
  have h1 : ContDiffAt ℝ ω (fun x : EdgeRead G d => f x.1) 0 := he.contDiffAt.comp _ contDiffAt_fst
  have h2 : ContDiffAt ℝ ω (fun x : EdgeRead G d => g x.2.2) 0 := hx.comp (f:=fun x : EdgeRead G d => x.2.2) (0:EdgeRead G d) (contDiffAt_snd.comp _ contDiffAt_snd)
  have h3 : ContDiffAt ℝ ω (fun x : EdgeRead G d => f (x.1-x.2.1)) 0 := he.contDiffAt.comp _ (by fun_prop)
  unfold peak; simp_rw [G.mat_mul,G.mat_inv]; exact (h1.mul h2).mul (((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt).comp _ h3)

lemma logo_smooth (G : Gauge) (d : ℕ) : ContDiffAt ℝ ω (logo (G:=G) (d:=d)) 0 := by
  exact (show ContDiffAt ℝ ω G.plog (G.mat (peak (0:EdgeRead G d))) from by rw [peak_root,G.mat_one]; exact G.plog_diff).comp (f:=fun x : EdgeRead G d => G.mat (peak x)) 0 (peak_smooth G d)

lemma plog_velocity (v : G.Color) : fderiv ℝ G.plog 1 (G.colorMat v) = v := by
  have hv : HasFDerivAt (fun z : G.Color => G.plog (G.mat (G.lieExp z))) ((fderiv ℝ G.plog 1) ∘L G.colorMat.toContinuousLinearMap) 0 :=
    (show HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (G.lieExp 0)) from
      (show G.mat (G.lieExp 0)=1 by simp).symm ▸ ((G.plog_diff.differentiableAt (by simp)).hasFDerivAt)).comp
      (f:=fun x => G.mat (G.lieExp x)) (0:G.Color) G.expDiff_zero
  have hg := (show HasFDerivAt (fun z : G.Color => z) (ContinuousLinearMap.id ℝ _) 0 from
    (hasFDerivAt_id 0)).congr_of_eventuallyEq G.plog_left
  exact DFunLike.congr_fun (hv.unique hg) v

lemma echoing (x : EdgeRead G d) : fderiv ℝ logo 0 x = steady x.2.2 + x.2.1 := by
  let u : ℝ → EdgeRead G d := fun t => t • x
  let a (y : G.Color) (t : ℝ) := G.mat (G.lieExp (t • y))
  have he (y : G.Color) : HasDerivAt (a y) (G.colorMat y) 0 := by
    have hv : HasDerivAt (fun t : ℝ => t • y) y 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const y
    exact G.expDiff_zero.comp_hasDerivAt_of_eq 0 hv (by simp)
  let g (y : Route G d) := G.mat (flight y 1)
  have heq (t : ℝ) : G.mat (peak (t • x))=a x.1 t*g (t•x.2.2)*star (a (x.1-x.2.1) t) := by
    unfold a peak g; simp only [G.mat_mul,G.mat_inv, Prod.smul_fst, Prod.smul_snd, smul_sub]
  have hg := (arrival G d).2.2 x.2.2
  have hp : HasDerivAt (fun t : ℝ => G.mat (peak (t • x))) (G.colorMat (steady x.2.2+x.2.1)) 0 := by
    rw [funext heq]
    apply (((he x.1).mul hg).mul (he (x.1-x.2.1)).star).congr_deriv
    simp only [Pi.mul_apply, a, zero_smul, G.mat_lieExp_zero,G.mat_one, no_flight, mul_one,one_mul,star_one,star_sub,G.colorMat_skew,map_sub,map_add]; abel
  have hy : HasDerivAt (fun t : ℝ => logo (t • x)) (steady x.2.2+x.2.1) 0 := by
    have hu := ((G.plog_diff.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt_of_eq (x:=0) hp (by rw [zero_smul,peak_root,G.mat_one]); exact hu.congr_deriv (plog_velocity ..)
  have hd := ((logo_smooth G d).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (x:=0)
    (show HasDerivAt u x 0 by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x) (show 0=u 0 from (zero_smul ..).symm)
  exact hd.unique hy

-- Separate unaffected pure site gauges (the disappearing part of every
-- pure-gauge log term at the top position degree).
private def start (G : Gauge) (d : ℕ) : G.Color →L[ℝ] EdgeRead G d := ContinuousLinearMap.inl ..
private def stopRest (G : Gauge) (d : ℕ) : G.Color × Route G d →L[ℝ] EdgeRead G d := ContinuousLinearMap.inr ..

lemma logo_cost (d : ℕ) (w : Fin n → E4 → G.Color) (X : Fin n → Snap G d) (a : Fin n → ℕ) (e : Axis)
    (ha : ∀ i, 0 < a i) (hw : ∀ i,w i∈ rangeLt G.Color (a i+1)) (hX : ∀ i, throughSlot (X i) (a i)) :
    let M := iteratedFDeriv ℝ n logo (0 : EdgeRead G d)
    (fun x : E4 => M fun i => (w i x,jump (w i) x e,road x e (X i))) ∈ rangeLt G.Color (∑ i,a i) := by
  classical
  intro M
  let u (i : Fin n) (x : E4) := stopRest G d (jump (w i) x e,road x e (X i))
  let y (i : Fin n) (x : E4) := start G d (w i x)
  let f i (s : Bool) x := if s then u i x else y i x
  have hg (i : Fin n) : u i∈rangeLt _ (a i) := by
    have hj := jump_band (hw i)
    have hl (W : Potential G) : _ := linear_band (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Axis => G.Color) e) (a i) (f:=W)
    exact linear_band _ _ (combine (hl _ hj) (rations (X i) (hX i) _))
  have he : (fun x : E4 => M fun i => (w i x, jump (w i) x e, road x e (X i)))=∑ s : Slices n,fun x => M (fun i => f i (s i) x) := by
    funext x; rw [Finset.sum_apply]
    have he i : (w i x, jump (w i) x e, road x e (X i)) = ∑ s : Bool, f i s x := by
      simp [f,y,u,start,stopRest]
    simp_rw [he]; exact M.map_sum (fun i s => f i s x)
  rw [he]; apply Submodule.sum_mem; intro s _
  by_cases h : ∃ i,s i=true
  · let b i := if s i then a i-1 else a i
    have hf i : (fun x => f i (s i) x)∈ rangeLt _ (b i+1) := by
      unfold f b; split; swap
      · exact linear_band _ _ (hw i)
      rw [Nat.sub_add_cancel (ha i)]; exact hg i
    have H : ∑ i, b i < ∑ i, a i := by
      obtain ⟨i,hi⟩ := h
      exact Finset.sum_lt_sum (fun j _ => by unfold b; split <;> omega)
        ⟨i,Finset.mem_univ _,by unfold b; rw [if_pos hi]; have := ha i; omega⟩
    exact grows _ H (multi_band M _ b hf)
  have hx : logo ∘ (start G d)=0 := by
    funext x; unfold logo peak comp
    simp [start,no_flight]
  have he : M.compContinuousLinearMap (fun _ => start G d)=0 := by
    rw [← jets_linear (start G d) ((logo_smooth G d).of_le le_top),hx, iteratedFDeriv_zero]; rfl
  push Not at h
  rw [show (fun x => M (fun i => f i (s i) x))=0 from ?_]
  · exact Submodule.zero_mem _
  funext x; simp only [f,h]; exact DFunLike.congr_fun he (fun i => w i x)

end YM.Planned.PrimaryIntegral295.Place
