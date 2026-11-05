import YM.Next.MAXWELL.Beacon
import YM.Next.MAXWELL.ComplexInk

/-!
# Entire identity transfer, finite-dimensional actions
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis Mink
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder

lemma from_real_parameter {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F G : ℂ → V} (h : AnalyticOnNhd ℂ F univ) (g : AnalyticOnNhd ℂ G univ)
    (hg : ∀ x : ℝ, F x=G x) : F=G := by
  apply h.eq_of_frequently_eq g (z₀:=0)
  have H : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x:=0)).mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
    filter_upwards [self_mem_nhdsWithin] with y hy; exact fun ht : (y:ℂ) = 0 => hy (by exact_mod_cast ht)
  by_contra! w
  obtain ⟨i,hi⟩ := (H.eventually w).exists; exact hi (hg _)

def lands (A : Ink) : Prop := ∀ p q : Ink → ℂ, ContDiff ℂ ω p → ContDiff ℂ ω q →
    (∀ s, p (paints s) = q (paints s)) → p A=q A

lemma product_lands {A B} (a : lands A) (b : lands B) : lands (follow A B) := by
  intro p q hp hq h
  have he (s : Ortho) : p (follow A (paints s)) = q (follow A (paints s)) :=
    a (fun A => p (follow A (paints s))) (fun A => q (follow A (paints s)))
      (hp.comp (follow_right _)) (hq.comp (follow_right _)) fun t => by simp only [follows]; exact h _
  exact b (fun B => p (follow A B)) (fun B => q (follow A B)) (hp.comp (follow_left A)) (hq.comp (follow_left A)) he

lemma boosted (a : SpaceAxis) (t : ℝ) : lands (stencil ((Ray.fromAxis a).boost t)) := by
  intro p q hp hq h
  have he : ∀ x : ℝ, p (stroll a x) = q (stroll a x) := fun x => by rw [← writes_axes]; exact h _
  have hh := from_real_parameter
    (funn p hp a) (funn q hq a) he
  rw [night]; exact congr_fun hh _
where
  funn (p : Ink → ℂ) (hp : ContDiff ℂ ω p) (a) : AnalyticOnNhd ℂ (fun z => p (stroll a z)) univ := fun z _ =>
    ((hp.comp (stroll_diff a)).contDiffAt).analyticAt

lemma boarded (g : Lorentz) : lands (stencil g) := by
  have h : g ∈ Bid.beamGens := by rw [show Bid.beamGens=⊤ from Work.A16.answer]; apply Subgroup.mem_top
  have hv : lands (stencil 1) := by intro p q hp hq hh; rw [stencil_one]; exact hh _
  suffices H : lands (stencil g) ∧ lands (stencil g⁻¹) from H.1
  induction h using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨s,hs,rfl⟩|⟨i,t,rfl⟩
    · refine ⟨fun p q hp hq h => by rw [photos _ hs]; exact h _,?_⟩
      obtain ⟨t,ht,H⟩ := Work.A16.exists_room_of_fix _ (fixed_inverse (L := Lorentz.room s hs) (spatial_axis s hs))
      intro p q hp hq h; rw [← H,photos t ht]; exact h _
    rw [Ray.boost_neg]; exact ⟨boosted _ _,boosted _ _⟩
  | one => simpa using And.intro hv hv
  | mul x y hx hy ha hb =>
    rw [stencil_mul,mul_inv_rev,stencil_mul]; exact ⟨product_lands ha.1 hb.1,product_lands hb.2 ha.2⟩
  | inv x hx H => rw [inv_inv]; exact And.symm H

lemma fixes_scripts (g : Lorentz) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {p q : Ink → V} (hp : ContDiff ℂ ω p) (hq : ContDiff ℂ ω q)
    (h : ∀ k : Ortho, p (paints k)=q (paints k)) : p (stencil g)=q (stencil g) := by
  let B := Module.finBasis ℂ V
  apply B.equivFun.injective; funext i
  let L := (B.coord i).toContinuousLinearMap
  exact boarded g _ _ (L.contDiff.comp hp) (L.contDiff.comp hq) (fun k => congr_arg L (h k))

variable {G : Gauge} (F : Labels.Frames G)

lemma settles (d : ℕ) : ∃ f : Ink → Module.End ℂ ((Model F).Field d),
    (∀ v, ContDiff ℂ ω fun A => f A v) ∧ ∀ s : Ortho, f (paints s)=((gear F).act d s).toLinearMap := by
  let B := Module.finBasis ℂ ((Model F).Field d)
  choose g hg hh using (show ∀ i j, Writes (fun s => B.coord i ((gear F).act d s (B j))) from fun i j =>
    writes_any F d (B.coord i) (B j))
  let f (A : Ink) := B.constr ℂ (fun j => ∑ i, g i j A • B i)
  refine ⟨f,?_,fun s => ?_⟩
  · intro v
    rw [← B.sum_repr v]; simp_rw [map_sum,map_smul]
    have he (j) (A : Ink) : f A (B j) = ∑ i, g i j A • B i := B.constr_basis ..
    simp_rw [he]
    apply ContDiff.sum; intro j _
    have ht : ContDiff ℂ ω fun x => ∑ i, g i j x • B i := ContDiff.sum fun i _ =>
      (show ContDiff ℂ ω (fun x => g i j x • B i) from (hg i j).smul (show ContDiff ℂ ω (fun _ : Ink => B i) from contDiff_const))
    exact ht.const_smul _
  apply B.ext
  intro j; simp only [f,Module.Basis.constr_basis,hh]; exact B.sum_repr _

def tracks (d : ℕ) := (settles F d).choose
lemma lit (d : ℕ) (s : Ortho) (v) : tracks F d (paints s) v=(gear F).act d s v := by
  unfold tracks; rw [(settles F d).choose_spec.2]; rfl
lemma lampCurve {d} (p : (Model F).Field d) : ContDiff ℂ ω fun A => tracks F d A p := (settles F d).choose_spec.1 _

def routine (d : ℕ) (x : Lorentz) := tracks F d (stencil x)

@[simp] lemma drives_one (d) (v) : routine F d 1 v=v := by rw [routine,stencil_one,lit,(gear_port F).fixes]
@[simp] lemma drives_mul (d) (v w : Lorentz) (x) : routine F d (v*w) x = routine F d v (routine F d w x) := by
  have h (s : Ortho) (g : Lorentz) (x : (Model F).Field d) :
      tracks F d (follow (paints s) (stencil g)) x = tracks F d (paints s) (tracks F d (stencil g) x) :=
    fixes_scripts g ((lampCurve F x).comp (follow_left (paints s)))
      (show ContDiff ℂ ω (fun A => tracks F d (paints s) (tracks F d A x)) from
        (LinearMap.toContinuousLinearMap (tracks F d (paints s))).contDiff.comp (lampCurve F _)) (fun k => by
      simp only [Function.comp_apply,follows,lit,(gear_port F).sends])
  unfold routine; rw [stencil_mul]
  exact fixes_scripts v ((lampCurve F x).comp (follow_right _)) (lampCurve F (tracks F d (stencil w) x)) fun s => h s w x

def hop (d) (x : Lorentz) := LinearEquiv.ofLinear (routine F d x) (routine F d x⁻¹)
  (by apply LinearMap.ext; intro v; rw [LinearMap.comp_apply,← drives_mul,mul_inv_cancel]; exact drives_one ..)
  (by apply LinearMap.ext; intro v; rw [LinearMap.comp_apply,← drives_mul,inv_mul_cancel]; exact drives_one ..)

lemma hop_eval (d) (v x) : hop F d v x=tracks F d (stencil v) x := rfl

lemma hop_coherent {d e} (h : d≤e) (x : Lorentz) (p : (Model F).Field d) :
    (scheme F).rise h (hop F d x p) = hop F e x ((scheme F).rise h p) := by
  simp only [hop_eval]
  exact fixes_scripts x (((scheme F).rise h).toContinuousLinearMap.contDiff.comp (lampCurve F p)) (lampCurve F _) (by
    intro s; simp only [Function.comp_apply,lit,(gear_laws F).filtered]; rfl)

lemma hop_cont (d : ℕ) (p : (Model F).Field d) : Continuous (fun s => hop F d s p) :=
  (lampCurve F p).continuous.comp stencil_cont

end YM.Maxwell.Free
