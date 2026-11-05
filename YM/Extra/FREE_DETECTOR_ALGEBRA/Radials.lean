import YM.Extra.FREE_DETECTOR_ALGEBRA.Harmonic
import YM.Extra.FREE_DETECTOR_ALGEBRA.Laplace
import YM.Extra.FREE_DETECTOR_ALGEBRA.Match


set_option warningAsError false

/-!
# Actual powers/angles of the entries of the one-leg kernel

No Fourier transform convention needed. Kelvin derivatives raise angular
degree by one in four dimensions (remain of pure harmonic degree), so
lower angular degree from a double contraction cannot be confused with it.
Germs on x≠0. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.SphereTest
open Function Filter Set Tensor Analysis Maxwell Wick
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge}
variable {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {f g : E4 → F} {j k : ℕ}

structure Spherical (f : E4 → F) (j : ℕ) : Prop where
  size : Pure j f
  harmonic : lap f=0

/-- `rr^(ℓ+1) f` with f spherical of angular degree ℓ. -/
def KelvinAng (j : ℕ) (f : E4 → F) : Prop := ∃ H : E4 → F, Spherical H j ∧ EqOn f (rr^(j+1) • H) away

lemma KelvinAng.near (h : KelvinAng j f) (he : EqOn f g away) : KelvinAng j g := by obtain ⟨H,hh,h⟩ := h; exact ⟨H,hh,he.symm.trans h⟩

lemma ang_zero (j : ℕ) : KelvinAng j (0:E4→F) :=
  ⟨0,⟨pure_zero _,lap_zero _⟩,fun x _ => by simp⟩

lemma ang_const (c : F) : KelvinAng 0 (fun x => rr x • c) :=
  ⟨fun _ => c, ⟨⟨contDiff_const,fun _ _ => by simp⟩,lap_zero _⟩,fun x _ => by simp⟩

lemma KelvinAng.diff (hf : KelvinAng j f) (x : E4) (hx : x∈away) : ContDiffAt ℝ ∞ f x := by
  obtain ⟨F,hF,h⟩ := hf
  refine ContDiffAt.congr_of_eventuallyEq (show ContDiffAt ℝ ∞ (rr^(j+1) • F) x from ((rr_smooth hx).pow _).smul hF.size.smooth.contDiffAt) ?_
  filter_upwards [open_away.mem_nhds hx] with y hy; exact h hy

lemma KelvinAng.sub (hf : KelvinAng j f) (hg : KelvinAng j g) : KelvinAng j (f-g) := by
  obtain ⟨F,hF,h⟩ := hf; obtain ⟨G,hG,H⟩ := hg
  refine ⟨F-G, ⟨hF.size.minus hG.size,?_⟩,fun x hx => ?_⟩
  · rw [lap_sub' hF.size.smooth hG.size.smooth,hF.harmonic,hG.harmonic,sub_self]
  simp [h hx,H hx,smul_sub]

lemma KelvinAng.add (hf : KelvinAng j f) (hg : KelvinAng j g) : KelvinAng j (f+g) := by
  have h := hf.sub ((ang_zero j).sub hg); simpa using h

lemma KelvinAng.scalar (hf : KelvinAng j f) (t : ℝ) : KelvinAng j (t • f) := by
  obtain ⟨F,hF,h⟩ := hf; refine ⟨t • F,⟨hF.size.vScale t,?_⟩,fun x hx => ?_⟩
  · rw [lap_scale' hF.size.smooth,hF.harmonic,smul_zero]
  change t • f x = _; rw [h hx]; simp [smul_comm t]

lemma KelvinAng.linear (hf : KelvinAng j f) (L : F →L[ℝ] M) : KelvinAng j (fun x => L (f x)) := by
  obtain ⟨F,hF,h⟩ := hf; refine ⟨fun x => L (F x),⟨hF.size.linear L,?_⟩,fun x hx => ?_⟩
  · rw [lap_linear hF.size.smooth L,hF.harmonic]; ext x; simp
  change L (f x)=_; rw [h hx]; exact map_smul L _ _

lemma ang_sum {ι : Type*} (s : Finset ι) (f : ι → E4 → F) (h : ∀ i∈s,KelvinAng j (f i)) : KelvinAng j (fun x => ∑ i∈s,f i x) := by
  classical
  have he : KelvinAng j (∑ i ∈ s, f i) := by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact ang_zero _
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self _ _)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
  rw [funext fun x => Finset.sum_apply x s f] at he; exact he

lemma lap_derives (hf : ContDiff ℝ ∞ f) (a : Axis) : lap (grad a f) = grad a (lap f) := by
  funext x; unfold lap
  rw [grad_sum_fun _ (f:=fun b => grad b (grad b f)) (fun b _ => (grad_diff_all (grad_diff_all hf b) b).contDiffAt)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he : grad b (grad a f) = grad a (grad b f) := by funext x; exact grad_exchange hf.contDiffAt b a
  rw [he]; exact grad_exchange (grad_diff_all hf b).contDiffAt b a

lemma radialRaise (hf : Spherical f j) (a : Axis) :
    Spherical (qRad • grad a f - (2*((j:ℝ)+1)) • (coordF a • f)) (j+1) := by
  let H := (coordF a • f)
  let B := ContinuousLinearMap.lsmul ℝ (E:=F) ℝ
  have hh : Pure (j+1) H := add_comm 1 j ▸ (pure_coordF a).bilinear hf.size B
  have he x : lap H x = (2:ℝ) • grad a f x := by
    rw [show lap H x = _ from lap_coordF_mul a hf.size.smooth x,hf.harmonic]; simp
  have hx1 (c : F) (a : Axis) : grad a (fun _ => c) = 0 := by ext1 z; simp [grad,D]
  have hR : Pure (j+1) (qRad • grad a f) ∧ (∀ x, lap (qRad • grad a f) x = (4*((j:ℝ)+1)) • grad a f x) := by
    cases j with
    | zero =>
      have hdf : grad a f=0 := by
        have he := hf.size.zeroth
        exact (congr_arg (grad a) he).trans (hx1 _ a)
      rw [hdf,smul_zero]; exact ⟨pure_zero _,fun x => (congr_fun (lap_zero (0:F)) x).trans (smul_zero ..).symm⟩
    | succ j =>
      have ht := hf.size.derive a
      refine ⟨Nat.add_comm 2 j ▸ pure_square.bilinear ht B,fun x => ?_⟩
      rw [lap_raise ht,lap_derives hf.size.smooth,hf.harmonic,
        show grad a (0:E4→F)=0 from hx1 _ a,smul_zero,add_zero]
      simp only [Pi.smul_apply]; congr 1; push_cast; ring
  let c : ℝ := 2*((j:ℝ)+1)
  refine ⟨hR.1.minus (hh.vScale _),?_⟩
  change lap (qRad • grad a f - c • H)=0
  rw [lap_sub' hR.1.smooth (hh.vScale _).smooth, lap_scale' hh.smooth]
  ext1 x; rw [Pi.sub_apply, Pi.smul_apply, he,hR.2]; change _ = (0:F); unfold c; module

theorem KelvinAng.gradient (hf : KelvinAng j f) (a : Axis) : KelvinAng (j+1) (grad a f) := by
  obtain ⟨F,hF,h⟩ := hf
  refine ⟨_,radialRaise hF a,fun x hx => ?_⟩
  have he : f=ᶠ[𝓝 x] rr^(j+1) • F := by filter_upwards [open_away.mem_nhds hx] with y hy; exact h hy
  rw [show grad a f x = grad a (rr^(j+1) • F) x from GermD _ he,
    grad_times (show ContDiffAt ℝ ∞ (rr^(j+1)) x from (rr_smooth hx).pow _) hF.size.smooth.contDiffAt,grad_power hx]
  change _ • F x + rr x^(j+1) • grad a F x = rr x^(j+2) • (qRad x • grad a F x - (2*((j:ℝ)+1)) • (x a • F x))
  have he : rr x*qRad x=1 := inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  simp only [smul_sub,smul_smul, Nat.cast_add,Nat.cast_one]
  rw [show rr x^(j+2)*qRad x=rr x^(j+1) by rw [pow_succ, mul_assoc,he,mul_one]]; module

theorem KelvinAng.jet (hf : KelvinAng j f) (k : ℕ) (v : Dirs k) : KelvinAng (j+k) (fun x => coeff f k x (dir v)) := by
  induction k generalizing j f with
  | zero => simpa only [add_zero,coeff_apply_zero] using hf
  | succ k ih =>
    let a := v 0
    let s := Fin.tail v
    have hv : v = Fin.cons a s := (Fin.cons_self_tail _).symm
    let q : ℝ := ((k+1:ℕ):ℝ)⁻¹
    have ht := (ih (hf.gradient a) s).scalar q
    rw [show j+1+k=j+(k+1) by omega] at ht
    apply ht.near
    intro x hx; rw [hv,dir_cons]
    change q • (coeff (grad a f) k x) (dir s) = coeff f _ x (Fin.cons (basis a) (dir s))
    rw [coeff_apply_cons]
    · rfl
    exact (hf.diff x hx).of_le (WithTop.coe_le_coe.mpr le_top)


end YM.Extra.FD.SphereTest
