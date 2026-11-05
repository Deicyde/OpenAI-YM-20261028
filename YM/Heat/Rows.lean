import Mathlib.Analysis.InnerProductSpace.StarOrder
import YM.Analysis.Weak
import YM.OS.Flow





/-!
# Continuous calculus on the bounded first-step, positive powers

No Stone postulated. Deliberately avoid atomic-at-zero pitfalls.
Right half plane contractive norm calculus (no op norm continuity edge assumed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S : Semigroup H a)

abbrev duration (t : ℝ≥0) := ((t:ℝ):ℂ)

abbrev inside : Set ℂ := {z | 0 < z.re}
lemma open_inside : IsOpen inside := isOpen_lt continuous_const continuous_re
lemma dur {t : ℝ≥0} : duration t ∈ inside ↔ 0<t := by
  change 0<(duration t).re ↔ _
  rw [duration,ofReal_re]
  rfl

lemma clock_mul (n : ℕ) (t) : S.E (n • t) = S.E t ^ n := by
  induction n with
  | zero => rw [zero_smul, S.eZero,pow_zero]; rfl
  | succ i ih => rw [add_smul,one_smul,S.time,ih,pow_succ]; rfl

lemma stare (t) : IsSelfAdjoint (S.E t) := S.sym t

lemma at_root {z : ℂ} {t} (h : z ∈ spectrum ℂ (S.E t)) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ z=(r:ℂ) := by
  -- square gives nonneg; split trivial Op case for spectral norm
  have he : SpectrumRestricts (S.E t) ContinuousMap.realToNNReal := by
    rw [show S.E t=S.E (2 • (t/2)) from congr_arg S.E (by rw [show ((2:ℕ)•(t/2))=(2:ℝ≥0)*(t/2) by simp]; field_simp), S.clock_mul]
    exact (S.stare (t/2)).sq_spectrumRestricts
  have hc := SpectrumRestricts.real_iff.mp (S.stare t).spectrumRestricts z h
  have hr := SpectrumRestricts.nnreal_iff.mp he _ ((S.stare t).coe_mem_spectrum_complex.mp (hc ▸ h)) -- may rewrite hc in rhs h ??
  refine ⟨z.re,hr,?_ ,hc⟩
  rcases subsingleton_or_nontrivial H.space with I|I
  · exfalso; apply h
    change IsUnit ((algebraMap ℂ H.Op) z - S.E t); rw [Subsingleton.elim ((algebraMap ℂ H.Op) z - S.E t) (1:H.Op)]; exact isUnit_one
  exact (re_le_norm _).trans ((spectrum.norm_le_norm_of_mem h).trans (S.shrinks _))

/-- Continuous on closed spec (includes zero possibly only in spectrum).
- Outside right halfplane use junk zero, never evaluate. -/
def adopt (t) (z : ℂ) (h : z ∈ inside) : C(spectrum ℂ (S.E t),ℂ) :=
  ⟨fun x => x.val ^ z, by
    apply continuous_iff_continuousAt.mpr; intro x
    have he : 0 ≤ x.val.re := by
      obtain ⟨r,hr,-,hy⟩ := S.at_root x.property; rwa [hy,ofReal_re]
    exact (continuousAt_cpow_const_of_re_pos (Or.inl he) h).comp continuous_subtype_val.continuousAt⟩

def roots (z : ℂ) : C(spectrum ℂ (S.E 1), ℂ) := if h : z ∈ inside then S.adopt 1 z h else 0

-- rights
lemma on_root {z} (h : z ∈ inside) (x) : S.roots z x=(x.val:ℂ)^z := by simp [roots,h,adopt]

lemma joins_root : ContinuousOn S.roots inside := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases x with ⟨⟨p,hp⟩,z⟩
  rw [show uncurry (fun (x : inside) y => (inside.restrict S.roots x) y) = fun x => x.2.val ^ (x.1.val : ℂ) from
    funext fun x => S.on_root x.1.property x.2]
  have he : 0 ≤ z.val.re := by
    obtain ⟨r,hr,-,hy⟩ := S.at_root z.property; rwa [hy,ofReal_re]
  exact ContinuousAt.comp (g := fun p : ℂ × ℂ => p.1^p.2) (f := fun x : ↥inside × ↥(spectrum ℂ (S.E 1)) => ((x.2.val:ℂ), x.1.val))
    (continuousAt_cpow_of_re_pos (p := (z.val,p)) (Or.inl he) hp)
    ((continuous_subtype_val.comp continuous_snd |>.prodMk (continuous_subtype_val.comp continuous_fst)).continuousAt)

lemma holo_root : AnalyticOnNhd ℂ S.roots inside := by
  let X := ↥(spectrum ℂ (S.E 1))
  let P (i : X) : C(X,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ i
  refine Analysis.lift_weak (Set.range P) (fun f g h => ContinuousMap.ext fun i => h (P i) (mem_range_self i)) open_inside S.joins_root ?_
  rintro _ ⟨x,rfl⟩
  refine (DifferentiableOn.congr (f := fun z : ℂ => x.val^z) ?_ (fun p hp => S.on_root hp x))
  by_cases h : x.val=0
  · simp only [h]
    apply DifferentiableOn.congr (differentiableOn_const (c := (0:ℂ))); intro z hz
    refine Complex.zero_cpow ?_
    rintro rfl; exact lt_irrefl (0:ℝ) hz
  apply (differentiable_id.const_cpow (Or.inl h)).differentiableOn

def F (z : ℂ) : H.Op := cfcHom (S.stare 1).isStarNormal (S.roots z)

lemma norm_row {z} (h : z∈inside) : ‖S.F z‖ ≤ 1 := by
  rw [F,(isometry_cfcHom _ (S.stare 1).isStarNormal).norm_map_of_map_zero (map_zero _)]
  apply ((S.roots z).norm_le (by norm_num)).mpr
  intro x
  obtain ⟨r,hr,hi,hh⟩ := S.at_root x.property
  rw [S.on_root h,hh, norm_cpow_eq_rpow_re_of_nonneg hr (show z.re ≠ 0 from LT.lt.ne' h)]
  exact Real.rpow_le_one hr hi (le_of_lt h)

lemma localHeat : AnalyticOnNhd ℂ S.F inside := by
  let V : C(spectrum ℂ (S.E 1),ℂ) →⋆ₐ[ℂ] H.Op := cfcHom (S.stare 1).isStarNormal
  let L : C(spectrum ℂ (S.E 1),ℂ) →L[ℂ] H.Op := ⟨V.toAlgHom.toLinearMap,cfcHom_continuous (S.stare 1).isStarNormal⟩
  intro z hz
  exact L.analyticAt _ |>.comp (S.holo_root z hz)

lemma pairs {z w} (h : z ∈ inside) (hv : w ∈ inside) : S.F (z+w)=(S.F z).comp (S.F w) := by
  have he : S.roots (z+w)=S.roots z*S.roots w := by
    apply ContinuousMap.ext
    intro x
    have hj : z+w∈inside := (add_pos (show 0<z.re from h) (show 0<w.re from hv))
    change S.roots (z+w) x=S.roots z x*S.roots w x
    rw [S.on_root hj, S.on_root h,S.on_root hv]
    by_cases H : x.val=0
    · rw [H,zero_cpow (show z+w≠0 from fun he => lt_irrefl (0:ℝ) (show (0:ℂ) ∈inside from he ▸ hj)),
          zero_cpow (show z≠0 from fun he => lt_irrefl (0:ℝ) (show (0:ℂ) ∈inside from he ▸ h)), zero_mul]
    exact cpow_add z w H
  unfold F; rw [he,map_mul]; rfl

lemma flip_row {z} (hz : z∈ inside) : (S.F z).adjoint=S.F (star z) := by
  have he : S.roots (star z)=star (S.roots z) := by
    apply ContinuousMap.ext; intro x; change _ = star _
    rw [S.on_root (show star z∈inside from hz),S.on_root hz]
    obtain ⟨r,hr,_,hx⟩ := S.at_root x.property
    rw [hx]
    change _ ^ (starRingEnd ℂ z) = _
    rw [cpow_conj (↑r) z (by rw [arg_ofReal_of_nonneg hr]; exact Real.pi_pos.ne),conj_ofReal]
    rfl
  unfold F; rw [he,map_star]; rfl

lemma stays {z} (_ : z∈ inside) (s : Cross a) : (S.F z).comp (S.U s)=(S.U s).comp (S.F z) := by
  have he : Commute (S.E 1) (S.U s) := S.independent 1 s
  exact (S.stare 1).commute_cfcHom (S.stare 1).isStarNormal he (S.roots z)
end YM.OS.Semigroup
