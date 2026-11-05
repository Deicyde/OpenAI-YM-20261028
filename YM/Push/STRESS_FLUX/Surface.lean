import YM.Push.STRESS_FLUX.Annular
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching

/-!
A surface version on closed coordinate boxes. Use Lebesgue volume in
THREE face coordinates (ordinary face measure, outward orientation), not
totalized ambient volume on the surface nor samples against a discontinuous
χ in `Table.shellGrad`. This does not assert a general Stokes theorem on
 arbitrary enclosing manifolds. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Surface
open Table Work.A01 Analysis MeasureTheory Function Filter Set Metric
open scoped Topology BigOperators ContDiff
abbrev Cube := Axis → ℝ
abbrev to4 := WithLp.toLp (V:= Cube) 2

def deep (l r : Cube) : Set E4 := {x | ∀ i, x i∈Ioo (l i) (r i)}
lemma deep_open (l r : Cube) : IsOpen (deep l r) := by
  rw [show deep l r = ⋂ i, (fun x : E4 => x i) ⁻¹' (Ioo (l i) (r i)) by ext; simp [deep]]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (by fun_prop)
lemma deep_in {l r : Cube} {x : E4} (h : x ∈ deep l r) : x.ofLp ∈ Icc l r := ⟨fun i => (h i).1.le, fun i => (h i).2.le⟩

def edge (l : Cube) (i : Axis) (w : Fin 3 → ℝ) := to4 (i.insertNth (l i) w)

def area (l r : Cube) (F : Axis → E4 → ℂ) := ∑ i : Axis,
  ((∫ w : Fin 3 → ℝ in Icc (l ∘ i.succAbove) (r ∘ i.succAbove), F i (edge r i w)) -
   ∫ w : Fin 3 → ℝ in Icc (l ∘ i.succAbove) (r ∘ i.succAbove), F i (edge l i w))

variable {G : Gauge} {L : Register G} {S : Table L} {W : DiffPlan S} {H : S.RealSpin}
    {n d : ℕ} {x : Points (n+1)} {V : E4 → E4} {l r : Cube} {J : S.Stress} {χ : E4 → ℝ}
structure Encloses (x : Points (n+1)) (l r : Cube) : Prop where
  center : x 0 ∈ deep l r
  avoids (i : Fin n) : (x i.succ).ofLp ∉ Icc l r

lemma Encloses.window (ht : Encloses x l r) : ∃ χ, Window x χ ∧ tsupport χ ⊆ deep l r := by
  obtain ⟨t,ht',h⟩ := nhds_basis_closedBall.mem_iff.mp ((deep_open ..).mem_nhds ht.center)
  let χ : ContDiffBump (x 0) := ⟨t/2,t,by positivity, by linarith⟩
  rw [show closedBall (x 0) t = _ from χ.tsupport_eq.symm] at h
  exact ⟨χ,⟨χ.contDiff,χ.hasCompactSupport,χ.eventuallyEq_one,fun j hy => ht.avoids j (deep_in (h hy))⟩, h⟩

def trunc (χ : E4 → ℝ) (F : Axis → E4 → ℂ) (a : Axis) (z : E4) := (1-χ z) • F a z
lemma near_trunc (hw : Window x χ) (F : Axis → E4 → ℂ) (a : Axis) : trunc χ F a =ᶠ[𝓝 (x 0)] fun _ => 0 := by
  filter_upwards [hw.2.2.1] with y hy; simp [trunc,hy]

section Wall
variable (q : Fin (n+1) → S.Tag) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hs : S.Smooth) (hx : x∈conf _) (hw : Window x χ) (ht : Encloses x l r)
include hx ht
lemma wall_conf {y : E4} (hy : y.ofLp ∈ Icc l r) (he : y ≠ x 0) : Points.cons y x ∈ conf _ :=
  conf_cons hx fun i => Fin.cases he (fun j h => ht.avoids j (h ▸ hy)) i
include hv hs hw
lemma wall_smooth {y : E4} (hy : y.ofLp ∈ Icc l r) (a : Axis) : ContDiffAt ℝ ∞ (trunc χ (current J V x q) a) y := by
  rcases eq_or_ne y (x 0) with e|e
  · exact e ▸ (contDiffAt_const.congr_of_eventuallyEq (near_trunc hw _ _))
  exact (contDiff_const.sub hw.1 |>.contDiffAt.smul (smooth_current J V q a hv (wall_conf hx ht hy e) hs))
lemma wall_div (hd : W.Derivatives S) (hJ : Conserved W H J) (hV : killing V) {y : E4} (hy : y.ofLp ∈ Icc l r) :
    ∑ a, D (basis a) (trunc χ (current J V x q) a) y = - ∑ a, D (basis a) χ y • current J V x q a y := by
  rcases eq_or_ne y (x 0) with e|e
  · subst y
    simp only [D,(near_trunc hw ..).fderiv_eq, hw.2.2.1.fderiv_eq, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply,zero_smul,Finset.sum_const_zero,neg_zero]
  have hp := wall_conf hx ht hy e
  let F := current J V x q
  have he a := smooth_current J V q a hv hp hs
  have hh a : D (basis a) (trunc χ F a) y = (1-χ y) • D (basis a) (F a) y - D (basis a) χ y • F a y := by
    unfold D trunc
    rw [fderiv_fun_smul (c:=fun z => 1-χ z) (f:=F a) (differentiableAt_const _ |>.sub (hw.1.differentiable (by simp) _)) ((he a).differentiableAt (by simp)), fderiv_fun_sub (differentiableAt_const _) (hw.1.differentiable (by simp) _)]
    simp [sub_eq_add_neg]
  have hD := divergence hs W hd J hJ V hv hV q hp
  change ∑ a, D _ (trunc _ F a) _ = _
  rw [Finset.sum_congr rfl (fun a _ => hh a),Finset.sum_sub_distrib,← Finset.smul_sum,hD,smul_zero,zero_sub]

end Wall

lemma wall_formula (q : Fin (n+1) → S.Tag) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hs : S.Smooth) (hx : x∈conf _) (ht : Encloses x l r)
    (hw : Window x χ) (he : tsupport χ ⊆ deep l r) (hd : W.Derivatives S) (hJ : Conserved W H J) (hV : killing V) :
    area l r (current J V x q) = ∫ y, -∑ a : Axis, D (basis a) χ y • current J V x q a y := by
  let F := current J V x q
  let Q : Cube →L[ℝ] E4 := (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap
  let f (a : Axis) := trunc χ F a ∘ Q
  let f' := fun i : Axis => fderiv ℝ (f i)
  let g (y : E4) := -∑ a : Axis, D (basis a) χ y • F a y
  have hle : l ≤ r := fun i => (ht.center i).1.trans (ht.center i).2 |>.le
  have hc a z (hz : z∈Icc l r) : ContDiffAt ℝ ∞ (trunc χ F a) (Q z) := wall_smooth q hv hs hx hw ht hz a
  have hu a z (hz : z∈Icc l r) := (hc a z hz).comp z Q.contDiff.contDiffAt
  have hpartial (z) (hz : z∈Icc l r) : (∑ a : Axis, f' a z (Pi.single a 1)) = g (Q z) := by
    have hh (a : Axis) : Q (Pi.single a 1) = basis a := PiLp.toLp_single 2 a 1
    calc
      _ = ∑ a, D (basis a) (trunc χ F a) (Q z) := by simp only [D,f',f, fderiv_comp _ ((hc _ z hz).differentiableAt (by simp)) (Q.differentiableAt (x:=z)), Q.fderiv,ContinuousLinearMap.comp_apply,hh]
      _ = _ := wall_div q hv hs hx hw ht hd hJ hV hz
  have hb (z) (hz : z ∈ univ.pi (fun i => Ioo (l i) (r i)) \ (∅:Set Cube)) : z ∈ Icc l r := deep_in (x:=to4 z) (fun i => hz.1 i (mem_univ i))
  have hi a : ContinuousOn (fun z => f' a z (Pi.single a 1)) (Icc l r) := fun z hz =>
    ((Analysis.dSmooth (show ContDiffAt ℝ ∞ (f a) z from hu a z hz) (Pi.single a 1) (m:=∞) (by simp)).continuousAt).continuousWithinAt
  have h := integral_divergence_of_hasFDerivAt_off_countable' (n:=3) l r hle f f' ∅ countable_empty (fun i z hz => (hu i z hz).continuousAt.continuousWithinAt)
    (fun z hz i => ((hu i z (hb z hz)).differentiableAt (by simp)).hasFDerivAt)
    (integrable_finsetSum _ fun i _ => (hi i).integrableOn_compact isCompact_Icc)
  have hχ a (t : Cube) (h : t=l ∨ t=r) (w : Fin 3 → ℝ) : χ (edge t a w)=0 := by
    by_contra hc
    have := he (subset_closure hc) a
    simp only [edge,to4,WithLp.ofLp_toLp,Fin.insertNth_apply_same,mem_Ioo] at this
    rcases h with h|h <;> subst t <;> linarith
  have ht' (t : Cube) (h : t=l ∨ t=r) a (w : Fin 3 → ℝ) : f a (a.insertNth (t a) w)=F a (edge t a w) := by change (1-χ (edge t a w)) • F a (edge t a w) = _; rw [hχ _ t h, sub_zero,one_smul]
  simp_rw [ht' l (Or.inl rfl),ht' r (Or.inr rfl)] at h
  change area l r F = ∫ y, g y
  rw [area,← h,setIntegral_congr_fun measurableSet_Icc hpartial]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    have hc : fderiv ℝ χ (Q z) = 0 := by_contra fun h' => hz (deep_in (he (tsupport_fderiv_subset ℝ (subset_closure h'))))
    simp [g,D,hc])]
  exact (PiLp.volume_preserving_toLp Axis).integral_comp (MeasurableEquiv.toLp 2 Cube).measurableEmbedding g

/-- Box flux = any smooth tested cutoff flux by conservation/symmetry.
The center must be STRICTLY inside; all other points STRICTLY outside the
closed box. Edges/corners aren't counted as contact insertions. `q` is never
restricted to any particular exterior word. -/
theorem box (q : Fin n → S.Tag) (B : S.Field d) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hs : S.Smooth) (hx : x∈conf _) (ht : Encloses x l r)
    (hw : Window x χ) (hd : W.Derivatives S) (hJ : Conserved W H J) (hV : killing V) :
    area l r (current J V x (Fin.cons ⟨d,B⟩ q)) = flux J χ V x q B := by
  obtain ⟨ψ,hp,he⟩ := ht.window
  have hi a := Annular.expanded (J:=J) hx hp hs q B (fun b => (hv b).continuous) a
  rw [wall_formula _ hv hs hx ht hp he hd hJ hV, integral_neg,integral_finsetSum _ (fun a _ => (hi a).1)]
  simp_rw [← (hi _).2]; exact Annular.independent hs hd hJ V hv hV hx hp hw q B

section Pre
variable {H : S.Hierarchy} {p : Climb.Parts S} {Y : Ward.SpinRows S} (q : Fin n → S.Tag) (B : S.Field d) (hx : x∈conf _) (ht : Encloses x l r)
    (hd : W.Derivatives S) (hJ : Climb.Pre H W J p Y)

include hx ht hd hJ


end Pre
end YM.StressFlux.Surface
