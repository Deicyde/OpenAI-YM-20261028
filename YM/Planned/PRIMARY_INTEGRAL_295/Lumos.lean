import YM.Planned.PRIMARY_INTEGRAL_295.Novas
/-!
# Exact moving genuine law E.LXE from Novas.T candidate

Uses TRUE local PSD (not charging any requests except authentic V), at gauged
trajectory in Clinic.Cloth. All θ rows conditional still. Outside positivity
not claiming; weak Strict later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Lumos
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Hives Candles Barges Hoods Flairs Pomp Novas
open Icebergs Tropics Kelps Nimbuses
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical RightActions MatrixOrder
variable {G:Gauge} {c f : Side} {d:ℕ} {F:Labels.Frame G d} {S:StepData c f}

section Logic
variable {ι : Type} [Fintype ι] {H J A: Matrix ι ι ℝ}
lemma stock {u:Plate ι}(hs:J.PosSemidef)(h:H.PosSemidef)(hh:MapB ι J=u * (MapB ι H)*star u) :
   MeasurePreserving u (multivariateGaussian 0 H) (multivariateGaussian 0 J) :=by
   refine ⟨u.continuous.measurable,?_⟩; apply Measure.ext_of_charFun (E:=Sky ι); ext x
   let μ:=multivariateGaussian 0 H
   have he:charFun (Measure.map u μ) x=charFun μ ((star u) x):=by
     rw [charFun_apply,charFun_apply, integral_map u.continuous.aemeasurable (by fun_prop)]
     apply integral_congr_ae; filter_upwards with y; rw [show ⟪u y,x⟫=⟪y,(star u) x⟫ from (ContinuousLinearMap.adjoint_inner_right ..).symm]
   have hf : ⟪(star u) x,(MapB ι H) ((star u) x)⟫ = ⟪x,(MapB ι J) x⟫ := by rw [hh]; exact ContinuousLinearMap.adjoint_inner_left ..
   change charFun (Measure.map u μ) x=_; rw [he]; unfold μ; rw [charFun_multivariateGaussian h,charFun_multivariateGaussian hs]; rw [Matrix.inner_toEuclideanCLM,Matrix.inner_toEuclideanCLM] at hf; simp [hf]
private lemma litPlate (h:J.PosSemidef)(hf:H=A*J*A.transpose):H.PosSemidef:=by
   rw [hf, ← conjTranspose_eq_transpose_of_trivial] -- lemma
   exact h.mul_mul_conjTranspose_same A
private lemma compactMap (hf:H=A*J*A.transpose): MapB ι H=(MapB ι A)*(MapB ι J)*star (MapB ι A):=by rw [hf,map_mul,map_mul,←conjTranspose_eq_transpose_of_trivial]; rw [show A.conjTranspose=star A from rfl,Tropics.starMap]
end Logic

variable (P:Torch G S) (z:Site c→G.El) (V:Config G c)(hb:S.patch.Branches S.kernel G)
section
include hb
lemma blaze (h:(P.staged (Lattice.gauge z V)).PosSemidef): MeasurePreserving (P.vapor z) (multivariateGaussian 0 (P.staged V)) (multivariateGaussian 0 (P.staged (Lattice.gauge z V))) ∧ (P.staged V).PosSemidef :=by
   have hp:= (P.garment z V hb 1).1
   have hx:(P.staged V).PosSemidef:= litPlate (ι:=P.Index) (A:=(harp P.clan).paint (flatten (S:=S) z)⁻¹) h hp.bounce.character
   exact ⟨stock (ι:=P.Index) (u:=P.vapor z) h hx (compactMap (ι:=P.Index) (A:=(harp P.clan).paint (flatten (S:=S) z)) hp.character),hx⟩

lemma treasure {H:Hol G}(T : SectionData F)(ht:T.Sound H)(i:F.Index)(t ξ:ℝ)(h:(P.staged (Lattice.gauge z V)).PosSemidef) :
     P.quest (Lattice.gauge z V) t ξ T i=P.quest V t ξ T i:=by
   let W:=Lattice.gauge z V; have he:MeasurePreserving (P.vapor z) (multivariateGaussian 0 (P.staged V)) (multivariateGaussian 0 (P.staged W)):= (blaze P z V hb h).1
   unfold Torch.quest; rw [show Lattice.gauge z V=W from rfl, ← he.map_eq, integral_map he.measurable.aemeasurable]
   · apply integral_congr_ae; apply Eventually.of_forall; intro x; dsimp only [Torch.heap,W]; rw [P.vapor_lamps z x ξ,P.broad z V hb]; rw [(T.placed_invariant ht (0:Site f) (Place.copy F i)) _ _]
   have hp : Continuous (P.heap W t ξ T i):= by
     unfold Torch.heap; exact (P.lamps_fine ξ).smul (((SectionData.continuous_places T (Place.copy F i) (0:Site f)).comp (P.keel_fine W t ξ)).const_smul (t^(F.grades i).2)⁻¹)
   exact hp.aestronglyMeasurable
end
end YM.Planned.PrimaryIntegral295.Lumos
