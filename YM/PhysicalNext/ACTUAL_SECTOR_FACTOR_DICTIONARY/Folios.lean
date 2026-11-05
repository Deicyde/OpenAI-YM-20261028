import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alabaster
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Chains
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Windows

/-! Physical chain supports at the actual protocol; even invalid
jumps (retaining every endpoint) still have legal locations and, in
particular, measurable local dictionary extensions even where the
true logdet/force decomposition is not licensed. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Notify
open Function Filter Set Matrix MeasureTheory Lattice RG Wilson Precision Pressure Tree
open Next.SectorChange Gaussian Schur FreeResolvent
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Typeset
open Numerals
section watches
variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι] [DecidableEq ι] (W : ι→Set ι)
    {A : X → Square ι} (h : Watched A)
include h

lemma season {f : X → ℝ} (he : Measurable f) : Watched fun x=> pie W (A x) (f x) := by
  apply Watched.panel
  exact Watched.plus h (fun i j=>he.mul (measurable_const (a:=(1:Square ι) i j)))
lemma rents (z : X → ℝ) (hz : Measurable z) : Watched fun x => defect W (A x) (z x) :=
  Watched.minus (Watched.times (Watched.plus h (fun i j=>hz.mul (measurable_const (a:=(1:Square ι) i j)))) (season W h hz)) Watched.one
lemma supplements : Watched fun x=> excess W (A x) := Watched.minus (Watched.times h (Watched.weather W h)) Watched.one

lemma rod {S : X→Square ι} (hs : Watched S) {n : ℕ} (i j : ι) (l : Fin n→ι) :
    Measurable fun x => road (A x) (S x) i j l := by
  induction n generalizing A i with
  | zero=> exact h i j
  | succ n ih=> exact (h _ _).mul (ih hs _ _)

lemma first (i : ι) : Measurable fun x=> letterBase W (A x) i := by
  let f (p : X × ℝ) := attenuation p.2-pie W (A p.1) p.2 i i
  have hm : Measurable f := by
    have ht : Watched (fun (y : X × ℝ) => A y.1) := fun i j=> (h i j).comp measurable_fst
    have hi : Measurable (fun p : X × ℝ => attenuation p.2) := by unfold attenuation; fun_prop
    exact hi.sub (season W ht measurable_snd i i)
  let μ := Measure.restrict volume (Ioi (0:ℝ))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable
lemma article (i : Letter ι 1) : Measurable fun x=> page W (A x) i := by
  let f (p : X×ℝ) := scroll W (A p.1) i.2.1 i.2.2 p.2
  have ht : Watched (fun (y : X × ℝ) => A y.1) := fun i j=> (h i j).comp measurable_fst
  have hh : Measurable f := (rod (season W ht measurable_snd) (Watched.negative (rents W ht _ measurable_snd)) _ _ i.2.2).neg
  let μ := Measure.restrict volume (Ioi (0:ℝ))
  exact (hh.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable
lemma printing (i : Letter ι 0) : Measurable fun x=> errata W (A x) i := by
  have ht:= Watched.negative (supplements W h)
  exact ((rod ht ht _ _ i.2.2).neg).div_const _
lemma lead {C : X → Square ι} (he : Watched C) (i j : ι) (u : Sequence ι) : Measurable fun x=> forward (A x) (C x) i j u :=
  rod h (Watched.minus Watched.one (Watched.times he h)) ..
end watches
end Typeset

section support
open Wires
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {k k' : S.Choices} (T : Tube G S) {x : ℝ}

def walkLens (S : StepData c f) (B : ℕ) (i j : Bond f) (l : Sequence (Bond f)) :=
  pocket (portOf S) 20 B i j l.2

lemma tint (i j : Full G f) {n : ℕ} (l : Fin n → Full G f) (B : ℕ) :
    pocket (Physical.place S) 20 B i j l = pocket (portOf S) 20 B i.1 j.1 fun q=> (l q).1 := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=> rw [pocket,pocket,ih]; rfl

theorem forward_law (hA : Map.Aperture S T x) (i j : Full G f)
    (s : Sequence (Full G f)) {X : Support c} (h : pocket (Physical.place S) 20 (radiusB x) i j s.2 ⊆ X)
    (hp : Physical.Reads X A A' F F' V V' k k') :
    forward (beam T k V x A F) (cloudX T x k V A F) i j s =
      forward (beam T k' V' x A' F') (cloudX T x k' V' A' F') i j s := by
  let D:=beam T k V x A F; let D':=beam T k' V' x A' F'
  let W:=Physical.windows S x (G:=G)
  let C:=clouded W D; let C':=clouded W D'
  let p:=Physical.place S (G:=G); let B:=radiusB x
  have stab (k:S.Choices) (V:Config G c) A F : (beam T k V x A F).IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j; unfold beam; simp only [Matrix.of_apply,and_comm,mul_comm,Matrix.one_apply,eq_comm]
  have he (k : S.Choices) (V : Config G c) A F : 1-cloudX T x k V A F*beam T k V x A F=
        -(excess W (beam T k V x A F)).transpose := by
    unfold excess; rw [transpose_sub,transpose_mul,(stab k V A F).eq,
      (Matrix.isHermitian_iff_isSymm.mp (self_cloud ..)).eq,Matrix.transpose_one]; abel
  unfold forward; rw [he,he]
  have hR := positioned T hA hp
  by_cases hJ : jumps (nearby p B) i j s.2
  · refine pocket_through p X s.2 h hJ ?_ ?_
    · exact fun i j hi _=> hR.kernel i ((Shields.full p i 20 B hi).shrink (by change 14*B ≤ 20*B; omega)) j
    intro i j hi hj
    have ht : Shields X (p j) (17*B) := (Shields.full p i 20 B hi).shift (by unfold nearby at hj; omega)
    exact congr_arg Neg.neg (hR.correction j ht i)
  have hz (k : S.Choices) (V : Config G c) (A F) :
      road (beam T k V x A F) (-(excess W (beam T k V x A F)).transpose) i j s.2=0 := by
    have hE := beam_aperture T hA k V A F
    refine road_drop _ _ ((range_limit T k V _ A F hA).trans (by have h := hA.spans; omega)) ?_ i j _ hJ
    intro i j hh
    have hp : ¬ nearby p B j i := by unfold nearby at *; rw [separation_comm]; exact hh
    rw [Matrix.neg_apply,Matrix.transpose_apply,hE.spare j i hp,neg_zero]
  rw [hz,hz]

lemma strand_law (hA : Map.Aperture S T x) (i j : Full G f)
    (s : Sequence (Bond f)) {X : Support c} (h : walkLens S (radiusB x) i.1 j.1 s ⊆ X)
    (hp : Physical.Reads X A A' F F' V V' k k') :
    strand (beam T k V x A F) (cloudX T x k V A F) i j s=
      strand (beam T k' V' x A' F') (cloudX T x k' V' A' F') i j s := by
  unfold strand; apply Finset.sum_congr rfl; intro l hl
  apply forward_law T hA _ _ _ _ hp
  dsimp only; rw [tint ..]; exact h

lemma essay_law (hA : Map.Aperture S T x) (i : Letter (Bond f) 1) {X : Support c}
    (h : inventory (portOf S) 20 (radiusB x) i ⊆ X) (hp : Physical.Reads X A A' F F' V V' k k') :
    let W := Physical.windows S x
    Paint.braid (page W (beam T k V x A F)) i=Paint.braid (page W (beam T k' V' x A' F')) i := by
  intro W; unfold Paint.braid; apply Finset.sum_congr rfl; intro j hj
  let he := Paint.hue i j
  have hf : inventory (Physical.place S) 20 (radiusB x) he ⊆ X := by unfold inventory; rw [tint]; exact h
  unfold AnalyticBridge.RelativeLogdet.page W
  have hl := (positioned T hA hp).manuscript (by change 17≤20; omega) he hf; unfold he at hl; rw [hl]

lemma errata_law (hA : Map.Aperture S T x) (i : Letter (Bond f) 0) {X : Support c}
    (h : inventory (portOf S) 20 (radiusB x) i ⊆ X) (hp : Physical.Reads X A A' F F' V V' k k') :
    let W := Physical.windows S x
    Paint.braid (errata W (beam T k V x A F)) i=Paint.braid (errata W (beam T k' V' x A' F')) i := by
  intro W; unfold Paint.braid; apply Finset.sum_congr rfl; intro j hj
  let r := Paint.hue i j
  exact (positioned T hA hp).notices (by change 17≤20; omega) r (show inventory (Physical.place S) 20 (radiusB x) r⊆X by
    unfold inventory; rw [tint]; exact h)
end support
end YM.PhysicalNext.Dictionary.Notify
