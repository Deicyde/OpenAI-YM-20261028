import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Desk
import YM.Work.F05.Reindex

/-!
# Expand base tails and path coefficients *at the native U,V* for a spot

No dropping true winding trajectories/candidate mask locations/offsets.
Only pre-expansion summability of these factors; no post-scale price for
the output polymer. Exponents and nonlocal scalar letter handling separate.
See .
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian
open Next.SectorChange.Rows YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open Next.Fluctuations.Sector
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S}

namespace Spot
section sums
variable {ι κ : Type} [Fintype ι]

/-- Finite placements of summable individual dictionaries. -/
lemma addresses {f : ι×κ→ℝ} {v : ι → ℝ} (h : ∀ i, HasSum (fun x => f (i,x)) (v i)) :
    HasSum f (∑ i,v i) := by
  have ht : Summable (fun x : ι×κ => ‖f x‖) := by
    refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
      ⟨fun i => ((h i).summable).norm,(hasSum_fintype _).summable⟩ -- implicit function types
  have he := ht.of_norm.hasSum.prod_fiberwise h
  rw [← he.unique (hasSum_fintype _)]
  exact ht.of_norm.hasSum
end sums

section paths
variable {F : PathData G} {c : Clip} {σ n Λ : ℝ}
variable {U : Config G f} {a : Cell f} {P : BudgetPoint} (K B : ℕ)

private lemma suppress (h : F.Bounds c σ n Λ) (i : Cell f) (U : Config G f) :
    Summable fun j => ‖shortenTerm F K B U i j‖ := by
  refine ((F.ell_dominated h i).absolute U).of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro j; unfold shortenTerm; split
  · exact le_rfl
  rw [norm_zero]; exact norm_nonneg _

private lemma pairs (f : ℕ → G.Color) (h : Summable fun i => ‖f i‖) :
    HasSum (fun p : ℕ×ℕ => inner ℝ (f p.1) (f p.2)) (‖∑' i,f i‖^2) := by
  let A (p : ℕ×ℕ) := inner ℝ (f p.1) (f p.2)
  have hx := h.mul_of_nonneg h (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have ha : Summable A := (.of_nonneg_of_le (fun i => norm_nonneg (A i))
    (fun i => abs_real_inner_le_norm (f i.1) (f i.2)) hx : Summable (fun i => ‖A i‖)) |>.of_norm
  let v := ∑' j,f j
  have he (i) : HasSum (fun j => A (i,j)) (inner ℝ (f i) v) := h.of_norm.hasSum.mapL (innerSL ℝ (f i))
  have hl : HasSum (fun i => inner ℝ (f i) v) (inner ℝ v v) := by
    rw [show (fun i => inner ℝ (f i) v)=fun i => inner ℝ v (f i) from funext (fun i => real_inner_comm _ _)]
    exact h.of_norm.hasSum.mapL (innerSL ℝ v)
  rw [real_inner_self_eq_norm_sq] at hl
  rw [← show (∑' p, A p)=‖∑' i,f i‖^2 from ((ha.hasSum.prod_fiberwise he).unique hl)]
  exact ha.hasSum

/-- One addressed path pair of the FULL minus the SHORT base.
A pair even cancelling in-place retains the paths. -/
def labelPath (F : PathData G) (c : Clip) (U : Config G f) (a : Cell f) (P : BudgetPoint) (p : ℕ × ℕ) : ℝ :=
    if PathData.kept c P.threshold a.1 U then (inner ℝ (F.ellTerms a p.1 U) (F.ellTerms a p.2 U)-
      inner ℝ (shortenTerm F K B U a p.1) (shortenTerm F K B U a p.2))/2 else 0

lemma labeled (h : F.Bounds c σ n Λ) (U : Config G f) (a : Cell f) (P : BudgetPoint) :
    HasSum (labelPath K B F c U a P) (cuff F c P B K U a) := by
  by_cases hh : PathData.kept c P.threshold a.1 U
  · unfold cuff PathData.baseTerm crown trunk
    rw [if_pos hh, if_pos hh,add_comm (PathData.clipped ..),add_sub_add_right_eq_sub]
    convert! ((pairs _ ((F.ell_dominated h a).absolute U)).sub (pairs _ (suppress K B h a U))).div_const 2 using 1
    · ext; simp [labelPath,hh]
    rw [sub_div]; rfl
  unfold cuff crown trunk PathData.baseTerm; rw [if_neg hh,if_neg hh,add_zero,zero_add,sub_self]
  unfold labelPath; simp_rw [if_neg hh]; exact hasSum_zero
end paths

section index
variable (u : Spot d)

abbrev Incoming (_f : Side) := ((Cell _f)×ℕ×ℕ) ⊕ Site _f × (ℕ ⊕ ℕ ⊕ ℕ)

private def atom (U : Config G f) (y : Site f × (ℕ ⊕ ℕ ⊕ ℕ)) := match y.2 with
    | .inl i => d.input.beta * (d.input.path.cubic i).placed d.input.p U y.1
    | .inr (.inl i) => d.input.beta * (d.input.path.quartic i).placed d.input.p U y.1
    | .inr (.inr i) => (d.input.path.loop i).placed d.input.p U y.1

/-- Before multiplication by orientation prices. -/
def old (q : Incoming f) : Config G f → ℝ := fun U => match q with
    | .inl (a,i) => d.input.beta * labelPath (till d.betaHat) 1 d.input.path d.input.clip U a d.input.p i
    | .inr i => atom (d:=d) U i

lemma old_sum (d : Desk G S) (h : d.Valid) (U : Config G f) :
    HasSum (fun i => old (d:=d) i U) (reduced d.input (till d.betaHat) U) := by
  let Q := d.input.beta
  let c (j : Cell f) := cuff d.input.path d.input.clip d.input.p 1 (till d.betaHat) U j
  let V := fun y => PathData.atomSeries d.input.path.cubic d.input.p U y
  let W := fun y => PathData.atomSeries d.input.path.quartic d.input.p U y
  let L := fun y => PathData.atomSeries d.input.path.loop d.input.p U y
  unfold reduced
  change HasSum _ (Q*((∑ j,c j)+∑ y,(V y+W y))+∑ y,L y)
  rw [show Q*((∑ j,c j)+∑ y,(V y+W y))+∑ y,L y=(∑ j,Q*c j)+ (∑ y,(Q*V y+(Q*W y+L y))) by
    simp_rw [Finset.sum_add_distrib]; simp_rw [← Finset.mul_sum]; ring]
  obtain ⟨σ,n,E,F,u,h⟩ := h.lawful
  apply HasSum.sum
  · apply addresses; intro i
    exact (labeled _ _ h.paths U i _).mul_left _
  apply addresses; intro i
  apply HasSum.sum
  · exact ((PathData.atom_dominated _ _ i h.paths.width h.paths.three).summable U).hasSum.mul_left _
  exact HasSum.sum (((PathData.atom_dominated _ _ i h.paths.width h.paths.four).summable U).hasSum.mul_left _)
    ((PathData.atom_dominated _ _ i h.paths.width h.paths.two).summable U).hasSum

abbrev BasePosts (c f : Side) := (Signed × Incoming f) ⊕ (Signed × Cell c × ℕ×ℕ)

def basePost (V : Config G c) (p : u.Visual) : BasePosts c f → ℝ
  | .inl i => (Fintype.card Signed:ℝ)⁻¹ * (-old (d:=d) i.2 (pull i.1 0 (u.hard V p)))
  | .inr (s,i,j) => d.input.beta*((Fintype.card Signed:ℝ)⁻¹ *
      labelPath (till d.betaHat) S.patch.L.val d.tube.down d.tube.low (pull s 0 V) i d.out j)

lemma base_sum (h : d.Valid) (V : Config G c) (p : u.Visual) : HasSum (u.basePost V p)
    (-averaged (fun s => reduced d.input (till d.betaHat) (pull s 0 (u.hard V p))) + coarseTail d.tube d.betaHat d.out V d.input.beta) := by
  let R := d.input
  let U := u.hard V p
  let a := fun s => reduced d.input (till d.betaHat) (pull s 0 U)
  let b := fun (s : Signed) (i : Cell c) => cuff d.tube.down d.tube.low d.out S.patch.L.val (till d.betaHat) (pull s 0 V) i
  let y := (Fintype.card Signed:ℝ)⁻¹
  obtain ⟨T,hT⟩ := h.funds; obtain ⟨n,m,-,hn⟩ := hT.feeds
  rw [← hT.low] at hn
  apply HasSum.sum
  · change HasSum _ (-(y*∑ s,a s))
    rw [← mul_neg, ← Finset.sum_neg_distrib,Finset.mul_sum]; refine addresses (fun i => ?_)
    exact ((old_sum d h (pull i 0 U)).neg.mul_left y)
  change HasSum _ (R.beta*(y*∑ s, ∑ i,b s i)); rw [Finset.mul_sum,Finset.mul_sum]; refine addresses ?_
  intro s; rw [Finset.mul_sum,Finset.mul_sum]; apply addresses; intro i
  exact ((labeled _ _ hn (pull s 0 V) i d.out).mul_left y).mul_left _
end index
end Spot
end YM.AnalyticBridge.LocalGaussian
