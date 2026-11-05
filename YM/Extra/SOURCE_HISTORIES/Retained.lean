import YM.Extra.SOURCE_HISTORIES.Tide
import YM.Next.FOUNDATIONS.Primary

/-!
# Retain every fixed m chart on one common extraction

Uses EXTRACTION ordered refinement machinery. Works as augmentation step;
e.g. if a RawLimits already chosen, **preserve** them. (A consumer example
also with CenterPort below.) Keep both inverses. Not extracting terminal maps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Charts
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion Extraction Next.Extract
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G) (h : C.Makes)

abbrev Linear (d : ℕ) := C.label d →L[ℂ] C.label d
abbrev Pair (d : ℕ) := Linear C d × Linear C d

def pose {d : ℕ} (X : Exchange C d) : Pair C d := ((X:Linear C d),(X.symm:Linear C d))

def glass (i : ℕ × ℕ) (N p : ℕ) : Pair C i.1 := pose C (window C h i.1 i.2 N p)

def Scroll (f : Extraction.Order) (x : ∀ d , ℕ → ℕ → Exchange C d) (y : ∀ d , ℕ → Exchange C d) :=
  Keeps f (fun _ _ => True) (glass C h) (fun i p => pose C (x i.1 i.2 p)) (fun i => pose C (y i.1 i.2))





variable (f : Extraction.Order)











variable {x : ∀ d , ℕ → ℕ → Exchange C d} {y : ∀ d , ℕ → Exchange C d}

namespace Scroll

lemma mesh (hS : Scroll C h f x y) (d m p) : Tendsto (fun j => pose C (window C h d m (f.mesh j) p)) atTop
    (𝓝 (pose C (x d m p))) := hS.rows (d,m) p trivial

lemma per (hS : Scroll C h f x y) (d m) : Tendsto (fun k => pose C (x d m (f.per k))) atTop
    (𝓝 (pose C (y d m))) := hS.outer (d,m)

lemma units (S : Scroll C h f x y) (d m) (hr : C.ref d ≤ m) :
    (∀ p, x d m p (C.refUnit d) = unitVec (C.labels.level d) C.path m) ∧
      y d m (C.refUnit d)=unitVec (C.labels.level d) C.path m := by
  let v := C.refUnit d
  let u := unitVec (C.labels.level d) C.path m
  have ht p : x d m p v=u := by
    have he := Dash.arcing (mesh C h f S d m p).fst_nhds (tendsto_const_nhds (x:=v))
    refine tendsto_nhds_unique (show Tendsto (fun j => window C h d m (f.mesh j) p v) atTop (𝓝 (x d m p v)) from he) ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [f.mesh.cofinal.eventually_ge_atTop m] with j hj
    exact (chart_unit C h d (f.mesh j) p m hr hj).symm
  refine ⟨ht,tendsto_nhds_unique
    (show Tendsto (fun k => x d m (f.per k) v) atTop (𝓝 (y d m v)) from
      Dash.arcing (per C h f S d m).fst_nhds (tendsto_const_nhds (x:=v))) ?_⟩
  simp only [ht]; exact tendsto_const_nhds

/-- True growth bounds survive to limit charts. Per *fixed m*.
Identifies the chart cocycle point evaluations (also composing and using
symm, by continuous evaluation). -/
lemma prices (S : Scroll C h f x y) (d m : ℕ) :
    let F := C.labels.level d
    let price (W : Exchange C d) := ∀ v, F.coeffSize (W v) ≤ ingress C m * F.coeffSize v ∧
      F.coeffSize (W.symm v) ≤ outgress C d m * F.coeffSize v
    (∀ p, price (x d m p)) ∧ price (y d m) := by
  intro F price
  have hp {a : ℕ → Exchange C d} {b : Exchange C d} (ht : Tendsto (fun j => pose C (a j)) atTop (𝓝 (pose C b)))
      (he : ∀ j, price (a j)) : price b := by
    intro v
    have hx : Tendsto (fun k => a k v) atTop (𝓝 (b v)) := Dash.arcing ht.fst_nhds tendsto_const_nhds
    have hy : Tendsto (fun k => (a k).symm v) atTop (𝓝 (b.symm v)) := Dash.arcing ht.snd_nhds tendsto_const_nhds
    exact ⟨le_of_tendsto' ((Size.continuous F).continuousAt.tendsto.comp hx) (fun j => (he j v).1),
      le_of_tendsto' ((Size.continuous F).continuousAt.tendsto.comp hy) (fun j => (he j v).2)⟩
  have he p : price (x d m p) := hp (mesh C h f S ..) (fun j v =>
    ⟨incoming C h d _ _ _ v,outer_charge C h d _ _ _ v⟩)
  exact ⟨he,hp (per C h f S ..) (fun j => he _)⟩
end Scroll
end YM.Extra.Histories.Charts
