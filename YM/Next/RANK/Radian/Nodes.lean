import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import YM.Next.RANK.EntryWord
import YM.Next.RANK.Foils
import YM.Overlay.Supplier

/-!
# Momentum tiles on cover. grid frequency in inverse *sites*.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric  Lattice CellsInt  VectorFourier Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {A : Type*} {n : ℕ} {r h : ℝ} {c : Side} {x : Cover}
def addr (c : Side) (x : Cover) : E4:= ((c.val:ℝ)⁻¹) • mapZ x
def room (c : Side) (R : ℕ) := Finset.Icc (fun _ : Axis=>- ↑(R*c.val:ℕ) : Cover) (fun _ : Axis=>↑(R*c.val:ℕ))

def mark (c : Side) (u : E4) : Cover:= fun i=> ⌈u i / (c.val:ℝ)⁻¹⌉
def tileP (c : Side) (x : Cover): Set E4:= {u | mark c u=x}
lemma positive (c : Side) : 0<(c.val:ℝ)⁻¹:= by have hx:= c.property; positivity
lemma tiles (c : Side) (x : Cover) :
    MeasurableSet (tileP c x) ∧ volume.real (tileP c x)=((c.val:ℝ)⁻¹)^4:= by
  let h:=(c.val:ℝ)⁻¹
  let p i:=Extraction.tile h (x i)
  have hp:0<h:=positive c
  let L : E4 → Axis →ℝ:=WithLp.ofLp
  have hL : MeasurePreserving L:= PiLp.volume_preserving_ofLp Axis
  have he:tileP c x=L ⁻¹' Set.pi Set.univ p:=by
    ext z; constructor
    · intro h i _; exact (Extraction.tile_bounds hp _ _).mp (congr_fun (show mark c z=x from h) i)
    exact fun h=> funext fun i=> (Extraction.tile_bounds hp _ _).2 (h i (Set.mem_univ i))
  have hb i : volume (p i)= ENNReal.ofReal h:= by unfold p Extraction.tile; rw [Real.volume_Ioc]; congr 1;ring
  have H: MeasurableSet (Set.pi Set.univ p):=MeasurableSet.pi Set.countable_univ fun _ _=>measurableSet_Ioc
  rw [he]; refine ⟨hL.measurable H,?_⟩; unfold Measure.real; rw [hL.measure_preimage H.nullMeasurableSet]; change (Measure.pi (fun _:Axis=> (volume:Measure ℝ)) _).toReal=_
  rw [Measure.pi_pi]; simp_rw [hb];simp [Axis,h]

lemma rock (u : E4) : dist (addr c (mark c u)) u ≤ 4*(c.val:ℝ)⁻¹:= by
  let L:= (c.val:ℝ)⁻¹
  have H i: |addr c (mark c u) i-u i| ≤ L:= by
    have hx:= (Extraction.tile_bounds (positive c) _ _).mp (show ⌈u i / _⌉ = mark c u i from rfl)
    obtain ⟨h,hp⟩:=hx; rw [abs_le]; change -L≤ L*↑(mark c u i)-_ ∧ L* ↑(mark c u i)-_≤L; constructor <;> unfold L <;> linarith [positive c]
  rw [dist_eq_norm]; have hp:=positive c
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity),EuclideanSpace.real_norm_sq_eq]; refine le_trans (Finset.sum_le_sum (g:=fun _ =>L^2) (fun i _=> by
    rw [sq_le_sq,abs_of_nonneg (show 0≤L from hp.le)];exact H i)) ?_; simp only [sum_const, nsmul_eq_mul,card_univ,Fintype.card_fin];unfold L; push_cast;nlinarith

-- square records in weighted K. choose 4 for compact lift.
lemma addressBW (x : Cover) (R : ℕ) (h : ‖addr c x‖≤R) : x∈room c R := by
  have he i := abs_real_inner_le_norm (basis i) (addr c x);simp only [basis_inner,basis_norm,one_mul] at he
  have hv i : -↑(R*c.val:ℕ) ≤ x i ∧ x i ≤ (R*c.val:ℕ):= by
    obtain ⟨hu,hb⟩:= abs_le.mp ((he i).trans h)
    have hh : addr c x i=(x i:ℝ)/ c.val:= div_eq_inv_mul ..|>.symm
    rw [hh] at hu hb; have hp:0<(c.val:ℝ):= by exact_mod_cast c.property
    rw [le_div_iff₀ hp] at hu; rw [div_le_iff₀ hp] at hb
    rw [neg_mul] at hu
    exact_mod_cast And.intro hu hb
  exact mem_Icc.mpr ⟨fun i=>(hv i).1,fun i=>(hv i).2⟩

-- sums of Tiling via sigma, exact. point sample even if σ singular.
def scansP (c : Side) (f : E4 →ℂ) (R : ℕ) := ((c.val:ℝ)⁻¹)^4 • ∑ i∈ room c R,f (addr c i)

def eventP (R : ℕ) (F : E4→ℂ) := ∀ x:E4,(R:ℝ) < ‖x‖ → F x=0
lemma grid_born (c : Side) (f : E4→ℂ) (R : ℕ) (h : eventP R f) :
    let X:= fun x=>f (addr c (mark c x))
    Integrable X∧ (∫ x,X x)=scansP c f R:= by
  intro X; let A i:= (tileP c i).indicator fun _=> f (addr c i)
  let W:= room c R
  have he x:X x=∑ i∈W,A i x:= by
    by_cases ht : mark c x∈W
    · rw [sum_eq_single (mark c x)]
      · exact (indicator_of_mem (show x∈tileP c _ from rfl) _).symm
      · intro j _ hz; exact indicator_of_notMem (fun (h : x∈tileP c j)=>hz (Eq.symm h)) _
      simp [ht]
    rw [Finset.sum_eq_zero (fun i hi=> indicator_of_notMem (fun (h : x∈tileP c i) => ht (by rwa [h])) _)]
    exact h _ (lt_of_not_ge fun hz=>ht (addressBW _ R hz))
  have hp : ∀ i∈W,Integrable (A i):= by
    intro i H; obtain ⟨hm,hx⟩:= tiles c i; apply (integrable_indicator_iff hm).2; apply integrableOn_const; intro he; have h:(0:ℝ)<volume.real (tileP c i):= hx ▸ pow_pos (positive c) _; rw [Measure.real,he] at h; simp at h
    simp
  constructor
  · rw [show X=_ from funext he]; exact integrable_finsetSum W hp
  rw [show X =_ from funext he, integral_finsetSum W hp]; unfold scansP; rw [Finset.smul_sum]; apply sum_congr rfl; intro i hi; unfold A; rw [integral_indicator (tiles ..).1,setIntegral_const,(tiles ..).2]
end YM.Next.Rank.Radian
