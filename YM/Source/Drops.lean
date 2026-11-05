import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.PCalc.Loop
import YM.Pressure.Gauge
import YM.Source.Construction





/-!
# Finite radial records and an alternative certificate for a REAL lattice section

Using recovery of low radial jets from a stencil of ALL placed square
readouts (finite subchoice; need proof). Projection.Sound is still the
literal current definition, NOT using C^1 rank instead of Jrad. See G## WPs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Source.Drops
open Lattice Wilson RG Labels InnerProductSpace MeasureTheory Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {d : ℕ}

abbrev Snap (G : Gauge) (d : ℕ) := (i : Fin (d-1)) → Taylor G i.val

instance : NormedSpace ℝ (Snap G d) := Pi.normedSpace
instance : FiniteDimensional ℝ (Snap G d) := by unfold Snap; infer_instance

def trunk (d : ℕ) (J : Jet G) : Snap G d := fun i => J i.val

def expand (d : ℕ) (p : Snap G d) : Jet G := fun i => if h : i<d-1 then p ⟨i,h⟩ else 0

@[simp] lemma trunks (p : Snap G d) : trunk d (expand d p)=p := by funext i; rcases i with ⟨i,h⟩; simp [trunk,expand,h]
@[simp] lemma expand_zero : expand d (0:Snap G d)=0 := by funext i; simp [expand]

lemma racts (u : Label G d) (p : Jet G) : read (expand d (trunk d p)) u.val=read p u.val := by
  classical
  -- monomial sum
  have hz : ∀ i ∈ u.val.support, height (G:=G) i ≤ d :=
    fun i hi => (MvPolynomial.mem_restrictSupport_iff ℂ).mp (show _ ∈ limited G d from u.property.1) hi
  have hy (i : Key G →₀ ℕ) (k : Key G) : i k * generation k ≤ height i := by
    by_cases h : i k=0
    · simp [h]
    unfold height; rw [Finsupp.weight_apply]; exact Finset.single_le_sum (f:=fun v => i v • generation v) (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr h)
  have hk (i : Key G →₀ ℕ) (hi : i∈u.val.support) (j) (hj : j∈i.support) : Labels.coord (expand d (trunk d p)) j=Labels.coord p j := by
    have hh : generation j ≤ d := (show generation j ≤ i j * generation j from le_mul_of_one_le_left (Nat.zero_le _) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj))).trans ((hy ..).trans (hz _ hi))
    have he : j.1<d-1 := by unfold generation at hh; omega
    simp [Labels.coord,he,expand,trunk]
  unfold Labels.read; rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Finset.sum_congr rfl; intro i hi
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [hk _ hi _ hj]

lemma truncate (J : Jet G) : potential d (expand d (trunk d J))=potential d J := by
  funext i x; apply Finset.sum_congr rfl; intro j hj; simp only [expand,trunk,dif_pos (Finset.mem_range.mp hj)]

lemma scales (H : Hol G) (p : Jet G) (v : ℝ) :
    H.links d p v=H.links d (expand d (trunk d (scaleJet p v))) 1 := by
  have he (i : Edge Cover) : partConnection d (expand d (trunk d (scaleJet p v))) 1 i=partConnection d p v i := by
    funext x; simp only [partConnection,one_smul,potential, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro j hj
    rw [Taylor.value_hom,smul_smul,show v*v^(j+1)=v^(j+2) by ring]
    simp only [expand,trunk,dif_pos (Finset.mem_range.mp hj)]
    simp [scaleJet,Taylor.value,Tensor.diagonal]; try rfl
  funext i
  exact congr_fun ((H.solves d p v i).unique (show SolvesLink _ _ from by rw [← he i]; exact (H.solves ..))) _

def takes (H : Hol G) (d : ℕ) (i : Slot) (J : Snap G d) := i.eval (H.links d (expand d J) 1)

theorem takes_zero (H : Hol G) (d : ℕ) (i : Slot) : takes H d i 0=0 := by
  have hz : scaleJet (0:Jet G) 0=0 := by funext j; simp [scaleJet]
  have ht : H.links d (0:Jet G) 1=1 := by
    have hh := H.flat d (0:Jet G)
    rw [scales H, hz,show trunk d (0:Jet G)=0 from rfl,expand_zero] at hh; exact hh
  unfold takes Slot.eval; rw [expand_zero, ht,show faceValue (1:CoverConfig G) (i.offset,i.plaq)=1 from ?_, G.curvature_unit, map_zero]
  unfold faceValue; apply Pressure.one

def Blurb (H : Hol G) (d : ℕ) (i : Slot) := fderiv ℝ (takes H d i) 0

def Cast (u : G.El) (p : Snap G d) : Snap G d := fun i => Taylor.paint u (p i)

-- Contains analytic at, gauge, and linearized cochain at lift. Possible costs post LUT.
def access (J : Snap G d) (p : Edge Cover) := ∫ s : ℝ in 0..1, partConnection d (expand d J) 1 p s
def glow (A : Snap G d) (i : Slot) := Exterior.linkSum (access A) i.offset (square i.plaq.val.1 i.plaq.val.2)

structure Peg (H : Hol G) (d : ℕ) : Prop where
  shot : ∀ v : Slot, AnalyticAt ℝ (takes H d v) 0
  observes : ∀ v : Slot, ∀ y : G.El,∀ A : Snap G d,takes H d v (Cast y A)=G.adjoint y (takes H d v A)
  initial : ∀ J v, Blurb H d v J = glow J v

def lifts (H : Hol G) (d : ℕ) (s : ℕ) (B : Fin s → Slot) :=
    ∀ A : Snap G d, (∀ i, Blurb H d (B i) A=0) → A=0

abbrev GaugePanel (G : Gauge) (s : ℕ) := Fin s → G.Color

def bring (H : Hol G) (d : ℕ) {s} (B : Fin s → Slot) (A : Snap G d) : GaugePanel G s := fun i => takes H d (B i) A

def rotates (u : G.El) {s} (x : GaugePanel G s) : GaugePanel G s := fun i => G.adjoint u (x i)

/-! Critical germ WIPE. `Sleeps` from already funded linear equivariant left projection. -/

def Vision (H : Hol G) (d : ℕ) {s} (B : Fin s → Slot) (F : GaugePanel G s → Snap G d) :=
    AnalyticAt ℝ F 0 ∧ F 0=0 ∧ (∀ᶠ i in 𝓝 0,F (bring H d B i)=i) ∧ ∀ (u : G.El), ∀ᶠ i in 𝓝 0,F (rotates u i)=Cast u (F i)

lemma rotates_cont {u : G.El} {s} : Continuous (rotates (s:=s) u) := by
  apply continuous_pi; intro i; exact (G.adjoint u).continuous_of_finiteDimensional.comp (continuous_apply i)
lemma Cast_cont {u : G.El} {d : ℕ} : Continuous (Cast (d:=d) u) := by
  apply continuous_pi; intro i; exact (Taylor.paint u).continuous_of_finiteDimensional.comp (continuous_apply i)

private lemma hammered {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : X → Y) (C : Y →L[ℝ] X) (h : AnalyticAt ℝ f 0) (hh : C.comp (fderiv ℝ f 0)=ContinuousLinearMap.id _ _) (hz : f 0=0) (p : ι → X → X) (q : ι → Y → Y)
    (hx : ∀ i,Tendsto (p i) (𝓝 0) (𝓝 0)) (hy : ∀ i,Tendsto (q i) (𝓝 0) (𝓝 0)) (HP : ∀ i x,f (p i x)=q i (f x)) (HQ : ∀ i x,C (q i x)=p i (C x)) : ∃ F : Y → X,
      AnalyticAt ℝ F 0 ∧ F 0=0 ∧ (∀ᶠ i in 𝓝 0,F (f i)=i) ∧ ∀ u,∀ᶠ i in 𝓝 0,F (q u i)=p u (F i) := by
  let g := C ∘ f
  have hg : ContDiffAt ℝ ω g 0 := ((C.analyticAt _).comp h).contDiffAt
  have ha : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ X).toContinuousLinearMap 0 := by
    rw [show (ContinuousLinearEquiv.refl ℝ X).toContinuousLinearMap= C.comp (fderiv ℝ f 0) from hh.symm]
    exact C.hasFDerivAt.comp 0 h.differentiableAt.hasFDerivAt
  let t := hg.toOpenPartialHomeomorph _ ha (by simp)
  have hw : ContDiffAt ℝ ω t.symm (g 0) := hg.to_localInverse ha (show ω≠(0:WithTop ℕ∞) by simp)
  have hT : g 0=0:=by simp [g,hz]
  have hs : (0:X)∈t.source:=ContDiffAt.mem_toOpenPartialHomeomorph_source ..
  have ht : t.symm (0:X)=0 := by nth_rw 1 [← hT]; exact t.left_inv hs
  rw [hT] at hw
  let F := t.symm ∘ C
  have hi : F 0=0 := by simp [F,ht]
  have hq := (show AnalyticAt ℝ (t.symm) (C 0) from by rw [map_zero]; exact hw.analyticAt) |>.comp (C.analyticAt _)
  refine ⟨F,hq,hi,?_,fun i => ?_⟩
  · filter_upwards [t.open_source.mem_nhds hs] with i hh; exact t.left_inv hh
  have he : 0∈t.target:= hT ▸ t.map_source hs
  have hl : Tendsto F (𝓝 0) (𝓝 0) := by simpa only [hi] using (show ContinuousAt F 0 from hq.continuousAt).tendsto
  have hu := t.open_source.mem_nhds hs
  have hH := t.open_target.mem_nhds he
  have hw : Tendsto C (𝓝 0) (𝓝 0) := by simpa only [map_zero] using C.continuous.tendsto 0
  filter_upwards [(hl.comp (hy i)).eventually hu,((hx i).comp hl).eventually hu,hw.eventually hH,(hw.comp (hy i)).eventually hH] with x ht hs he hb
  apply t.injOn ht hs
  change t (t.symm (C (q i x))) = g (p i (F x))
  rw [t.right_inv (show C (q i x) ∈ t.target from hb), show g (p i (F x))=p i (t (t.symm (C x))) from by
    change C (f _)=p i (C (f (F x)))
    rw [HP,HQ], t.right_inv he]
  exact HQ _ _

set_option maxHeartbeats 300000 in
lemma insight {H : Hol G} {s d} {B : Fin s → Slot} (he : AnalyticAt ℝ (bring H d B) 0) (C : GaugePanel G s →ₗ[ℝ] Snap G d)
    (h : ∀ x,C (fderiv ℝ (bring H d B) 0 x)=x)
    (hv : ∀ u x,C (rotates u x)=Cast u (C x)) (hp : Peg H d) : ∃ F,Vision H d B F := by
  letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
  refine hammered (bring H d B) C.toContinuousLinearMap he (ContinuousLinearMap.ext h) ?_ (Cast (d:=d) (G:=G)) (fun u => rotates u (s:=s)) ?_ ?_ (fun i x => funext fun _ => hp.observes _ _ _) hv
  · exact funext fun i => takes_zero H d (B i)
  · intro u; simpa only [show Cast (d:=d) u 0=0 from funext fun i => map_zero _] using! Cast_cont (u:=u) (d:=d)|>.tendsto 0
  intro u; simpa only [show rotates (s:=s) u 0=0 from funext fun i => map_zero _] using! rotates_cont (u:=u) (s:=s)|>.tendsto 0
end YM.Source.Drops
