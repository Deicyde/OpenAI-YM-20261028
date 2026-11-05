import YM.Planned.PRIMARY_INTEGRAL_295.LocalLog

/-!
# One stencil and its gauge-jet log chart

Germs at the true identity on the stencil, including *both* degrees.
Linear joint input includes gauge parameters at sites **together**, not a
separate choice of gauge for each link. This is not a torus entire chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Filter Lattice Labels Source Source.Drops RG Wilson WardBin MeasureTheory Next.Foundations
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d n : ℕ} {S : Finset Cover}

abbrev Spot (S : Finset Cover) := {p : S × Axis // (p.1.val + step p.2) ∈ S}

def first (p : Spot S) : S := p.val.1
def beam (p : Spot S) : Axis := p.val.2
def placeEdge (p : Spot S) : Edge Cover := ((first p).val,beam p)
def last (p : Spot S) : S := ⟨(first p).val+step (beam p),p.property⟩

abbrev Dev (S : Finset Cover) (G : Gauge) := Spot S → G.Color
abbrev EntryCode (S : Finset Cover) (G : Gauge) (d : ℕ) := (S → G.Color) × Snap G d

def ping (S : Finset Cover) : Potential G →ₗ[ℝ] Dev S G where
  toFun f p := f (seat (first p).val) (beam p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def singleReader (G : Gauge) (d : ℕ) (p : Spot S) : EntryCode S G d →L[ℝ] EdgeRead G d :=
    LinearMap.toContinuousLinearMap {
      toFun X := (X.1 (first p),X.1 (first p)-X.1 (last p),road (seat (first p).val) (beam p) X.2)
      map_add' X Y := by simp; abel
      map_smul' r X := by simp [smul_sub] }

def opened (S : Finset Cover) (X : EntryCode S G d) : Dev S G := fun p => logo (singleReader G d p X)

lemma opened_smooth (S : Finset Cover) (G : Gauge) (d : ℕ) : ContDiffAt ℝ ω (opened S (G:=G) (d:=d)) 0 := by
  apply contDiffAt_pi.mpr; intro i
  have he := logo_smooth G d
  exact (show ContDiffAt ℝ ω logo (singleReader G d i 0) by rw [map_zero]; exact he).comp _ (singleReader G d i).contDiff.contDiffAt

@[simp] lemma opened_zero (S : Finset Cover) : opened S (0 : EntryCode S G d) = 0 := by funext _; simp [opened]

def expandCode (S : Finset Cover) (w : E4 → G.Color) (A : Snap G d) : EntryCode S G d :=
    (fun p => w (seat p.val), A)

set_option maxHeartbeats 500000 in
lemma opened_coeffs (n : ℕ) (X : Fin n → EntryCode S G d) (i : Spot S) :
    iteratedFDeriv ℝ n (opened S) 0 X i = iteratedFDeriv ℝ n logo (0:EdgeRead G d) (fun j => singleReader G d i (X j)) := by
  let P : Dev S G →L[ℝ] G.Color := ContinuousLinearMap.proj i
  calc
    _ = iteratedFDeriv ℝ n (P ∘ opened S) 0 X := by
      rw [P.iteratedFDeriv_comp_left (opened_smooth S G d) le_top]; rfl
    _ = _ := by
      change iteratedFDeriv ℝ n (logo ∘ singleReader G d i) 0 X=_
      have hu := jets_linear (E:=EdgeRead G d) (X:=EntryCode S G d) (singleReader G d i)
        ((logo_smooth G d).of_le (show (n : WithTop ℕ∞) ≤ ω from le_top))
      exact DFunLike.congr_fun hu X

lemma opened_launch (w : E4 → G.Color) (A : Snap G d) :
    fderiv ℝ (opened S) 0 (expandCode S w A)=ping S (jump w + sampled A) := by
  ext1 i
  have hv := opened_coeffs 1 (fun _ => expandCode S w A) i
  rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,echoing] at hv
  rw [hv]; change steady (road (seat (first i).val) (beam i) A) + (w (seat (first i).val)-w (seat (last i).val))=_
  rw [add_comm, last]; simp only [seat_add,seat_step]; rfl

lemma opened_audits (S : Finset Cover) (w : Fin n → E4 → G.Color) (X : Fin n → Snap G d) (a : Fin n → ℕ)
    (ha : ∀ i,0 < a i) (hw : ∀ i,w i∈rangeLt G.Color (a i+1)) (hX : ∀ i,throughSlot (X i) (a i)) :
    ∃ f : Potential G, f∈ rangeLt (Axis→G.Color) (∑ i,a i) ∧ ping S f = iteratedFDeriv ℝ n (opened S) 0 (fun i => expandCode S (w i) (X i)) := by
  let V (e : Axis) := logo_cost d w X a e ha hw hX
  refine ⟨_, vector_band _ V, ?_⟩; ext1 i
  rw [opened_coeffs]; change iteratedFDeriv ℝ n logo _ _ = _
  congr! 1; ext1 k
  change (_,w k _-w k (seat (first i).val + basis (beam i)),_) = (_,w k _-w k (seat (last i).val),_)
  simp [last,expandCode]

/-- The local stencil cylinder with arbitrary filler. -/
def pore (v : Dev S G) : CoverConfig G := fun p =>
    if h : p.1∈S ∧ p.1+step p.2∈S then G.lieExp (v ⟨(⟨p.1,h.1⟩,p.2),h.2⟩) else 1
lemma pore_site (v : Dev S G) (p : Spot S) : pore v (placeEdge p) = G.lieExp (v p) :=
    dif_pos (show _ ∧ _ from ⟨(first p).2,p.property⟩)
@[simp] lemma pore_zero : pore (0 : Dev S G)=1 := by funext x; unfold pore; split <;> simp

def pureQuest (H : Hol G) (X : Snap G d) := H.links d (expand d X) 1

def gaugeQuest (v : S → G.Color) (p : Cover) := if h:p ∈ S then G.lieExp (v ⟨p,h⟩) else 1

lemma port_acts (H : Hol G) (Z : EntryCode S G d) (p : Spot S) : peak (singleReader G d p Z) =
    gauge (gaugeQuest Z.1) (pureQuest H Z.2) (placeEdge p) := by
  unfold peak Lattice.gauge pureQuest gaugeQuest
  change G.lieExp (Z.1 (first p)) * flight (road _ _ _) _ * (G.lieExp (Z.1 (first p) - (Z.1 (first p) - Z.1 (last p))))⁻¹ = _
  rw [sub_sub_cancel, show flight (road (seat (first p).val) (beam p) Z.2) 1 = H.links d (expand d Z.2) 1 (placeEdge p) from congr_fun (flight_test H (placeEdge p) Z.2) 1]
  rw [dif_pos (show (placeEdge p).1 ∈ S from (first p).property),dif_pos (show (placeEdge p).1+step (placeEdge p).2∈S from p.property)]; rfl

lemma opened_valid (H : Hol G) : ∀ᶠ X : EntryCode S G d in 𝓝 0,
    Agrees S (pore (opened S X)) (gauge (gaugeQuest X.1) (pureQuest H X.2)) := by
  have he (i : Spot S) : ∀ᶠ v : EntryCode S G d in 𝓝 0,
      pore (opened S v) (placeEdge i)=peak (singleReader G d i v) := by
    have hx : Tendsto (peak (G:=G) (d:=d)) (𝓝 0) (𝓝 1) := by
      rw [← peak_root G d]; exact
        ((G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr (peak_smooth G d).continuousAt).tendsto
    have ht : Tendsto (singleReader G d i) (𝓝 0) (𝓝 0) := by
      rw [← map_zero (singleReader G d i)]; exact (singleReader G d i).continuous.tendsto _
    filter_upwards [ht.eventually (hx.eventually G.plog_right)] with x hx
    rw [pore_site]; exact hx
  filter_upwards [eventually_all.mpr he] with v h
  intro p h1 h2
  let i : Spot S := ⟨(⟨p.1,h1⟩, p.2),h2⟩
  exact (h i).trans (port_acts H v i)

/-- Unmasked read through the joint gauge chart (as germs). -/
lemma lit {Y : Type*} {f : CoverConfig G → Y} (S : Finset Cover)
    (he : LocalOn S f) (hh : GaugeInvariant f) (H : Hol G) (d : ℕ) :
    (fun X : EntryCode S G d => f (pore (opened S X))) =ᶠ[𝓝 0] fun X => f (pureQuest H X.2) :=
    (opened_valid H).mono (fun v h => (he _ _ h).trans (hh (gaugeQuest v.1) _))

end YM.Planned.PrimaryIntegral295.Place
