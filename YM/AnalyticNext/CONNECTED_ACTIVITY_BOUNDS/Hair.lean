import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Dice
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Kettle
import YM.Push.RELAY_DIFFERENCE.SingleMajorant


/-!
# Charging new inherited addresses and supports

Bind on the PRESENTED label arrays, paths authoritative. Cost price
for powers of L consumed explicitly. Uses `AbsoluteSums.Paths` and
cross-compilation. `extentCost` may be paid post-L, but exponential
reserve must be purchased BEFORE L. Signed actual channel footprints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Calls
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Corona Animals
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- all in coarse footprints; raise η for Actual Support, not diameter

def extent (l : ℕ) (X : Support c) (x : ℝ) := halo (l*radiusB x) X

def fittings (S : StepData c f) (U : Support c) := univ.filter fun i : Bond f => home S i ∈ U

def priorE (S : StepData c f) (X : Support f) := (inspected X).image S.ratio.parent

def costE (S : StepData c f) (x : ℝ) (X : Support f) := extent 120 (priorE S X) x

def guards (Y : Mint T F A x) (X : Support c) (a : ArrayR G f) := robe Y (fittings S (extent 4 X x)) a



-- pay in both/spun shapes, can't take one center in parent-self-lifts
lemma forged {v : Type*} (s : Signed) (X : v → Support c) (k : ℕ) (w : v → ℝ)
    (a C : ℝ) (hw : ∀ i,0 ≤ w i) (hp : 0≤a) (h : Ac.Hit X k w a C) :
    Ac.Hit (fun i => (X i).image s.act) k w a C := by
  intro x
  obtain ⟨y,rfl⟩ := (show Surjective (s.act (R:=Per c)) from s.actEquiv.surjective) x
  apply budget_mono (h y)
  · intro i; split
    next => exact mul_nonneg (hw i) (Real.exp_pos _).le
    next => rfl
  intro i; split
  next he =>
    obtain ⟨z,hz,hy⟩ := mem_image.mp he
    have hf := s.act_injective (R:=Per c) hy
    rw [if_pos (hf ▸ hz)]; gcongr
    · exact hw i
    simpa only [show (s.act (R:=Per c))=Lattice.affine s (0:Site c) from funext fun i => (add_zero _).symm] using
      Push.RelayDifference.Single.cover_price s 0 (X i) k
  next he => exact (h y).1 i

lemma many {v u : Type*} [Fintype v] {w : v×u→ℝ} {a C : ℝ} {p : v×u → Support c} {B : ℕ}
    (h : ∀ j : v,Ac.Hit (fun i => p (j,i)) B (fun i => w (j,i)) a C) :
    Ac.Hit p B w a ((Fintype.card v:ℝ)*C) := by
  intro x
  let y := Labels.unitPrice p B w a x
  refine budget_of_sum (fun i => (h i.1 x).1 i.2) fun s => ?_
  change ∑ i∈s,y i ≤ _
  have ht j : ∑ i ∈ s with i.1=j, y i ≤ C := by
    let f : Finset (v × u) := s.filter fun i => i.1=j
    have he i (hi : i∈f) : (j,i.2)=i := by rw [← (mem_filter.mp hi).2]
    calc
      _ = ∑ i ∈ f.image Prod.snd,y (j,i) := by
        rw [Finset.sum_image]
        · exact Finset.sum_congr rfl fun i hi => by rw [he i hi]
        intro i hi b hb eq
        exact (he i hi).symm.trans ((congr_arg _ eq).trans (he b hb)) -- fix
      _ ≤ C := budget_sum (h j x) _
  calc
    _ = ∑ j, ∑ i∈s with i.1=j,y i := (Finset.sum_fiberwise_of_maps_to (fun i _ => mem_univ i.1) _).symm
    _ ≤ ∑ _j : v,C := Finset.sum_le_sum fun i _ => ht i
    _ = _ := by simp

-- include any fixed halos in post-L prices even for winding paths;
-- `K` parameter for the universal extent. Here k=0; always allows
-- common marked polynomial application first at full tested exponent.
lemma award (G : Gauge) (D : Patch) (P K : ℕ) (R a ε r s b : ℝ) (hε : 0<ε) (hr : 0 ≤ R) (hs : s<r) (_hb : 0≤ b) :
    ∀ᶠ x : ℝ in atTop, ∀ (v : ℕ), v≤K*(1+radiusB x) → ∀ C γ : ℝ, 0 ≤ C → 0 ≤ γ →
    C*γ ≤ R*amend G D x r → payment P v 0 ε C γ a b ≤ amend G D x s := by
  let M := payment P 0 0 ε 1 1 a b
  let N : ℝ := (2*K+1:ℝ)^4
  have hM : 0≤ M := by
    unfold M payment degreeIncome; have he : 0<1-Real.exp (-ε) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    positivity
  have hN : 0≤ N := by unfold N; positivity
  filter_upwards [instills G D (M*N*R) s r 4 (by positivity) hs] with x hx v hv C γ hC hγ he
  let L := tab G D x
  have h1 : 1 ≤ L := Delay.bill_ge ..
  have h2 : (radiusB x:ℝ)+1 ≤ L := by unfold L tab Delay.bill; linarith [sq_nonneg (Real.log (betaF G x D.L))]
  have hp : (ballCost v:ℝ) ≤ N*L^4 := by
    have hu : (v:ℝ) ≤ K*(1+(radiusB x:ℝ)) := by exact_mod_cast hv
    unfold N ballCost; rw [← mul_pow]; push_cast; gcongr; nlinarith only [hu,h2,h1,mul_le_mul_of_nonneg_left h2
      (show 0 ≤ (2:ℝ)*K by positivity)]
  have ht : payment P v 0 ε C γ a b = M*ballCost v*(C*γ) := by
    simp only [M,payment,degreeIncome,Footprint.spread,show ballCost 0=1 from rfl,Nat.cast_mul,Nat.cast_one]; ring
  calc
    _ ≤ (M*(N*L^4))*(R*amend G D x r) := ht.le.trans (mul_le_mul (mul_le_mul_of_nonneg_left hp hM) he
      (mul_nonneg hC hγ) (by positivity))
    _ = (M*N*R)*L^4*amend G D x r := by ring
    _ ≤ _ := hx
end YM.AnalyticNext.ConnectedActivity.Calls
