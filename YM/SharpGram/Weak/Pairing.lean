import YM.SharpGram.Matrix.Stability
import YM.SharpGram.Weak.Reading
/-!
# Positive actual matrix on the normalized inlet basis

This uses our tilt to the reflected free detector, always including the time
adjoint of the second **label**. Not claiming the tilted physical test is
symmetric because of reflection, and never use a Cauchy-Schwarz inequality
on it! We use the real part. Positive lower and finite upper are uniform for
all sufficiently large k, in the corresponding measuring basis. Get them from
component convergence on all offshell pairs using the full true conditional
comparison in Reading and op norm residual estimates for the *projected*
matrix. No assertion of positivity on that bigger family. Also price its real
pairings with arbitrary off-shell input via station, even those whose free
limit vanishes. No assertion that these prices stay bounded without the
measuring basis transformations described!
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank PhysicalNext.RankCovariance
open Org Spec Next.Rank.Station Further.CorrectedLift Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
section pulls
variable {A B C : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [NormedSpace ℝ A] [NormedSpace ℝ B] [NormedSpace ℝ C] [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]

def pullBoth (P : A →ₗ[ℝ] C) (Q : B →ₗ[ℝ] C) (T : RealForm C C) : RealForm A B := toForm
  { toFun := fun x => (T (P x)).toLinearMap.comp Q
    map_add' := fun a b => LinearMap.ext fun z => by simp
    map_smul' := fun a b => LinearMap.ext fun z => by simp }
lemma pullBoth_read (P : A →ₗ[ℝ] C) (Q : B →ₗ[ℝ] C) (T : RealForm C C) (x : A) (y : B) :
    pullBoth P Q T x y = T (P x) (Q y) := rfl
end pulls

namespace Weak.Portfolio
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(U:Final C f S)
variable {D:ℕ}{u:Filter (ℕ×ℕ)}{H:C.Makes} (X : Portfolio C H D u)
local notation "F"=> standard C
local notation "σ"=> U.room.kernel.spin
local notation "θ"=> Maxwell.Free.spin_free C.labels

-- convenience instance (local scope ONLY)
local instance (V : Gauge) (s : Register V) (K : Table s) (d : ℕ) : FiniteDimensional ℝ (K.Field d) := Module.Finite.trans ℂ _
open Push.FiniteDetection.Free
-- Via complete-real label choice of the free quotient; grows in actual labels.
def draw (S:Table C.book)(k : ℕ)(d : Fin (D+1)) : (F).Field d →ₗ[ℂ] S.Field d :=
  (X.visible S k d).comp (ladder C d).toLinearMap

def enlarged (k : ℕ) (d : Fin (D+1)) : RealForm (C.label d) (C.label d) :=
    pullBoth ((X.visible S k d).restrictScalars ℝ) ((X.visible S k d).restrictScalars ℝ)
      (glass S σ d (X.detector k))

def model (C' : Family G) (d : ℕ) : RealForm ((standard C').Field d) ((standard C').Field d) :=
    glass (standard C') (Maxwell.Free.spin_free C'.labels) d Push.FiniteDetection.Free.detectors

-- reusable perturbation at measuring coordinates
-- omit C in ClockForm before building
def modelFull (C' : Family G) (d : ℕ) : RealForm (C'.label d) (C'.label d) :=
    pullBoth (((standard C').project d).restrictScalars ℝ) (((standard C').project d).restrictScalars ℝ) (model C' d)

def measured (k : ℕ)(d : Fin (D+1)) : RealForm ((standard C).Field d) ((standard C).Field d) :=
    pullBoth ((X.draw S k d).restrictScalars ℝ) ((X.draw S k d).restrictScalars ℝ) (glass S σ d (X.detector k))

lemma pay (k : ℕ) (d : Fin (D+1)) (x y : (F).Field d) :
    measured U X k d x y = enlarged U X k d (ladder C d x) (ladder C d y) := rfl
lemma pay0 (d : ℕ)(x y : (F).Field d) : model C d x y=modelFull C d (ladder C d x) (ladder C d y) := by
  change model C d x y = model C d ((standard C).project _ (ladder C _ x)) ((standard C).project _ (ladder C _ y))
  rw [ladder_reads,ladder_reads]
lemma measured_unit k (d : Fin (D+1)) (x : (F).Field d) : measured U X k d x x =
    (OPE.Levy.pair d S (X.detector k) (X.draw S k d x) (S.adj σ d timeAxis (X.draw S k d x))).re := rfl -- d cast inference?

lemma freely (d : ℕ) : ∃ δ : ℝ, 0 < δ ∧ coercive (model C d) δ :=
    margin _ (fun x hx => OPE.Levy.free_positive (C:=C) d x hx)
variable (hG:G.Simple) {W r T0} (T : OPE.TableTickets C W r T0) [u.NeBot] (hf : u ≤ f.fuse)
include hG T hf
set_option maxRecDepth 4000 in
lemma readAll (d : Fin (D+1))(x y : C.label d) :
  Tendsto (fun k => enlarged U X k d x y) atTop (𝓝 (modelFull C d x y)) := by
  let v := (![x, C.book.adj d timeAxis y] : Fin 2 → C.label d)
  have h := Complex.continuous_re.continuousAt.tendsto.comp (X.twoC U hG T hf (t:=fun _=>d) v) -- arg order? dot X
  have hr(k): (![X.visible S k d x, X.visible S k d (C.book.adj d timeAxis y)] : Fin 2 → S.Field d) =
      fun j => X.visible S k d (v j) := by ext1 i; fin_cases i <;> rfl
  have hr' : (![(F).project d x,(F).adj θ d timeAxis ((F).project d y)] : Fin 2 → (F).Field d)=fun j=> (F).project d (v j) := by
    ext1 i; fin_cases i <;> rfl
  have hx : modelFull C d x y=((F).classMoment (F) (fun j : Fin 2=>d.val) detectors (fun j=>(F).project d (v j))).re := by
    change glass (F) θ d detectors ((F).project d x) ((F).project d y)=_
    rw [glass_reads, hr']
  rw [hx]
  refine h.congr' (X.onLevel.mono fun k hk=> ?_)
  change _ = glass S σ d (X.detector k) (X.visible S k d x) (X.visible S k d y)
  rw [glass_reads, show S.adj σ d timeAxis (X.visible S k d y)= _ from (lendsAdj hk.2.2.1 U hf hk.2.2.2 d y).symm]
  exact congr_arg Complex.re (DFunLike.congr_arg _ (hr k).symm)

lemma detectorAll (d : Fin (D+1)) : Tendsto (fun k => enlarged U X k d) atTop (𝓝 (modelFull C d)) :=
    formsLimits _ _ (readAll U X hG T hf d)
set_option maxHeartbeats 600000 in
lemma detectorActual (d : Fin (D+1)) : Tendsto (fun k => measured U X k d) atTop (𝓝 (model C d)) :=
    formsLimits (V:=(standard C).Field d) (X:=(standard C).Field d) _ _ (fun x y => by
      simp_rw [pay U X]
      rw [pay0 d x y]
      exact readAll U X hG T hf d (ladder C d x) (ladder C d y))

/-- Real-part coercive **only** on the independent moving basis (space of
free fields of grade ≤ d, its quotient semantics), not on enlarged. Includes
all k beyond a threshold, and supplies surjectivity needed to interpret these
prices invariantly on the physical field space. -/
lemma certified (d : Fin (D+1)) (δ : ℝ) (he : 0<δ) (hc : coercive (model C d) δ) :
    ∀ᶠ k : ℕ in atTop,
      ‖measured U X k d - model C d‖ ≤ δ/2 ∧
      ‖enlarged U X k d - modelFull C d‖ ≤ 1 ∧
      coercive (measured U X k d) (δ/2) ∧ Bijective (X.draw S k d) := by
  have hx := SharpGram.stayNear (detectorActual U X hG T hf d) (half_pos he)
  have hw := SharpGram.stayNear (detectorAll U X hG T hf d) zero_lt_one
  filter_upwards [hx,hw] with k hk ha
  have ht : coercive (measured U X k d) (δ/2) := absorb _ _ δ _ hc (by simpa only [sub_half] using hk)
  have hF : Injective (X.draw S k d) := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)
    by_contra! hy
    have hu := ht x
    change δ / 2 * ‖x‖^2 ≤ glass S σ d (X.detector k) (X.draw S k d x) (X.draw S k d x) at hu
    rw [hx,map_zero] at hu
    exact (mul_pos (half_pos he) (pow_pos (norm_pos_iff.mpr hy) 2)).not_ge hu
  obtain ⟨H,hH⟩ := U.phase.transport.comparator
  obtain ⟨e,-,-⟩:=hH d
  exact ⟨hk,ha,ht,hF, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e.symm.finrank_eq).1 hF⟩

omit T hG
lemma drawUnit (d : Fin (D+1)) : ∀ᶠ k in atTop,X.draw S k d ((F).unit d) = S.unit d := by
  filter_upwards [X.onLevel] with k hk
  change S.project _ (X.field k d (ladder C d _)) = _
  rw [ladder_unit,constant hk.2.2.1 hf hk.2.2.2]; rfl
end Weak.Portfolio
end YM.SharpGram
