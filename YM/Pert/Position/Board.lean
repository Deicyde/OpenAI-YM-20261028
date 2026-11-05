import YM.Pert.Position.Implicit
/-! A square finite-position-test board. Before coupling inversion. Tests and derivative projections act on real numbers; the profiles themselves can be complex. Frame increments are constrained by conjugation, signed lattice rotations, the filtration and the unit. No automatic nonsingularity. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 220000
noncomputable section
namespace YM.Pert.Position
open Filter Function Set Orb Lattice Labels Maxwell RawLabels Full Table MeasureTheory Analysis Ward Extra.FD
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (F : Frames G) {d e : ℕ}
abbrev E (F : Frames G) (d : ℕ) := (Maxwell.freeTable F).Field d
abbrev operator (d : ℕ) := E F d →L[ℝ] E F d

def stair (e d : ℕ) : Set (E F d) := {p | ∃ q : Labels.Label G d, enroll F d q=p ∧ q.val ∈ Labels.localFields G e}
lemma upward (h : e≤d) (W : DiffPlan (freeTable F)) (hW : W.Inclusions (freeTable F)) : stair F e d = LinearMap.range (W.rise h) := by
  ext p; constructor
  · rintro ⟨q,rfl,hp⟩
    refine ⟨enroll F e ⟨_,hp⟩,UVNext.FreeStress.rise_embed F W hW h (⟨_,hp⟩:Label G e)⟩
  rintro ⟨q,rfl⟩
  refine ⟨Labels.raiseLabel G h (physicalLabel F e q),?_,(physicalLabel F e q).property⟩
  change UVNext.FreeStress.embed F d _ = _
  rw [show _ = _ from Eq.symm (UVNext.FreeStress.rise_embed F W hW h (physicalLabel F e q)), show UVNext.FreeStress.embed F e = RawLabels.enroll F e from rfl,physical_round]

def lower (e d : ℕ) : Submodule ℂ (E F d) := LinearMap.range (enroll F d ∘ₗ (localFields G e ⊓ localFields G d).inclusion (?_ : localFields G e ⊓ localFields G d ≤ localFields G d)) where finally
  exact inf_le_right
lemma stairs_eq (e d : ℕ) : stair F e d = (lower F e d : Set _) := by
  ext x; constructor
  · rintro ⟨q,rfl,h⟩; exact ⟨⟨q.val,h,q.property⟩,rfl⟩
  rintro ⟨q,rfl⟩; exact ⟨⟨q.val,q.property.2⟩,rfl,q.property.1⟩

def buffers (d : ℕ) : Submodule ℝ (operator F d) where
  carrier := {B | B ((freeTable F).unit d) = 0 ∧ (∀ e<d, ∀ p∈lower F e d, B p∈lower F e d) ∧
    (∀ p, (freeTable F).conj (table_spin F) d (B p) = B ((freeTable F).conj (table_spin F) d p)) ∧
    (∀ (s : Signed) p, rideO F s.ortho d (B p) = B (rideO F s.ortho d p)) ∧ (∀ p, B (Complex.I • p) = Complex.I • B p)}
  zero_mem' := by simp
  add_mem' {x y} h e := by
    exact ⟨by simp [h.1,e.1],fun j hj p hp => (lower F j d).add_mem (h.2.1 j hj p hp) (e.2.1 j hj p hp),fun p=> by simp [h.2.2.1,e.2.2.1],fun s p=> by simp [h.2.2.2.1,e.2.2.2.1],fun p=> by simp [h.2.2.2.2,e.2.2.2.2,smul_add]⟩
  smul_mem' r x h := by
    have he p : (r • x) p = (↑r:ℂ) • x p := RCLike.real_smul_eq_coe_smul (K:=ℂ) r _
    exact ⟨by rw [he,h.1,smul_zero],fun j hj p hp => he p ▸ (lower F j d).smul_mem _ (h.2.1 j hj p hp),fun p=> by rw [he,he,map_smulₛₗ]; simp [h.2.2.1], fun s p=> by rw [he,he,map_smul,h.2.2.2.1],fun p=> by rw [he,he,h.2.2.2.2,smul_comm]⟩
-- Above self-reference is not needed; replace before build.
abbrev Buffer (d : ℕ) := ↥(buffers F d)
instance : NormedSpace ℝ (Buffer F d)  := by exact @Submodule.normedSpace ℝ ℝ _ _ _ (operator F d) _ _ _ _ (buffers F d)
instance (d): CompleteSpace (Buffer F d) := (buffers F d |>.closed_of_finiteDimensional |>.completeSpace_coe)
def motor {d} (b : Buffer F d) : operator F d := 1+b.val
lemma invertible_tail (d : ℕ) : ∀ᶠ b : Buffer F d in 𝓝 0, IsUnit (motor F b) := by
  have hc : Continuous (motor F (d:=d)) := continuous_const.add continuous_subtype_val
  refine (hc.continuousAt (x:=0)).tendsto.eventually (show ∀ᶠ q : operator F d in 𝓝 _, IsUnit q from ?_)
  rw [show motor F 0= (1:operator F d) by unfold motor; change 1+0=1; exact add_zero _]
  exact (Units.isOpen (R:=operator F d)).mem_nhds (x:=(1:operator F d)) (show (1:operator F d) ∈ {q : operator F d | IsUnit q} from isUnit_one)


local notation "X" => ℂ -- only coefficients
structure Conditions {G : Gauge} (F : Frames G) (d count : Nat) where
  slots : ℕ
  arity : Fin slots → ℕ
  columns (i : Fin slots) : Fin (arity i) → E F d
  profiles (i : Fin slots) : Points (arity i) → X
  chisels : (Fin slots → ℝ) →ₗ[ℝ] (Fin count→ℝ)

abbrev ChartIx (d) := Fin (Module.finrank ℂ (E F d))
def baring (d) := Module.finBasis ℂ (E F d)
variable {F} {count : ℕ} (Q : Conditions F d count)
abbrev inklet (i : Fin Q.slots) := Fin (Q.arity i) → ChartIx F d
abbrev Ledger := ∀ i : Fin Q.slots, inklet Q i → ℂ

def decode (v : Ledger Q) {i : Fin Q.slots} (p : Fin (Q.arity i) → E F d) :=
   ∑ k : inklet Q i, (∏ j, (baring F d).coord (k j) (p j)) * v i k
def chart (w : Ledger Q × Buffer F d) : Fin count→ℝ := Q.chisels (fun i => Complex.re (decode Q w.1 (fun j => motor F w.2 (Q.columns i j))))
private lemma pay {i : Fin Q.slots}(p : Fin (Q.arity i) → E F d) (M : MultilinearMap ℂ (fun _ : Fin (Q.arity i) => E F d) ℂ) (v : Ledger Q) (hv : ∀ k, v i k = M (fun j => baring F d (k j))) :
    decode Q v p = M p := by
  have ht (j : Fin (Q.arity i)) := (baring F d).sum_equivFun (p j)
  conv_rhs => rw [←funext ht]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ,decode]
  refine Finset.sum_congr rfl fun k _ => ?_; rw [M.map_smul_univ,hv k]; rfl

private def wheelL (p : E F d) : Buffer F d →ₗ[ℝ] E F d where
  toFun b := b.val p
  map_add' x y := by simp
  map_smul' r x := by simp
lemma motor_diff (p : E F d) : ContDiff ℝ ω (fun b => motor F b p) := by
  change ContDiff ℝ ω (fun b : Buffer F d => p + wheelL p b)
  have hb := ContinuousLinearMap.contDiff (E:=Buffer F d) (F:=E F d) (𝕜:=ℝ) (n:=ω) ((wheelL p).toContinuousLinearMap)
  exact ContDiff.add contDiff_const hb
private lemma chart_component (i : Fin Q.slots) : ContDiff ℝ ω (fun z : Ledger Q × Buffer F d => Complex.re (decode Q z.1 (fun j=> motor F z.2 (Q.columns i j)))) := by
  apply Complex.reCLM.contDiff.comp (f:=fun z : Ledger Q × Buffer F d => decode Q z.1 (fun j=> motor F z.2 (Q.columns i j)))
  let R (k : inklet Q i) := LinearMap.comp (LinearMap.proj (R:=ℝ) (φ:=fun _=>ℂ) k) (LinearMap.proj (R:=ℝ) (φ:=fun i : Fin Q.slots => inklet Q i → ℂ) i)
  have eval_h (k : inklet Q i) : ContDiff ℝ ω (fun x : Ledger Q × Buffer F d => x.1 i k) := (R k).toContinuousLinearMap.contDiff.comp (f:=Prod.fst) contDiff_fst
  unfold decode; refine ContDiff.sum (fun k _ => ContDiff.mul (contDiff_prod (fun j _ => (_root_.ContDiff.comp (g:=fun v => ((baring F d).coord (k j) |>.restrictScalars ℝ |>.toContinuousLinearMap) v) ?_ ?_))) (eval_h k))
  · fun_prop
  apply (motor_diff _).comp (f:=Prod.snd) contDiff_snd
lemma chart_diff : ContDiff ℝ ω (chart Q) := by
  let f : Ledger Q × Buffer F d → Fin Q.slots → ℝ := fun z i => Complex.re (decode Q z.1 (fun j=> motor F z.2 (Q.columns i j)))
  have hf : ContDiff ℝ ω f := contDiff_pi.mpr (chart_component Q)
  exact Q.chisels.toContinuousLinearMap.contDiff.comp (g:=fun u => Q.chisels u) hf


def finite (Q : Conditions F d count) (L : Side) (m : ℕ) (k : ℕ) (i : Fin Q.slots) (z : inklet Q i) := PowerSeries.coeff k (Full.profile d (Q.arity i) F L m (Q.profiles i) (fun j => baring F d (z j)))
lemma value_finite L m k (b : Buffer F d) : chart Q (finite Q L m k, b) = Q.chisels (fun i => Complex.re (PowerSeries.coeff k (Full.profile d (Q.arity i) F L m (Q.profiles i) (fun j => motor F b (Q.columns i j))))) :=
  congrArg Q.chisels (funext fun i=> congrArg Complex.re (pay Q _ ((PowerSeries.coeff k).compMultilinearMap (Full.profile d (Q.arity i) F L m (Q.profiles i))) _ (fun _ => rfl)))

/-- Tested free hierarchy (not the actual continuum used as a perturbative coefficient). -/
def white (i : Fin Q.slots) (z : inklet Q i) : X :=
  ∫ x : Points (Q.arity i), Q.profiles i x * disc (fun j => (Sigma.mk d (baring F d (z j)) : (freeTable F).Tag)) x
/-- Exactly the nondegeneracy needed at leading order for the square position equations in the prescribed numbering. -/
def square : Prop := (fderiv ℝ (chart Q) (white Q, (0 : Buffer F d)) ∘L ContinuousLinearMap.inr ℝ _ _).IsInvertible
lemma squareSolve (h : square Q) : ∃ φ, Reports (chart Q) (white Q) 0 φ := by apply Reports.of_square (chart_diff Q).contDiffAt; exact h
end YM.Pert.Position
