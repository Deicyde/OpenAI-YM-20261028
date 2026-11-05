import YM.Extra.FREE_DETECTOR_ALGEBRA.LabelTurn
import YM.Extra.FREE_DETECTOR_ALGEBRA.WickPositive

set_option warningAsError false

/-!
# Exact all-spectator quotient of the free table

This is not a quotient of the interacting family! The same gauge,
reference convention and polynomial bases can and should be used to read
both when applying comparisons. `equationIdeal` means restriction to
Maxwell+Bianchi ordinary Taylor variables. The original `table_spin` &
projection machinery uses real signed-permutation symmetries only; here
O(4) transports also make sense already at this *free* quotient, with the
obvious tensor action. No analog inference for the dynamical hierarchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix

variable {G : Gauge} {d : ℕ}

lemma sector_bar {P : WickPol G} (hp : P ∈ shellSector G d) : barPol P ∈ shellSector G d := by
  obtain ⟨q,rfl⟩ := hp; exact ⟨Labels.realBar q,observe_bar _⟩
lemma sector_rot {P : WickPol G} (hp : P ∈ shellSector G d) (s : Ortho) : pullSol s P ∈ shellSector G d := by
  obtain ⟨q,rfl⟩ := hp; exact ⟨Labels.tensor s q,observe_rot _ _⟩

/-- One admissible point pair detects each nonzero on-shell sector vector. -/
lemma point_probe (P : shellSector G d) {x y : E4} (hx : x≠y) :
    let q : ProbeFamily G := ⟨1,(fun _ => d), (fun _ => ⟨pullSol (face (x-y)) (barPol P.val),sector_rot (sector_bar P.property) _⟩), couple x y, couple_ok hx⟩
    q.test d P = duplex x y P.val P.val := by
  intro q; rw [test_formula, duplex,aligned_apply]
  unfold q join
  congr 1; ext1 i; fin_cases i <;> rfl

theorem no_residual (G : Gauge) (d : ℕ) : residual G d = ⊥ := by
  refine le_antisymm (fun P hp => (Submodule.mem_bot ℂ).mpr ?_) bot_le
  apply Subtype.ext
  let e := basis timeAxis; let x := (0:E4)
  have hx : x ≠ e := by
    intro hh
    have : (0:ℝ)=e timeAxis := congr_arg (fun a : E4 => a timeAxis) hh
    simp [e] at this
  have he := point_probe P hx
  change P.val = 0
  by_contra h
  have hh := (reflected_positive hx P.val).mpr h
  dsimp only at he
  rw [← he] at hh
  have ht := congr_fun (show LinearMap.pi (fun i : ProbeFamily G => i.test d) P = 0 from hp)
  have hz (i : ProbeFamily G) : i.test d P = 0 := ht i
  rw [hz] at hh; exact lt_irrefl _ hh

variable (F : Labels.Frames G)

theorem free_null (d : ℕ) : (freeTable F).null d = LinearMap.ker (snap F d) := by
  ext1 p; rw [← projectionExact, no_residual, Submodule.mem_bot,LinearMap.mem_ker]



/-- Survive precisely as polynomial labels evaluated on the shell. -/
def exactField (d : ℕ) : (freeTable F).Field d ≃ₗ[ℂ] ↥(shellSector G d) :=
    (Submodule.quotEquivOfEq _ _ (free_null F d)).trans <| (snap F d).quotKerEquivOfSurjective (full F d)

lemma exact_project (d : ℕ) (p : (standard F).Ref d) : exactField F d ((freeTable F).project d p)=snap F d p := by
  unfold exactField; simp

def writes (d : ℕ) : (freeTable F).Field d →ₗ[ℂ] WickPol G :=
    (shellSector G d).subtype.comp (exactField F d).toLinearMap



lemma writes_inj (d : ℕ) : Injective (writes F d) := Subtype.val_injective.comp (exactField F d).injective

lemma writes_project (p : (standard F).Ref d) : writes F d ((freeTable F).project d p)=polish F d p :=
  congr_arg Subtype.val (exact_project F d p)

lemma writes_eval {n : ℕ} (x : Points n) (t : Fin n → (freeTable F).Tag) :
    (freeTable F).useAt (freeTable F) x t = moment G x (fun i => writes F _ (t i).snd) := by
  let T := freeTable F
  have he (i) : writes F (t i).1 (t i).snd = polish F (t i).1 (T.representative _ (t i).snd) := by rw [← writes_project,T.rep]
  simp_rw [he]; rfl

lemma writes_bar (h : (freeTable F).RealSpin) (p : (freeTable F).Field d) :
    writes F d ((freeTable F).conj h d p) = barPol (writes F d p) := by
  obtain ⟨p,rfl⟩ := (freeTable F).onto d p; rw [Table.conj_project, writes_project, writes_project,polish_conj]



lemma writes_unit (d : ℕ) : writes F d ((freeTable F).unit d) = 1 := by rw [Table.unit,writes_project,polish_unit]





/-- O(4) action for testing (not asserting continuity yet). -/
def ride (s : Ortho) (d : ℕ) : (freeTable F).Field d →ₗ[ℂ] (freeTable F).Field d :=
    (exactField F d).symm.toLinearMap.comp (((pullSol s).toLinearMap.comp (writes F d)).codRestrict _ fun P =>
      sector_rot ((exactField F d P).property) s)

theorem ride_at (p : (freeTable F).Field d) (s : Ortho) : writes F d (ride F s d p) = pullSol s (writes F d p) := by
  unfold writes ride; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; rfl

def rideO (s : Ortho) (d : ℕ) : (freeTable F).Field d ≃ₗ[ℂ] (freeTable F).Field d where
  toLinearMap := ride F s d
  invFun := ride F s⁻¹ d
  left_inv x := by apply writes_inj F d; change writes F d (ride F s⁻¹ d (ride F s d x)) = _; rw [ride_at,ride_at,← pull_mul,inv_mul_cancel,pull_one]
  right_inv x := by apply writes_inj F d; change writes F d (ride F s d (ride F s⁻¹ d x)) = _; rw [ride_at,ride_at,← pull_mul,mul_inv_cancel,pull_one]
end YM.Extra.FD
