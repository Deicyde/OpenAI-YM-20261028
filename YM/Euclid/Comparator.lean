import YM.Euclid.Differential
import YM.Maxwell.Reorder

/-!
# The actual free filtered comparator

Intrinsic exterior-null *after* Bianchi and Maxwell built into the kernel.
It is not assumed no further null or any nonzero-rank theorem. Uses a
modelling of Wick labels by invariant polynomials before restriction, as .
The same coordinate basis with real form will be used in short distance comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Function Set Filter
open Wick Labels
open scoped ContDiff Topology BigOperators

variable {G : Gauge}

def standard (F : Frames G) : Register G := ⟨F,fun _ => 1,fun _ => zero_lt_one⟩

def freeTable (F : Frames G) : Table (standard F) where
  value d x := (correlation G x d).compLinearMap fun _ => (F.level _).coords.symm.toLinearMap

variable (F : Frames G)

/-- Full-arity read using invariant polynomial lift, before any physical quotient. -/
lemma decodes {n} (p : Fin n → (standard F).Token) (x : Points n) :
    (freeTable F).read x p = moment G x (fun i => observable G _ ((F.level _).coords.symm (p i).2)) := rfl

lemma table_sym : (freeTable F).Symmetric where
  same := by
    intro n r x hx v; exact (Wick.exchangeSites r hx (fun i => observable G _ ((F.level _).coords.symm (v i).2))).symm

lemma table_regular : (freeTable F).Basic where
  __ := table_sym F
  trivial f x := by
    rw [decodes]
    rw [show (fun i => observable G _ ((F.level _).coords.symm (f i).2)) = fun _ => 1 from Subsingleton.elim ..]
    exact constants _
  unital := by
    intro n x hx d v
    rw [decodes,decodes]
    -- freeze reader functions
    let A (p : (standard F).Token) := observable G _ ((F.level p.1).coords.symm p.2)
    change moment G x (A ∘ Fin.cons (α := fun _ => (standard F).Token) ((standard F).one d) v) = moment G _ (A ∘ v)
    let B := Fin.cons (α := fun _ : Fin (n+1) => (standard F).Token) ((standard F).one d) v
    have ht : A ((standard F).one d) = 1 := by
      change observable G d ((F.level _).coords.symm ((standard F).scalar d)) = 1
      rw [show (standard F).scalar d = (F.level d).coords (Labels.unit G d) by simp [standard, Register.scalar, Register.coord]; exact one_smul _ _,
        (F.level d).coords.symm_apply_apply]
      exact map_one reduceEq
    rw [show (A ∘ B) = Fin.cons (α := fun _ => WickPol G) 1 (A ∘ v) by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [B, ht]]
    rw [← show Points.cons (x 0) (Points.tail x) = x by ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons,Points.tail]]
    rw [← adjoin]
    · congr 1
    exact Points.tail_in hx

theorem table_smooth : (freeTable F).Smooth where
  on_conf d v := smooth d fun i => (F.level _).coords.symm (v i)

def shellSector (G : Gauge) (d : ℕ) : Submodule ℂ (WickPol G) := LinearMap.range (observable G d)

/-- What remains null in actual on-shell sector. -/
structure ProbeFamily (G : Gauge) where
  n : ℕ
  d : Fin n → ℕ
  exterior (i : Fin n) : shellSector G (d i)
  x : Points (n+1)
  clear : x ∈ conf _

def ProbeFamily.test (v : ProbeFamily G) (d : ℕ) : shellSector G d →ₗ[ℂ] ℂ :=
  ((moment G v.x).toLinearMap (Fin.cons (α := fun _ => WickPol G) 0 (fun i => (v.exterior i).val)) 0).comp (shellSector G d).subtype

lemma test_formula (v : ProbeFamily G) (d p) : v.test d p = moment G v.x (Fin.cons p.val fun i => (v.exterior i).val) := by
  unfold ProbeFamily.test
  simp only [LinearMap.comp_apply,MultilinearMap.toLinearMap_apply]
  congr 1
  ext1 i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

def residual (G : Gauge) (d : ℕ) : Submodule ℂ (shellSector G d) :=
  LinearMap.ker <| LinearMap.pi fun i : ProbeFamily G => i.test d

def snap (d : ℕ) : (standard F).Ref d →ₗ[ℂ] shellSector G d :=
  (observable G d).rangeRestrict.comp (F.level d).coords.symm.toLinearMap

theorem full (d : ℕ) : Surjective (snap F d) :=
  (LinearMap.surjective_rangeRestrict _).comp (F.level d).coords.symm.surjective

lemma bridge {n : ℕ} (d) (u : (standard F).Ref d) (z : Fin n → (standard F).Token) {x} (hx : x ∈ conf (n+1)) :
    let v : ProbeFamily G := ⟨n, fun i => (z i).1, fun i => snap F _ (z i).2, x, hx⟩
    (freeTable F).read x (Fin.cons ⟨d,u⟩ z) = v.test d (snap F d u) := by
  intro v
  rw [decodes,test_formula]
  congr 1
  ext1 i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

lemma projectionExact {d c} : snap F d c ∈ residual G d ↔ c ∈ (freeTable F).null d := by
  rw [(freeTable F).criterion]
  constructor
  · intro h n v x hx
    rw [bridge F _ _ _ hx]
    exact congr_fun (show _ from LinearMap.mem_ker.mp h) _
  intro h
  apply LinearMap.mem_ker.mpr
  funext y
  choose w hw using fun i => full F _ (y.exterior i)
  let z (i : Fin y.n) : (standard F).Token := ⟨y.d i, w i⟩
  change y.test d (snap F d c) = 0
  have he := h y.n z y.x y.clear
  rw [bridge F d c z y.clear] at he
  have ha : (ProbeFamily.mk _ (fun i => (z i).1) (fun i => snap F _ (z i).2) _ y.clear)=y := by
    congr 1; exact funext hw
  exact ha ▸ he

def collapsed (d : ℕ) : (standard F).Ref d →ₗ[ℂ] (shellSector G d) ⧸ residual G d :=
  (residual G d).mkQ.comp (snap F d)

theorem exactKer (d) : LinearMap.ker (collapsed F d) = (freeTable F).null d := by
  ext1 x
  exact (Submodule.Quotient.mk_eq_zero _).trans (projectionExact F)

/-- The two-step comparison space and `(freeTable F).Field d` agree. -/
def addresses (d : ℕ) : (freeTable F).Field d ≃ₗ[ℂ] (shellSector G d) ⧸ residual G d :=
  (Submodule.quotEquivOfEq _ _ (exactKer F d).symm).trans <|
    (collapsed F d).quotKerEquivOfSurjective ((residual G d).mkQ_surjective.comp (full F d))

/-- Ranks assertion levelwise (E in terms of successive differences, with the ranks below zero stipulated zero).

It is complex equivalence, compatible separately with conjugation and H-action. -/
def Ranks {L : Register G} (S : Table L) (H : S.RealSpin) : Prop :=
  ∃ h : (freeTable L.grid).RealSpin, ∀ d : ℕ,
    ∃ f : S.Field d ≃ₗ[ℂ] (freeTable L.grid).Field d,
      (∀ x, f (S.conj H d x) = (freeTable L.grid).conj h d (f x)) ∧
      (∀ k x, f (S.mirror H d k x) = (freeTable L.grid).mirror h d k (f x))

end YM.Maxwell
