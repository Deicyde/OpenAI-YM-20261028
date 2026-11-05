import YM.FullVolume.Roll.Fiscal
import YM.RG08.Redo.Access
import YM.Integration.NativePostLengthPayment

/-!
# The native component recipe on a supplied original clock

The secondary quote and the flat/curvature/dual floors are selected from
the original Sheet before any block lengths. The post-facing quote is
exactly raging s T. Redo's finite native rail and Yamen's finite native
need are then included in the same pre-length floor.

The post-length bill is the maximum of the actual Redo and Yamen bills.
The realization below uses a supplied Levels and Horizon throughout;
it never calls Redo.join, June.holdem, or another Family constructor.
It does not identify the resulting formal marked data with physical
MarkedPackets, nor prove the full joint qlocal selection theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeComponentRecipe
open Lattice Laurent RG RG.Supply Precision Stationary Bloch
open PhysicalNext PhysicalNext.ThroughLaunch Next.Free
open RG08

variable {G : Gauge}

/-- All nonnumerical suppliers are selected from the original Sheet. -/
structure Choice (s : Sheet G) where
  secondary : MapPrices
  flatFloor : ℕ → ℕ
  flat_supply : ∀ a : Levels G, a.clock.kernel = s.kernel →
    a.clock.stage = s.profile →
    (∀ i, flatFloor (a.clock.J (i + 1)) ≤ (a.S.block i).val) →
    ∀ e, Flat.Delay a secondary e →
      ∃ (F : ℕ → Pert.Bulk.Kernel Flat.Links Flat.Links) (A B : ℝ)
        (d l : ℕ) (c : ℝ),
        ∀ (H : Horizon a) (P : MapPrices), H.Suffices P →
          Flat.Quorum (Flat.curve secondary) F e H A B d l c
  swornFloor : ℕ → ℕ
  sworn_supply : ∀ a : Levels G, a.clock.kernel = s.kernel →
    a.clock.stage = s.profile →
    (∀ i, swornFloor (a.clock.J (i + 1)) ≤ (a.S.block i).val) →
    ∀ (H : Horizon a) (P : MapPrices), H.Suffices P →
      ∀ i N n, i ≤ N → Bid.Sworn (H.H N i) n G
  dualFloor : ℕ → ℕ
  dual_supply : ∀ a : Levels G, a.clock.kernel = s.kernel →
    a.clock.stage = s.profile →
    (∀ i, dualFloor (a.clock.J (i + 1)) ≤ (a.S.block i).val) →
    ∀ (H : Horizon a) (P : MapPrices), H.Suffices P →
      Aura.licensed a H

/-- The original native suppliers construct this choice before L. -/
theorem available (hG : G.Simple) (s : Sheet G) : Nonempty (Choice s) := by
  obtain ⟨X, E, hE⟩ := Flat.entrance_gate hG s.kernel s rfl
  obtain ⟨Y, hY⟩ := Cast.assured G s.kernel s rfl
  obtain ⟨D, hD⟩ := Aura.dual_support G s
  exact ⟨⟨X, E, hE, Y, fun a hk hs hL H P hP => hY a hk hs hL H hP,
    D, fun a hk hs hL H P hP => hD a hk hs hL H hP⟩⟩

def floor (s : Sheet G) (T : MapPrices) (C : Choice s) (i : ℕ) : ℕ :=
  max (max (C.flatFloor i) (C.swornFloor i))
    (max (C.dualFloor i)
      (max (Yamen.need G (raging s T) C.secondary s.kernel i)
        (Redo.rail G s.kernel (raging s T) C.secondary i)))

def width (s : Sheet G) (T : MapPrices) (C : Choice s) (E i : ℕ) : ℝ :=
  Redo.reef G s.kernel (raging s T) C.secondary E i

/-- The pre-length countable request for every fixed native width family. -/
def numeric (s : Sheet G) (T : MapPrices) (C : Choice s) (E i : ℕ) : ℝ :=
  (width s T C E i)⁻¹

/-- Only this bill uses the already selected block lengths. -/
def post (s : Sheet G) (T : MapPrices) (C : Choice s)
    (lengths : ℕ → ℕ) (i : ℕ) : ℝ :=
  max (Redo.after G s.kernel (raging s T) C.secondary lengths i)
    (Yamen.shade G (raging s T) C.secondary s.kernel
      (Next.Foundations.chart G) lengths i)

theorem width_positive (s : Sheet G) (T : MapPrices) (C : Choice s)
    (E i : ℕ) : 0 < width s T C E i :=
  Redo.reef_life G s.kernel (raging s T) C.secondary E i

theorem width_le_one (s : Sheet G) (T : MapPrices) (C : Choice s)
    (E i : ℕ) : width s T C E i ≤ 1 :=
  (Redo.reef_cap G s.kernel (raging s T) C.secondary E i).trans
    (min_le_left _ _)

/-- The native after bill implies the native actual-patch receipt. -/
theorem openBook_of_stagePaid (a : Levels G) (K : KernelChoices)
    (P X : MapPrices) (hk : a.clock.kernel = K)
    (hpaid : NativePostLengthPayment.StagePaid
      (Redo.after G K P X (fun j => (a.clock.factor j).val)) a) :
    Redo.OpenBook a P X := by
  intro i
  rw [hk]
  have hf := hpaid i
  unfold Redo.after at hf
  let f := fun j => (a.clock.factor j).val
  let j := a.clock.J (i + 1)
  have hx : ∃ S : Patch, S.J = j ∧ S.L.val = f j :=
    ⟨RG08.Supplies.stone a i, rfl,
      congrArg Subtype.val (a.fits.sameFactor i).symm⟩
  rw [dif_pos hx, show hx.choose = RG08.Supplies.stone a i from ?_] at hf
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hf
  have extPatch (P Q : Patch) (h : P.J = Q.J) (hL : P.L = Q.L) :
      P = Q := by
    cases P
    cases Q
    simp_all
  exact extPatch _ _ hx.choose_spec.1
    (Subtype.ext (hx.choose_spec.2.trans
      (congrArg Subtype.val (a.fits.sameFactor i))))

/-- These are conclusions on the same supplied native Levels and Horizon. -/
structure Realized (s : Sheet G) (T : MapPrices) (C : Choice s)
    (a : Levels G) (H : Horizon a) : Prop where
  door : Redo.OpenDoor a (raging s T) C.secondary
  book : Redo.OpenBook a (raging s T) C.secondary
  bill : Yamen.Bill G (raging s T) C.secondary a
  payment : Yamen.Payment G (raging s T) C.secondary
    (Next.Foundations.chart G) a
  licensed : Aura.licensed a H
  supplies : Yamen.Supplies H (raging s T) (Next.Foundations.chart G)
  flat : ∃ (F : ℕ → Pert.Bulk.Kernel Flat.Links Flat.Links) (A B : ℝ)
    (d l : ℕ) (c : ℝ),
    Flat.Quorum (Flat.curve C.secondary) F 0 H A B d l c

/-- Pre-length floors and the constructed post-length bill suffice.
The caller must bind these two numerical receipts to its original Run. -/
theorem realize (s : Sheet G) (T : MapPrices) (C : Choice s)
    (a : Levels G) (H : Horizon a)
    (hk : a.clock.kernel = s.kernel) (hs : a.clock.stage = s.profile)
    (hfloor : ∀ i, floor s T C i ≤ (a.clock.factor i).val)
    (hpaid : NativePostLengthPayment.StagePaid
      (post s T C (fun j => (a.clock.factor j).val)) a)
    (hH : H.Suffices (raging s T)) : Realized s T C a H := by
  have hstep (i : ℕ) :
      floor s T C (a.clock.J (i + 1)) ≤ (a.S.block i).val := by
    rw [← a.fits.sameFactor]
    exact hfloor _
  have hflat (i : ℕ) :
      C.flatFloor (a.clock.J (i + 1)) ≤ (a.S.block i).val :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (hstep i))
  have hsworn (i : ℕ) :
      C.swornFloor (a.clock.J (i + 1)) ≤ (a.S.block i).val :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (hstep i))
  have hdual (i : ℕ) :
      C.dualFloor (a.clock.J (i + 1)) ≤ (a.S.block i).val :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (hstep i))
  have hbill : Yamen.Bill G (raging s T) C.secondary a := by
    intro i
    rw [hk]
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (hfloor i)))
  have hdoor : Redo.OpenDoor a (raging s T) C.secondary := by
    intro i
    rw [hk]
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (hstep i)))
  have hafter : NativePostLengthPayment.StagePaid
      (Redo.after G s.kernel (raging s T) C.secondary
        (fun j => (a.clock.factor j).val)) a :=
    fun i => (le_max_left _ _).trans (hpaid i)
  have hpayment : Yamen.Payment G (raging s T) C.secondary
      (Next.Foundations.chart G) a := by
    intro i
    rw [hk]
    exact (le_max_right _ _).trans (hpaid i)
  have hdelay : Flat.Delay a C.secondary 0 := by
    intro i _
    have he := Yamen.hatch hpayment i
    exact ((Yamen.stamped G (raging s T) C.secondary a.clock.kernel
      (Next.Foundations.chart G) (RG08.Supplies.stone a i)).arms
      (a.clock.J i) (a.fits.mono (Nat.le_succ i))).trans he
  obtain ⟨F, A, B, d, l, c, hF⟩ := C.flat_supply a hk hs hflat 0 hdelay
  exact ⟨hdoor, openBook_of_stagePaid a s.kernel _ _ hk hafter,
    hbill, hpayment, C.dual_supply a hk hs hdual H _ hH,
    ⟨hH, fun N i n hi => C.sworn_supply a hk hs hsworn H _ hH i N n hi,
      Next.Foundations.chart_ok G⟩,
    F, A, B, d, l, c, hF H _ hH⟩

end YM.Integration.NativeComponentRecipe
end
