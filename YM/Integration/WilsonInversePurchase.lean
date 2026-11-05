import YM.Integration.WilsonInverseSchedule

/-! The inverse charge is a genuine post-length request.  It can be paid
before the common Run is selected, without changing its lengths or kernel.
The chosen Names are transported by the native Paid.kernel identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInverseSchedule

open Filter Function Lattice Wilson RG RG.Supply Next.Free
open RG08 RG08.Admission Push.PriceCompiler
open scoped Topology Classical

variable {G : Gauge}

private def postPrice (L : Side) (w : Need) (j i : ℕ) (s : RG.Stage) : ℝ :=
  if h : Odd L.val ∧ 3 ≤ L.val ∧ 4 ≤ j ∧ i ≤ j ∧ j ≤ i + 1 then
    w.cost j i ⟨L, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, .top j⟩ s
  else 0

/-- A zero-precondition Need costs only a delay increase, on every larger
delay and its original native Paid Levels. -/
theorem zeroPreDelay {s : Sheet G} {P : Rolls s} {θ : Protection P}
    (w : Need) (hpre : ∀ i, w.pre i = 0) (V : Delays θ) :
    ∃ X : Delays θ, DelayLe V X ∧
      ∀ (Z : Delays θ) (Y : Bar Z) (J : Wait Y) (a : Levels G),
        DelayLe X Z → Paid J a → Affords w a 0 := by
  have affordable (j : ℕ) : ∀ᶠ x : ℝ in atTop,
      ∀ i : ℕ, i ≤ j → postPrice (P.L j) w j i (s.profile i) ≤ zview x := by
    have finite : ∀ᶠ x : ℝ in atTop, ∀ i : Fin (j + 1),
        postPrice (P.L j) w j i (s.profile i) ≤ zview x :=
      eventually_all.mpr (fun _ => z_rises.eventually (eventually_ge_atTop _))
    filter_upwards [finite] with x hx i hi
    exact hx ⟨i, by omega⟩
  obtain ⟨X, hX, _, works⟩ := delay_extra V
    (fun j x => ∀ i : ℕ, i ≤ j → postPrice (P.L j) w j i (s.profile i) ≤ zview x)
    (fun _ _ _ => True) affordable
    (fun _ _ => Eventually.of_forall (fun _ => True.intro))
  refine ⟨X, hX, fun Z Y J a hZ ha => ?_⟩
  constructor
  · intro m _
    rw [hpre]
    exact Nat.zero_le _
  · intro m _
    have hF : a.S.block m = P.L (a.clock.J (m + 1)) := by
      simpa only [ha.lengths] using (a.fits.sameFactor m).symm
    have bound := (works Z hZ).1 _ _ (ha.pays m) (a.clock.J m)
      (a.fits.mono (Nat.le_succ m))
    rw [← hF, postPrice,
      dif_pos ⟨a.S.block_odd _, a.S.block_large _, a.clock.adm _,
        a.fits.mono (Nat.le_succ _), a.fits.stepSlow _⟩, ← ha.stage] at bound
    exact bound

/-- The Names and their paid inverse charge belong to this very Levels. -/
def InverseFunded (a : Levels G) : Prop :=
  ∃ N : Names G a.clock.kernel, Affords (inverseNeed N) a 0

/-- The original common-construction numerical-request hook can buy the
inverse charge before selecting its Run.  No inverse-growth estimate is
assumed, and no second physical witness is chosen. The result is the exact
definitional expansion of `R2I.EventuallyPaid InverseFunded`, allowing this
purchase to compile independently of the broad construction endpoint. -/
theorem inverseEventuallyPaid (hG : G.Simple) :
    ∀ (s : Sheet G) (P : Rolls s) (θ : Protection P) (V : Delays θ),
      ∃ X, DelayLe V X ∧ ∀ (Z : Delays θ), DelayLe X Z →
        ∀ (Y : Bar Z) (J : Wait Y) (a : Levels G), Paid J a → InverseFunded a := by
  intro s P θ V
  obtain ⟨N⟩ := names hG s.kernel
  obtain ⟨X, hX, works⟩ := zeroPreDelay (inverseNeed N) (fun _ => rfl) V
  refine ⟨X, hX, fun Z hZ Y J a ha => ?_⟩
  have transport : ∃ N' : Names G a.clock.kernel, inverseNeed N' = inverseNeed N := by
    rw [ha.kernel]
    exact ⟨N, rfl⟩
  obtain ⟨N', hN⟩ := transport
  refine ⟨N', ?_⟩
  rw [hN]
  exact works Z Y J a hZ ha

end YM.Integration.WilsonInverseSchedule
