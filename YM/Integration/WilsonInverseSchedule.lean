import YM.RG08.Calendar.Basis
import YM.RG08.Invert.Campus
import YM.Integration.WilsonInverseLimits

/-!
The inverse-map receipt on the same actual RG08 schedule.

The original thirteen-charge `Admission.fast`, `Ball`, and `Docks` retain
their meanings.

The resulting contour limit is a cutoff limit of the actual formal rows;
this file does not identify it with the physical Scout/MS prescription.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonInverseSchedule
open RG08

open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function
open Next.Free RG RG.Supply Bloch Stationary Conductor Staffer Reflect UVExt.Paths
open Work.F08 Push.AbsoluteSums UVExtension.Free
open RG08 RG08.Admission RG08.Wings RG08.Drift
open scoped BigOperators Topology Real Classical

variable {G : Gauge} {K : KernelChoices} {I : Type}

/-- The additional charge uses the original patch, axis forest and width. -/
def inverseNeed (N : Names G K) : Need :=
  ⟨fun _ => 0, fun j i f _ =>
    Invert.turnsCost G f.patch K (Repeated.axisRule f.L f.odd)
      (N.bridge.alpha j i)⟩

/-- An explicitly stronger budget, without changing `Admission.fast`. -/
def fastWithInverse (N : Names G K) (D : ChartRatio G) (E d : ℕ) : Need :=
  (fast N D E d).brings (inverseNeed N)

/-- The coefficient is fixed by G before the window family or its index.
The estimate uses the actual paid inverse cost, not an assumed growth law. -/
theorem inverseCostBound {a : Levels G} {N : Names G a.clock.kernel}
    {u : I → Windows} (hp : G.Simple) (hu : NearZ a u)
    (paid : ∀ i, Affords (inverseNeed N) a (u i).start) (i : Launch u) :
    Invert.turnsCost G ((Chain.actual a).patch i.i) a.clock.kernel
      ((Chain.actual a).trees i.i)
      (N.bridge.alpha (a.clock.J (i.i + 1)) (a.clock.J i.i)) ≤
        (1 + G.slopeConstant) * Launch.farY (Chain.actual a) i := by
  have funded := (paid i.b).hi i.i i.geC
  change Invert.turnsCost G ((Chain.actual a).patch i.i) a.clock.kernel
    ((Chain.actual a).trees i.i)
    (N.bridge.alpha (a.clock.J (i.i + 1)) (a.clock.J i.i)) ≤ z a i.i at funded
  apply funded.trans
  apply (z_older hp a i.i (u i.b).k).trans
  have hSlope := Gauge.slopeConstant_pos hp
  have hWindow := hu i.b
  have hPositive := (u i.b).pos
  have hDistance := abs_nonneg (a.S.scale i.i - a.S.scale (u i.b).k)
  unfold Launch.farY
  change z a (u i.b).k + G.slopeConstant *
    |a.S.scale i.i - a.S.scale (u i.b).k| ≤
      (1 + G.slopeConstant) * (2 + (u i.b).Z +
        |a.S.scale i.i - a.S.scale (u i.b).k|)
  nlinarith

/-- The new receipt is derived from an ordinary paid Need on this Levels. -/
theorem inverseEarned {a : Levels G} {N : Names G a.clock.kernel}
    {u : I → Windows} (hp : G.Simple) (hu : NearZ a u)
    (paid : ∀ i, Affords (inverseNeed N) a (u i).start) :
    Weighed (Launch.farY (u := u) (Chain.actual a))
      (fun i => Invert.turnsCost G ((Chain.actual a).patch i.i)
        a.clock.kernel ((Chain.actual a).trees i.i)
        (N.bridge.alpha (a.clock.J (i.i + 1)) (a.clock.J i.i))) := by
  exact Affords.cash_w hp hu paid
    (fun _ => Invert.turnsCost_pay _ _ _ _ (N.bridge.ap _ _))
    (fun _ => le_rfl)

structure BallWithInverse {a : Levels G} (N : Names G a.clock.kernel)
    (D : ChartRatio G) (ν : G.ColorIndex) (u : I → Windows) (E d : ℕ) : Prop
    extends Ball N D ν u E d where
  earns : Weighed (Launch.farY (u := u) (Chain.actual a))
    (fun i => Invert.turnsCost G ((Chain.actual a).patch i.i)
      a.clock.kernel ((Chain.actual a).trees i.i)
      (N.bridge.alpha (a.clock.J (i.i + 1)) (a.clock.J i.i)))

theorem mattersWithInverse {a : Levels G} {N : Names G a.clock.kernel}
    {D : ChartRatio G} {ν : G.ColorIndex} {u : I → Windows} {E d : ℕ}
    (hu : NearZ a u) (hp : G.Simple)
    (height : ∀ i, 5 ≤ a.clock.J (u i).start)
    (paid : ∀ i, Affords (fastWithInverse N D E d) a (u i).start) :
    BallWithInverse N D ν u E d := by
  exact ⟨matters hu hp height
      (fun i => (paid i).of_sub (Need.Higher.front ..)),
    inverseEarned hp hu (fun i => (paid i).of_sub (Need.Higher.back ..))⟩

/-- The native contour comparison needs no separately assumed inverse bound. -/
theorem BallWithInverse.contours {a : Levels G} {N : Names G a.clock.kernel}
    {D : ChartRatio G} {ν : G.ColorIndex} {u : I → Windows} {E d : ℕ}
    (paid : BallWithInverse N D ν u E d) :
    RowBoth (menu (u := u) (Chain.actual a)) (chop (Chain.actual a) (1 / 104))
      (fun i : Wings u 1 => Invert.contour (Chain.actual a) G i.i i.N)
      (fun i => Invert.contour (Chain.actual a) G i.i i.M)
      (fun i => N.bridge.alpha (a.clock.J (i.i + 1)) (a.clock.J i.i)) := by
  exact Invert.contour_shot paid.yes paid.plays paid.earns

/-- The limit uses the original actual contour family at every cutoff. -/
def contourLimit (a : Levels G) (m : ℕ) :=
  apex (fun n => Invert.contour (Chain.actual a) G m n)

theorem BallWithInverse.contourLimitRate
    {a : Levels G} {N : Names G a.clock.kernel} {D : ChartRatio G}
    {ν : G.ColorIndex} {u : I → Windows} {E d : ℕ}
    (paid : BallWithInverse N D ν u E d) :
    RowBoth (menu (u := u) (Chain.actual a)) (chop (Chain.actual a) (1 / 104))
      (fun i : Wings u 1 => Invert.contour (Chain.actual a) G i.i i.N)
      (fun i => contourLimit a i.i)
      (fun i => N.bridge.alpha (a.clock.J (i.i + 1)) (a.clock.J i.i)) := by
  exact rowLimitRate (S := Chain.actual a) (u := u)
    (α := fun i => Co (a.S.block i) (Loc G 0)) (β := fun _ => Loc G 1)
    (F := fun n i => Invert.contour (Chain.actual a) G i n)
    (σ := fun i => N.bridge.alpha (a.clock.J (i + 1)) (a.clock.J i)) (t := 1)
    (by norm_num : (0 : ℝ) < 1 / 104) (fun _ => N.bridge.ap _ _) paid.contours

/-- On an admitted window, the chosen limit is an actual limit of the
same contour sequence; no off-admission fallback is used. -/
theorem BallWithInverse.contourConverges
    {a : Levels G} {N : Names G a.clock.kernel} {D : ChartRatio G}
    {ν : G.ColorIndex} {u : I → Windows} {E d : ℕ}
    (paid : BallWithInverse N D ν u E d) (i : Wings u 1) :
    Tendsto (fun n => Invert.contour (Chain.actual a) G i.i n)
      atTop (𝓝 (contourLimit a i.i)) := by
  obtain ⟨_, _, _, _, _, _, data⟩ :=
    rowLimitData (S := Chain.actual a) (u := u)
      (α := fun i => Co (a.S.block i) (Loc G 0)) (β := fun _ => Loc G 1)
      (F := fun n i => Invert.contour (Chain.actual a) G i n)
      (σ := fun i => N.bridge.alpha (a.clock.J (i + 1)) (a.clock.J i)) (t := 1)
      (by norm_num : (0 : ℝ) < 1 / 104) (fun _ => N.bridge.ap _ _) paid.contours
  exact (data i).1.entries

theorem BallWithInverse.contourLimit_whole
    {a : Levels G} {N : Names G a.clock.kernel} {D : ChartRatio G}
    {ν : G.ColorIndex} {u : I → Windows} {E d : ℕ}
    (paid : BallWithInverse N D ν u E d) (i : Wings u 1) :
    Whole (contourLimit a i.i) :=
  paid.contourLimitRate.again.status (fun _ => N.bridge.ap _ _) i

end YM.Integration.WilsonInverseSchedule
