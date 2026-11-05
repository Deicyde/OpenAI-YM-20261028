import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Progress.DIRECTED_RECIPE.Deploy
import YM.Progress.JOINT_CALENDAR.Delivery

set_option warningAsError false

/-!
# Joint issuance with Wilson start

Freeze inked before `Quote`. Top widths/costs are themselves bought by
the proposed `counter`, including the actual true-length costs of this top.
`Loaded`/`Package` and period attenuation for further uses not superseded
by our waits. Keep access to the stronger **old** horizon so only one Kin
bill (UNCHANGED Planned, same Levels, final Beam.price on both) need ever
be asked for: either on that old horizon, or one on the displayed repainted
horizon. See `SupplyShelf.switch`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Planned.Port
open Filter Function Lattice RG RG.Supply Bid Precision Exterior Bloch Next Next.Scheduling Next.Scheduling.Weak
open WilsonStartup Progress.Joint Pressure
variable {G : Gauge} {A : Authorities G}







/-- Early Clip table & final pricing. -/
def table (O : Desk A) (i : ℕ) := ((startSheet A O.b O.direct O.pos).profile i).clip
def finalMap (O : Desk A) := inked (table O) O.T









section prices
variable {s : Survey G} {q : Quote} (O : Desk A)






end prices

section shelves
variable (O : Desk A) {s : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {T : Protection D} {V : Delays T} {Y : Bar V} {I : Wait Y}
    {a : Levels G} {F : ℕ → ℕ → Postage} {B : Beam (finalMap O) D}
    {e : ℕ → ℕ → Exchange} {R : Radios (finalMap O) D}
    {rate : ℕ → ℝ} {t : ℕ → ℕ}

/-- Reusable purchases at a particular Levels, including startup timing.

`usual` gives all of Wares on the *unchanged* certified free route; plus
that horizon is already qualified at the prior price (avoid selecting before
remembering this).

`display` and station work, Operates and future
path questions can equally operate at the **boundary altered** H, with
unchanged widths/profiles and the same chart and Beam.price.

Substantial
new trajectory uses that require more preserved need separate proofs and may
not be compatible with this top.

`Painting.lower` and `Painting.guess_all/t`
for exact parts kept; `usual.reference` etc already independent of H. -/
structure SupplyShelf (B : Beam (finalMap O) D) (R : Radios (finalMap O) D) (F : ℕ → ℕ → Postage)
    (rate : ℕ → ℝ) (t : ℕ → ℕ) (M U H : Horizon a) : Prop where
  large : ∀ i, Design.Suitable G (a.params i)
  kickoff N : Start.Allows a N ∧ ∀ d ≤ a.clock.J N, WilsonStartup.Mark.Ready a (s.B.entry d) N
  usual : Wares B R F M U O.l rate t
  old : U.Suffices O.T
  repaint : Painting H U
  enough : H.Suffices (finalMap O)
  swears : Swears H
  operates : Operates R H
  paths (L : Restriction G) : Progress.Joint.Invoices H B F s.B.chart L →
    ∃ k : Kin H s.B.chart, k.Planned (B.price F) ∧
      (∀ N m,m ≤ N → OnPage H L N m (k.path N m)) ∧
      ∀ N m,m < N → WarmAt H N m (B.η (a.clock.J (m+1))) (k.path N (m+1)) (k.stationary N m)

variable {O} {M U H : Horizon a}

/-- Only one **exact** Kin.Planned hypothesis, no extra alignment, even if
supplied by producers on the Free route. Consume on THIS schedule priced
for the common, final, post-L Beam (and A0 held fixed throughout); NOT
transporting a Kin from a prior rollout with different prices. Uses actual
WilsonStartup.Change.engine. -/
lemma SupplyShelf.switch (h : SupplyShelf O B R F rate t M U H) (k : Kin U s.B.chart)
    (hk : k.Planned (B.price F)) : ∃ y : Kin H s.B.chart,y.Planned (B.price F) ∧ y.path=Change.revised k ∧
    y.alpha=k.alpha ∧ ∀ N m p X,m+1<N → y.stationary N m p X=k.stationary N m p X :=
  Change.engine h.repaint.toOverlay s.B.chartRatio hk h.large



variable (O)


end shelves

section receive
variable (O : Desk A) {s : Survey G} {q : Quote} {v : ℕ → ℕ} {e : ℕ → ℕ → Exchange}




end receive



end YM.Planned.Port
