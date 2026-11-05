import YM.Progress.JOINT_CALENDAR.Kinetics
import YM.Progress.JOINT_CALENDAR.Period


/-!
# Deployment checks

Enlarge the periods simultaneously as promised in Period. Bind numerical,
linear, stationary, Teller and source reference receipts on exactly one set
of choices. No conclusion of `Kin.Planned` without the explicit higher
matching invoices at their genuine quantifier scope. Expose Teller budget
for arbitrary supported paths and each Plot on this horizon INDEPENDENTLY
of those higher invoices -- the oriented plot/slice prerequisites and paths
are substantial, not an estimate on a whole E/K integration!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open Filter Function Lattice RG RG.Supply Wilson Precision Exterior Tree Bid Pressure Next Next.Scheduling Next.Scheduling.Weak
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {K : MapPrices} {s : Survey G} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)}
    {Θ : Protection D} {V : Delays Θ} {Y : Bar V} {J : Wait Y} {a : Levels G}
    {B : Beam K D} {P : ℕ → ℕ → Postage} {e : ℕ → ℕ → Exchange} {R : Radios K D}

def carriage {a : Levels G} (H : Horizon a) (N m n : ℕ) (U V : PathData G) : Tube G (a.clock.op m n) :=
    ⟨H.towers N m, U,(a.params (m+1)).clip,V,(a.params m).clip⟩

def Operates (R : Radios K D) {a : Levels G} (H : Horizon a) := ∀ N m n : ℕ,m<N →
    let S := a.clock.op m n; let x := a.clock.hatBeta m; let j := a.clock.J (m+1); let i:=a.clock.J m
    ∀ U V, Attached (H.H N (m+1)) U → Attached (H.H N m) V → FitsAt a (m+1) U → FitsAt a m V →
    ∀ (X : Stores S) (Y : Config G _) (Z : Config G _) (k : S.Choices) (A : Forest S.ratio), Stores.SliceSet S A Y →
      Stores.Plot X Y k Z x (R.W j i) →
      R.strength j i * (a.clock.threshold (m+1))^2*X.shares ≤ X.assessed (carriage H N m n U V) x Y (S.prediction Y k) Z

lemma operate (ha : Paid J a) (hr : Transmitting R V) {H : Horizon a} (hh : H.Suffices K) : Operates R H := by
  intro N m n h S x j i U V hu hv hU hV X Y Z k A hs hz
  have hx : s.first ≤ i := ha.firstZero.ge.trans (a.fits.mono (Nat.zero_le m))
  have hf : R.floorBeta j i ≤ x := (hr _ _ (Deployment.adj a m)).trans (ha.pays m)
  have hT : Teller.Funds (Testing.query (s.paper q v) K j i) _ (carriage H N m n U V) := by
    refine ⟨ha.kernel,rfl,s.B.has _,hh.costs _ _ h,congr_arg Stage.clip (Deployment.params ha _),congr_arg Stage.clip (Deployment.params ha _),?_,
      ⟨_,_,hu,hv,hh.stack _ _ _ h⟩⟩
    unfold FitsAt at hU hV; rw [Deployment.params ha] at hU hV
    exact ⟨_,_,hU,hV⟩
  have Ht := R.reaches j i (Deployment.adj a m) hx x hf _ _ S (Deployment.block ha m) (by rw [add_comm]; exact a.fits.sizeT m n)
    (carriage H N m n U V) hT A X Y k Z hs hz
  have he : fiery G x (D.L j) = a.clock.threshold (m+1) := by
    unfold fiery betaF Calendar.threshold Calendar.hatCoupling Calendar.monitor
    rw [← Deployment.block ha,← Deployment.hat]; rfl
  exact he ▸ Ht

/-- Also keep each Loaded/etc witness (see
`Package.receive`).

Use `H` again in any continuation; availability
statement is on THIS B,P,J etc, not existential feasibility of invoices.

Even when W₀ silent as initial display, never infer that `Kin.Planned`
uses those zero higher arrays.

All clauses valid also for m=0 when relevant. -/
structure Wares (B : Beam K D) (R : Radios K D) (P : ℕ → ℕ → Postage)
    {a : Levels G} (M H : Horizon a) (l rate : ℕ → ℝ) (t : ℕ → ℕ) : Prop where
  rack : Craft.Rack a s.X M
  present : Free.Present a M l
  retained : Bid.Retained H M
  enough : H.Suffices K
  permanent : Free.Present a H l
  oath : Swears H
  operates : Operates R H
  sized : Attenuated (B.price P) a rate t
  demo : ∃ W : ℕ → ℕ → PathData G, ∀ N m,m≤N → Attached (H.H N m) (W N m) ∧
    FitsAt a m (W N m) ∧ ∀ i,((W N m).cubic i).coeff=0 ∧ ((W N m).quartic i).coeff=0 ∧ ((W N m).loop i).coeff=0
  paths (L : Restriction G) : Invoices H B P s.B.chart L → ∃ u : Kin H s.B.chart, u.Planned (B.price P) ∧ ∀ N m,m ≤ N → L N m (u.path N m)
  reference : ∃ r : ℕ → ℕ, (∀ d m,r d ≤ m ↔ Admits s.requests (a.clock.J m) d) ∧
    ∀ H : History G, H.levels = a → RefLi H s.B.frames s.B.entry s.B.hol r

variable {l γ : ℕ → ℝ} {b : ℕ → ℕ}

theorem wares (h : Package s K q e v l γ b) (hq : Designing K q) (ha : Paid J a)
    (hv : Regime B e P V) (hr : Transmitting R V) {rate t} (ht : Attenuated (B.price P) a rate t) :
    ∃ M H : Horizon a, Wares B R P M H l rate t := by
  obtain ⟨M,H,hM,hP,hH,hK,hP',hO⟩ := (h.serves D ha).2
  exact ⟨M,H,hM,hP,hH,hK,hP',hO,operate ha hr hK,ht, hq.display ha hK,
    fun L => planning ha h.prices hq hv hK hO s.B.chartRatio (L:=L), Deployment.refAt ha hv⟩

/-- Now with simultaneous phase-mesh exponential suppression payments at
the same quantifier order (post-L and post-P additional bills, *before*
Levels). `Invoices` not obtained here. Use this producer with `establish`
and `Desk.pay` or `joint_budget`; `design` ensures the width check below.
Subsequent numerical refinements allowed at the indicated entry binders.
Not a YU producer. -/
theorem Package.receive (h : Package s K q e v l γ b) (hq : Designing K q) (D : Rolls (s.paper q v)) (extraW : ℕ → ℕ → ℝ) :
    ∃ (B : Beam K D) (R : Radios K D), (∀ i j,extraW i j ≤ R.W i j) ∧
      ∀ (F : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus) (extra : ℕ → ℝ),
      (∀ i,0 < extra i) → ∃ T : Protection D,T.theta ≤ extra ∧
        ∀ (rate : ℕ → ℝ) (t : ℕ → ℕ) (V : Delays T), ∀ c d u,
          ∃ W : Delays T, Boost V W ∧ Loaded B W e F m f ∧ Extent d c W ∧ Routed e u W ∧ Bumper e W ∧
          Transmitting R W ∧ Testing.Ringing K R.W W ∧
          ∀ r : ℝ,∃ Y : Bar W,r ≤ Y.value ∧ ∀ J : Wait Y,
            ∃ I : Wait Y, Behind J I ∧ Billed I e f ∧ (∃ a : Levels G,Paid I a) ∧
              ∀ a : Levels G,Paid I a → ∃ M H : Horizon a,Wares B R F M H l rate t := by
  obtain ⟨B,R,hR,hB⟩ := h.afterL D extraW
  refine ⟨B,R,hR,fun F m f extra he => ?_⟩
  obtain ⟨T,hT,hE⟩ := hB F m f extra he
  refine ⟨T,hT,fun rate t V c d u => ?_⟩
  obtain ⟨z,hz,hZ⟩ := Attenuated.offer (B.price F) rate t
  obtain ⟨V₀,hh,H⟩ := hz.prepare V
  obtain ⟨W,hw,hL,hx,hu,hB,hr,hK,hy⟩ := hE V₀ c d u
  refine ⟨W,hh.chain hw,hL,hx,hu,hB,hr,hK,fun r => ?_⟩
  obtain ⟨Y,hY,hj⟩ := hy r
  refine ⟨Y,hY,fun J => ?_⟩
  obtain ⟨J',hh',hp⟩ := (H.later hw).clear hz J
  obtain ⟨I,hI,hb,ha⟩ := hj J'
  exact ⟨I, ⟨hh'.first.trans hI.first,hh'.win.trans hI.win,hh'.psize.trans hI.psize⟩,hb,ha,
    fun a HA => wares h hq HA hL.taxed hr (hZ HA (hp hI _ HA))⟩
end YM.Progress.Joint
