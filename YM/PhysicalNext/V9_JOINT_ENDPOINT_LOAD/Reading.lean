import YM.Extra.ITERATION_NO_LOSS.Production
import YM.Extra.MULTISOURCE_TRAJECTORIES.Prepared
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Calendar
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Collector
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Step


/-!
# Spending on a funded calendar. Construction of Desk is here,
# construction of Programme/Run/Slices/Reading on IT is NOT.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Clockwork
open Function Filter Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Push.SectorMeasure Presented
open AnalyticBridge.AnnulusRatioInsertions AnalyticBridge.AnnulusRatioInsertions.Prism Portfolio
open RG.Supply Testing Push.PriceCompiler Input RG.Shoot Next.Scheduling MeasureTheory Spot Spot.Programme Notice
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {Z : ChartRatio G} {s : Sheet G} {K : MapPrices} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {w : ℕ → ℕ → ℝ} {b : ℕ → ℕ → Cafe} {C : ℕ → ℕ → Booth} {t : ℕ → ℕ → Menu} {a : Levels G}
    (h : Funded Z K b C t w W) (hp : Paid I a) (m p : ℕ) (T : Tube G (a.clock.op m p)) (u : Rep G (a.S.side (m+1) p))

include h hp in
lemma loaded : let j := a.clock.J (m+1); let i := a.clock.J m
    Enough (C j i) (b j i) (t j i) (Testing.query s K j i) Z (w j i) (a.clock.op m p).patch (a.clock.hatBeta m) :=
  ((h _ _ (hp.pays m) _ (step_paid a m) (first_le hp m)).bills _ rfl (block_eq hp m))

def desk : Desk G (a.clock.op m p) :=
  let e := loaded h hp m p; let j := a.clock.J (m+1); let i := a.clock.J m
  ⟨T,a.clock.hatBeta m,w j i,u,a.budget m,(b j i).r * fiery G (a.clock.hatBeta m) (a.S.block m),Z,(t j i).q,(t j i).q,
    e.rates.thermal.large,e.rates.thermal.frames.1⟩

structure Scanned {c f : Side} {S : StepData c f} (Q : Teller G) (b : Cafe) (C : Booth) (t : Menu) (d : Desk G S) : Prop where
  day : Day C.Q t.θ t.E d.out.order t.power d
  trip : Trip d C.W
  r4 : Medium C.paint G S.patch Q d.betaHat
  caller : Calling Q d.chart d.broadCut d.out.power b.r d.betaHat d
  ann : Ann b t Q S.patch.L d.W d.betaHat d.chart
  profile : d.profile=d.broadCut
  certifies : (∃ σ v Λ δ τ, d.input.Lawful σ v Λ δ τ) → Fits d.tube d.input d.betaHat →
    ∀ A F κ V, A.flags=RG.flags (temp d.betaHat) V →
    d.Valid ∧ Clearing (spectacle d A F κ) V ∧ Admitted A F d.betaHat V κ d.chart d.allocation d.radius

theorem scanned (hQ : (Testing.query s K (a.clock.J (m+1)) (a.clock.J m)).Funds (a.clock.op m p) T) (hu : u.beta∈band a (m+1)) :
    let j := a.clock.J (m+1); let i := a.clock.J m
    Scanned (Testing.query s K j i) (b j i) (C j i) (t j i) (desk h hp m p T u) := by
  intro j i; let d := desk h hp m p T u; let Q := Testing.query s K j i; let R := a.clock.op m p; let M := b j i
  have hr := loaded h hp m p
  have hc : Calling Q Z (t j i).q Q.below.power M.r (a.clock.hatBeta m) d := by
    refine ⟨by rw [add_comm]; exact a.fits.sizeT m p,hQ,rfl,?_ ,rfl,rfl,rfl,?_,rfl⟩
    · rw [show (a.clock.op m p).patch.L=a.S.block m from rfl]
      rw [show betaF G (a.clock.hatBeta m) (a.S.block m)=a.clock.hatBeta (m+1) from ?_]
      · exact hu
      rw [beta_eq hp m, block_eq hp m]
    change (s.profile i).power=(a.params m).power; rw [params_eq hp]
  obtain ⟨hd,hW⟩ := hr.all R rfl d hc
  have he : d.out.order=Q.below.order := congr_arg Stage.order (params_eq hp m)
  exact ⟨he.symm ▸ hd,hW,hr.r4, hc.powers ▸ hc,hr.rates,rfl,fun hL hF A F κ V hv => hd.certified hc hr.rates hL hF hv⟩

section directed
variable {P : PostCost D} (B : Input.Directed G I Z K P) (N : ℕ) (u : Rep G (B.a.S.side (m+1) p))

abbrev assigned := desk h B.valid m p (ships B N m p) u

theorem aboard (hm : m<N) (he : Lives B.bake N (m+1) p u) (hu : u.beta ∈ band B.a (m+1)) :
    let d := assigned h m p B N u; let j := B.a.clock.J (m+1); let i := B.a.clock.J m
    Scanned (Testing.query s K j i) (b j i) (C j i) (t j i) d ∧
      ∀ A F κ V, A.flags=RG.flags (temp d.betaHat) V →
        d.Valid ∧ Clearing (spectacle d A F κ) V ∧ Admitted A F d.betaHat V κ Z d.allocation d.radius := by
  have hx := scanned h B.valid m p (ships B N m p) u (proceeds B N m p hm) hu
  intro d j i
  exact ⟨hx,hx.certifies ⟨_,_,_,_,_,he.valid⟩ (SectorTools.ActualScalar.fits B N m p he)⟩
end directed

section clients
variable {c f : Side} {S : StepData c f} {Pt : Teller G} {b : Cafe} {C : Booth} {t : Menu} {d : Desk G S}
    (hx : Scanned Pt b C t d) {A : Stores S} {F : Forest S.ratio} {κ : S.Choices} {V : Config G c}
    {ι H R α β γ : Type} [Fintype ι] [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ]
    {X : Support c} {Ω : Set (Config G c)} {l : Viewport (spectacle d A F κ) X H R ι}
    {D' : (spectacle d A F κ).Slices} {b' : Finset ℕ} {q : Programme D' b'} {z : q.Run α β γ}
    (s' : Seats l z) {a' : Notice l} (B' : Reading a' z) (M : Income α β γ (H⊕R)) (o : Site c)
    (hr : ∃ σ w Λ δ τ, d.input.Lawful σ w Λ δ τ) (ht : Fits d.tube d.input d.betaHat) (hV : A.flags=RG.flags (temp d.betaHat) V)
include hx hr ht hV

omit hr ht [Fintype ι] [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] in
/-- Pay on the entire underlying charged physical alphabet at ANY bona fide enumeration
of the ratio paths (color-block rather than per-scalar exponent; encode a
whole ordered list into its Nat address, keeping the rest of its sector data).
Prevents an implicit requirement for a subset on which all long-but-nonzero
returns must be omitted in order to meet this capacity. Not constructing the
local/log/gate dictionary and not claiming a sum over sector variants.
-/
theorem Scanned.fits_all (F : Forest S.ratio) (κ : S.Choices) : let u := spectacle d A F κ; let v := C.Q.v
    let bound := v.top G S.patch d.betaHat
    Nonempty (Serial u.ActiveKey) ∧ At v u V d.out.order ∧
    (∀ (e : Serial u.ActiveKey) (i j : u.InKey), HasSum (Sseries u e V i j) (((u.C V)⁻¹-u.shiftGram V) i j)) ∧
    (2*bound + Arc.pinch C.Q.cap ≤ C.Q.cap⁻¹/8) ∧ ∀ i, Summable (v.audited d.betaHat A F G i) ∧ ∑' j, v.audited d.betaHat A F G i j ≤ bound := by
  intro u v bound
  obtain ⟨-,h⟩ := hx.day.capacity A F κ V hV
  have hl := hx.day.limits
  obtain ⟨f,hf⟩ := Countable.exists_injective_nat (Σ m, Tracks u.ActiveKey m)
  exact ⟨⟨fun _ _ => ⟨f,hf⟩⟩,h,Value.correct h rfl hl,hl.small,v.priced d.betaHat A F G rfl hl.paths⟩

omit [Fintype ι] in
theorem Scanned.sells : let k := d.out.order; let Q := C.Q; let u := spectacle d A F κ; let T := request s' Q M t.θ o k
    d.Valid ∧ u.Clearing V ∧
      T.rents.Lease ∧ (∀ i,T.watch i + ∑ j,T.hit j i ≤ T.capacity⁻¹/8) ∧
      0<T.eps ∧ (T.expose.Nonempty → 0<T.rooted) ∧
      (∀ z:Prices G (H⊕R), z∈triggered M.expose (JointLoad.bills u t.θ) → T.rents.Event z) ∧
      (Orders B' M s' Q.v t.θ (4*d.radius) Q.L o V k → B'.Clearance (4*d.radius) T.rents V (d.out.dirBound o) k) ∧
      ask d t.E t.power^M.expose.card * payoff T.rents ≤ saving d Q t.θ M.expose.card * stageCost T := by
  obtain ⟨hd,hC,-⟩ := hx.certifies hr ht A F κ V hV
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hx.day.pays s' M o
  exact ⟨hd,hC,h₀,h₂,h₃,h₁,fun z => (s'.enters _ _ hx.day.limits hx.day.beta hx.day.marked z).2.1, hx.day.admitted hC, hx.day.savings s' M o⟩

end clients
end YM.PhysicalNext.JointLoad.Clockwork
