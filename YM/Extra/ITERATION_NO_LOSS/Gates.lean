import YM.Extra.ITERATION_NO_LOSS.Determinant
import YM.Extra.ITERATION_NO_LOSS.Post


/-!
# Local inputs to the arbitrary-depth unmasked iteration

Exact remaining top/high-jet and pure determinant hypotheses, not even
vStep.

Needed with pre/post constants chosen in the order given in Pre,
including `U` from free/frame/slot-width-type information **not** by running
one trial through many steps and taking minima.

The type is specialized
to the actual clocks/Horizon; call only where all the receipts (paid etc.)
were already established on them.

Both choices of
indices as output, and arbitrary input depth (including repeated equal indices)
on the chosen calendar, need independent estimates.

See report.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG RG.Supply Precision Pressure Tree Bloch Bid Craft Input Calibration Inherited
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {P : Sheet G} {D : Rolls P} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G}

abbrev Branch (a : Levels G) (m : ℕ) := ∀ (p : ℕ) (F : Forest (a.clock.op m p).ratio), Dir G (a.S.side m p) → AxisChart G F

structure Ticket (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (N m : ℕ) (T : PathData G) : Prop where
  rooted : Aligned T (M.H N m)
  funded : T.Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m)
  cube : Charged T.cubic (a.params m).width (A.cap U K (a.clock.J m))
  quartic : Charged T.quartic (a.params m).width (A.cap U K (a.clock.J m))

structure OnShell (M : Horizon a) (Q : PostCost D) (N m : ℕ) (T : PathData G) (ρ : Branch a m) : Prop where
  gap (p F) : PriceGap F (a.params (m+1)).clip T (S:=(a.clock.op m p)) (Q.η (a.clock.J (m+1)))
  critical p F : Critical F (a.params (m+1)).clip T (S:=(a.clock.op m p)) (ρ p F)
  guessed p F : Guessed F (installed (a.clock.op m p).ratio (M.towers N m).A0) (S:=(a.clock.op m p)) (ρ p F)
  quadratic p F : HeatG F (a.params (m+1)).clip T (S:=(a.clock.op m p)) (ρ p F) (M.H N m)

abbrev inherit (M : Horizon a) (n m : ℕ) {k : ℕ} (T : ℕ → Atom G k) := Inherited.classicalPart (M.H n (m+1)) (M.H n m) (M.towers n m) T
abbrev inheritLoop (M : Horizon a) (n m : ℕ) (T : ℕ → Atom G 2) := Inherited.loopPart (M.H n (m+1)) (M.H n m) (M.towers n m) T

def rem3 (A r3 : ℝ) (L : Side) := A*(1+r3/(L.val:ℝ)^2)
def rem4 (A r3 r4 : ℝ) (L : Side) := A*(1+r3/(L.val:ℝ)^2+(r3/(L.val:ℝ)^2)^2+r4/(L.val:ℝ)^4)

/-- Local *dynamical* problems still to be solved (beyond the lower jet, IFT
germ, inherited and aperture gates).

Using canonical `rooted` and transmitted
paths for its consumers.

All stationarity and determinant readouts tested
on the actual physical score/Haar-ratio expressions with the full channel
choices.

No alpha needed for the inherited calculation; it is the *fresh*
problem that still needs the kinetic term and its right sign/pre-L bound.

A
solution in another path convention or only on a favorable period need not
fill this interface.

Requests permit choosing a forest and a tag for each
p, but the emitted relative tensors (and the correction itself, including the
alpha) are independent of p.

`j` here means stage not level.

This is on the
zero-kinetic-insertion setting, no quantitative continuation assumed from
finite fixed-field Taylor identities. -/
structure Rates (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (H : QuantumCosts)
    (Q : PostCost D) (O : ChartRatio G) : Prop where
  initial (N : ℕ) : ∃ (t : ℕ → Atom G 3) (v : ℕ → Atom G 4), SymmetricAtoms t ∧ SymmetricAtoms v ∧
    Charged t (a.params N).width (A.top (a.clock.J N)) ∧ Charged v (a.params N).width (A.top (a.clock.J N)) ∧
    ∀ p j, 3 ≤ j → j ≤ 4 → jet j (main (bundle (M.H N N) t v (fun _ => blank G 2)) (n:=a.S.side N p) (a.params N).clip)=
      jet j (Wilson.energy ∘ represent)
  classicalPart (N m : ℕ) (T : PathData G) (ρ : Branch a m) : m < N → Ticket M K U A N (m+1) T → OnShell M Q N m T ρ →
    ∀ r3 r4, Charged T.cubic (a.params (m+1)).width r3 → Charged T.quartic (a.params (m+1)).width r4 →
    let B := A.fresh (a.clock.J (m+1)) (a.clock.J m)
    ∃ t v, SymmetricAtoms t ∧ SymmetricAtoms v ∧ Charged t (a.params m).width (rem3 B r3 (a.S.block m)) ∧
      Charged v (a.params m).width (rem4 B r3 r4 (a.S.block m)) ∧ ∀ p, ∃ F e,
      Fresh (S:=a.clock.op m p) F e T (bundle (M.H N m) (join t (inherit M N m T.cubic))
        (join v (inherit M N m T.quartic)) T.loop) (a.params (m+1)).clip (a.params m).clip (ρ p F) t v
  quantum (N m : ℕ) (T : PathData G) (ρ : Branch a m) : m < N → Ticket M K U A N (m+1) T → OnShell M Q N m T ρ →
    let j := a.clock.J (m+1); let L := a.S.block m
    ∃ (α : ℝ) (v : ℕ → Atom G 2), SymmetricAtoms v ∧ Silent v ∧ Charged v (a.params m).width (H.det j (a.clock.J m)*(L.val:ℝ)^4) ∧
      |α + G.slopeConstant * Real.log L.val| ≤ H.slope j (a.clock.J m) ∧ ∀ p, ∃ F e,
        FreshDet (S:=a.clock.op m p) F e T (bundle (M.H N m) T.cubic T.quartic v) (a.params (m+1)).clip (a.params m).clip (ρ p F) O α (Q.Γ j) (Q.c j)

variable {M : Horizon a} {K : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts} {Q : PostCost D} {O : ChartRatio G}

lemma cap_loop_ge (m : ℕ) : (1:ℝ) ≤ a.clock.loopCap m := by
  refine one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_rpow ?_ (a.fits.thetaRange m).1.le)
  exact Real.one_le_exp (sq_nonneg _)

variable (hc : Before P U A H K) (hm : M.Suffices K)

include hm hc
lemma make_ticket (hS : a.clock.stage = P.profile) (n m : ℕ) (he : m ≤ n) (T : PathData G)
    (h : Aligned T (M.H n m)) (h2 : SymmetricAtoms T.loop) (h3 : SymmetricAtoms T.cubic) (h4 : SymmetricAtoms T.quartic)
    (ht : Silent T.loop) (hp : Charged T.loop (a.params m).width (a.clock.loopCap m))
    (hj : Charged T.cubic (a.params m).width (A.cap U K (a.clock.J m))) (hk : Charged T.quartic (a.params m).width (A.cap U K (a.clock.J m))) :
    Ticket M K U A n m T := by
  refine ⟨h,Aligned.bound (A:=K.Ω (a.clock.J m)) h (a.params m).width_pos (fun i j => ?_) (hm.all n m he) hp hj hk ht h2 h3 h4 (a.params m).paths ?_ ?_ ?_,hj,hk⟩
  · exact ((hm.rows n m he).2.2.2.1 i j).mono (by unfold Levels.params Calendar.params; rw [hS]; exact hc.roots _) le_rfl
  all_goals unfold Levels.params Calendar.params; rw [hS]; first | exact hc.row _ | exact hc.curves _

omit hc hm in
lemma smaller_towers {L : Side} {T : Towers L} {η σ C : ℝ} {k : ℕ} (h : T.Deep η C k) (he : σ ≤ η) : T.Deep σ C k := by
  obtain ⟨h1,h2,h3,h4⟩ := h
  exact ⟨fun i j => (h1 i j).mono he le_rfl,fun i j => (h2 i j).mono he le_rfl,fun i j => (h3 i j).mono he le_rfl,
    fun l hl => ⟨fun i j => ((h4 l hl).1 i j).mono he le_rfl,fun i j => ((h4 l hl).2 i j).mono he le_rfl⟩⟩

structure Provision (M : Horizon a) (U : Apertures) (A : ClassicalCosts) (K : MapPrices) (N m : ℕ) : Prop where
  early : Early U A K (a.params (m+1)) (a.clock.J (m+1)) (a.clock.J m) (a.S.block m)
  high : ((M.H N (m+1)).dual_diag).strip (U.clear K (a.clock.J (m+1)) (a.clock.J m)) (K.Ω (a.clock.J (m+1)))
  low : ((M.H N m).diagonal).strip (U.clear K (a.clock.J (m+1)) (a.clock.J m)) (K.Ω (a.clock.J m))
  tower : (M.towers N m).Deep (U.clear K (a.clock.J (m+1)) (a.clock.J m)) (K.Ω (a.clock.J (m+1))) (a.clock.J (m+1)-2)
  width : (a.params m).width ≤ U.clear K (a.clock.J (m+1)) (a.clock.J m)

lemma provision (hp : Paid I a) (N m : ℕ) (he : m < N) : Provision M U A K N m := by
  have h1 := a.fits.mono (Nat.le_succ m); have h2 := a.fits.stepSlow m
  have hh : ∀ i, a.params i = P.profile (a.clock.J i) := fun i => congr_fun hp.stage _
  refine ⟨hh (m+1) ▸ hc.enough _ _ _ h1 h2 (by rw [block_eq hp]; exact (D.large _).need),fun i j => ?_,fun i j => ?_,?_,
    ?_⟩
  · exact ((hm.rows N (m+1) he).2.2.2.2 i j).mono ((min_le_left ..).trans (min_le_left ..)) le_rfl
  · exact ((hm.rows N m he.le).1 i j).mono ((min_le_left ..).trans (min_le_right ..)) le_rfl
  · exact smaller_towers (hm.costs N m he) ((min_le_left ..).trans (min_le_left ..))
  rw [hh m]
  have hx := ((hc.port _ _ h1 h2).trans (U.port_clear ..)); linarith only [hx, (P.profile (a.clock.J m)).width_pos]
end YM.Extra.Iteration
