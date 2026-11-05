import YM.Progress.DIRECTED_RECIPE.Bands

/-!
# Continuously firing the oven

Payment for all β values on the full surviving closed intervals, barriers and
nested shrinks as in Shoot.steps. Here maintain a stronger induction than
delivered by just `Directed.holding`: retain identities, information on the
WHOLE intervals (and wider where testing) at the various temperatures, and the
unassembled per-period plans on which they work. Not constructing Q by gluing
inputs at separate values. Meals assembled only for the *exact path* from the
same cost auctions. Uses existing barrier theorems of Shoot.Reach (outward
price and narrow selection). Does not assume output remains in the band at
the old endpoints! Works even when the level-zero barrier has equal endpoints.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe
open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Input Precision
open Next.Scheduling RG.Supply MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {a : Levels G} {M : Horizon a} {O : ChartRatio G}
    {k : Kin M O} {r : Permissions a} {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage}
variable {s : Survey G} {q : Quote} {v : ℕ → ℕ} {K : MapPrices} {D : Rolls (s.paper q v)}
    {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {mould : Beam K D}
variable {N m p : ℕ}

structure Tuning (a : Levels G) (p : ℕ) where
  lower : ℕ → ℝ
  upper : ℕ → ℝ
  factory : ∀ i, ℝ → Rep G (a.S.side i p)
  adjust : ℕ → ℝ → ℝ
  panels : ∀ i, Pipes G (a.S.side i p)
  taps : ∀ i, ℝ → Tap G (a.S.side i p)

def Tuning.knob (b : Tuning a p) (i) := Icc (b.lower i) (b.upper i)

/-- Data domain. Values/functions off the relevant levels/parameter domain are
arbitrary; equality prescriptions outside parameter intervals are conventions
for padding, not proofs of good reps there. `knob i` is still a range of β_N's,
not of β_i's. `record` keeps one raw dictionary and installation over each
WHOLE larger firing (`i+1`) interval. -/
structure Fired (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (r : Permissions a)
    (N m p : ℕ) (b : Tuning a p) : Prop where
  depth : m ≤ N
  bill : Menu k r N p (b.panels N) (b.taps N)
  pose : b.factory N = fun x => fromTop k N p x (b.panels N) (b.taps N x)
  init : b.lower N = floorBeta a N ∧ b.upper N = ceilBeta a N
  order i : m ≤ i → i ≤ N → b.lower i ≤ b.upper i
  bills i : m ≤ i → i ≤ N → Ingress k e F r N i p (b.factory i) (b.knob i) ∧
      (b.factory i (b.lower i)).beta=floorBeta a i ∧ (b.factory i (b.upper i)).beta=ceilBeta a i ∧
      MapsTo (fun x => (b.factory i x).beta) (b.knob i) (Icc (floorBeta a i) (ceilBeta a i))
  inside i : m ≤ i → i < N → b.knob i ⊆ b.knob (i+1)
  record i : m ≤ i → i < N → Draft k e F r N i p (b.factory (i+1)) (b.knob (i+1))
      (b.adjust i) (b.panels i) (b.taps i) ∧
      b.factory i=fun x => receive k N i p (b.factory (i+1) x) (b.adjust i x) (b.panels i) (b.taps i x)

namespace Menu
/-- Extend any given prepay top plan, not an independent invocation. -/
lemma first {X d} (h : Menu k r N p X d) (hg : G.Simple) (e F) :
    ∃ b : Tuning a p, b.panels N=X ∧ b.taps N=d ∧ Fired k e F r N N p b := by
  let u : Tuning a p :=
    { lower := floorBeta a, upper := ceilBeta a, adjust := 0
      panels := Function.update (fun i => drawer G _) N X
      taps := Function.update (fun i _ => ⟨0,0,0⟩) N d
      factory := Function.update (fun i (_ : ℝ) => trunk (k.path N i) (a.params i).clip (a.budget i)
        (drawer G _) ⟨0,0,0⟩ 0 0) N fun x => fromTop k N p x X (d x) }
  have ht : u.panels N=X := by simp only [u,update_self]
  have hu : u.taps N=d := by simp only [u,update_self]
  have hv : u.factory N=fun x => fromTop k N p x X (d x) := by simp only [u,update_self]
  obtain ⟨hx,hy⟩ := limits a hg N
  have he : u.knob N ⊆ band a N := hy
  refine ⟨u,ht,hu, ⟨le_rfl, by rw [ht,hu]; exact h, by rw [ht,hu]; exact hv, ⟨rfl,rfl⟩,
    fun i _ _ => (limits a hg i).1, ?_, fun _ a b => ((a.trans_lt b).false).elim, fun _ a b => ((a.trans_lt b).false).elim⟩⟩
  intro i hi Hi
  obtain rfl := Nat.le_antisymm hi Hi
  rw [hv]
  exact ⟨⟨h.starts.mono he, fun i h' => (h.engages e F).2 i (he h')⟩,rfl,rfl,fun _ H => H⟩
end Menu

/-- Retain earlier notebooks.

All calls from Q=factory
on the indicated *full* knob. -/
theorem refill (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) (hg : G.Simple) {b : Tuning a p}
    (hb : Fired k e F r N (m+1) p b) {X d Δ}
    (hv : Draft k e F r N m p (b.factory (m+1)) (b.knob (m+1)) Δ X d) :
    ∃ b' : Tuning a p, b'.panels m=X ∧ b'.taps m=d ∧ b'.adjust m=Δ ∧
      (∀ i, m < i → b'.panels i = b.panels i ∧ b'.taps i = b.taps i ∧ b'.adjust i = b.adjust i ∧
        b'.factory i=b.factory i ∧ b'.lower i=b.lower i ∧ b'.upper i=b.upper i) ∧
      Fired k e F r N m p b' := by
  let Z := b.knob (m+1)
  let B := prepared k e F r paid hM hT hk
  have hi : m < N := hb.depth
  obtain ⟨ig,hl,hu,w⟩ := hb.bills (m+1) le_rfl hi
  let f := fun x => receive k N m p (b.factory (m+1) x) (Δ x) X (d x)
  have hy := hv.returns ig paid tax hM hT hk
  have ht := hv.reload_all ig paid tax hk isCompact_Icc
  have ho x (hx : x∈Z) : (recipe k e F r).Relays N m p (f x) (b.factory (m+1) x) := B.links hi (hy x hx)
  have hm := hb.order _ le_rfl hi
  have he := (gates (ho _ (left_mem_Icc.mpr hm)) hg (Drifting.pay paid)).1 hl
  have hE := (gates (ho _ (right_mem_Icc.mpr hm)) hg (Drifting.pay paid)).2 hu
  obtain ⟨hz,H⟩ := limits a hg m
  obtain ⟨l,hh,u,hh',hL,hU,hX⟩ := narrow (f:=fun x => (f x).beta) hm ht.beta he.le hz hE.le
  have hs : Icc l u ⊆ Z := Icc_subset_Icc hh.1 hh'.2
  let b' : Tuning a p :=
    { panels := update b.panels m X, taps := update b.taps m d, adjust := update b.adjust m Δ,
      lower := update b.lower m l, upper := update b.upper m u, factory := update b.factory m f }
  have old (i) (h : m < i) : b'.panels i = b.panels i ∧ b'.taps i = b.taps i ∧ b'.adjust i = b.adjust i ∧
      b'.factory i=b.factory i ∧ b'.lower i=b.lower i ∧ b'.upper i=b.upper i := by
    dsimp only [b']; simp only [update_of_ne h.ne', and_self]
  have hN := old N hi
  have hq (i) (h : m < i) : b'.knob i=b.knob i := by
    unfold Tuning.knob; rw [(old i h).2.2.2.2.1,(old i h).2.2.2.2.2]
  refine ⟨b', update_self .., update_self .., update_self ..,old,hi.le, ?_,?_,
    ⟨hN.2.2.2.2.1.trans hb.init.1,hN.2.2.2.2.2.trans hb.init.2⟩,?_,?_,?_,?_⟩
  · rw [hN.1,hN.2.1]; exact hb.bill
  · simp_rw [hN.2.2.2.1,hN.1,hN.2.1]; exact hb.pose
  · intro i hj hn
    rcases eq_or_lt_of_le hj with rfl|hj
    · simp only [b',update_self]; exact hh'.1
    rw [(old i hj).2.2.2.2.1,(old i hj).2.2.2.2.2]; exact hb.order i hj hn
  · intro i hj hn
    rcases eq_or_lt_of_le hj with rfl|hj
    · dsimp only [b',Tuning.knob]
      simp only [update_self]
      refine ⟨⟨ht.mono hs, fun x hx => ⟨(hy x (hs hx)).bundle.loads, H (hX hx)⟩⟩,hL,hU,hX⟩
    rw [(old i hj).2.2.2.1,hq i hj,(old i hj).2.2.2.2.1,(old i hj).2.2.2.2.2]
    exact hb.bills i hj hn
  · intro i hj hn
    rw [hq (i+1) (by omega)]
    rcases eq_or_lt_of_le hj with rfl|hj
    · simp only [b',Tuning.knob, update_self]; exact hs
    rw [hq i hj]; exact hb.inside i hj hn
  intro i hj hn
  rw [(old (i+1) (by omega)).2.2.2.1,hq (i+1) (by omega)]
  rcases eq_or_lt_of_le hj with rfl|hj
  · dsimp only [b']; simp only [update_self]; exact ⟨hv,rfl⟩
  rw [(old i hj).1,(old i hj).2.1,(old i hj).2.2.1,(old i hj).2.2.2.1]
  exact hb.record i hj hn

lemma rolls (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) (hg : G.Simple) {X d} (hp : Menu k r N p X d)
    (H : ∀ m, m<N → ∀ l u : ℝ, l ≤ u → ∀ Q, Ingress k e F r N (m+1) p Q (Icc l u) →
      ∃ Δ X d, Draft k e F r N m p Q (Icc l u) Δ X d)
    (hm : m≤N) : ∃ b : Tuning a p,b.panels N=X ∧ b.taps N=d ∧ Fired k e F r N m p b := by
  induction hm using Nat.decreasingInduction with
  | self => exact hp.first hg e F
  | of_succ i hi ih =>
    obtain ⟨b,hX,hd,hb⟩ := ih
    obtain ⟨Δ,X',d',hx⟩ := H i hi _ _ (hb.order _ le_rfl hi) _ (hb.bills _ le_rfl hi).1
    obtain ⟨b',-, -, -, hh, ht⟩ := refill paid tax hM hT hk hg hb hx
    exact ⟨b',(hh N hi).1.trans hX,(hh N hi).2.1.trans hd,ht⟩

namespace Fired
variable {b : Tuning a p}

/-- All higher-step domains retain the parameters where a value is being used. -/
lemma series (A : Fired k e F r N m p b) {j} (hg : m ≤ j) (hh : j ≤ N) : b.knob m ⊆ b.knob j := by
  induction j, hg using Nat.le_induction with
  | base => exact subset_rfl
  | succ i hI ih => exact (ih (Nat.le_of_succ_le hh)).trans (A.inside i hI hh)

/-- At all parameters where it was fired, not merely the narrowed interval. -/
lemma move (A : Fired k e F r N m p b) (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) (i : ℕ) (hi : m ≤ i) (ht : i<N) :
    Curve (a.budget i) (b.factory i) (b.knob (i+1)) ∧
      ∀ x∈b.knob (i+1), (prepared k e F r paid hM hT hk).Move N i p (b.factory i x) (b.factory (i+1) x) := by
  obtain ⟨hu,hv⟩ := A.record i hi ht
  have hh := (A.bills (i+1) (hi.trans (Nat.le_succ _)) ht).1
  simp only [hv]
  exact ⟨hu.reload_all hh paid tax hk isCompact_Icc,hu.returns hh paid tax hM hT hk⟩

lemma top (A : Fired k e F r N m p b) (x : ℝ) : (b.factory N x).beta=x := by rw [A.pose]; rfl

lemma test (A : Fired k e F r N m p b) (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) (x : ℝ) (hh : x∈b.knob m) :
    let B := prepared k e F r paid hM hT hk
    let g := fun i => b.factory i x
    Competes B.bake p N m g ∧ ∀ i : ℕ, m ≤ i → i<N → B.Move N i p (g i) (g (i+1)) := by
  intro B g
  have hu i (hi : m ≤ i) (ht : i ≤ N) := (A.bills i hi ht).1.2 x (A.series hi ht hh)
  have hv (i : ℕ) (hi : m ≤ i) (ht : i<N) : B.Move N i p (g i) (g (i+1)) :=
    (A.move paid tax hM hT hk i hi ht).2 x (A.series (by omega) ht hh)
  refine ⟨⟨fun i hi ht => ?_, ?_, fun i hi ht => B.links ht (hv i hi ht)⟩,hv⟩
  · obtain ⟨h1,h2⟩ := hu i hi ht
    exact ⟨(h1.packed paid tax hk).lives,h2⟩
  have he := (hu N A.depth le_rfl).2
  rw [A.top] at he
  change (recipe k e F r).Starter N p (b.factory N x)
  rw [A.pose]
  exact starter (A.bill.law x he) he e F
end Fired

/-- One exact run, not choose arbitrary Selected separately. Use lower final
knob as the shooting point. -/
def seriesOf (a : Levels G) (J : ℕ → ∀ p, Tuning a p) (N p : ℕ) : Trail a p :=
  fun i => (J N p).factory i ((J N p).lower 0)

lemma fresh (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F))
    (J : ℕ → ∀ p,Tuning a p) (h : ∀ N p, Fired k e F r N 0 p (J N p)) :
    let B := prepared k e F r paid hM hT hk
    let f := seriesOf a J
    B.bake.Stays f ∧ (B.bake.make f).Selected ∧ ∀ N m p, m < N → B.Move N m p (f N p m) (f N p (m+1)) := by
  intro B f
  let R := B.bake.make f
  have hL N p : (J N p).lower 0 ∈ (J N p).knob 0 := (left_mem_Icc.mpr ((h N p).order 0 le_rfl (Nat.zero_le _)))
  have he N p := (h N p).test paid tax hM hT hk _ (hL N p)
  have hβ N p : R.β N p 0 = R.levels.clock.bar :=
      ((h N p).bills 0 le_rfl (Nat.zero_le _)).2.1.trans (by show floorBeta _ _ = a.clock.bar; simp [floorBeta])
  refine ⟨fun N p => (he N p).1,?_,fun N m p hi => (he N p).2 m (Nat.zero_le _) hi⟩
  have hl (N p m : ℕ) (h : m ≤ N) := ((he N p).1.prices m (Nat.zero_le _) h)
  have ht (N p m : ℕ) (h : m<N) : R.Transfer N p m := by
    have hh := (he N p).1.persists m (Nat.zero_le _) h
    exact ⟨hh.link,hh.drift⟩
  exact ⟨fun N p q m hm => (hl N p m hm).1.path.trans (hl N q m hm).1.path.symm, fun N p m h =>
    ⟨(hl N p m h).1.point,(hl N p m h).1.clip,(hl N p m h).1.valid,(hl N p m h).2⟩,
    fun N p => ⟨(he N p).1.fromTop.scalars,(he N p).1.fromTop.raw⟩, ht, hβ,trajectory R hβ ht⟩

/-- The physical estimates charged exactly as in `Bands`, at EVERY
cutoff and period. Based on Sect. Keep this `J` through
downstream deployments. -/
theorem design (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) (hg : G.Simple)
    (hp : Origins k r) (hw : Invoices k e F r) :
    let B := prepared k e F r paid hM hT hk
    (∀ N p, Bid.Oust B N p) ∧ B.Program ∧ ∃ J, (∀ N p, Fired k e F r N 0 p (J N p)) ∧
      B.bake.Stays (seriesOf a J) ∧ (B.bake.make (seriesOf a J)).Selected ∧
      ∀ N m p, m<N → B.Move N m p (seriesOf a J N p m) (seriesOf a J N p (m+1)) := by
  intro B
  choose X d h using fun i j => hp i j
  choose b hb hJ Hv using fun N p => rolls paid tax hM hT hk hg (h N p) (hw N p) (Nat.zero_le _)
  exact ⟨fun N p => Menu.shelves _ paid hM hT hk (Hv N p).bill,
    programs paid tax hM hT hk hp hw,b,Hv, fresh paid tax hM hT hk _ Hv⟩
end YM.Progress.DirectedRecipe
