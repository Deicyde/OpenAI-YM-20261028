import YM.Next.SCHEDULE.Post
import YM.Work.I01
import YM.Work.I02
import YM.Work.I03
import YM.Work.I04

/-!
# Paid levels: numerical gates at every step

Apply contractual prices to ACTUAL Levels; same Beam and pinned kernel
for every call. Still no assertion that the procedure supplies a Rack or
any iterative RG data. Quantifiers below include startup at N=0 (level-0
funding is why both first stages must match).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter RG RG.Supply Function Precision Input Bid Pressure Lattice Source
open scoped Topology

namespace Deployment
variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {B : Beam K D} {F : ℕ → ℕ → Postage}

lemma adj (a : Levels G) (m : ℕ) : Adj (a.clock.J (m+1)) (a.clock.J m) :=
    ⟨a.fits.mono (by omega),a.fits.stepSlow _⟩

lemma params (h : Paid I a) (m : ℕ) : a.params m=s.melt q (a.clock.J m) := congr_fun h.stage _

lemma block (h : Paid I a) (m : ℕ) : a.S.block m=D.L (a.clock.J (m+1)) := (a.fits.sameFactor _).symm.trans <| congr_fun h.lengths _

lemma learns (h : Paid I a) (g : Prepaid s K q e v) (m : ℕ) :
    Buy s q (e (a.clock.J (m+1)) (a.clock.J m)) (a.clock.J (m+1)) (a.clock.J m) (a.S.block m).val := by
  rw [block h m]; exact g.each D _ _ (adj a _)

lemma pulse (h : Paid I a) (p : Regime B e F W) (m : ℕ) :
    let j:=a.clock.J (m+1); let i:=a.clock.J m; let L:ℝ := (a.S.block m).val
    BandGate s q (e j i) Instrument.plain (F j i) j i L (a.clock.theta j) (a.clock.theta i) ((B.price F).g j)
      (G.slopeConstant*Real.log L) (a.clock.hatBeta m) := by
  intro j i L; unfold L; rw [block h m, h.theta]; exact (p.all _ _ (adj a _) _ (h.pays _)).1

lemma hat (m : ℕ) : a.clock.hatBeta m + G.slopeConstant*Real.log (a.S.block m).val=a.clock.hatBeta (m+1) := by
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]; unfold Levels.S; ring



lemma period (h : Paid I a) (m p : ℕ) : W.shells (a.clock.J (m+1)) ≤ (a.S.side m p).val := by
  apply le_trans ?_ (h.volume m p); apply Nat.le_mul_of_pos_right; positivity



lemma step_larger (h : Paid I a) (p : Regime B e F W) (m n : ℕ) : Larger (a.clock.op m n) (G:=G) := by
  refine ⟨(a.blocks m n).branches,?_,?_⟩
  · apply le_trans ?_ (Nat.mul_le_mul_left (a.S.period n).val (a.S.den_strict.monotone (Nat.le_succ m)))
    apply le_trans ?_ (period h m n)
    let j:=a.clock.J (m+1); have he := (p.big j).1
    apply le_trans ?_ he
    change 100*((j+3)*(a.S.block m).val+4*(a.S.block m).val) ≤ _
    rw [block h m]; exact Nat.le_add_right _ _
  apply lt_of_lt_of_le _ (le_trans (p.big _).1 (period h m n)); unfold required; omega

lemma funds (h : Paid I a) (g : Prepaid s K q e v) : Bank q.finish.W a ∧ roomCost a q.finish.W :=
  g.cash D _ h.stage h.lengths

lemma metered {C : Family G} (hL : C.path.levels=a) (hG : G.Simple)
    (h : Paid I a) (p : Regime B e F W) (hE : C.Makes)
    (hC : ∀ d (r : ℝ),0<r → Mix.Circle C d r) : Metered C := by
  have hM : Mix.paidL C := by intro i; rw [hL,params h i]; exact s.factorial q _
  exact Bid.installs hG Work.I01.answer Work.I02.answer Work.I03.answer Work.I04.answer hE hM
    (hL.symm ▸ Stock.consumes h p.prices) hC

lemma offers (h : Paid I a) (g : Prepaid s K q e v) :
    ∀ C : Horizon a, Craft.Rack a s.X C → ∃ H : Horizon a, Retained H C ∧ H.Suffices K :=
  g.pins _ h.stage h.kernel

/-- η(B) released before trying to solve recursion. Propagate the *same*
towers, including floor choice. Conditional calls accept any W with the needed
attachment and width retained at BandGate. -/
lemma scene (h : Paid I a) (p : Regime B e F W) (m n N : ℕ) (hk : m < N) (H : Horizon a)
    (ht : H.Suffices K) (P : PathData G) (hP : P.Bounds (a.params (m+1)).clip (a.params (m+1)).width
      (a.params (m+1)).paths (a.clock.loopCap (m+1))) (H1 : Attached (H.H N (m+1)) P)
    (H2 : Sworn (H.H N (m+1)) (a.S.side (m+1) n) G) :
    let j:= a.clock.J (m+1); let S:=a.clock.op m n; let c:=(a.params (m+1)).clip
    ∀ U : Tree.Forest S.ratio,
      PriceGap U c P ((B.price F).η j) ∧ ∃ ρ, Critical U c P ρ ∧
        Guessed U (Bloch.installed S.ratio (H.towers N m).A0) ρ ∧ HeatG U c P ρ (H.H N m) := by
  intro j S c U
  exact B.uses j _ _ S h.kernel (block h m) rfl (step_larger h p m n) U (H.H N (m+1)) (H.H N m) c (a.params m).clip P
    _ _ _ _ _ _ _ (ht.crossings N m n hk) (ht.all N (m+1) hk (a.S.side (m+1) n)) hP H1 H2
      (ht.all N m hk.le (a.S.side m n))

open Finset in
lemma exposure (h : Paid I a) (p : Regime B e F W) (d m : ℕ) (hh : Admits s.requests (a.clock.J m) d)
    (n : ℕ) : ∀ x ∈ (s.B.entry d).stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ (a.S.side m n).val := by
  intro x hx i
  have he : 20*((x i).natAbs+1) ≤ entrance s (a.clock.J m) := by
    let F (x : Cover) := univ.sup (fun i : Axis => 20*((x i).natAbs+1))
    have hp : 20*((x i).natAbs+1) ≤ F x := le_sup (f:=fun i => 20*((x i).natAbs+1)) (mem_univ i)
    exact le_trans (hp.trans (le_sup hx)) (le_sup (s:=range (a.clock.J m+1))
      (f:=fun d => (s.B.entry d).stencil.sup F) (mem_range.mpr (by have := hh.1; omega)))
  refine (he.trans (p.big _).2).trans ?_
  cases m with
  | zero => rw [h.firstZero,← h.firstOne]; exact period h 0 n
  | succ m => exact (period h m n).trans (Nat.mul_le_mul_left _ (a.S.den_strict.monotone (Nat.le_succ m)))

/-- Choose first m admitting d, not period-dependent. Reference exposures
for ALL finer N. Weak uses can insist on levels on plateau already admitting
the requests (`refAt` consequence below). -/
lemma refAt (h : Paid I a) (p : Regime B e F W) : ∃ r : ℕ → ℕ,
    (∀ d m,r d ≤ m ↔ Admits s.requests (a.clock.J m) d) ∧
    ∀ H : History G, H.levels = a → RefLi H s.B.frames s.B.entry s.B.hol r := by
  classical
  have hx (d) : ∃ m, Admits s.requests (a.clock.J m) d :=
    (a.fits.deep.eventually (Need.exhaust _ d)).exists
  let r := fun d => Nat.find (hx d)
  have he (d) : Admits s.requests (a.clock.J (r d)) d := Nat.find_spec (hx d)
  have hf d (N : ℕ) : r d ≤ N ↔ Admits s.requests (a.clock.J N) d :=
    ⟨fun hu => (he d).later (a.fits.mono hu), fun hu => Nat.find_min' (hx d) hu⟩
  refine ⟨r,hf,fun H hm => ⟨s.B.sound,fun d => ?_,fun d N p' hN => ?_,fun d N hk => ?_⟩⟩
  · rw [hm]; refine ⟨(he d).1,fun i hi => ?_⟩
    rw [params h]; exact s.o.eng _ d ((hf d _).1 hi)
  · unfold History.S; rw [hm]; exact exposure h p d N ((hf d _).1 hN) _
  rw [hm]; dsimp only [Levels.budget]; rw [params h]; exact s.credit q d _ ((hf d _).1 hk)
end Deployment
end YM.Next.Scheduling
