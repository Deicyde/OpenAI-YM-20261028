import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Extra.SOURCE_HISTORIES.Song


/-!
# RPaper → RMakes on one supplied Bolt (conditional new producer)

This is a pointwise
`PaidAtom` socket at each m (not one already-selected coherent source output),
and top Shelf.

No assumption of coherence+existence of column families/their
inverses/own estimates; proved here.

All arithmetic typed on the very same
Bolt, and one sufficient numerical prepayment theorem.

This text does **not**
claim construction of an unmarked trajectory or satisfaction of the gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Issue
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion Next.Foundations Doors
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (H : History G)

/-- Sufficient references. Don't silently adjust after this stage. Also
works with given deeper references (sufficiency theorems use the inequality).
-/
theorem choose_reference (K : Levels G) : ∃ r : ℕ → ℕ, ∀ d, d+3≤K.clock.J (r d) := by
  choose r hr using fun d : ℕ => (K.fits.deep.eventually_ge_atTop (d+3)).exists
  exact ⟨r,hr⟩

variable (W : Worth) (C : ℕ → ℝ) (Y : ∀ N p, Shelf (H.rep N p N).activities) (r : ℕ → ℕ)

theorem refer (h : Budget H.levels C W) (hv : ∀ d, d+3≤H.levels.clock.J (r d)) :
    RefLi H (frames G) (localSection G) (hol G) r := by
  have he (d m) (hm : r d ≤ m) : d+3 ≤ H.levels.clock.J m := le_trans (hv d) (H.levels.fits.mono hm)
  refine refLi G H r (fun d => ⟨hv d, fun m hm => ⟨?_,?_⟩⟩) ?_ (fun _ N _ => h.sectionBudget N)
  · exact le_trans (by omega : d+1 ≤ d+3) ((he d m hm).trans (h.stage m).1)
  · exact le_trans (by omega : d ≤ d+3) ((he d m hm).trans (h.stage m).2)
  intro d N p hr
  exact (h.sequences N d (by have := he d N hr; omega)).lengths p

/-- E / cost convention in
`LocalDebt`.

The Heading/equivariant-map prediction is accountable by the
stated direction estimates at actual masked columns. η purchase needs local
proof EVER sufficient after anticipative pre/post-L constraints; here the
exact premise on given history not an assertion such schedule can be bought. -/
def PerBlock : Prop := ∀ d N p m : ℕ, r d ≤ m → m<N →
    ∃ T : Heading ((frames G).level d), AtomStep (localSection G d) H N p m (hol G) T
      (C (H.levels.clock.J (m+1))) (rate (H.S.block m))

/-- The printed transfer with receipts traceable to choices from `Music`,
so a next campaign can retain the same histories, note labels etc. No coherence
of DIFFERENT bare cutoffs' Music asserted (A stage estimates only on their
own bolt path). -/
structure Printed (T : ∀ d N p : ℕ, TransferData ((frames G).level d) H N p) : Prop where
  terms : Budget H.levels C W
  reads : RefLi H (frames G) (localSection G) (hol G) r
  issued : (Family.mk H (hol G) (frames G) (localSection G) r T).Makes
  traces d N p : r d ≤ N → ∃ M : Music ((frames G).level d) H N p,
    M.tone N=topVoice (localSection G d) H N p (Y N p) d ∧
    Sung (localSection G d) H N p (hol G) W (r d) M ∧
      (T d N p).entries = (M.draft H).inits -- stronger estimates on those entries

/-- No assumption of Paper.Clocks, not even assuming the source top
representation exists. Use production library at exact chosen label sections. -/
theorem press (hp : H.Selected) (h : Budget H.levels C W) (hr : ∀ d, d+3 ≤ H.levels.clock.J (r d))
    (hc : PerBlock H C r) : ∃ T, Printed H W C Y r T := by
  have he (d m) (hm : r d ≤ m) : d ≤ H.levels.clock.J m :=
    (by omega : d ≤ d+3).trans ((hr d).trans (H.levels.fits.mono hm))
  have hh := refer H W C r h hr
  have issue (d N p) : ∃ T : TransferData ((frames G).level d) H N p, r d ≤ N →
      T.Based (hol G) (localSection G d) (r d) ∧ ∃ M : Music ((frames G).level d) H N p,
        M.tone N=topVoice (localSection G d) H N p (Y N p) d ∧
          Sung (localSection G d) H N p (hol G) W (r d) M ∧ T.entries=(M.draft H).inits := by
    by_cases ht : r d ≤ N
    · let B := localSection G d
      have hx := onTop B H N p (hol G) hp (sound G d) (Y N p) d (cameras_ge G d) (fun i => cameras_holds G d _ i 0)
        ((h.sequences N d (he d N ht)).receipts p 0)
      obtain ⟨M,hM,hS⟩ := pursue B H N p (hol G) W hp h.room h.bank (r d) ht _ hx fun i hi ht =>
        let ⟨T,hT⟩ := hc d N p i hi ht; ⟨_,_,T,h.fits H rfl i d (he d i hi),hT⟩
      obtain ⟨T,hU,hT⟩ := Work.G08.answer W H h.room h.bank N p d (r d) _ (M.draft H) B _
        (Sung.clocks B H N p (hol G) W _ M hS)
      exact ⟨T,fun _ => ⟨hT,M,hM,hS,hU⟩⟩
    exact ⟨⟨fun _ v => primary 0 v,LinearEquiv.refl ℂ _⟩, fun u => False.elim (ht u)⟩
  choose T hT using issue
  refine ⟨T,h,hh,⟨hp,hh.gets,hh.order,hh.fits,?_,fun d N p ht => (hT d N p ht).1⟩,
    fun d N p ht => (hT d N p ht).2⟩
  intro d N p hr
  exact fun o v => hh.loaded d N hr _ rfl rfl _ o v

open RG.Supply RG.Shoot Org
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D}

/-- Name the originating path. -/
abbrev trail (V : Bolt A) := A.B.bake.make V.history

theorem bolt (V : Bolt A) (L : Budget (trail V).levels C W) (Y : ∀ N p, Shelf ((trail V).rep N p N).activities)
    (h : ∀ d, d+3 ≤ (trail V).levels.clock.J (r d)) (hb : PerBlock (trail V) C r) :
    ∃ T, Printed (trail V) W C Y r T ∧
      Spec.Calibrated (Family.mk (trail V) (hol G) (frames G) (localSection G) r T) := by
  obtain ⟨T,hT⟩ := press (trail V) W C Y r V.choice L h hb
  exact ⟨T,hT,M.p,D,A.θ,A.delay,A.bar,A.asks,M.O,M.K,A.post,A.B,V.history,V.sticks,rfl,V.moves⟩

/-- Numerical thresholds operate on the *same* chosen Alloy/Bolt. This
consumer retains them inside `Printed`: β-entrance uses its DELAYS, not
"delay again at readout". Still conditional. -/
theorem activate (M : Metals G) (hM : Plans M.p C W) :
    ∃ a : ℕ → ℕ, ∃ b : ℕ → ℝ, ∀ c : ℕ → ℕ, a ≤ c →
    let K := {M with p:={M.p with floorL:=c}}
    ∀ (D : Rolls K.p) (A : Alloy K D) (V : Bolt A), b ≤ A.delay.betaEntry →
    ∀ Y : ∀ N p, Shelf ((trail V).rep N p N).activities,
    ∃ r : ℕ → ℕ,(∀ d, d+3≤(trail V).levels.clock.J (r d)) ∧
    (PerBlock (trail V) C r → ∃ T, Printed (trail V) W C Y r T ∧
      Spec.Calibrated (Family.mk (trail V) (hol G) (frames G) (localSection G) r T)) := by
  obtain ⟨a,b,he⟩ := Doors.afford M.p C W hM
  refine ⟨fun j => max (M.p.floorL j) (a j), b,?_⟩
  intro c hc K D A V hd Y
  obtain ⟨r,hr⟩ := choose_reference (trail V).levels
  refine ⟨r,hr,fun hb => bolt W C r V ?_ Y hr hb⟩
  apply he c (fun j => (le_max_right ..).trans (hc j)) D
  · exact A.B.valid.lengths
  · exact A.B.valid.stage
  intro i
  exact (hd _).trans (A.B.valid.pays i)

end YM.Extra.Histories.Issue
