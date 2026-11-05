import YM.Next.MULTISOURCE.Adjoining
import YM.Next.MULTISOURCE.Middle
import YM.Next.MULTISOURCE.Reach

/-!
# DESCEND with all mixed coefficients together
 -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Marker Function Filter Finset MeasureTheory Source Labels Mix
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

structure Locale (C : Family G) (d k : ℕ) (b : ℝ) (i : ℕ) : Prop where
  buckets : ∀ N p, i≤N → Room (C.path.rep N p i)
  adjacent : Adjoining C d i
  adept : Spot (C.path.levels.budget i)
  reservation : Maquette.room (C.localSection d) ≤ C.path.levels.clock.coverSize i
  budget (N p) : i≤N → ∀ v : C.label d,(C.labels.level d).coeffSize v ≤ b →
      width C 1 k i*Single.tariff C N p i v ≤ 1/8
  price : width C 1 k i * touch C d i * neighboring C i / width C 1 k (i+1) ≤ Real.exp (C.path.levels.clock.coverSize i /64:ℝ)

theorem sectioning (C : Family G) (d) (h : G.Simple) (H : C.Makes) (HT : Stock.Tabs C.path.levels)
    (he : Margins C.path.levels) (hs : Addresses C) (A : Responsive C d) :
    ∃ k : ℕ, ∀ b : ℝ, 0≤b → ∀ᶠ i in atTop, Locale C d k b i := by
  obtain ⟨k,hk⟩ := Wage.reception C h H he d
  refine ⟨k,fun b hb => ?_⟩
  let B := C.path.levels.clock.coverSize
  have hR : Tendsto B atTop atTop := Wage.ranges h _
  filter_upwards [hR.eventually Convoy.launch,hR.eventually_ge_atTop 8,hR.eventually_ge_atTop (Maquette.room (C.localSection d)),
    hs.2,hk b hb,A,Wage.feasible C h HT k d] with i hi h8 hu ha hf hp hj
  exact ⟨ha,hp,⟨h8,hi⟩,hu,hf,hj⟩

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} (C : Family G)
variable {d N i p m k j : ℕ} {b : ℝ}

abbrev Roll (R : Census V) (p j : ℕ) := Hot R → Pulse G (C.side j p)

structure Rolling {d p : ℕ} (C : Family G) (R : Census V) (v : V→C.label d) (o : ∀ j,V→Site (C.side j p))
    (k i N : ℕ) (D : ∀ j, Roll C R p j) : Prop where
  accepts (j : ℕ) : i ≤ j → j ≤ N → ∃ f : Hot R → ℝ, (∀ i,D j (Hot.one R i) = Single.one C N (d:=d) (p:=p) (j:=j) (v i) (o j i) ∧
      f (Hot.one R i) = Single.tariff C N p j (d:=d) (v i)) ∧
      Afield (C.path.rep N p j).p (money C.path.levels j) (o j) (D j) f (width C 1 k j)
  starts : D N=prepare (C.path.rep N p N) R (fun i => Single.cache C (d:=d) (N:=N) (p:=p) (v i) (o N i))
  exacts (j : ℕ) : i ≤ j → j < N → ∀ t : R.Mode, (fun U => (many (C.path.rep N p j) R (D j) U).part t)=
      ((touch C d j:ℂ)^t.val.card) • (C.path.levels.clock.op j p).push (C.path.β N p (j+1))
        (fun U => (many (C.path.rep N p (j+1)) R (D (j+1)) U).part t)


section
variable {C} (R : Census V) (H : C.Makes) {p : ℕ} (o : ∀ j,V→Site (C.side j p)) (v : V→C.label d)
    (hT : ∀ i,(C.labels.level d).coeffSize (v i)≤b)
include H hT

lemma breaks (he : C.ref d ≤ N) (hx : Locale C d k b N) (hh : Spaced (o N) (C.path.levels.clock.coverSize N))
    (ht : Mint (C.path.rep N p N) 2 (money C.path.levels N)) : ∃ D, Rolling C R v o k N N D := by
  let P := C.path.rep N p N
  let W i := Single.cache C (N:=N) (p:=p) (d:=d) (v i) (o N i)
  have h (i : V) := Single.verify_cache H (v i) (o N i) he hx.reservation
  let Y := prepare P R W
  have e := (H.wilson.represents N p N le_rfl).vac
  have hs : Spaced (o N) P.p.B := by unfold P; rw [e]; exact hh
  have hi : Spot P.p := by rw [show P.p=_ from e]; exact hx.adept
  obtain ⟨g,hg,hH⟩ := startups P W R (o N) (p:=fun i => Single.tariff C N p N (v i))
    (b:=fun i => Single.ankle C N p N (v i)) (m:= (C.localSection d).stencil.card) h
    (H.wilson.represents N p N le_rfl).good.labels (money_accepted ..).1 (money_accepted ..).2 ht hs hi
    (Wage.width_positive C N k) (fun i => hx.budget N p le_rfl (v i) (hT i))
  let D := Function.update (fun (j : ℕ) => (0:Roll C R p j)) N Y
  refine ⟨D,⟨?_,Function.update_self ..,fun i hi hj => False.elim (by omega)⟩⟩
  intro j hj he; obtain rfl := le_antisymm hj he
  unfold D; rw [Function.update_self]; refine ⟨g,fun i => ?_, hH⟩
  exact ⟨(birth_copy P W R i).trans (Single.initialized (v i) (o N i)).symm, hg i⟩

lemma rolling (hF : C.ref d ≤ i) (hi : i ≤ N) (he : ∀ m,i≤m → m≤N → Locale C d k b m)
    (ht : Mint (C.path.rep N p N) 2 (money C.path.levels N))
    (hh : ∀ m, i ≤ m → m ≤ N → Spaced (o m) (C.path.levels.clock.coverSize m))
    (hz : ∀ m : ℕ, i ≤ m → m < N → ∀ x,
      (C.path.levels.clock.op m p).ratio.embed (o m x)=o (m+1) x) :
    ∃ D, Rolling C R v o k i N D := by
  induction hi using Nat.decreasingInduction with
  | self => exact breaks R H o v hT hF (he _ le_rfl le_rfl) (hh _ le_rfl le_rfl) ht
  | of_succ i hi ih =>
    obtain ⟨Y,hY⟩ := ih (hF.trans (by omega)) (fun m hm => he m (by omega)) (fun m hm => hh m (by omega))
      (fun m hm => hz m (by omega))
    obtain ⟨g,hg,hP⟩ := hY.accepts (i+1) le_rfl hi
    let A := C.path.levels
    let S := A.clock.op i p
    let P := C.path.rep N p i
    let Q := C.path.rep N p (i+1)
    let f (x) := Single.one C N (v x) (p:=p) (j:=i) (o i x)
    let p' (x) := Single.tariff C N p i (d:=d) (v x)
    have hf := (H.wilson.represents N p i hi.le)
    have hQ := (H.wilson.represents N p (i+1) hi)
    have hI : i ≤ i := le_rfl
    have hL := he i hI hi.le
    have hU := hh i hI hi.le
    have hB : P.p=A.budget i := hf.vac
    have ht : Spot P.p := hB.symm ▸ hL.adept
    have hM : Spaced (o i) P.p.B := hB.symm ▸ hU
    have hop : S.ratio.embed ∘ o i=o (i+1) := funext (hz i hI hi)
    have hA : Afield Q.p (money A (i+1)) (S.ratio.embed ∘ o i) (Y (i+1)) g _ := hop.symm ▸ hP
    have hJ x : tangent P (f x)=(touch C d i:ℂ) • S.push Q.beta (tangent Q (Y (i+1) (Hot.one R x))) := by
      rw [(hg x).1, ← congr_fun hop x]
      have he := Single.higher H (v x) (o i x) hi hF
      unfold touch
      push_cast; exact he
    have hG := hL.adjacent N p hi V R (o i) hU v (Y (i+1)) g hA.present
      (fun x => ⟨(hg x).1.trans (congrArg (Single.one C (p:=p) N (v x) (j:=i+1)) (congrFun hop x).symm), (hg x).2⟩)
    obtain ⟨D',k',hK,hW,hv'⟩ := move_book (o i) (Y (i+1)) g _ _ _ _ _ _ f p' hf.good.labels hQ.good
      (A.transition_mass ..) ((H.wilson.steps N p i hi).1) hM ht (touch_pos ..) (Real.exp_pos _).le
      (Wage.width_positive C (i+1) k) (Wage.width_positive C i k) (money_accepted ..).1
      (show width C 1 k i * touch C d i * neighboring C i / width C 1 k (i+1) ≤ Real.exp (P.p.B / 64 : ℝ) by rw [hB]; exact hL.price)
      (fun x => ⟨hL.budget N p (by omega) (v x) (hT x), Single.one_credit H (v x) (o i x) hi hF hL.reservation⟩) hA
      hJ hG
    · refine ⟨Function.update Y i D', ⟨?_,?_,?_⟩⟩
      · intro j hj he; rcases eq_or_lt_of_le hj with h|h
        · subst j; simp only [Function.update_self]; exact ⟨k',hK,hW⟩
        rw [Function.update_of_ne (Ne.symm h.ne)]; exact hY.accepts _ h he
      · rw [Function.update_of_ne (Ne.symm hi.ne)]; exact hY.starts
      intro j hj hl v
      rcases eq_or_lt_of_le hj with h|h
      · subst j; rw [Function.update_self,Function.update_of_ne (show i+1≠i by omega)]
        exact hv' v
      rw [Function.update_of_ne (Ne.symm h.ne),Function.update_of_ne (show j+1≠i by omega)]; exact hY.exacts _ h hl v
end
end YM.Multi
