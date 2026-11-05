import YM.Extra.SOURCE_HISTORIES.Counter
import YM.MergeProof.Accord
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Relay
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G) (W : Worth) (M : Music F H N p)

open PhysicalNext.Repeat Lotus YM.MergeProof
set_option quotPrecheck false
variable (D:∀ i:ℕ,i < N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)) (s:ℕ→ℝ)
lemma eaves {r l m : ℕ} (hr : r  ≤  l) (hl : l ≤ m) (hM : m ≤ N) (h : H.Selected)
    (hm : Sung B H N p A W r M)
    (P : Solo F H p m) (hp : Keyed H N p A m P) (he : ∀ i ≥ l, ∀ hm:i < m, (∃ η:ℝ,Tones B H N p A (s i) i η (D i (lt_of_lt_of_le hm hM))) ∧ Carol B H N p i (D i (lt_of_lt_of_le hm hM)) (M.tone (i+1)) (M.tone i) (s i)) :
    ∃ Q : ∀ i, Solo F H p i, Q m=P ∧ Challenge B H N p A W M l m Q ∧ (∀ i:ℕ,l  ≤  i → ∀ hm:i < m,Accord B H N p M (s i) i (D i (lt_of_lt_of_le hm hM)) (Q (i+1)) (Q i)) := by
  induction hl using Nat.decreasingInduction with
  | self =>
    let v (i : ℕ) : Solo F H p i := ⟨0,primary 0 0,0⟩
    refine ⟨update v m P,update_self ..,⟨fun i hi hI => ?_,fun i hi hI => by omega⟩,fun i hi hI=> by omega⟩
    obtain rfl : i=m := le_antisymm hI hi
    rw [update_self]; exact hp
  | of_succ k hk ih =>
    obtain ⟨Q,hQ,hx,hY⟩ := ih (hr.trans k.le_succ) (fun i hi => he i (by omega))
    obtain ⟨⟨η,hT⟩,hR⟩ := he k le_rfl hk
    have hz := lt_of_lt_of_le hk hM
    obtain ⟨X,hX,hv,hb⟩ := acclaim B H N p A W M h hz (hm.earned k hr hz.le) (hm.earned _ (hr.trans k.le_succ) hz)
        (hm.step _ hr hz) hR hT (hx.chairs _ le_rfl hk)
    let t := update Q k X
    have hl (i : ℕ) (hi : k  <  i) : t i = Q i := update_of_ne hi.ne' X Q
    refine ⟨t,(hl m hk).trans hQ,⟨fun i hi hy => ?_,fun i hi hy => ?_⟩,fun i hi hy=>?_⟩
    · rcases lt_or_eq_of_le hi with he|he
      · rw [hl i he]; exact hx.chairs _ he hy
      subst i; unfold t; rw [update_self]; exact hX
    · rcases lt_or_eq_of_le hi with he|he
      · rw [hl i he,hl (i+1) (by omega)]; exact hx.ships _ he hy
      subst i; rw [hl (k+1) k.lt_succ_self]; unfold t; rw [update_self]; exact hv
    rcases lt_or_eq_of_le hi with he|he
    · rw [hl i he,hl (i+1) (by omega)]; exact hY _ he hy
    subst i; rw [hl (k+1) k.lt_succ_self]; unfold t; rw [update_self]; exact hb
theorem antilles {r l m : ℕ} (hr : r  ≤  l) (hl : l ≤ m) (hM : m ≤ N) (h : H.Selected)
    (hm : Sung B H N p A W r M)
    (he : ∀ i ≥ l, ∀ hm:i < m, (∃ η:ℝ,Tones B H N p A (s i) i η (D i (lt_of_lt_of_le hm hM))) ∧ Carol B H N p i (D i (lt_of_lt_of_le hm hM)) (M.tone (i+1)) (M.tone i) (s i))
    (X : Coefficient F (H.S.side m p)) {t w : ℝ} (hx : X.Format 0 A (H.rep N p m))
    (ht : X.remBound 0 (H.rep N p m) (Real.sqrt (H.levels.clock.forcedAllowance m)) t)
    (hw : F.coeffSize X.x+t ≤ w) (hR : roomCost H.levels W) (hB : Bank W H.levels) :
    ∃ Q : ∀ i, Solo F H p i, Q m=pair H N p M X t ∧ Challenge B H N p A W M l m Q ∧ (∀ i:ℕ,l  ≤  i → ∀ hm:i < m,Accord B H N p M (s i) i (D i (lt_of_lt_of_le hm hM)) (Q (i+1)) (Q i)) ∧
      (∀ v, ((Q m).bar M v).x=X.x+(M.tone m).index v ∧
       ((Q m).bar M v).density 0 B (H.rep N p m) = X.density 0 B (H.rep N p m) +
        ((M.tone m).plays v).density 0 B (H.rep N p m)) ∧
      let P := dualize H N p M l m Q (-(Q l).a)
      ((Q l).bar M 0).x=(M.tone l).index (Q l).a ∧ P.Woke A W B w ∧ ∀ i, l  ≤  i → i  ≤  m →
        gainChart H m i*(P.cost i+F.coeffSize (P.voice i).x)  ≤  4*(1+(H.levels.params m).columns)*w := by
  let V := pair H N p M X t
  obtain ⟨hV,hL⟩ := originate B H N p A M hM h (hm.earned _ (hr.trans hl) hM) hx ht hw
  obtain ⟨Q,hq,HQ,HY⟩ := eaves B H N p A W M D s hr hl hM h hm V hV he
  have hT i (hi : l  ≤  i) (he : i ≤ m) v := keys B H N p A M v (HQ.chairs i hi he) (hm.earned i (hr.trans hi) (he.trans hM))
  let a := (Q l).a
  let P := dualize H N p M l m Q (-a)
  have hp : P.Woke A W B w := by
    refine ⟨⟨hl,hM⟩,fun i hi he => (hT i hi he _).2,?_,fun i hi he => (HQ.ships i hi he).tunes _,
      fun i hi he => (HQ.ships i hi he).debt _,?_,?_⟩
    · intro i hi he
      let q := (H.levels.clock.op i p).ratio
      change 0=q.parent 0; have hu := q.embed_parent 0; rw [embed_origin] at hu; exact hu.symm
    · change ((Q l).bar M _).x=_; rw [(hT l le_rfl hl _).1]; simp [a]
    change (Q m).cost M _ ≤ _
    simp_rw [show P.voice m=(Q m).bar M (-a) from rfl,hq]; exact (hL _).2.2
  refine ⟨Q,hq,HQ,HY, fun v => ?_,?_,hp,?_⟩
  · rw [hq]; exact ⟨(hL v).1,(hL v).2.1⟩
  · rw [(hT l le_rfl hl _).1]; simp
  exact Work.G09.answer W H hR hB N p d l m F B A P w (by
    have hi := Work.G08.size_nonneg F X.x; linarith only [hw,hi,rem_nonneg ht]) hp
end YM.Extra.Histories.Relay
