import YM.Extra.SOURCE_HISTORIES.Accompany

/-!
# Single isolated terminal comparison production on these columns

Output chooses WHICH continuation, a dictionary including this test &
primary subtractions. Input true test represented on the music's very same
vacuum at a fitted stop. (Any statement that such an input represents a
particular *other* cutoff cylinder has to be shown separately.) Constructs
a matched point & path and signed discrepancy bounds; does NOT assert a
bound for paths allowed to go through arbitrarily different choices, nor a
many-marker bound, rents etc. All origins 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Relay
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G) (W : Worth) (M : Music F H N p)

def dualize (l m : ℕ) (P : ∀ i : ℕ, Solo F H p i) (v : F.Coeff) : Duet H F N p l m where
  voice i := (P i).bar M v
  cost i := (P i).cost M v
  atPoint _ := 0

structure Challenge (l m : ℕ) (P : ∀ i : ℕ, Solo F H p i) : Prop where
  chairs i (hi : l≤ i) (hm : i≤m) : Keyed H N p A i (P i)
  ships i (hi : l≤ i) (hm : i<m) : Answers B H N p W M i (P (i+1)) (P i)

-- `prelim` given calls along Music and starting Solo


/-- Level m initial special presentations on SAME pencil/dictionary, even
if P and its reflected/negative counterparts are compared. v indexes the
*bare* coefficient of the propagated primary being ADDED. `duet`
result will use negative of terminally normalized correction.
-/
def pair {m : ℕ} (X : Coefficient F (H.S.side m p)) (t : ℝ) : Solo F H p m :=
  let V := M.tone m
  let c := V.index.symm X.x
  ⟨c,beside X (V.plays (-c)), t + V.charge (-c)⟩

lemma originate {m : ℕ} (hM : m≤N) {X : Coefficient F (H.S.side m p)} {t w : ℝ} (h : H.Selected)
    (hs : Heard B H N p A m (M.tone m)) (hx : X.Format 0 A (H.rep N p m))
    (hr : X.remBound 0 (H.rep N p m) (Real.sqrt (H.levels.clock.forcedAllowance m)) t)
    (ht : F.coeffSize X.x+t≤w) :
    let Y := pair H N p M X t; let R := H.rep N p m; let u := M.tone m
    Keyed H N p A m Y ∧ ∀ v : F.Coeff,
    (Y.bar M v).x=X.x+u.index v ∧ (Y.bar M v).density 0 B R = X.density 0 B R + (u.plays v).density 0 B R ∧
      Y.cost M v ≤ w +(H.levels.params m).columns * (w+F.coeffSize (Y.bar M v).x) := by
  intro Y R u
  let c := u.index.symm X.x
  have he : u.index c=X.x := u.index.apply_symm_apply _
  obtain ⟨hF,hK⟩ := presentation hx hr (hs.earns (-c)).1 (hs.earns (-c)).2
  have hg : Keyed H N p A m Y := by
    refine ⟨hF,hK,?_⟩
    change (beside X (u.plays (-c))).x=_; rw [reckon,show (u.plays (-c)).x=u.index (-c) from hs.currents _,map_neg,he]
    exact add_neg_cancel _
  refine ⟨hg,fun v => ?_⟩
  have hy : (Y.bar M v).x=u.index (c+v) := (keys B H N p A M v hg hs).1
  refine ⟨hy.trans (by rw [map_add,he]),?_,?_⟩
  · have hW := (h.represents N p m hM).good
    let f (a) := (u.plays a).density 0 B R
    have hh : IsLinearMap ℂ f := hs.values
    change (beside (beside X (u.plays (-c))) (u.plays (c+v))).density 0 B R=X.density 0 B R+_
    have hv := plus hW hK (hs.earns (c+v)).2 B
    refine hv.trans ((congr_arg (· + f (c+v)) (plus hW hr (hs.earns (-c)).2 B)).trans ?_)
    change _+f (-c)+f (c+v)=_+f v
    rw [show f (-c) = -f c from (IsLinearMap.mk' f hh).map_neg _, hh.map_add]; abel
  rw [hy]; change (t+u.charge (-c))+u.charge (c+v)≤_
  let a := (H.levels.params m).columns
  have ha : 0≤a := zero_le_one.trans (H.levels.params m).columns_ge
  have hb y : u.charge y ≤ a*F.coeffSize (u.index y) := (hs.cone y).trans
    (mul_le_mul_of_nonneg_left (Work.G08.size_core ..) ha)
  have hL : F.coeffSize (u.index (-c))≤w := by
    rw [map_neg,he,show F.coeffSize (-X.x)=F.coeffSize X.x by simp [Frame.coeffSize]]
    linarith only [ht,rem_nonneg hr]
  have hi := Work.G08.size_nonneg F X.x
  exact (add_le_add (add_le_add (by linarith only [ht,hi] : t≤w)
    ((hb _).trans (mul_le_mul_of_nonneg_left hL ha))) (hb _)).trans_eq (by unfold a; ring)



/-- At the top bar one may use the disjoint exact presentation right
from X, at the *same* direction price, without the two cancelling
primary packages appearing as well. Doesn't change x or density, and this
presentation still uses exact subtraction on coordinates (linear fixed-support
Voice). Even without doing so, `originate` gives exact density/x equality.
-/
lemma purchase {m} (hM : m≤N) (h : H.Selected) {X : Coefficient F (H.S.side m p)} {t : ℝ}
    (hs : Heard B H N p A m (M.tone m)) (hx : X.Format 0 A (H.rep N p m))
    (hr : X.remBound 0 (H.rep N p m) (Real.sqrt (H.levels.clock.forcedAllowance m)) t) (v : F.Coeff) :
    let a := M.tone m
    let Y := pair H N p M X t
    let P := beside X (a.plays v)
    let R := H.rep N p m
    P.Format 0 A R ∧ P.remBound 0 R (Real.sqrt (H.levels.clock.forcedAllowance m)) (Y.cost M v) ∧
        P.density 0 B R=(Y.bar M v).density 0 B R ∧ P.x=(Y.bar M v).x := by
  intro a Y P R
  let w := F.coeffSize X.x+t
  have ht : (Y.bar M v).x=X.x+a.index v ∧ (Y.bar M v).density 0 B R=X.density 0 B R+(a.plays v).density 0 B R ∧
      Y.cost M v≤w+(H.levels.params m).columns*(w+F.coeffSize (Y.bar M v).x) :=
    (originate B H N p A M hM h hs hx hr (le_refl (F.coeffSize X.x+t))).2 v
  obtain ⟨ha,hb⟩ := presentation hx hr (hs.earns v).1 (hs.earns v).2
  refine ⟨ha,rem_mono hb ?_,(plus (h.represents N p m hM).good hr (hs.earns v).2 B).trans ht.2.1.symm,?_⟩
  · change t+a.charge v≤t+a.charge (-Y.a)+a.charge (Y.a+v)
    have he : a.charge v≤ a.charge (-Y.a)+a.charge (Y.a+v) := by
      have hg : -Y.a+(Y.a+v)=v := by abel
      conv_lhs => rw [← hg]
      exact hs.summed _ _
    rw [add_assoc]; exact add_le_add_right he _
  change (beside ..).x=_
  rw [reckon,ht.1]; exact congr_arg _ (hs.currents v)




end YM.Extra.Histories.Relay
