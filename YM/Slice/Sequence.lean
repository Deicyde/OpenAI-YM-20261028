import YM.Slice.Tour

/-!
# Chronological tours realize traces

Values given by successive strictly supported field segments.
Tracks alignment in actual Site periods. Generic over QFT future uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open MeasureTheory Measure Filter Function Set Wilson Lattice TimeKernel Analysis
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable (a : Axis) {m : ℕ} {n : Side} {G : Gauge}

structure Brick (a : Axis) (G : Gauge) (n : Side) where
  joints : ℕ -- window steps = `joints+1`
  symbol : FieldTest joints G a n
  reads : Continuous symbol

namespace Brick
variable {a}
def width (D : Brick a G n) := D.joints+1

def value (D : Brick a G n) (t : Per n) (U : Config G n) := D.symbol (crop a t D.joints (leaves a U))
def pulse (D : Brick a G n) (β : ℝ) := testB β D.symbol

@[simp] lemma width_pos (D : Brick a G n) : 0 < D.width := by simp [width]



def step (a) (G) (n) : Brick a G n := ⟨0, (fun _ => 1), continuous_const⟩
@[simp] lemma step_value (t U) : (step a G n).value t U=1 := rfl
@[simp] lemma step_pulse β : (step a G n).pulse β=heat (G := G) (n := n) a β := funext fun _ => funext fun _ => visible ..
@[simp] lemma step_width : (step a G n).width=1 := rfl

def reflect (D : Brick a G n) : Brick a G n := { D with symbol := starred D.symbol, reads := star_cont D.reads }
@[simp] lemma reflect_width (D : Brick a G n) : D.reflect.width=D.width := rfl
@[simp] lemma reflect_pulse (D : Brick a G n) β : D.reflect.pulse β = op (D.pulse β) := starB _ _ D.reads
end Brick

namespace Time
variable {a}
abbrev Braid (a : Axis) (G : Gauge) (n : Side) := List (Brick a G n)

/-! Natural indexing before wrapping. -/
variable (B : Braid a G n)
def duration : ℕ := (B.map Brick.width).sum
def tick (i : Fin B.length) := duration (B.take i)

def traceTimes (b : Per n) (i : Fin B.length) := b+(tick B i:Per n)

def word (t : Per n) (V : Config G n) := ∏ i : Fin B.length, (B.get i).value (traceTimes B t i) V

def cores (β : ℝ) := B.map fun p => p.pulse β

@[simp] lemma starts (X : Brick a G n) : duration (X::B)=X.width+duration B := by simp [duration]


lemma tick_succ (X : Brick a G n) (i : Fin B.length) :
    tick (X::B) (Fin.cast (by simp) i.succ)=X.width+tick B i := by simp [tick,duration]

lemma entering (X : Brick a G n) (b : Per n) (i : Fin B.length) :
    traceTimes (X::B) b (Fin.cast (by simp) i.succ)=traceTimes B (b+X.width) i := by simp only [traceTimes,tick_succ, Nat.cast_add,add_assoc]

lemma read (X : Brick a G n) (b : Per n) (U : Config G n) :
    word (X::B) b U=X.value b U*word B (b+X.width) U := by
  unfold word
  change ∏ i : Fin (B.length+1), _ = _
  rw [Fin.prod_univ_succ]
  congr 1
  · simp [traceTimes,tick,duration]
  exact Finset.prod_congr rfl (fun i _ => congr_arg (fun y => (B.get i).value y U) (entering B X b i))

theorem following (x : Fin B.length) (y : ℕ) (he : y=x.val+1) :
    duration (B.take y)=tick B x + (B.get x).width := by
  unfold tick
  subst y; rw [List.take_succ_eq_append_getElem x.isLt]; simp only [duration,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil, add_zero];rfl

lemma clippedTick (i j : ℕ) (h : i ≤ j) : duration (B.take i) ≤ duration (B.take j) := by
  induction B generalizing i j with
  | nil => simp
  | cons p B ih =>
    cases i
    · simp [duration]
    rename_i i; cases j
    · omega
    rename_i j; simp only [List.take_succ_cons,starts]; exact Nat.add_le_add_left (ih _ _ (by omega)) _

lemma tick_small (i : Fin B.length) : tick B i + (B.get i).width ≤ duration B := by
  rw [← following B _ (i.val+1) rfl]
  simpa only [List.take_length] using clippedTick B _ _ (show i.val+1≤B.length from i.isLt)

lemma measureTime : ∑ i : Fin B.length, (B.get i).width=duration B := by
  have hv : List.ofFn (Brick.width ∘ B.get)= B.map Brick.width := by rw [← List.map_ofFn,List.ofFn_get]
  change ∑ i, (Brick.width ∘ B.get) i = _
  rw [← List.sum_ofFn, hv];rfl

private lemma turnaround (p : Fin m) (hp : p.val+1=m) : (finRotate m p).val=0 := by
  cases m
  · exact Fin.elim0 p
  rename_i m; rw [show p=Fin.last _ by ext; simp only [Fin.val_last]; omega, finRotate_last]; rfl

private lemma forwardR (p : Fin m) (hp : p.val+1<m) : (finRotate m p).val=p.val+1 := by
  cases m
  · exact Fin.elim0 p
  rename_i m; exact congr_arg Fin.val (finRotate_of_lt (n := m) (show p.val<m by omega))

private lemma closedViaList {k : List (K (Leaf G a n))} (h : k.length=m) (v : Fin m → K (Leaf G a n)) (hv : ∀ i, k.get i=v (Fin.cast h i)) :
    TimeKernel.closed (trans n G a) k= ∫ p, TimeKernel.cycle v p ∂(Measure.pi fun _ : Fin m => trans n G a) := by
  subst m; unfold TimeKernel.closed
  rw [show k.get=v from funext hv]

def travelTour (b : Per n) (h : duration B=n.val) : Tour n B.length where
  window i := (B.get i).joints
  start i := traceTimes B b i
  steps i := by
    let t := i.val
    rcases eq_or_lt_of_le (show t+1≤B.length from i.isLt) with he|he
    · have hh : ((finRotate _ i)).val=0 := turnaround i he
      unfold traceTimes tick
      rw [hh,List.take_zero,show duration (a := a) (G := G) (n := n) []=0 from rfl,Nat.cast_zero,add_zero]
      have hv : tick B i + (B.get i).width= n.val := by rw [← following B _ _ he.symm,List.take_length,h]
      rw [add_assoc]
      change b=b+(↑(tick B i)+(↑(B.get i).width:Per n))
      rw [← Nat.cast_add,hv]; simp [Per]
    have hh : (finRotate _ i).val=i.val+1 := forwardR i he
    rw [traceTimes,traceTimes,tick,following _ _ _ hh,Nat.cast_add,add_assoc]; rfl
  bins := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨?_,?_⟩
    · intro x y he
      obtain ⟨u,i⟩ := x; obtain ⟨v,j⟩ := y
      let V (p : Sigma fun i : Fin B.length => Fin ((B.get i).joints+1)) := tick B p.1+p.2.val
      have hx (p) : V p<n.val := calc
        _ < (tick B p.1) + (B.get p.1).width := add_lt_add_right (show p.2.val < (B.get p.1).width from p.2.isLt) _
        _ ≤ n.val := (tick_small B p.1).trans h.le
      change b+_+_=b+_+_ at he
      rw [add_assoc,add_assoc] at he
      have H : ((V ⟨u,i⟩:ℕ) : Per n)=((V ⟨v,j⟩:ℕ) : Per n) := by unfold V; rw [Nat.cast_add,Nat.cast_add]; exact add_left_cancel he
      have heq : V ⟨u,i⟩=V ⟨v,j⟩ := by simpa only [ZMod.val_natCast_of_lt (hx _)] using congr_arg ZMod.val H
      have hh (p q) (hp : p.1 < q.1) : V p < V q :=
        calc
          _ < tick B p.1 + (B.get p.1).width := by unfold V; gcongr; exact p.2.isLt
          _ ≤ tick B q.1 := by rw [← following B _ (p.1.val+1) rfl]; exact clippedTick B _ _ hp
          _ ≤ V q := Nat.le_add_right _ _
      rcases lt_trichotomy u v with hu|hu|hu
      · exact False.elim ((hh ⟨u,i⟩ ⟨v,j⟩ hu).ne heq)
      · subst v
        exact congr_arg (Sigma.mk u) (Fin.ext (Nat.add_left_cancel heq))
      exact False.elim ((hh ⟨v,j⟩ ⟨u,i⟩ hu).ne heq.symm)
    simp only [Fintype.card_sigma,Fintype.card_fin,Per,ZMod.card]
    exact (measureTime B).trans h

lemma closed_eval (β) (b : Per n) (h : duration B=n.val) :
    (partition G n β:ℂ)* moment β (word B b) = TimeKernel.closed (trans n G a) (cores B β) := by
  let K (i : Fin B.length) := (B.get i).pulse β
  rw [closedViaList (m := B.length) (by simp [cores]) K (by simp [cores,K])]
  let T := travelTour B b h
  exact T.calculated a β (fun i => (B.get i).symbol) (fun i => (B.get i).reads)
end Time
end YM.Slice
