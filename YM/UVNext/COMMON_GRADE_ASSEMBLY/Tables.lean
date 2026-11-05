import YM.Push.COMMON_WITNESSES.RankMatrix
import YM.Push.COMMON_WITNESSES.Scheduler
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Persistence

/-! # At rank and grid stock ports -- lowering to persistent prices

For stock receipts already on some RBase, `from_base`. But often want to
state the precursor in terms of OnDemand stock answers per faithful cutoff
demand BEFORE any tables, e.g. in pricing contracts. AND one can eliminate
a Rank dimension premise in certain Projector based campaigns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common Snap Push.CutoffProjectors
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {T : Table C.book} {b : Presentation C} {d : ℕ}

/-- Offers/Trials don't even contain T inputs that have mathematical
content (the type depends on T to give their use WHEN we evaluate The table).
Thus allow committing rank geometry and costs before seeing which T. -/
def transfer (X : Offers T) (S : Table C.book) : Offers S where
  cols d := ⟨(X.cols d).dim,(X.cols d).H,(X.cols d).basis,(X.cols d).realBasis,(X.cols d).initial,
    (X.cols d).amount,(X.cols d).row,(X.cols d).full⟩
  cylinder d := ⟨(X.cylinder d).depth,(X.cylinder d).width,(X.cylinder d).window,(X.cylinder d).scale,
    (X.cylinder d).positive,(X.cylinder d).zoom,(X.cylinder d).mark,(X.cylinder d).lift,(X.cylinder d).later,
    (X.cylinder d).gap,(X.cylinder d).allowed,(X.cylinder d).small⟩
  cost := X.cost

lemma transfer_sound (S : Table C.book) (X : Offers T) (H : X.sane) : (transfer X S).sane := by
  refine ⟨fun d => ?_,H.2⟩
  obtain ⟨a,b,c,r,g,w,p,f⟩ := H.1 d
  exact ⟨a,b,c,r,g,w,p,f⟩

/-- Discharge SizeBill after upper-dimensional identification e.g. via
projectors at S. Don't require a Loan for it a second time during the ranked
job on the same Base. `shapePrices` are just the quantitative root and lift
bills. -/
def shapePrices (X : Offers T) (d : ℕ) : (Bool × ℕ × ℕ) → Extraction.Order → Prop
    | (false,k,p),u => LiftBill (X.cylinder d) u k p (X.cost d k)
    | (true,k,p),u => CheapBill (X.cylinder d) u k (toll p)

lemma shaped (X : Offers T) (i : Bool × ℕ × ℕ) : shapePrices X d i f ↔ X.prices b (d,some i) f := by
  rcases i with ⟨(_ | _),i,p⟩ <;> rfl



lemma shape_transfer {S : Table C.book} (X : Offers T) (i : Bool × ℕ × ℕ) (p : shapePrices X d i f) :
    shapePrices (transfer X S) d i f := by rcases i with ⟨(_|_),i,p'⟩ <;> exact p

def ShapeAccount (X : Offers T) (f : Extraction.Order) := Stationed f fun j : ℕ×(Bool × ℕ × ℕ) => shapePrices X j.1 j.2

lemma ShapeAccount.ported (X : Offers T) (p : ShapeAccount X f) (S : Table C.book) : ShapeAccount (transfer X S) f := by
  obtain ⟨r,hr,H⟩ := p
  refine ⟨r,hr,fun j => ?_⟩
  obtain ⟨i,hi⟩ := H j; exact ⟨i,shape_transfer X _ hi⟩

lemma size_stock {w : Snap C} {u : Upper w} (X : Offers u.T) (p : Risen u b f)
    (h : DimAbove u.T) (H : X.sane) (ht : ShapeAccount X f) : Push.Common.Stock b u.T f := by
  obtain ⟨r,hr,hx⟩ := ht
  refine ⟨X,H,r,hr,?_⟩
  rintro ⟨d,_|i⟩
  · refine ⟨0,(Tails.late (Tails.refine f (r 0))) ((size_pay p.projections p.base _).2 ?_)⟩ -- unfolded?
    convert h d using 1
    rw [Module.finrank_eq_card_basis (X.cols d).basis,Fintype.card_fin]
  obtain ⟨k,hk⟩ := hx (d,i); exact ⟨k,(shaped X i).mp hk⟩

/-- Option to pay the ranks e.g. even BEFORE arriving at final Risen.
Needs geometry above financial exponents etc for this committed C of course,
including lifts, w/r/root costs FULLY and comparison positions; and can clean
up norm/roots etc via Stationed UNDER any new order. But doesn't care which S
was chosen, nor need new extraction input beyond what is shown.
-/
structure EarlyRank (X : Offers T) (f : Extraction.Order) : Prop where
  sound_ : X.sane
  pay : OnDemand f fun j : ℕ × (Bool × ℕ × ℕ) => shapePrices X j.1 j.2

lemma EarlyRank.persists {X : Offers T} (p : EarlyRank X f) (h : Tails g f) : EarlyRank X g := ⟨p.sound_,demand_persists p.pay h⟩
lemma EarlyRank.jobs {X : Offers T} {w : Snap C} {u : Upper w} (p : EarlyRank X f) (h : Risen u b g)
    (hp : Tails g f) (hk : DimAbove u.T) : Push.Common.Stock b u.T g :=
  size_stock (transfer X u.T) h hk (transfer_sound _ _ p.sound_)
    (ShapeAccount.ported X ((p.persists hp).pay.stations) u.T)

/-- Persistent grid bills. No assumptions on phase or t-dependent coverage
needed directly. `Study` is an actual single-field estimate request
(on finitely-many basis fields incl herbs rotated by full Spin frames at d,
with `toll` tolerances, real and bounded, against replicated arrays of this
same C; h before tolerance and **arity**, cofinally). -/
lemma study_persistent (p : Study C f) (h : Tails g f) : Study C g := demand_persists p h
lemma charges_grid (p : Study C f) {w : Snap C} {u : Upper w} (ht : Risen u b g) (h : Tails g f) : GrillInputs C g :=
    studying ht.base.center ht.base.family (study_persistent p h)









end YM.UVNext.Grade
