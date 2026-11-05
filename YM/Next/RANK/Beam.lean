import YM.Next.RANK.Monitors
import YM.Work.B10
import YM.Work.D01
import YM.Work.D02
import YM.Work.D03
import YM.Work.D04
import YM.Work.D05
import YM.Work.D06










/-!
# Choose refinement only while preserving inputs

Use real `Arrives`, not a version with `S` already measurable at ties pointwise
in the cutoff lattice. Each weight gets its own real-basis lanes before
refining; for all their slots keep same order when refining. This file has
conditional consumers (and one uses B10 & D04 etc.). In particular Spans
follows for the precise R of `EquationCount` and the Cleaner can use it. On
S cleaned, use the *same trials* which testified before it to build Seed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beam
open Set Filter Metric MeasureTheory RG Extraction Dash Cells Market Bid Org Spec
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {P : ℕ→ Table C.book} {R : Bin S} {T : Table C.book} {W : DiffPlan T}

def reindex (T : Table C.book) {d} (X : Columns C S d) : Columns C T d :=
  ⟨X.dim,X.H,X.basis,X.realBasis,X.initial,X.amount,X.row,X.full⟩

def replay (T : Table C.book) {d} {X : Columns C S d} (Y : X.Trials) : Columns.Trials (reindex T X) :=
  ⟨Y.depth,Y.width,Y.window,Y.scale,Y.positive,Y.zoom,Y.mark,Y.lift,Y.later,Y.gap,Y.allowed,Y.small⟩

def learned {d} {X : Columns C S d} (Y : X.Trials) (L : ℕ → Fin (X.dim+1) → C.book.Ref d) : X.Trials := { Y with later := L }

lemma reviewed {d} {X : Columns C S d} {Y : X.Trials} (h : Purchases Y) (T) : Purchases (replay T Y) :=
  ⟨h.proportion,h.flat,h.shrinks,h.real,h.literal,h.bounded,h.tuned,h.fit,h.axis,h.arrays⟩

lemma saved {d} {X : Columns C S d} {Y : X.Trials} (h : Purchases Y) (L) : Purchases (learned Y L) :=
  ⟨h.proportion,h.flat,h.shrinks,h.real,h.literal,h.bounded,h.tuned,h.fit,h.axis,h.arrays⟩

variable {d : ℕ}

lemma carries {X : Columns C S d} {Y : X.Trials} (h : Cleaner S P T W f) (u : Arrives C f S P)
    (hp : C.Makes) (he : Spans u.born R f) (hg : Detect.EquationCount R f d)
    (hx : Purchases Y) (hy : lands Y f) :
    T.null d=LinearMap.ker (R d).trueP.toLinearMap ∧
      Module.finrank ℂ (T.Field d)=Module.finrank ℂ ((standard C).Field d) ∧
        (replay T Y).Valid f := by
  obtain ⟨H,B,M⟩ := Detect.stocked u.born u.census.regular hx hp hy ⟨P,u.census.mesh,u.census.volume⟩
    R (he.p d) u.census.integral hg
  have hv := Bin.transfer R u.born h.sharp h.basic.toSymmetric h.smooth d H.symm
  have ha := hv.trans H.symm
  refine ⟨hv, ?_, (reviewed hx T).to_rank (show lands (replay T Y) f from hy) ?_⟩
  · unfold Table.Field; rw [ha]; exact B
  change ∀ᶠ k in atTop, Submodule.span ℂ (Set.range fun i => (T.null d).mkQ (Y.later k i))=⊤
  rwa [ha]

lemma retained (X : (d : ℕ) → Columns C S d) (Y : (d : ℕ) → Columns.Trials (X d))
    (h : ∀ d,Purchases (Y d)) (f : Order) :
    ∃ (g : Order) (L : (d : ℕ) → ℕ → Fin ((X d).dim+1) → C.book.Ref d), ∀ d,
      Purchases (learned (Y d) (L d)) ∧ lands (learned (Y d) (L d)) (f.refine g) := by
  choose B hB using fun d k => (h d).bounded k
  let I := (d : ℕ) × ℕ × Fin ((X d).dim+1)
  let F (i : I) := fun N p => (Y i.1).lift i.2.1 N p i.2.2
  let K (i : I) : Set (C.label i.1) := Metric.closedBall 0 (B i.1 i.2.1)
  haveI : Countable I := inferInstanceAs (Countable (Sigma _))
  have he (i : I) (p : ℕ) : ∀ᶠ j in atTop, F i (f.mesh j) p ∈ K i := by
    refine Eventually.of_forall fun j =>?_
    rw [show K i= _ from rfl, Metric.mem_closedBall, dist_zero_right]; exact hB i.1 i.2.1 (f.mesh j) p i.2.2
  obtain ⟨g,T,ht⟩ := Extraction.collect f (fun (_ : I) _ => True) (fun _ => Eventually.of_forall fun _ => trivial) F
    (K:=K) (fun i => isCompact_closedBall ..) (fun i p _ => he i p)
  let L (d k : ℕ) (i : Fin ((X d).dim+1)) : C.book.Ref d := T ⟨d,k,i⟩
  exact ⟨g,L,fun d => ⟨saved (h d) (L d),fun k i => (ht ⟨d,k,i⟩).2⟩⟩

-- RelayBin retained even when refined x is chosen with `dollar` only for that new filter.
lemma holds (f g : Order) : (f.refine g).fuse ≤ f.fuse := fun S hx =>
    Order.late_refine (A:=fun N p => (N,p)∈S) f g hx
lemma center_retains (g : Order) (h : CenterPort C f) : CenterPort C (f.refine g) := by
  constructor
  · intro v p; filter_upwards [h.per v p] with m H; obtain ⟨A,h,Ht⟩ := H
    exact ⟨A,h,g.mesh.cofinal.eventually Ht⟩
  exact recur h.cells g

private lemma raise_close (g : Order) {x y : Lease.Trial C} (h : Bid.close C f x)
    (he : ∀ i j, x ((f.refine g).mesh i) ((f.refine g).per j)= y ((f.refine g).mesh i) ((f.refine g).per j)) :
    Bid.close C (f.refine g) y := by
  obtain ⟨v,hv,hc⟩ := h
  refine ⟨v,hv.mono_left (holds f g),fun i j => ?_⟩
  obtain ⟨k,hk,H⟩ := hc i j
  have hx := Order.late_refine f g H
  unfold Order.late at hx
  refine ⟨k,hk,hx.mono fun m hm => hm.mono fun j hj => ?_⟩
  dsimp only at hj ⊢; rw [he] at hj; exact hj

private lemma occupants (f g : Order) (A : ℕ→ℕ→ Prop) (h : (f.refine g).late A) : f.late fun N p =>
    N∈ Set.range (f.refine g).mesh → p∈Set.range (f.refine g).per → A N p := by
  obtain ⟨P,h⟩ := eventually_atTop.mp h
  unfold Order.late; filter_upwards [eventually_ge_atTop (g.per P)] with j hj
  by_cases he : f.per j ∈ Set.range (f.refine g).per
  · obtain ⟨v,hv⟩ := he
    have hg : g.per v=j := f.per.monotone.injective hv
    obtain ⟨K,hK⟩ := eventually_atTop.mp (h v (g.per.monotone.le_iff_le.mp (hj.trans_eq hg.symm)))
    filter_upwards [eventually_ge_atTop (g.mesh K)] with i hi H _
    obtain ⟨s,hs⟩ := H
    have hk : g.mesh s=i := f.mesh.monotone.injective hs
    rw [← hs,← hv]; exact hK s (g.mesh.monotone.le_iff_le.mp (hi.trans_eq hk.symm))
  exact Eventually.of_forall fun i _ h => False.elim (he h)

lemma relay_retains (g : Order) (h : RelayBin C R f d) : RelayBin C R (f.refine g) d := by
  classical
  let T := f.refine g
  have he (j) (x : Lease.Trial C) (hx : vet C f j x) : vet C T j x := by
    obtain ⟨p,hP,hh⟩ := hx; exact ⟨p,fun ε hε => Order.late_refine _ _ (hP _ hε), raise_close g hh (fun _ _ => rfl)⟩
  refine ⟨Tendsto.mono_left h.P (holds _ _), fun x hx ht => ?_,fun w hy v => he _ _ (h.transit _ hy v),fun v i => he _ _ (h.pace v i)⟩
  let u : Rowe C d := fun i => if i.1 ∈ Set.range T.mesh ∧ i.2 ∈ Set.range T.per then x i else 0
  have hr (j) : (R d).step j (u j)=0 := by dsimp only [u]; split;exact hx _;exact map_zero _
  have hd : dollar C f u := by
    intro ε he
    apply (occupants f g _ (ht ε he)).mono fun j H => H.mono ?_
    intro i hi
    dsimp only [u]; split_ifs with h
    · exact hi h.1 h.2
    rw [map_zero,norm_zero]; exact (Real.exp_pos _).le
  obtain ⟨b,hb,H,k⟩ := h.mark u hr hd
  refine ⟨b,Order.late_refine _ _ hb,fun i j a l hl => Order.late_refine _ _ (H i j a l hl),raise_close g k ?_⟩
  intro i j
  have hi : T.mesh i ∈ Set.range T.mesh ∧ T.per j ∈ Set.range T.per := ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩
  change (C.O _ _ (u (T.mesh i,T.per j)))-_= C.O _ _ (x (T.mesh i,T.per j))-_
  simp only [u,if_pos hi]

lemma equation_retains (H : Detect.EquationCount R f d) (ht : Bin.Matrix R d f) (g : Extraction.Order) : Detect.EquationCount R (f.refine g) d := by
  obtain ⟨i,hi,hv⟩ := (H.and_eventually (Detect.reconciled R ht)).exists
  rw [hv] at hi
  exact (((Detect.reconciled R ht).filter_mono (holds f g) : ∀ᶠ i in (f.refine g).fuse,
    Module.finrank ℂ (LinearMap.ker ((R d).step i).toLinearMap)=Module.finrank ℂ (LinearMap.ker (R d).trueP.toLinearMap)).mono
      fun j hj => by rw [hj]; exact hi).frequently


/-- Conditional consumer, using B70 integration and arriving with the same
order as the corrected tests. Doesn't assert the producer of `Purchases`.
`RBase` wired via `u.serves`, goals also for any Cleaner. -/
lemma arriving_seed (h : C.Makes) (β : CenterPort C f) (M : RawLimits C f S P)
    (R : Bin S) (x : ∀ d, RelayBin C R f d) (he : ∀ d,Detect.EquationCount R f d)
    (X : (d : ℕ) → Columns C S d) (Y : (d : ℕ) → Columns.Trials (X d)) (hp : ∀ d,Purchases (Y d)) :
    ∃ (g : Order) (L : (d : ℕ) → ℕ → Fin ((X d).dim+1) → C.book.Ref d),
      let Z := fun d => learned (Y d) (L d)
      let f' := f.refine g
      ∃ u : Arrives C f' S P,
        Spans u.born R f' ∧ (∀ d, Purchases (Z d) ∧ lands (Z d) f') ∧
          (∃ T W, Cleaner S P T W f') ∧
            ∀ T W, Cleaner S P T W f' → Seed C f' T ∧ ∀ d,
              T.null d=LinearMap.ker (R d).trueP.toLinearMap ∧ Module.finrank ℂ (T.Field d)=Module.finrank ℂ ((standard C).Field d) ∧
                (replay T (Z d)).Valid f' := by
  classical
  obtain ⟨g,L,hv⟩ := retained X Y hp f
  let p := f.refine g
  have ht : CenterPort C p := center_retains g β
  have hm : RawLimits C p S P := Extraction.copy_down C f M g
  have hZ : p.PointLimits C S := ⟨P,hm.mesh,hm.volume⟩
  have hl (d) : RelayBin C R p d := relay_retains g (x d)
  have hi (d : ℕ) := equation_retains (he d) (x d).P g
  have short (h' : Live S) d : Bin.shortage R h' d := Detect.demanded h' M.regular (hv d).1 h (hv d).2 hZ R (hl d).P (hi d)
  have u := Bid.arriving ht h Work.D01.answer Work.D02.answer Work.D03.answer Work.D04.answer P hm R hl short
  have H : Spans u.born R p := Work.D04.answer Work.D01.answer Work.D02.answer Work.D03.answer u.born h ht hm.integral R hl (short _)
  refine ⟨g,L,u,H,hv,u.serves h ht,fun T W hT => ?_⟩
  have ha d := carries hT u h H (hi d) (hv d).1 (hv d).2
  obtain ⟨hs,-⟩ := Bid.healthy h ht Work.D05.answer Work.B10.answer Work.D06.answer hT
  exact ⟨⟨h,hT.mesh.integral,⟨P,hT.mesh.mesh,hT.mesh.volume⟩,hs,ht.cells,fun d =>
    ⟨reindex T (X d),replay T _,(ha d).2.2⟩⟩,ha⟩
end YM.Next.Rank.Beam
