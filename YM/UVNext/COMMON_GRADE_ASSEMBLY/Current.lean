import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.BETA_TRANSPORT.Margins
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression

/-! # Buy the UV shell laws from basis-only legs (vs full Probed)

For each leg we need some coherent cofinal small shells for that leg;
needn't be able to find ONE e or even one exterior side k that works for all
the legs let alone all centered observables. Reason: use the annular theorem
separately; the conclusion needed on all fields is LINEAR, even though the
estimates themselves on these shells might be difficult to add. Keep all
legs' receipts on one inherited order. Across further orders transfer via
actual Tails.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {S : Table C.book}
variable {d D h k m : ℕ}

/-- Shell test bill at ONE specified lattice shell node. No assertion of finite
bounds anywhere except on these tails, but upper bound for the counterterm
coefficients must be payable uniformly on those. Require the *actual*
centered root, incl `hand` in the seam. Cannot substitute inequality on
one isolated copy in `CutNode`. Like Annulus.lean, exponent h=3/4,
contact power included in fragment and not partly on supplier partly on
consumer. (See `price_node` / `Basis`.) -/
def CutNode (F : Extraction.Order) (D h k m : ℕ) (y : Cover) (e ε : ℝ) (J : C.book.Ref 4) (v : C.book.Ref d) :=
  C.S.gridPoint m y ∈ annulus e → ∃ A : ℝ, 0 ≤ A ∧ F.late fun N p =>
    ∃ (x : C.book.Ref D) (hN : k+1≤N), ‖x‖≤A ∧
        let T := terrace C.S k hN p
        let B := fragment (d:=d) (C:=C) (D:=D) h e J v m y N p x
        Interior (T.chamber 0) B ∧ T.rootTest (C.beta N p) B ≤ ε

lemma CutNode.persists {e ε : ℝ} {J : C.book.Ref 4} {v : C.book.Ref d} {y : Cover}
    (p : CutNode (d:=d) (C:=C) f D h k m y e ε J v) (ht : Tails g f) : CutNode (d:=d) (C:=C) g D h k m y e ε J v := by
  intro hA; obtain ⟨A,hA,H⟩ := p hA; exact ⟨A,hA,ht.late H⟩

/-- Allow producer to choose x at just the purchased N,p's. We could also
permit tolerance slop in NodeBound instead, with x fixed while testing ε
calls; going back from there choose half the desired ε for the call below. -/
theorem price_node {e ε : ℝ} {J : Axis → Axis → C.book.Ref 4} {v : C.book.Ref d}
    (p : ∀ i j m y, CutNode (d:=d) (C:=C) f D h k m y e ε (J i j) v) : NodeBound C f D h k (d:=d) e ε J v where
  live i j m y he := by
    classical
    obtain ⟨A,-,hp⟩ := p i j m y he
    let t (u : ℕ×ℕ) (x : C.book.Ref D) := ∃ hN : k+1≤u.1, ‖x‖≤A ∧
        let T := terrace C.S k hN u.2
        let B := fragment (d:=d) (C:=C) (D:=D) h e (J i j) v m y u.1 u.2 x
        Interior (T.chamber 0) B ∧ T.rootTest (C.beta u.1 u.2) B ≤ ε
    let X (u : ℕ×ℕ) := if P : ∃ x, t u x then Classical.choose P else 0
    have hq (u) (P : ∃ x,t u x) : t u (X u) := by unfold X; rw [dif_pos P]; exact Classical.choose_spec P
    have he : f.late fun N p => t (N,p) (X (N,p)) := hp.mono fun _ hl => hl.mono fun _ hi => hq _ hi
    refine ⟨X,⟨A,he.mono fun i hi => hi.mono fun j ⟨_,hj,hunused⟩ => hj⟩,
      fun η hη => he.mono fun i hi => hi.mono fun j ⟨h,_hun,hs,hB⟩ => ⟨h,hs,hB.trans (le_add_of_nonneg_right hη.le)⟩⟩

lemma Node_bound_back {e ε : ℝ} {J : Axis → Axis → C.book.Ref 4} {v : C.book.Ref d} (hle : 0 < ε)
    (hp : NodeBound C f D h k (d:=d) e (ε/2) J v) (i j : Axis) (m : ℕ) (y : Cover) :
    CutNode (d:=d) (C:=C) f D h k m y e ε (J i j) v := by
  intro he
  obtain ⟨x,⟨A,hx⟩,ht⟩ := hp.live i j m y he
  refine ⟨max A 0,le_max_right ..,?_⟩
  have H := ht (ε/2) (half_pos hle)
  unfold Order.late at *
  filter_upwards [hx,H] with i1 hi1 hi2
  filter_upwards [hi1,hi2] with i3 hb hh
  obtain ⟨hn,ht',hB⟩ := hh
  exact ⟨_,hn,hb.trans (le_max_left ..),ht',hB.trans (by linarith)⟩

-- translation leg (`false`): D=d+1, h=3; rotation (`true`): D=d, h=4.
def payLevel (d : ℕ) (t : Bool) : ℕ := if t then d else d+1
def shellWeight (t : Bool) : ℕ := if t then 4 else 3

def legRow (F : Extraction.Order) (d : ℕ) (t : Bool) (J : S.Stress) (v : S.Field d) :=
  ShellBound F (payLevel d t) (shellWeight t) v J

abbrev spectrum (S : Table C.book) (d : ℕ) := Module.finBasis ℂ (S.Field d)
abbrev Orbits (S : Table C.book) (d : ℕ) := Fin (Module.finrank ℂ (S.Field d))
abbrev Leg (S : Table C.book) := Σ d : ℕ, Bool × Orbits S d

def leg (S : Table C.book) (l : Leg S) (J : S.Stress) (F : Extraction.Order) :=
  legRow F l.1 l.2.1 J (spectrum S l.1 l.2.2)

def Legs (F : Extraction.Order) (J : S.Stress) := ∀ l, leg S l J F





/-- Buying a single leg. Raw reps can be chosen differently across legs.
Indexing e above tol l in `price` only when *asked*, and using a tolerance
of toll there, still gives the same full output (no stronger requirement).
Precisely: k_l arbitrarily far paid even with fixed F for all accuracies;
e_lj arbitrarily small paid even for all *positions* m,y at that k_l. Keep
the e^h power even if e≪1. -/
structure Rates where
  k : ℕ → ℕ
  large l : l ≤ k l
  e : ℕ → ℕ → ℝ
  positive l j : 0 < e l j
  short l j : e l j ≤ toll j

/-- ℓ request for tiling scale (k_ℓ fixed before tolerance or position), j for
accuracy. -/
abbrev ShellCall := (ℕ × ℕ) × (Axis × Axis × ℕ × Cover)

def wages (t : Bool) (d : ℕ) (B : Axis → Axis → C.book.Ref 4) (x : C.book.Ref d) (K : Rates) :
    ShellCall → Extraction.Order → Prop
  | ((l,j),a,b,m,y),F => CutNode (d:=d) (C:=C) F (payLevel d t) (shellWeight t) (K.k l) m y (K.e l j) (toll j) (B a b) x

def ClearedLeg (J : S.Stress) (l : Leg S) (F : Extraction.Order) :=
  ∃ (B : Axis → Axis → C.book.Ref 4) (x : C.book.Ref l.1) (K : Rates),
    (∀ i j,S.project 4 (B i j)=J i j) ∧ S.project l.1 x=spectrum S l.1 l.2.2 ∧ ∀ i, wages (C:=C) l.2.1 l.1 B x K i F

lemma wages_persist {t : Bool} {B : Axis→Axis→C.book.Ref 4} {x : C.book.Ref d} {K : Rates} (i : ShellCall) :
    wages (C:=C) t d B x K i f → Tails g f → wages (C:=C) t d B x K i g := by
  rcases i with ⟨⟨l,j⟩,a,b,m,y⟩
  exact CutNode.persists



theorem cleared_iff {J : S.Stress} {l : Leg S} : ClearedLeg J l f ↔ leg S l J f := by
  constructor
  · rintro ⟨B,x,K,hB,hx,hK⟩
    refine ⟨B,x,hB,hx,fun i => ⟨K.k i,K.large i,fun ε hε δ hδ => ?_⟩⟩
    obtain ⟨j,hj⟩ := within _ (lt_min hε hδ)
    have hu := hj.trans (min_le_left ..)
    have ht := hj.trans (min_le_right ..)
    refine ⟨K.e i j,K.positive i j,(K.short i j).trans ht,price_node ?_⟩
    intro a b m y hp; obtain ⟨A,hA,h⟩ := hK ((i,j),a,b,m,y) hp
    exact ⟨A,hA,h.mono fun k hk => hk.mono fun k' ⟨x,hn,hx,hb,hv⟩ => ⟨x,hn,hx,hb,hv.trans hu⟩⟩
  intro he
  obtain ⟨B,x,hB,hx,H⟩ := he
  choose k hk ht using H
  choose e he hE hN using fun i j => ht i _ (half_pos (toll_pos j)) _ (toll_pos j)
  exact ⟨B,x,⟨k,hk,e,he,hE⟩,hB,hx,fun ⟨⟨i,j⟩,a,b,m,y⟩ => Node_bound_back (toll_pos j) (hN i j) a b m y⟩

section axis
/-- Scaling a *single* leg's purchase, in the unnormalized currents.
Hence our on-demand supply can even choose *some* nonzero conserved line
member separately for each leg. No assuming a change of the *free* sign
from degree to degree. -/
private lemma fr_sc {N p m h : ℕ} {x : C.book.Ref d} {z : C.book.Ref D} (J : C.book.Ref 4)
    (c : ℂ) (e : ℝ) (y : Cover) :
    fragment (d:=d) (C:=C) (D:=D) h e (c • J) x m y N p (c • z) = c • fragment (d:=d) (C:=C) (D:=D) h e J x m y N p z := by
  funext u
  unfold fragment
  have he (b : ℕ) (t : Site (C.side N p)) (J : C.book.Ref b) : C.seen ⟨b,c • J⟩ t u=c * C.seen ⟨b,J⟩ t u :=
    congr_fun ((C.linearO N p b t).map_smul c J) u
  change (e:ℂ)^_ * _ * _ - _ = _ * _
  rw [he,he]; ring

lemma legRow_scale (t : Bool) {J : S.Stress} {v : S.Field d} (p : legRow f d t J v) (c : ℂ) : legRow f d t (c • J) v := by
  obtain ⟨B,x,hB,hx,H⟩ := p
  refine ⟨c • B,x,fun i j => ?_,hx,fun l => ?_⟩
  · simp only [Pi.smul_apply,map_smul,hB]
  obtain ⟨k,hk,H⟩ := H l
  refine ⟨k,hk,fun ε hε δ hδ => ?_⟩
  let M := ‖c‖+1; have hm : 0 < M := by dsimp [M]; positivity
  obtain ⟨e,he',he,hN⟩ := H (ε/(2*M)) (by positivity) δ hδ
  refine ⟨e,he',he,⟨fun i j m y hy => ?_⟩⟩
  obtain ⟨X,⟨A,hA⟩,hX⟩ := hN.live i j m y hy
  refine ⟨c • X,⟨‖c‖*A,hA.mono fun k hk => hk.mono fun l hl => by
    simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left hl (norm_nonneg _)⟩,fun η hη => ?_⟩
  refine (hX (ε/(2*M)) (by positivity)).mono fun k hk => hk.mono ?_
  rintro k' ⟨hN,hS,hC⟩; refine ⟨hN,?_⟩
  let T := terrace C.S _ hN (f.per k)
  let β := C.beta (f.mesh k') (f.per k)
  simp_rw [Pi.smul_apply,fr_sc]; constructor
  · exact hS.scale c
  rw [Next.UVStress.root_smul]
  have hh : ε/(2*M) + ε/(2*M) = ε/M := by field_simp; try ring
  apply (mul_le_mul_of_nonneg_left hC (norm_nonneg _)).trans
  rw [hh]
  calc
    _ ≤ M*(ε/M) := by gcongr; unfold M; linarith
    _ = ε := mul_div_cancel₀ _ hm.ne'
    _ ≤ _ := le_add_of_nonneg_right hη.le

end axis
end YM.UVNext.Grade
