import YM.Bid.Drops
import YM.Work.A01.Support


/-!
# RClose port adapters across independent Table choices

Additional compatibility lemma for actually hooking producers to
`synchronized`. If a Rank or Climb producer produces estimates on another
Table from one of the requested order refinements, but **same** anchored
cutoff, no need to assume the two Table choices actually lean-equal. Glue
by the all-spectator quotient, respecting even differentiation and the shell
and UV tests. Keep the SAME S that the consumer asked for. No claim we
can do this without already-equal separated limits!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY
open Filter Set Function MeasureTheory
open Extraction Org Cells Climb Spec
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {C : Family G} {S T : Table C.book}

/-- On all separated data. In particular T is not a competing separate-order
choice with potentially different smooth limits. -/
def Alias (S T : Table C.book) : Prop := ∀ n (v : Fin n → C.book.Token),
  EqOn (fun x => S.read x v) (fun x => T.read x v) (conf n)

namespace Alias
variable (h : Alias S T)



include h in
theorem kernels (d : ℕ) : S.null d=T.null d := by
  ext p
  rw [Table.criterion, Table.criterion]
  refine ⟨fun y n B x hx => ?_, fun y n B x hx => ?_⟩
  · exact (h (n+1) (Fin.cons ⟨d,p⟩ B) hx).symm.trans (y n B x hx)
  exact (h (n+1) (Fin.cons ⟨d,p⟩ B) hx).trans (y n B x hx)

def labels (d : ℕ) : S.Field d ≃ₗ[ℂ] T.Field d := Submodule.quotEquivOfEq _ _ (h.kernels d)

theorem mark (d : ℕ) (p : C.book.Ref d) : h.labels d (S.project d p)=T.project d p :=
  Submodule.quotEquivOfEq_mk _ _ _ _

def name (x : S.Tag) : T.Tag := ⟨x.1, h.labels x.1 x.2⟩

theorem behind {n : ℕ} (v : Fin n → T.Tag) : ∃ w : Fin n → S.Tag, v=h.name ∘ w := by
  let w (i : Fin n) : S.Tag := ⟨(v i).1,(h.labels (v i).1).symm (v i).2⟩
  exact ⟨w, funext fun i => by simp [name, w]⟩

lemma reflect {hs : S.RealSpin} {ht : T.RealSpin} (d : ℕ) (p : S.Field d) (t : Signed) :
    h.labels d (S.mirror hs d t p)=T.mirror ht d t (h.labels d p) := by
  obtain ⟨p,rfl⟩ := S.onto d p
  rw [S.mirror_project, h.mark, h.mark, T.mirror_project]

lemma real {hs : S.RealSpin} {ht : T.RealSpin} (d : ℕ) (p : S.Field d) :
    h.labels d (S.conj hs d p)=T.conj ht d (h.labels d p) := by
  obtain ⟨p,rfl⟩ := S.onto d p
  rw [S.conj_project, h.mark, h.mark, T.conj_project]

lemma read (hs : S.Symmetric) (ht : T.Symmetric) {n : ℕ} (v : Fin n → S.Tag)
    {x : Points n} (hx : x∈conf n) :
    S.useAt S x v=T.useAt T x (h.name ∘ v) := by
  choose p hp using fun i => S.onto (v i).1 (v i).2
  let w : Fin n → C.book.Token := fun i => ⟨(v i).1,p i⟩
  have hv : v=S.classTokens ∘ w := by
    funext i; exact Sigma.ext rfl (heq_of_eq (hp i).symm)
  have hh : h.name ∘ S.classTokens ∘ w=T.classTokens ∘ w := by
    funext i
    change (⟨(w i).1, h.labels (w i).1 (S.project (w i).1 (w i).2)⟩:T.Tag)=T.classTokens (w i)
    rw [h.mark]
  rw [hv, S.at_project S hs (fun _ => le_rfl) hx, hh,
    T.at_project T ht (fun _ => le_rfl) hx]; exact h n w hx

private lemma head (hs : S.Symmetric) (ht : T.Symmetric) {n d : ℕ}
    (v : Fin n → S.Tag) (q : S.Field d) {x : Points (n+1)} (hx : x∈conf (n+1)) :
    S.useAt S x (Fin.cons ⟨d,q⟩ v)=T.useAt T x (Fin.cons ⟨d,h.labels d q⟩ (h.name ∘ v)) := by
  rw [h.read hs ht _ hx, Work.A01.comp_cons]; rfl

variable {P : DiffPlan S} {Q : DiffPlan T}

/-- Inclusions at the requested Table automatically match those at any
other Table witnessing the same kernels. -/
theorem filtered (hs : S.Symmetric) (ht : T.Symmetric) (hp : P.Inclusions S) (hq : Q.Inclusions T)
    {d e : ℕ} (u : d≤e) (x : S.Field d) : h.labels e (P.rise u x)=Q.rise u (h.labels d x) := by
  apply T.field_ext ht
  intro n v y hy
  obtain ⟨w,rfl⟩ := h.behind v
  rw [← h.head hs ht _ _ hy, hq.kernels u _ hy]
  exact (hp.kernels u x hy _).trans (h.head hs ht _ _ hy)

theorem turn (hs : S.Symmetric) (ht : T.Symmetric) (hp : P.Derivatives S) (hq : Q.Derivatives T)
    (d : ℕ) (a : Axis) (x : S.Field d) : h.labels (d+1) (P.deriv d a x)=Q.deriv d a (h.labels d x) := by
  apply T.field_ext ht
  intro n v y hy
  obtain ⟨w,rfl⟩ := h.behind v
  rw [← h.head hs ht _ _ hy, hp.kernels d a x hy w, hq.kernels d a _ hy _]
  apply Analysis.GermD
  filter_upwards [(conf_open _).mem_nhds hy] with q hq using h.head hs ht _ _ hq

variable {d : ℕ}

private def shuttle (f : S.Field d→ₗ[ℂ] S.Field d) :=
  (h.labels d).toLinearMap.comp (f.comp (h.labels d).symm.toLinearMap)

private def angle : (S.Field d→ₗ[ℂ] S.Field d) →ₗ[ℂ] (T.Field d→ₗ[ℂ] T.Field d) where
  toFun := h.shuttle
  map_add' := by intro p q; ext; simp [shuttle]
  map_smul' := by intro c p; ext; simp [shuttle]

def back (I : IR (C:=C) S) : IR (C:=C) T where
  J a b := h.labels 4 (I.J a b)
  p d a := (h.labels (d+1)).toLinearMap.comp ((I.p d a).comp (h.labels d).symm.toLinearMap)
  Y d := (h.angle.restrictScalars ℝ).comp (I.Y d)





open Table Work.A01 in
private lemma localFlux (hs : S.Symmetric) (ht : T.Symmetric) {n : ℕ} (x : Points (n+1))
    (hx : x∈conf _) {χ : E4 → ℝ} (hw : Table.Window x χ) (I : IR (C:=C) S)
    (Z : E4 → E4) (v : Fin n → S.Tag) (b : S.Field d) :
    Work.A01.flux I.J χ Z x v b=Work.A01.flux (h.back I).J χ Z x (h.name ∘ v) (h.labels d b) := by
  unfold Work.A01.flux
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro j _
  apply integral_congr_ae; filter_upwards with y
  by_cases hy : Analysis.D (YM.basis a) χ y=0
  · simp [term, hy]
  have he : Points.cons y x∈conf _ := separated_of_D hx hw hy
  unfold term
  rw [h.read hs ht _ he, comp_cons, comp_cons]; rfl



def transferScaling (A : Scaling S) : Scaling T where
  U i d := (A.U i d).trans (h.labels d)
  xi := A.xi
  r := A.r
  sign := A.sign
  positive := A.positive
  later := A.later
  drips := A.drips

private lemma align (hs : S.Hierarchy) (ht : T.Hierarchy) (hp : P.Inclusions S) (hq : Q.Inclusions T)
    (A : Scaling S) {W : MaxwellData C} (ha : A.Align P W.T.W hs.spin W.hT.spin d) :
    (h.transferScaling A).Align Q W.T.W ht.spin W.hT.spin d := by
  refine ⟨fun k w p => ?_, fun k w p => ?_, fun k a b t z v => ?_⟩
  · have he := ha.Hsym k w p
    constructor
    · intro g u; simp only [transferScaling, LinearEquiv.trans_apply, he.1, h.reflect (ht:=ht.spin)]
    intro x; simp only [transferScaling, LinearEquiv.trans_apply, he.2, h.real (ht:=ht.spin)]
  · rw [transferScaling]
    simp only [LinearEquiv.trans_apply, ha.carries k w p]; exact h.mark w _
  simp only [transferScaling, LinearEquiv.trans_apply, ha.incl k a b t z v]
  exact h.filtered hs.laws.toSymmetric ht.laws.toSymmetric hp hq t _

-- Use R ≥ 1 (as actually requested). Need x in Conf whenever testing
-- positions here. Does not ask equality of tables off Conf.
theorem track (hs : S.Hierarchy) (ht : T.Hierarchy) (hp : P.Inclusions S) (hq : Q.Inclusions T)
    {A : Scaling S} {I : IR (C:=C) S} {W : MaxwellData C} {N m : ℕ} {R : ℝ} (hr : 1≤R)
    (p : Track A P W.T I.J hs.spin W.hT.spin N d m R) :
    Track (h.transferScaling A) Q W.T (h.back I).J ht.spin W.hT.spin N d m R := by
  refine ⟨h.align hs ht hp hq A p.path, ?_, ?_⟩
  · intro n hn j hj v hv z hz
    filter_upwards [p.thick n hn j hj v hv z hz] with k hk
    intro x hx
    have H : x∈conf n := spaced_conf (by positivity) hx.1
    have he : (fun y => Ward.disc ((h.transferScaling A).pins k ∘ v) ((h.transferScaling A).r k • y))=ᶠ[𝓝 x]
        (fun y => Ward.disc (A.pins k ∘ v) (A.r k • y)) := by
      filter_upwards [(conf_open _).mem_nhds H] with y hy
      have he : A.r k • y∈conf n := by
        intro i j e
        exact (show Injective y.ofLp from hy) (smul_right_injective E4 (A.positive k).ne' e)
      exact (h.read hs.laws.toSymmetric ht.laws.toSymmetric (A.pins k ∘ v) he).symm
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]; exact hk x hx
  intro i j
  apply (p.loc i j).congr
  intro k
  dsimp only [transferScaling, back, LinearEquiv.trans_apply, LinearEquiv.trans_symm]
  simp



section ranks

/-- Cast column and trial data without changing rows or lifts. -/
def renameColumns (T : Table C.book) (d : ℕ) (X : Columns C S d) : Columns C T d :=
  ⟨X.dim, X.H, X.basis, X.realBasis, X.initial, X.amount, X.row, X.full⟩

def renameTrials (X : Columns C S d) (Z : X.Trials) (T : Table C.book) : (renameColumns T d X).Trials :=
  ⟨Z.depth, Z.width, Z.window, Z.scale, Z.positive, Z.zoom, Z.mark, Z.lift, Z.later, Z.gap, Z.allowed, Z.small⟩

include h in
theorem retains_rank (X : Columns C S d) {Z : X.Trials} {f : Order} (H : Columns.Trials.Valid f Z) :
    Columns.Trials.Valid f (renameTrials X Z T) := by
  have he := h.kernels d
  refine ⟨H.ratios, H.same_stage, H.scale_down, H.conjugate, H.unit, H.responds, H.bounded,
    ?_, H.tuned, H.seams, H.generic, H.cheap⟩
  filter_upwards [H.span] with i hi
  change Submodule.span ℂ (Set.range (fun j => T.project d (Z.later i j)))=⊤
  unfold Table.project
  rw [← he]
  exact hi
end ranks
end Alias




end YM.Next.BOUNDARY
