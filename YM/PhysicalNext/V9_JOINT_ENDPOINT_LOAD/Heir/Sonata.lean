import YM.MultiNext.VACUUM_STABILITY.Component.Entrance
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Carillon
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Piccolo
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Harp



/-!
# Receipt for one execution of a principal linear unforced E singleton

`Plays` table inputs and `Rehearsed` clock numerics, funded in a later
file. Does NOT bake the θ/tags or an application of the RG expansion.
The support hypotheses still apply; no declaration that every occurrence
admits this no-hole-only purchase. The integral bound and global-regularity
release later rely on a separate Γ address whose schedule/stencil tests
must be carried through each authorization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Push.SectorMeasure SelectedOrderedKernels SelectedOrderedKernels.Sector Next.SectorChange.Rows Wisps
    Exterior Planned.AtomRegular.Foliage AnalyticBridge.NonflatCovarianceLocality.Placement
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n l r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G}

structure Libretto (G : Gauge) (n : ℕ) where
  Z : Collar G n
  rights : Rights G n
  web : Web G
  δ : ℝ
  width : 0<δ
  N : ℝ
  price : 0 ≤ N
  M : ℝ
  matins : 1 ≤ M

abbrev Libretto.C (C : Libretto G n) := Cube.fee C.Z
lemma Libretto.C_one (C : Libretto G n) : 1≤ C.C := Cube.fee_one C.Z

structure Record where
  r : ℝ
  radius : 0 < r
  Q : ℝ
  majorant : 1 ≤ Q
  ε : ℝ
  guards : 0 < ε
  K : ℝ
  peak : 1 ≤ K
  Z : ℝ
  chimes : 1 ≤ Z

structure Rehearsed (C : Libretto G n) (D : Record) (P B : BudgetPoint) (L : Side) (x : ℝ) : Prop where
  test : P.order=n
  orders : n ≤ B.order
  powers : P.power ≤ B.power
  temp_eq : P.threshold=temp x
  fiery_eq : B.threshold=fiery G x L
  early : licensed C.δ C.N L
  wire : Cube.Wire P (reach x) C.Z
  tensions : Tension C.web C.δ D.Q D.ε x D.r (loom P (reach x) C.C) B.threshold
  weft : Weft G L P B D.Q C.C x

structure Plays (C : Libretto G n) (D : Record) (P B : BudgetPoint) (Pt : Teller G) (T : Tube G S) (x : ℝ) : Prop where
  bulletin : Folio.Bulletin x Pt T
  stages F : Matins T F B.power (2*C.C) C.M
  sew : Seam T C.δ C.N
  acts F k : Act T F x k n D.r D.Q
  harps F k : Psalm.Harp T F x k n D.r D.Q
  budget (A : Stores S) (F : Forest S.ratio) (k : S.Choices) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ↪ In x A F (G:=G)) (o : Site c) (R : ℕ) (V : Config G c) :
    (∀ i,separation (front A F (e i)) o ≤ R) → A.flags=RG.flags P.threshold V → Carillon (eddy T x A F k e) V n P o D.K D.Z B.threshold R
  space : 100*(1+radiusB x)≤c.val
  rehearsed : Rehearsed C D P B S.patch.L x

variable {C : Libretto G n} {D : Record} (h : Plays C D P B Pt T x) (a : Museum F x A X Y ι)
    (he : Seed B o X f') (hV : Healthy P.threshold Y V)
namespace Plays
include h hV
lemma cantos (hw : Walled S X Y x r) (ho : o∈X) : Carillon (a.twilight k T) V n P (S.ratio.parent o) D.K D.Z B.threshold (scope B X r x) := by
  have he := h.rehearsed.temp_eq
  rw [a.twilight_price h.bulletin (he ▸ hV)]
  refine h.budget (amended x A V) F k _ _ _ _ (fun i => ?_) (by rw [he,amended])
  exact scope_inside hw _ ho _ (a.stores i.1 (halo_subset _ _ (Finset.mem_singleton_self _)))
include he

def price (C : Libretto G n) (D : Record) (P B : BudgetPoint) (L : Side) (X : Support f) (x : ℝ) (u : ℝ) (z : Prices G ι) := if (coverNumber B.B X)^3 < L.val
    then shortFee C.rights * (C.M + tranche L n D.Q (loom P (reach x) C.C) (u*‖tape z‖) B.threshold)^n * ((L.val:ℝ)⁻¹)^5
    else grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n

omit [DecidableEq ι] in
lemma prior (hG : G.Simple) (U : Config G f) (z : Prices G ι) (hu : 0 ≤ u) (hw : u*‖tape z‖ ≤ D.ε*B.threshold) (hτ : B.supBounds o X f' τ) :
    ContDiffAt ℝ n (fun z : Directions G c × Prices G ι => f' (a.received k T q d u (increment V z.1) U z.2)) (0,z) ∧
    ∀ l ≤ n, ∀ A : Slab G c l, (∀ j,P.dirBound (S.ratio.parent o) (A j)) →
      ‖iteratedFDeriv ℝ l (fun y => f' (a.received k T q d u (journey V l A y) U z)) 0‖ ≤ price C D P B S.patch.L X x u z * τ := by
  obtain ⟨h0,hO,hP,h₁,h₂,hL,hW,ht,hf⟩ := h.rehearsed
  have H l (hl : l ≤ n) (A : Slab G c l) (hA : ∀ j,P.dirBound (S.ratio.parent o) (A j)) := recital_fee (q:=q) (k:=k) (d:=d) C.rights a h.bulletin (h.acts F k) (h.stages F) he hτ
    D.majorant C.matins hl hO h₁ hP hA U z hu h.sew C.width C.price hG hL C.web C.Z rfl ht hW hf (by have := P.order_ge; omega) h.space hV hw
  exact ⟨(H 0 (Nat.zero_le _) 0 (fun j => j.elim0)).1,fun l hl A hA => (H l hl A hA).2.2 l hl⟩
end Plays
end YM.PhysicalNext.JointLoad.Heir
