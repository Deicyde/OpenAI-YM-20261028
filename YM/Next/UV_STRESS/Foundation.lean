import YM.Next.UV_STRESS.Grill
import YM.Next.UV_STRESS.Limit
import YM.Next.UV_STRESS.Ward
import YM.Work.D06




/-!
# Simultaneous construction (conditional)

Use the actual RBase-era/seed and free inputs. Shell, root budgets, UV
station costs have to be obtained at compatible parameters and on *this*
Family/Order; no independent sequence argument assumes them. Extra
refinements preserve receipts. No outer flux assumption or phase parent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {W : DiffPlan S}

/-- RBase-level prep also callable without taking `UV`, `Seed.corrected`
etc as *logical* prerequisites (dimension upper bound suffices for that part
of Seed). `Probed` is distinct from the weak station bounds. -/
theorem current_ready (hC : C.Makes) (h : F.Ordered C S) (hp : F.PointLimits C S) (H : S.Hierarchy)
    (hx : CellHyp C F) (hw : W.Inclusions S) (hv : W.Derivatives S)
    (above : DimAbove S) (T : Lighthouse C.book) (a : (Bel C.book).Hierarchy)
    (u : T.W.Inclusions (Bel C.book)) (v : T.W.Derivatives (Bel C.book)) (p : T.W.Orientation a.spin) (hF : FreeDiv T a p) (he : Stations C F a.spin)
    (budget : ∀ J : KernelSpace H.spin, J.val≠0 → Conserved W H.spin J.val → Probed F J.val) :
    W.Orientation H.spin ∧ ∃ (I : IR (C:=C) S) (X : Scaling S),
      I.J≠0 ∧ I.J∈KernelSpace H.spin ∧ Probed F I.J ∧
        Approaches (path X) (isoPanel X) ∧ Stable H.spin a.spin W T.W X ∧
          X.meter I.J T.J ∧ Pre H W I.J I.p I.Y ∧ ActLaw W T I.J H.spin a.spin := by
  have hh := Work.D06.answer hC H.smooth H.laws.toSymmetric hp W hv hw H.spin
  obtain ⟨Y,hY,hy⟩ := Stations.equivalences H h a he hw hh u p above
  obtain ⟨J,X,hn,hJ,hX,hZ,ha⟩ := produce_current H hv hh a T v p hF Y hY hy
  have hc := (linear_cons W H.spin hh J).1 hJ
  have hu := budget J hn hc
  have ht := focused H hv a T v X hX hZ _ ha
  obtain ⟨p,A,hA⟩ := shells_operate hC hx hp H hv J.val hc hu
  exact ⟨hh,⟨J.val,p,A⟩,X,hn,J.property,hu,hX,hZ,ha,⟨hc,(sym_mem.mp (kernel_mem.mp J.property).1).2.2,hA⟩,ht⟩

variable (T : MaxwellData C)

/-- We obtain the full UV witness. Record also one curve (ActLaw consumer may use tails of it),
centering/nonzero, and shell budgets for those I fields. -/
theorem foundation (h : Seed C F S) (hw : W.Inclusions S) (hv : W.Derivatives S)
    (hF : FreeDiv T.T T.hT T.lit.hers)
    (hu : Stations C F T.hT.spin)
    (budget : ∀ J : KernelSpace h.kernel.spin,J.val ≠ 0 → Conserved W h.kernel.spin J.val → Probed F J.val)
    (grill : Furnace C F) :
    ∃ (I : IR (C:=C) S), ∃ X, I.J≠0 ∧ I.J∈KernelSpace h.kernel.spin ∧ Probed F I.J ∧
      Approaches (path X) (isoPanel X) ∧ Stable h.kernel.spin T.hT.spin W T.T.W X ∧
        X.meter I.J T.T.J ∧ UV C F S W T I := by
  obtain ⟨hf,I,X,hI,hX,hA,hZ,hS,hM,hp,ha⟩ := current_ready h.cutoff h.ordered h.generic h.kernel h.copies hw hv
    (cap_given h.corrected) T.T T.hT T.lit.edges T.lit.pales T.lit.hers hF hu budget
  exact ⟨I,X,hI,hX,hA,hZ,hS,hM,⟨h,hf,hp,ha,provides_Grill C h.cutoff h.copies grill⟩⟩

section refine



lemma refineSeed (h : Seed C F S) (f) : Seed C (F.refine f) S where
  cutoff := h.cutoff
  copies := recur h.copies f
  kernel := h.kernel
  ordered := Extraction.Order.upon h.ordered f
  generic := F.point_retained C S h.generic f
  corrected d := by
    obtain ⟨X,Y,H⟩ := h.corrected d
    exact ⟨X,Y,Y.refresh F H f⟩

lemma refines_grid {n k : ℕ} {v : Fin n → C.book.Token} {x : Fin n → Lattice.Cover}
    (Y : OS.Grid.Covering k v x) (h : Y.Works k v x F) (f) : Y.Works k v x (F.refine f) where
  controls i t j := F.late_refine f (h.controls i t j)
  fillings k i j he := (h.fillings k i j he).mono fun _ hs => F.late_refine f hs

lemma Stations.upon {a} (h : Stations C F a) (f : Extraction.Order) : Stations C (F.refine f) a where
  arbitrarily d N R ε δ hr he hd := by
    obtain ⟨X,hX,hS⟩ := h.arbitrarily _ _ _ _ _ hr he hd
    exact ⟨X, X.refreshed hX f,hS⟩





-- These are persistence lemmas, not producers from such hypotheses.
lemma onward_uv (I : IR (C:=C) S) (h : UV C F S W T I) (f) : UV C (F.refine f) S W T I where
  basis := refineSeed h.basis f
  aligned := h.aligned
  planet := h.planet
  weak := h.weak
  tables := by
    intro d m
    obtain ⟨k,hk,H⟩ := h.tables d m
    refine ⟨k,hk,fun n v hp hw x he => ?_⟩
    obtain ⟨P,Y⟩ := H n v hp hw x he
    exact ⟨P,refines_grid _ Y f⟩

open Dash



end refine
end YM.Next.UVStress
