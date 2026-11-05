import YM.Next.BOUNDARY.Assembly
import YM.Next.EXTRACTION.Raw
import YM.Next.PHASE.Seats
import YM.Push.STRESS_FLUX.Charges
import YM.Push.STRESS_FLUX.Cylinder
import YM.Push.STRESS_FLUX.Weak


/-!
Explicit stress-flux supplier and downstream consumers on the same Base and
(after scheduling) the same UV data. Conditional, in particular `ShellGate`,
rank/Maxwell and `Nonstress` not YU proofs. These gates can use further
per-weight etc. refinements because PointLimits and all the centered budgets
used here stay available on them. Never change continuum hierarchy when doing
so. The inner two powers/target weights are different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Table Org Extraction Annular Next.BOUNDARY Spec
open scoped Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {W : DiffPlan S}

def ShellGate (C : Family G) (f : Extraction.Order) {S : Table C.book} (W : DiffPlan S) := ∀ (w : Coeff), ‖w‖ = 1 → nabla W (material S w)=0 → Centers (material S w) →
  ∀ d (B : C.label d), (∃ g, Matching.Quotes (f.refine g) (token C w) B (d+1) 3) ∧ (∃ g, Matching.Quotes (f.refine g) (token C w) B d 4)

lemma complete_pre (hp : C.Makes) (hr : CenterPort C f) (hS : f.PointLimits C S) (hs : S.Hierarchy) (hd : W.Derivatives S)
    (hq : ShellGate C f W) {w : Coeff} (hw : ‖w‖=1) (hn : nabla W (material S w)=0) (hc : Centers (material S w)) :
    ∃ p A, Climb.Pre hs W (material S w) p A := by
  obtain ⟨hh,hJ⟩ := material_conserved W hs.spin hn
  have he {d D h : ℕ} (B : C.label d) (hh : ∃ g, Matching.Quotes (f.refine g) (token C w) B D h) := hh.elim fun g hg =>
    Matching.snip hp (((Next.Extract.Tails.refine f g).center hr).book ..) (Extraction.Order.point_retained _ _ _ hS g) hg
  have H (d) (B : C.book.Ref d) := And.intro (he B ((hq w hw hn hc d B).1)) (he B ((hq w hw hn hc d B).2))
  obtain ⟨p,A,ht⟩ := Annular.laws hs hd (v:=token C w) hh H
  exact ⟨p,A,hh,hJ,ht⟩



/-- Weak data EXCLUDING the physical stress hypotheses. The free J
choice has explicit normalization. No rotation-free Maxwell producer,
ordered multi-scale estimates, Bin extraction, etc. claimed here. -/
def Bridge (C : Family G) {S : Table C.book} (H : S.Hierarchy) (W : DiffPlan S) := ∃ (P : MaxwellData C) (τ : ℝ), τ≠0 ∧
    P.T.J=τ • material (Climb.Bel C.book) weyl ∧ Nonstress H.spin W P.hT.spin P.T.W

theorem at_seed (h : G.Simple) (hr : CenterPort C f) (s : Seed C f S) (ht : Grill C f) (hu : W.Inclusions S) (hd : W.Derivatives S)
    (hz : Bridge C s.kernel W) (hq : ShellGate C f W) : ∃ w : Coeff, ‖w‖=1 ∧ Centers (material S w) ∧
      ∃ P p A, UV C f S W P ⟨material S w,p,A⟩ := by
  obtain ⟨P,τ,hτ,hP,H⟩ := hz
  have hw := Work.D06.compat s.kernel.smooth s.kernel.laws.toSymmetric s.kernel.spin W hd hu
  obtain ⟨w,hn,hj,hc,hT⟩ := stress_weak h s.kernel hw hd P.T hτ hP H
  obtain ⟨p,A,H⟩ := complete_pre s.cutoff hr s.generic s.kernel hd hq hn hj hc
  exact ⟨w,hn,hc,P,p,A,⟨s,hw,H,hT,ht⟩⟩

variable {M : Metals G} {D : RG.Supply.Rolls M.p} {A : Alloy M D} {B : Bolt A} {S₀ : Table C.book} {P : ℕ → Table C.book}

/-- Localized `BOUNDARY.Producers` step. Stress and flux obligations there
are discharged by our supplier under explicit, still outstanding gates.
Orders synchronized by BOUNDARY before asking for these per-stress inputs. -/
theorem sync (hg : G.Simple) (hB : Assembly B C) (h : Arrives C f S₀ P) (hc : Cleaner S₀ P S W f)
    (hr : AtRank C f S) (ht : AtGrid C f S) (hq : ∀ g, ∀ s : Seed C (f.refine g) S, Grill C (f.refine g) →
      Bridge C s.kernel W ∧ ShellGate C (f.refine g) W) : ∃ g : Extraction.Order, Arrives C (f.refine g) S₀ P ∧
      Cleaner S₀ P S W (f.refine g) ∧ ∃ (P : MaxwellData C) (I : IR (C:=C) S), UV C (f.refine g) S W P I := by
  refine synchronized hg hB h hc hr ht (fun g s hv => ?_)
  obtain ⟨hz,he⟩ := hq g s hv
  obtain ⟨w,-,-,P,p,A,H⟩ := at_seed hg (hB.port hg _) s hv hc.ready hc.tilt hz he
  exact ⟨P,⟨material S w,p,A⟩,H.planet,H.weak⟩

theorem endpoint (hg : G.Simple) (hB : Assembly B C) (h : Arrives C f S₀ P) (hc : Cleaner S₀ P S W f)
    (hr : AtRank C f S) (ht : AtGrid C f S) (hq : ∀ g, ∀ s : Seed C (f.refine g) S, Grill C (f.refine g) →
      Bridge C s.kernel W ∧ ShellGate C (f.refine g) W) (miles : Bid.Miles) :
    ∃ g, Arrives C (f.refine g) S₀ P ∧ Cleaner S₀ P S W (f.refine g) ∧ ∃ F : Final C (f.refine g) S, F.sector.derivatives = W ∧
      Compatible S F.α.unselected F.sector F.action.spin F.room.kernel.spin F.B ∧ Compatible S F.α.slabs F.sector F.action.spin F.room.kernel.spin F.A := by
  obtain ⟨g,ha,hb,P,I,U⟩ := sync hg hB h hc hr ht hq
  obtain ⟨c,V,J,e,K,hK,F,hF,h',HX,Hy⟩ := at_order hB hb U miles Next.Phase.seats
  exact ⟨g,ha,hb,F,hF ▸ rfl,h' ▸ HX,h' ▸ Hy⟩
end YM.StressFlux
