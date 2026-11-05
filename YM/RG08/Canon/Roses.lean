import YM.RG08.Canon.Mesh
import YM.UVExtension.Reports.Ultraviolet
/-! # Adapter promised for the ONE provider in `CONSTRUCTION`. No
 extra path/kernel choice. Inputs here to identification at low order on
 ACTUAL data (not estimates of actual beta error on order-2 derivative).
 Other consumers REQUIRE polynomial growth PILL prescriptions explicitly; not
 claimed on this SOME witness from some Floral construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory Function Tree Lattice RG Wilson Precision Exterior Laurent Finset Next.Free Bloch Input Org Conductor
open RG.Supply UVExtension UVExtension.Reports UVExtension.Oasis PhysicalNext.Repeat.Legato
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}

structure TruePath {H:History G}{C:Horizon H.levels}{D:ChartRatio G} (v: Kin C D):Prop where
    chosen N i p : i≤N → (H.rep N p i).path=v.path N i ∧ (H.rep N p i).clip=(H.levels.params i).clip

-- qualifies ANY mercy from Floral, no arbitrary property F.Geo assumed; now
-- schedule/cost confirmation for this provider or another one still required.
theorem roses {C:Family G} (h:G.Simple) (P:Oasis.Floral (hG:=h) C):
    ∃ (s: RG.Supply.Sheet G) (L : RG.Supply.Rolls s) (B:PostCost L) (M:Horizon C.path.levels) (D:ChartRatio G), LocalRatio D ∧ ∃ U: Kin M D, Kin.Planned U B ∧ TruePath (H:=C.path) U ∧
        ∀ ν:G.ColorIndex, (∀ N m,m≤N → sameC U ν N m) ∧ ∀ N m,m<N → compass ν ((Chain.actual C.path.levels).compassRaw ν D N m) 1= U.alpha N m := by
  obtain ⟨Q,K,A,R,S,T,x,X,w,Z,L,hR,rfl,hX,H⟩:=P
  refine ⟨Q.p, K,A.post,A.B.M,Q.O,Q.oga,A.B.kin,A.B.support,?_,fun ν=>⟨ planned_pay A.B.support ν h Q.oga, planned_turn A.B.support ν h Q.oga⟩⟩
  constructor; intro N i p hi
  let v:= Mast.roseA S
  have hp:= offset_tests L v N p i hi; dsimp only at hp
  -- v.keys 0 center
  let b:= (v N p).val
  have he: b=0:=rfl
  -- pull along exact history levels
  have hx := hX.actual i p N hi b (by rw [he,abs_zero]; exact hX.open_at)
  have hr := hp.2.2.2.1
  exact ⟨(congr_arg RG.Rep.path hr).trans hx.1, (congr_arg RG.Rep.clip hr).trans hx.2.1⟩
end YM.RG08.Canon
