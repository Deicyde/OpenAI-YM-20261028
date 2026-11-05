import YM.TraceExtension.Margin.Prow
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open scoped Matrix.Norms.Frobenius
abbrev DCard {d:ℕ}(H:Hol G)(F:Labels.Frame G d)(x:ℝ)(T:Peat G s):=F.coords (Push.Local.project H 0 (tempQ x) (filmR T) d)
def Triple {d:ℕ}(H:Hol G)(F:Labels.Frame G d)(x:ℝ) (R:Rep G s) (T:Peat G s) := Push.Local.weighted H F 0 (tempQ x) R.p.threshold (filmR T)
variable {d:ℕ}(F:Frame G d){t:ℝ}{A:Peat G s}{B:BudgetPoint}{R:Rep G s}
lemma card_reads(hp:B.Regular (tempQ t) (filmR A))(hn:d ≤ B.order)(ht:Nonwrapping (tempQ t (n:=s)) 0): JetTest H 0 (F.coords.symm (DCard H F t A)) (Complex.ofRealCLM ∘ A):=by
    rw[DCard,LinearEquiv.symm_apply_apply]; have hu:= Push.Local.project_reads H 0 hp hn; rw[Reads,if_pos ht] at hu; exact hu
lemma card_realV(hp:B.Regular (tempQ t) (filmR A))(hn:d ≤ B.order): realBar (F.coords.symm (DCard H F t A))=F.coords.symm (DCard H F t A):=by
    rw [DCard,LinearEquiv.symm_apply_apply]; let R:=Push.Local.project H 0 (tempQ t) (filmR A) d
    have hx:=Push.Local.project_reads H 0 hp hn; have hu:= reads_bar hx; rw[show star (filmR A)=filmR A from funext fun v=>by simp[filmR] ] at hu; exact Reads.unique hu hx
lemma vacancy(v:F.Coeff): Labels.read (0:Jet G) (F.coords.symm v).val=v 0:=by
    have hv : F.scaled 0 v=v 0 • F.e0:=by
          ext1 i; by_cases h:i=0; · subst i; simp [F.zero_degree,Frame.e0]
          simp [Frame.e0, Pi.single_eq_of_ne h, pow_succ, (F.factors_pos i h).ne']
    have hp:= read_frame_scaled (0:Jet G) F (v:=v) (θ:=0); rw[show (0:ℝ) • (0:Jet G)=0 from zero_smul _ _,hv] at hp;
    rw[← hp,map_smul,← F.coords_unit,LinearEquiv.symm_apply_apply,Submodule.coe_smul,map_smul]; simp [Labels.unit]
lemma card_zero (hp:B.Regular (tempQ t) (filmR A))(hn:d ≤ B.order)(ht:Nonwrapping (tempQ t (n:=s)) 0)(hv:A∈loom G s): (DCard H F t A) 0=0:=by
    let Z:loom G s:=⟨A,hv⟩; rw[← vacancy F (DCard H F t A)]; have hz: A 1=0:=loom0 Z
    have he:= (card_reads F hp hn ht (H:=H) (0:Jet G)).2.2 0 (Nat.zero_le _)
    -- testLinks 0
    simp at he
    rw[test_one,hz,Complex.ofReal_zero,show scaleJet (0:Jet G) 0=0 from funext fun i=>smul_zero (0^(i+2):ℝ)] at he; rw[DCard, LinearEquiv.symm_apply_apply, ← he]
lemma pricedU(hp:R.p.Regular (tempQ t) (filmR A))(hn:d ≤ R.p.order)(ht:Nonwrapping (tempQ t (n:=s)) 0)(hv:A∈loom G s)(h:G.Simple)(he:d≤5): Triple H F t R A= R.p.threshold^(2:ℕ) • DCard H F t A:=by
    let Z:= DCard H F t A;let y:=R.p.threshold; ext1 i; change ((↑(y^(F.grades i).2):ℂ)*_)=(y^ (2:ℕ):ℝ) • Z i; change _*Z i=_
    by_cases hx:i=0
    · subst i; rw[show Z 0=0 from card_zero F hp hn ht hv,mul_zero,smul_zero]
    rw [(nbase F he i hx h).2.2];rfl
end YM.Trace.Margin
