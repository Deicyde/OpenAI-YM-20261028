import YM.TraceExtension.Cask.Elude
import YM.TraceExtension.Terrace.SkyEar
import YM.Push.GRID_APPROXIMATION.Translate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Finset Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Next.UVStress
open Further.PhysicalPeriodLimitF933 Next.Rank.Spindle Cells PhysicalNext.Repeat.Legato.Bandage Push.GridApprox
open UVNext.FreeStress (camera)
open MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
section pairing
variable (S:Schedule) {i j k N p:ℕ} (h:i ≤ k) (β:ℝ)
def pew (x y:Site (S.side i p))(f g: Config G (S.side k p)→ℂ) :ℂ := Wilson.moment β ((f ∘ translate (anchor S p h x))*(g ∘ translate (anchor S p h y)))
set_option quotPrecheck false
local notation "T"=> tilesAt S p h
variable (x y:Site (S.side i p)) {f g F H: Config G (S.side k p)→ℂ} {hS:Seam G (S.side k p) β}
lemma pulpit (hv:x≠y) (hF: Interior ((tilesAt S p h).chamber 0) F)(hh:Interior ((tilesAt S p h).chamber 0) H) (hQ:Seam G (S.side k p) β):
    ‖pew S h β x y F H‖ ≤ (T).rootTest β F*(T).rootTest β H:=by
    let v:= ![x,y]; have he : Injective v:=by intro i j he; fin_cases i <;> fin_cases j <;>simp_all [v,Ne.symm hv]
    let X:=![F,H]; have hx : ∀ i, Interior ((T).chamber 0) (X i):=Fin.forall_fin_two.mpr ⟨hF, hh⟩
    have ht:= rooted_translates S h β hQ v he X hx
    simp_rw [Fin.prod_univ_two] at ht; exact ht
private lemma pioneer {F:Config G (S.side k p)→ℂ}(w:Site (S.side k p))(he:Envelope F):Envelope (F ∘ Lattice.translate w):= ⟨he.meas.comp (show Continuous (Lattice.translate w : Config G (S.side k p)→_) by unfold Lattice.translate; fun_prop).measurable,_,fun U=> he.cost.choose_spec _⟩
lemma slides (hf: Interior ((tilesAt S p h).chamber 0) f)(hg: Interior ((tilesAt S p h).chamber 0) g)(hF: Interior ((tilesAt S p h).chamber 0) F)(hh:Interior ((tilesAt S p h).chamber 0) H):pew S h β x y F H=pew S h β x y f g+ pew S h β x y F (H-g)+pew S h β x y (F-f) g :=by
    let v:=law G (S.side k p) β; have hu(f g:Config G (S.side k p)→ℂ)(hf:Interior ((tilesAt S p h).chamber 0) f)(hg: Interior ((tilesAt S p h).chamber 0) g):Integrable ((f ∘ translate (anchor S p h x))*(g ∘ translate (anchor S p h y))) v:=by
        have hw(f: Config G (S.side k p)→ℂ)(hx:Interior ((T).chamber 0) f)(u:Site (S.side k p)):= pioneer S u (cylinder_env hx)
        have hl := (Cask.envUmul (hw f hf (anchor S p h x)) (hw g hg (anchor S p h y))); exact Cask.capped hl v
    unfold pew Wilson.moment; symm; change _=∫ U, (_:ℂ) ∂v; rw [← integral_add' (hu _ _ hf hg) (hu _ _ hF (Next.UVStress.minus hh hg)), ← integral_add' ((hu _ _ hf hg).add (hu _ _ hF (Next.UVStress.minus hh hg))) (hu _ _ (Next.UVStress.minus hF hf) hg)]; apply congr_arg (fun f:Config G (S.side k p) →ℂ=>∫ U,f U∂v); ext1 U; simp only[Pi.add_apply,Pi.mul_apply, comp_apply, Pi.sub_apply]; ring
lemma theme {t:ℝ}(ht:0 ≤ t)(f g : Config G (S.side k p)→ℂ): pew S h β x y (t • f) g=t • pew S h β x y f g:=by unfold pew Wilson.moment; simp only[Pi.smul_apply, Pi.mul_apply,comp_apply,smul_mul_assoc]; rw [integral_smul]
end pairing
end YM.Trace.Terrace
