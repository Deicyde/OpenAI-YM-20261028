import YM.RG08.Needle.Ascent
/-!
# Orientation of recalibration and inverse return
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PowerSeries Conductor
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {I: Type} [Fintype I] [DecidableEq I] {L c f p: Side} {R A B:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ} {F:Labels.Frame G d} {Q: StripU G L}{U: BoardU D R G}{φ : I → BoardU D R G}
private def oldU (V:StripU G L)(τ d:ℕ) := filop V.cv V.tree V.song none τ d (D:=D) (R:=R)
omit [Fintype I] [DecidableEq I] in
lemma old_sum {u:I→BoardU D R G}(s:Finset I) (h:Fair Q)(hp:1/2≤R)(d:ℕ)(hu:∀ i∈s,Marvel τ (u i)): oldU Q τ d (∑ i∈s,u i)=∑ i∈s,oldU Q τ d (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>
    rw [sum_empty,sum_empty]
    have hx: Marvel τ (0:BoardU D R G) := choir_none
    simpa only [oldU,zero_smul] using filop_scale h.cm h.ct hx.cap h.odds hx.hem h.tune h.lived hp d 0
  | insert i s hi ih=>
    rw [sum_insert hi,sum_insert hi]; have hx k (hk:k∈s):= hu k (mem_insert_of_mem hk); have hh:= choir_array s hx; have hg:=hu i (mem_insert_self ..)
    exact (filop_plus h.cm h.ct hg.cap hh.cap h.odds hg.hem hh.hem h.lived h.tune hp d).trans (by rw [← ih hx]; rfl)
-- exact charge scalar old↔common on ANY books transported as columns
lemma old_study (q: Native I)(h:Fair Q)(hp:1/2≤R)(t d:ℕ)(ht:∀ i,Marvel t (φ i)): oldU Q t d (edgeBook φ q)=edgeBook (fun i=>oldU Q t d (φ i)) q := by
  let F:=oldU Q t d (D:=D) (R:=R)
  have hy i j: Marvel t (coeff j (q i) • fem j (φ i)) := choir_weight (stemmed (ht i) (Nat.le_add_right ..)) _
  have hx i j: F (coeff j (q i) • fem j (φ i))= coeff j (q i) • fem j (F (φ i)) := by
    have he: t≤t+j := Nat.le_add_right ..
    have hh:= stemmed (ht i) he; have hv:= ht i
    rw [show F _=_ from filop_scale h.cm h.ct hh.cap h.odds hh.hem h.tune h.lived hp d (coeff j (q i))]
    rw [filop_fem h.cm h.ct hv.cap h.odds hv.hem h.tune h.lived hp he d]; rfl
  funext e
  let t' e i := adapt (φ i) (q i) e
  rw [edge_marks _ q e e le_rfl] -- RHS?
  change F (edgeBook φ q) e=(∑ i,adapt (oldU Q t d (φ i)) (q i) e) e
  have hu i : F (t' e i)= adapt (F (φ i)) (q i) e:= by
    unfold F t' adapt; rw [old_sum (range _) h hp d (fun j _=>hy i j)]; exact Finset.sum_congr rfl (fun j _=> hx i j)
  have hv: F (edgeBook φ q) e=F (∑ i,t' e i) e:= filop_init (M:=Q.cv) (edge_marks φ q e) d e le_rfl -- fix
  rw [hv,show F _= _ from old_sum (u:=t' e) univ h hp d (fun i _=> choir_array (range (e+1)) (fun j _=>hy i j))]
  exact congr_fun (Finset.sum_congr rfl (fun i _=> hu i)) e
lemma eng_in (V:PowerSeries ℝ)(F:BoardU D R G)(t : Voice D R →L[ℝ] ℝ) (r:ℕ) (a: Beads (Loc G 1) r):
    PowerSeries.mk (fun i=> t (Tall.hill V F i r a)) = V⁻¹ ^ r * PowerSeries.subst (PowerSeries.X*V) (PowerSeries.mk (fun i=> t (F i r a))) := by
  ext i; unfold Tall.hill; rw [PowerSeries.coeff_mk, Tall.glaze_orient]; simp [Finset.sum_apply]
variable (ψ: PowerSeries ℝ)
-- tilt polynomial series convention

def swapU (v: Native I): Native I := fun i=>PowerSeries.subst (PowerSeries.X*ψ) (v i)
lemma hill_studies (φ:I→BoardU D R G)(q:Native I): Tall.hill ψ (edgeBook φ q) = edgeBook (fun i=>Tall.hill ψ (φ i)) (swapU ψ q) := by
  apply speak_basis; intro r x a
  rw [eng_in,mugs_tot,mugs_tot]
  have hm : HasSubst (PowerSeries.X * ψ) := PowerSeries.HasSubst.of_constantCoeff_zero ((show constantCoeff (PowerSeries.X*ψ)=0 by simp))
  let s : PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ := PowerSeries.substAlgHom hm
  have he : ⇑s= PowerSeries.subst (PowerSeries.X*ψ):= coe_substAlgHom _
  simp_rw [eng_in]; unfold swapU; rw [← he,_root_.map_sum, Finset.mul_sum]; apply sum_congr rfl; intro i _; rw [_root_.map_mul]; simp_rw [he]; ring
lemma study (ψ:ReadsU F D R)(v:Native (Letter F))(h:Fair Q)(hp:1/2≤R)(hφ:Boards ψ) :
    Needle.push Q d d (edgeBook ψ v)=edgeBook (uprise Q ψ) (swapU Q.scale v) := by
  unfold Needle.push; rw [show filop Q.cv Q.tree Q.song none d d (edgeBook ψ v) = _ from old_study v h hp d d (fun i=> wider (hφ.rank i) (slot_le i)), hill_studies]; congr 1; funext i
  have hx:= hφ.rank i; have he := filop_epoch (Q:=Q.tree) h.cm hx.cap h.odds hx.hem h.tune h.lived hp (slot_le i) d; exact congr_arg (Tall.hill Q.scale) he
end YM.RG08.Needle
