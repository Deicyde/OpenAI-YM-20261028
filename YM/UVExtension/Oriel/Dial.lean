import YM.UVExtension.Oriel.Loop
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Completion. No Gateaux holomorphy assumption at non-real inputs.
    Only claiming curve reception. This is what is used even if B is
    evaluated on the holomorphic cutoff profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Oriel
open Function Filter Set Metric Lamppost Complex
open scoped BigOperators Topology ContDiff Classical NNReal
variable {X Y R : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (F:X→Y)(S:Submodule ℂ X) {G:Set X} (hs:IsOpen G) {L:ℝ≥0}

include hs
private lemma lineT (hY: Dense (S:Set X))(hF : LipschitzOnWith L F G)
    (hp:∀ x∈G,x∈S →∀ y∈ S, DifferentiableAt ℂ (fun z:ℂ=> F (x+z • y)) 0) (x)(hx:x∈G)(y:X): DifferentiableAt ℂ (fun z:ℂ=> F (x+z • y)) 0:=by
  obtain ⟨u,hu,hQ⟩:= mem_closure_iff_seq_limit.mp (hY x)
  obtain ⟨v,hv,hV⟩:= mem_closure_iff_seq_limit.mp (hY y)
  obtain ⟨r,hr,hR⟩:= Metric.nhds_basis_ball.mem_iff.mp (hs.mem_nhds hx)
  let w i (z:ℂ):= u i+ z • v i
  let g z:= x+ (z:ℂ) • y
  let δ:=r/(3*(‖y‖+1)); have hd:0<δ:=by unfold δ; positivity
  let T:=ball (0:ℂ) δ
  have hm(z:ℂ)(hz:z∈T): g z∈ G:= by
    apply hR; rw [mem_ball]; simp only [g,dist_eq_norm,add_sub_cancel_left,norm_smul]; apply lt_of_le_of_lt (mul_le_mul (mem_ball_zero_iff.mp hz|>.le) (le_add_of_nonneg_right zero_le_one) (norm_nonneg _) hd.le); unfold δ; field_simp; linarith
  have hJ : ∀ᶠ i in atTop,MapsTo (w i) T G:=by
    filter_upwards [(hQ.eventually (ball_mem_nhds x (show 0<r/2 by positivity))),hV.norm.eventually (gt_mem_nhds (lt_add_one _))] with i hi hh
    intro z hz; apply hR; rw [mem_ball]
    calc
      _ ≤ dist (w i z) (u i)+ dist (u i) x:= dist_triangle ..
      _ < δ*(‖y‖+1)+r/2:= add_lt_add_of_le_of_lt (by unfold w; rw [dist_eq_norm,add_sub_cancel_left,norm_smul]; exact mul_le_mul (mem_ball_zero_iff.mp hz|>.le) hh.le (norm_nonneg _) hd.le) (mem_ball.mp hi)
      _< _:=by unfold δ; field_simp; nlinarith only [norm_nonneg y,hr]
  have ht: TendstoUniformlyOn (fun i=> F ∘ w i) (F ∘ g) atTop T:=by
    refine Metric.tendstoUniformlyOn_iff.mpr ?_
    intro ε hε
    let b i:=dist (u i) x+δ*‖v i-y‖
    have he' : Tendsto (fun i=>(L:ℝ)*b i) atTop (𝓝 0):=by
      have hv:= Tendsto.const_mul (L:ℝ) ((hQ.dist (tendsto_const_nhds (x:=x))).add ((hV.sub_const y).norm.const_mul δ))
      simpa using! hv
    filter_upwards [hJ, he'.eventually (gt_mem_nhds hε)] with i hp he
    intro z hz
    have hg : dist (w i z) (g z) ≤ b i:= (dist_add_add_le ..).trans (by
       nth_rw 2 [dist_eq_norm]; rw [← smul_sub,norm_smul]; exact add_le_add_right (mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hz|>.le) (norm_nonneg _)) _)
    rw [dist_comm]; exact (le_trans (hF.dist_le_mul _ (hp hz) _ (hm z hz)) (mul_le_mul_of_nonneg_left hg L.property)).trans_lt he
  refine (ht.tendstoLocallyUniformlyOn.differentiableOn (hJ.mono fun i H=> fun z hz=> ?_) isOpen_ball).differentiableAt (ball_mem_nhds _ hd)
  have hu : w i z∈ S:= S.add_mem (hu i) (S.smul_mem z (hv i)); let f(y:ℂ):= F (w i z+y • v i)
  have ht : DifferentiableAt ℂ f (z-z):= by rw [sub_self]; exact hp _ (H hz) hu _ (hv i)
  apply DifferentiableAt.differentiableWithinAt; apply (ht.comp (f:=fun w=> w-z) z (show DifferentiableAt ℂ (fun t=> t-z) z from differentiableAt_id.sub_const _)).congr_of_eventuallyEq
  filter_upwards with u; change F (w i u)=F (w i z+ (u-z) • v i); unfold w; rw [sub_smul,add_assoc,add_sub_cancel]
lemma across (hY: Dense (S:Set X))(hF : LipschitzOnWith L F G)
    (hp:∀ x∈G,x∈S →∀ y∈ S, DifferentiableAt ℂ (fun z:ℂ=> F (x+z • y)) 0) : Bumps G F := by
  intro T f ht h hf z hz
  let v:= deriv f z; let g(w:ℂ):= f z+(w-z) • v
  have he := (hf.differentiableAt (ht.mem_nhds hz)).hasDerivAt
  have hL : DifferentiableAt ℂ (fun z₁:ℂ=> F (f z+z₁ • v)) (z-z):= by rw [sub_self]; exact lineT F S (hs:=hs) hY hF hp (f z) (h hz) v -- hs unused?
  have hh := (show DifferentiableAt ℂ (fun w=> F (g w)) z from hL.comp (f:=fun w=> w-z) z (show DifferentiableAt ℂ (fun w=> w-z) z from differentiableAt_id.sub_const _)).hasDerivAt
  apply HasDerivWithinAt.differentiableWithinAt
  apply HasDerivAt.hasDerivWithinAt (f':=deriv (fun w=> F (g w)) z)
  have hG : g z=f z:=by simp [g]
  have hJ: Asymptotics.IsLittleO (𝓝 z) (fun x=> f x-g x) (fun x=> x-z):= he.isLittleO.congr_left (by intro i; unfold g; abel)
  have h' : Asymptotics.IsLittleO (𝓝 z) (fun w=> F (f w)-F (g w)) (fun x=> x-z):=by
    apply Asymptotics.IsBigO.trans_isLittleO _ hJ; refine Asymptotics.isBigO_iff.mpr ⟨L,?_⟩
    filter_upwards [ht.mem_nhds hz, (show Continuous g by unfold g; fun_prop).continuousAt.preimage_mem_nhds (x:=z) (by rw [hG]; exact hs.mem_nhds (h hz))] with w hw hv
    simpa only [dist_eq_norm] using! hF.dist_le_mul _ (h hw) _ (show g w∈G from hv)
  exact HasDerivAt.of_isLittleO ((hh.isLittleO.add h').congr_left (fun i=> by rw [hG]; abel))

omit hs [NormedSpace ℂ X] [NormedSpace ℂ Y] in
lemma wells {f:X→Y} {T:Set X} (h:LipschitzOnWith L f T) {M:ℝ}(he : ∀ x∈T, ‖f x‖≤ M) : ∃ F:X→Y,EqOn F f T∧ (∀ x∈closure T, ‖F x‖ ≤ M)∧ LipschitzOnWith L F (closure T):= by
  let F:= extendFrom T f
  have hX (x) (hx:x∈closure T): ∃ y,Tendsto f (𝓝[T]x) (𝓝 y):= by
    haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
    exact CompleteSpace.complete ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le h.uniformContinuousOn (by unfold nhdsWithin; exact inf_le_right))
  have hp: EqOn F f T:= fun x hx=> extendFrom_extends h.continuousOn x hx
  have hv: LipschitzOnWith L F (closure T):= LipschitzOnWith.closure (continuousOn_extendFrom Subset.rfl hX) (lipschitzOnWith_iff_dist_le_mul.mpr (fun i hi j hj=> by rw [hp hi,hp hj]; exact h.dist_le_mul i hi j hj))
  refine ⟨F,hp,fun x hx=> ?_,hv⟩
  haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  refine le_of_tendsto (tendsto_extendFrom (hX x hx)|>.norm) ?_; filter_upwards [self_mem_nhdsWithin] with y hy; exact he _ hy

variable [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X] [AddCommGroup R] [Module ℝ R]
variable (U:R→ₗ[ℝ] X){f : R→Y}{M:ℝ}(P:Firm U)(h:Charted U f M)
omit hs
include h P
open Charted
lemma conquest : ∃ F:X→Y, Bumps Grip F ∧ (∀ x∈Grip, ‖F x‖≤ M)∧(∀ x∈Grip,∀ y∈Grip, ‖F x-F y‖ ≤ M*‖x-y‖)∧∀ x, U x∈Grip → F (U x)=f x:=by
    have hS : IsOpen (Grip (X:=X)):= isOpen_ball
    have ht : 0 < rim:=by norm_num [rim]
    have hu := Charted.canvas U P h (x:=0) (mem_ball_self ht) ((undertone U).zero_mem)
    let L: ℝ≥0:=⟨M,(norm_nonneg _).trans hu⟩
    let v:= Charted.fill U f M
    let T:= well U; have hJ: Grip ⊆ closure T:= fun x hx=> IsOpen.inter_closure hS ⟨hx,P.runs x⟩
    obtain ⟨F,hF,hM,hL⟩:= wells (f:=v) (T:=T) (L:=L) (lipschitzOnWith_iff_dist_le_mul.mpr (fun x (hx:x∈Grip∩_) y (hy:y∈Grip∩_)=> by simp only [dist_eq_norm]; exact slides U P h hy.1 hy.2 hx.1 hx.2)) (fun x (hx:x∈Grip∩_)=> canvas U P h hx.1 hx.2)
    refine ⟨F, across F (undertone U) hS P.runs (hL.mono hJ) (fun x hx hs y hy=>?_),fun x hx=>hM _ (hJ hx), fun x hx y hy=> ?_, fun x hx=> (hF (show U x∈ T from ⟨hx,inkwell U x⟩)).trans (meets U P h x (mem_ball_zero_iff.mp hx))⟩
    · apply (gate U P h hx hs hy).congr_of_eventuallyEq; let g(z:ℂ):=x+z • y; have hg : g 0=x:=by simp [g]
      filter_upwards [(show Continuous g by unfold g; fun_prop).continuousAt.preimage_mem_nhds (x:=0) (by rw [hg]; exact hS.mem_nhds hx)] with z hz
      exact hF (show g z∈T from ⟨hz,(undertone U).add_mem hs ((undertone U).smul_mem _ hy)⟩)
    simpa only [dist_eq_norm] using! hL.dist_le_mul _ (hJ hx) _ (hJ hy)
end YM.UVExtension.Oriel
#print axioms YM.UVExtension.Oriel.conquest
