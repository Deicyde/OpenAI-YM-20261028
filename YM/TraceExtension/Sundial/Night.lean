import YM.TraceExtension.Sundial.Yawn
import YM.TraceExtension.Sundial.Noon

/-! Transfer *leading* trace coefficient to arbitrary other alignment with
 only the leading position normalization on this sector, allowing also
 uncentered unit mixing. Orientation fixed by UV prescription, not by tests
 of the trace field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
variable {P P':ℝ→change S 4}(hP:PlotX F H 𝓛 h P)(hQ:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)
variable {χ:E4→ℝ}{x y:ℝ→ℝ}(p:Posed H h P P' x y)(q: ShellNorm P' χ)

-- unselected normalization of scalar
section
variable {L:Register G}{T:Table L}
def oval (t:T.Field 4)(x:Points 2):= T.classMoment T (fun _=>4) x (fun _=> centering T 4 t)
lemma oval_real(t:T.Field 4)(x:Points 2)(a:ℝ): oval (a • t) x= a^2 • oval t x:=by
   unfold oval; let F:=T.classMoment T (fun _=>4) x; let D:= centering T 4; rw[ (show D (a • t)=a • D t from (D.restrictScalars ℝ).map_smul ..)]
   have he (v: Fin 2→ T.Field 4): F (fun i=>(a:ℂ) • v i)= (∏ _ : Fin 2,(a:ℂ)) • F v := F.map_smul_univ _ _; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) a]; change F (fun i:Fin 2=>(a:ℂ) • D t)=a^2 • F (fun i:Fin 2=> D t);rw [show F (fun i:Fin 2=> (a:ℂ) • D t)=_ from he (fun _=> D t)]; simp[Complex.real_smul]
lemma oval_norm (t:T.Field 4)(x:Points 2)(H:T.Hierarchy): oval (centering T 4 t) x=oval t x:=by unfold oval; rw [show centering _ _ _=_ from zero_center (⟨_,center_lands H t⟩:Active T)]
end

def WickS(C:Family G):=oval (stepField C) sail
include h H in
lemma tax_nonzero : WickS C≠0:=by
    unfold WickS oval; have hz: centering (F₀) 4 (stepField C)=stepField C:= zero_center (⟨_,sceneV H⟩:Active (F₀))
    rw[hz]
    have hx:= Trace.wick_norm (L:=C.book) (x:=sail) (fun he=> zero_ne_one (sail_at he)); change _≠ (0:ℂ); apply ne_of_eq_of_ne hx
    apply Complex.ofReal_ne_zero.mpr; have ht:0 < G.lieDim:=by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos
    have hv : 0 < ‖sail 0-sail 1‖:= norm_pos_iff.mpr (sub_ne_zero.mpr fun he=> zero_ne_one (sail_at he)); positivity

structure Month (L:ℝ→change S 4): Prop where
    aligned : ∀ᶠ i in trail, AlignO F.sector F.room.kernel.spin H 4 (L i)
    oriented : ∀ᶠ i in trail,BranchV F 𝓛 H (centering S 4 (L i (stepField C)))
    compatible : Tendsto (fun i=> oval (L i (stepField C)) (i • sail)) trail (𝓝 (WickS C))
variable {L:ℝ→ change S 4}
include H
include h hP hQ
lemma december : Month (𝓛:=𝓛) F H P:=by
    let f:=stepField C; have he:∀ᶠ i in trail,centering S 4 (P i f)=P i f:=hP.mono fun i hi=> zero_center (⟨P i f,(show expectation S 4 _=0 by rw[hi.1.frame.cent]; exact sceneV H)⟩:Active S)
    refine ⟨hP.mono (fun i hi=>hi.1.frame.align),(he.and hP).mono (fun i hi=> (show centering S 4 _=_ from hi.1).symm ▸ hi.2.2),?_⟩
    have ht: centering (F₀) 4 f=f:=zero_center (⟨f, sceneV H⟩: Active (F₀))
    apply Metric.tendsto_nhds.mpr; intro ε hε; filter_upwards[he,Pilot.jets F.room.kernel H _ hQ (fun _:Fin 2=>f) 0 {sail} isCompact_singleton (singleton_subset_iff.mpr sail_at) ε hε] with s hs hV; specialize hV _ (mem_singleton _); rw [dist_eq_norm]; unfold WickS oval; rw[hs,ht]; rw [show ∀ F G:Points 2→ℂ, iteratedFDeriv ℝ 0 F sail-iteratedFDeriv ℝ 0 G sail=iteratedFDeriv ℝ 0 (F-G) sail from fun F G =>ContinuousMultilinearMap.ext (fun p=>by simp),norm_iteratedFDeriv_zero] at hV; exact hV
include hp
lemma lamplimit (p:Month (𝓛:=𝓛) F H L): ∃ f:ℝ→ ℝ,Tendsto f trail (𝓝 1)∧∀ᶠ i in trail, 0 < f i∧ centering S 4 (L i (stepField C))= f i • P i (stepField C):=by
    let t:=stepField C; have he:∀ᶠ i in trail,∃ f:ℝ,0<f∧centering S 4 (L i t)=f • P i t:=by
       filter_upwards [p.oriented,hP] with i hi hu
       obtain ⟨c,hc,hE⟩:= gardens F h _ hi hp.every; obtain ⟨d,hd,hS⟩:= gardens F h _ hu.2 hp.every; refine ⟨c/d,div_pos hc hd,?_⟩; change centering _ _ _=_ at hE; change P i t=_ at hS; rw[hS,hE,smul_smul,div_mul_cancel₀ _ hd.ne']
    let g(i:ℝ):=if h:∃ f:ℝ,0<f∧centering S 4 (L i t)=f • P i t then h.choose else 1; have hv:=he.mono (fun i hi=> (show 0 < g i∧ centering S 4 (L i t)= g i • P i t from by unfold g; rw[dif_pos hi]; exact hi.choose_spec)); refine ⟨g,?_,hv⟩
    let c:= WickS C; have hN:c ≠0:=tax_nonzero H h; have hh:=(december F H h hP hQ).compatible; have hx:= p.compatible.div hh hN; rw [div_self hN] at hx
    have hs:Tendsto (fun i=>(((g i)^2:ℝ):ℂ)) trail (𝓝 1):=by
        apply hx.congr'; filter_upwards[hv,hh.eventually_ne hN] with i hi hp; change oval (L i t) (i • sail)/oval (P i t) (i • sail)=_; rw [← oval_norm (L i t) (i • sail) F.room.kernel,hi.2, oval_real,Complex.real_smul,mul_div_cancel_right₀ _ (show oval _ _≠0 from hp)]
    have hp':Tendsto (fun i=>g i^2) trail (𝓝 1):= Complex.continuous_re.continuousAt.tendsto.comp hs
    have hx:= hp'.sqrt; rw[Real.sqrt_one] at hx; exact hx.congr' (hv.mono (fun i hi=> Real.sqrt_sq hi.1.le))

open TraceExtension
omit h hP hQ hp in

lemma upholster {L: change S 4}{t a d e:ℝ}(ht:Pith.Measures F t L a d e)(hp: AlignO F.sector F.room.kernel.spin H 4 L): t^ (4:ℕ) • lum F= (4*d) • centering S 4 (L (stepField C)):=by
   let K:= centering S 4; let M:=(F₀).unit 4; let T:= stressTrace F.sector.energy; have he:=ht.codes F; let u:=stepField C
   have hh:= congr_arg (fun R:Table.Stress S=>∑ i,R i i) he
   have hx:T=T:=rfl
   dsimp only at hh; simp only[Pi.add_apply,Pi.smul_apply,Pith.post, Finset.sum_add_distrib,Pith.erase,if_true, ← Finset.smul_sum] at hh
   have hK : K T=lum F:=by unfold T; rw[value_center];rw[onepoint];rfl
   rw[← hK];
   have hu (v:S.Field 4): ∑ _ : Axis,v=(4:ℝ) • v:=by rw [Fin.sum_univ_four]; module
   rw [← map_sum L, trace_none,map_zero,smul_zero,zero_add,hu,hu] at hh
   let V:=K.restrictScalars ℝ
   have hg:= congr_arg V hh; rw[hp.unit,map_smul,map_add,map_smul,map_smul,map_smul,map_smul, show V _=0 from const_out F.room.kernel.laws,smul_zero,smul_zero,add_zero,smul_smul, mul_comm d 4] at hg; exact hg
omit hP hQ in
lemma december_move (p:Month (𝓛:=𝓛) F H L): ∃ (d:ℝ→ℝ), (∀ᶠ i in trail,∃ a e, Pith.Measures F i (L i) a (d i) e) ∧ (∀ g:ℝ→ℝ,Coupling G g→Through g d (![0,d2 G]:Pilot.Jet)):=by
    obtain ⟨P,hP,hQ⟩:= glenned F h hp
    obtain ⟨x,hx,hX⟩:= lamplimit F H h hp (P:=P) hP hQ p
    obtain ⟨f,hS,hV⟩:= s_color F h hp P hP
    let d(i:ℝ):= f i/x i; let T:=stepField C
    refine ⟨d,?_,?_⟩
    · filter_upwards [p.aligned, hX, hS,hP] with i ht hv hu hb
      obtain ⟨a,d',e,hD⟩:= grossEnergy F h i (L i) ht
      have he:Pith.Measures F i (L i) a d' e:= ⟨fun k j=>by rw [hD]; by_cases he:k=j<;> simp[Pith.erase,he,add_assoc]⟩
      have hx:d i=d':=by
          have hp:= hu.symm.trans (upholster F H he ht); have he:P i T≠0:=fun hz=> (scale_alive h H) ((P i).injective (hz.trans (map_zero _).symm));rw [hv.2, smul_smul] at hp; unfold d; rw[div_eq_iff hv.1.ne']; apply mul_left_cancel₀ (by norm_num:(4:ℝ) ≠ 0); rw [← mul_assoc];exact smul_left_injective ℝ he hp
      exact ⟨a,e,hx.symm ▸ he⟩
    intro g hG; have hp:=(hV g hG).div hx one_ne_zero; rw [div_one] at hp; unfold Through; rw [show (![0,d2 G]:Pilot.Jet) 0=0 from rfl]; refine hp.congr (fun i=> ?_); change f i/_/x i= _; unfold d; ring
end YM.Trace.Sundial
