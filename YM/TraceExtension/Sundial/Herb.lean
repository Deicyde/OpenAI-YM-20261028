import YM.TraceExtension.Sundial.Night
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(H:(Bel C.book).Hierarchy)(K:S.Hierarchy)
local notation "F₀"=> Bel C.book
variable {P P':ℝ→change S 4}(hQ:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)(ht:Tendsto (fun t=>moveV (S:=S) 4 (P t) (P' t)) Pilot.trail (𝓝 1))
include H K hQ ht
local instance(n:ℕ): ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
set_option maxHeartbeats 800000 in
lemma reconst {n:ℕ} (v:Fin n→(Bel C.book).Field 4)(k:ℕ)(s:Set (Points n))(hs:IsCompact s)(he:s⊆conf n)(ε:ℝ)(hε:0<ε):∀ᶠ r in Pilot.trail,∀ x∈s,
     ‖iteratedFDeriv ℝ k (fun q=> S.classMoment S (fun _=>4) (r • q) (fun j=>P' r (v j))) x-iteratedFDeriv ℝ k (fun q=>(F₀).classMoment (F₀) (fun _=>4) q v) x‖≤ε:=by
    let I:= Fin n→ PegC C 4; let M:=PoleC C 4; let V(i:I):= M∘i; let β(w:Fin n→(Bel C.book).Field 4)(i:I):= ∏ j:Fin n,(M.repr (w j)) (i j); let q(t:ℝ):= moveV (S:=S) 4 (P t) (P' t); let w(t)(j):= q t (v j)
    have hv(i:I): Tendsto (fun t=> β (w t) i) Pilot.trail (𝓝 (β v i)):=by
        apply tendsto_finsetProd; intro j hj; exact ((M.coord (i j)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (Dash.arcing ht (tendsto_const_nhds (x:=v j))))
    let Z(x:Points n):=(F₀).classMoment (F₀) (fun _=>4) x; let b(i:I):=fun x=> Z x (V i); let Y(t:ℝ)(x:Points n):=(S.classMoment S (fun _=>4) (t • x)).compLinearMap fun _=>(P t).toLinearMap; let B(t:ℝ)(i:I)(x:Points n):= Y t x (V i); let m:= max 1 (Fintype.card I:ℝ)
    have hh (A:MultilinearMap ℂ (fun _ : Fin n=> (Bel C.book).Field 4) ℂ) (w: Fin n→(Bel C.book).Field 4): A w= ∑ i:I,β w i • (A (V i)):=by
       conv_lhs=> rw [show w= fun j=> ∑ i, M.repr (w j) i • M i from funext (fun i=> (M.sum_repr _).symm)]
       rw [MultilinearMap.map_sum];exact Finset.sum_congr rfl fun i _=> A.map_smul_univ _ _
    have hC(i:I):ContDiffOn ℝ k (b i) (conf n):=((F₀).class_smooth (F₀) H.smooth (fun j:Fin n=>⟨4,V i j⟩)).of_le (WithTop.coe_le_coe.mpr le_top)
    let a(t:ℝ)(i:I):=β (w t) i; let d:=ε/(2*m); have hm:0 < m:= lt_max_of_lt_left zero_lt_one; have hd:0<d:=by unfold d; positivity
    have hp(i:I):∀ᶠ t in Pilot.trail,∀ x∈s,‖a t i • iteratedFDeriv ℝ k (B t i) x- β v i • iteratedFDeriv ℝ k (b i) x‖ ≤ d+d:=by
       let f(x):=‖iteratedFDeriv ℝ k (b i) x‖; have he':ContinuousOn f s:=by
           refine ContinuousOn.mono (s:=conf n) ?_ he; exact ((hC i).continuousOn_iteratedFDerivWithin le_rfl (conf_open n).uniqueDiffOn).norm.congr (fun x hx=> congr_arg Norm.norm ((iteratedFDerivWithin_of_isOpen (𝕜:=ℝ) (f:=b i) k (conf_open _) hx).symm))
       obtain ⟨T,hT⟩:= (hs.image_of_continuousOn he').bddAbove; let t:=max T 1; let c:=‖β v i‖+1; have ht:0<t:=by unfold t; positivity
       have hc:0 < c:=by unfold c; positivity
       filter_upwards [Metric.tendsto_nhds.mp (hv i) (d/t) (by positivity), jets K H P hQ (V i) k s hs he (d/c) (by positivity), (hv i|>.norm).eventually (ge_mem_nhds (lt_add_one _))] with r hr hh hx z hz
       have h₁: ‖a r i‖≤ c:= hx; have h₂:‖a r i-β v i‖ ≤ d/t:= (dist_eq_norm (a r i) (β v i)).symm.trans_le hr.le; let U:= iteratedFDeriv ℝ k (B r i) z; let p:= iteratedFDeriv ℝ k (b i) z; have h₃:‖U-p‖≤ d/c:= (hh z hz).le; have h₄:‖p‖≤t:= le_trans (show f z ≤ T from hT (mem_image_of_mem _ hz)) (le_max_left ..)
       calc ‖a r i • U- β v i • p‖ = ‖a r i • (U-p)+(a r i-β v i) • p‖:=by rw[smul_sub,sub_smul]; congr 1;abel
            _ ≤ ‖a r i • (U-p)‖+‖(a r i-β v i) • p‖:= norm_add_le ..
            _ ≤ _:=by simp only[norm_smul]; refine add_le_add ?_ ?_; apply (mul_le_mul h₁ h₃ (norm_nonneg _) hc.le).trans_eq (mul_div_cancel₀ _ hc.ne');exact (mul_le_mul h₂ h₄ (norm_nonneg _) (by positivity)).trans_eq (div_mul_cancel₀ _ ht.ne')
    filter_upwards [eventually_all.mpr hp,self_mem_nhdsWithin] with t ht hu x hx
    have hu : t • x∈conf n:= Work.A05.smul_conf (show 0<t from hu) (he hx)
    have hz(i:I): ContDiffAt ℝ k (B t i) x:= (((S.class_smooth S K.smooth (fun j:Fin n=>⟨4,P t (V i j)⟩)).contDiffAt ((conf_open _).mem_nhds hu)).of_le (WithTop.coe_le_coe.mpr le_top)).comp x (contDiffAt_id.const_smul t)
    have hK(i:I): ContDiffAt ℝ k (b i) x:= (hC i).contDiffAt ((conf_open n).mem_nhds (he hx))
    simp_rw [show ∀ j:Fin n,P' t (v j)=P t (w t j) from fun j=> (LinearEquiv.apply_symm_apply (P t) _).symm]
    change ‖iteratedFDeriv ℝ k (fun p=>Y t p (w t)) x-iteratedFDeriv ℝ k (fun p=>Z p v) x‖ ≤ ε
    rw [show (fun p=> Y t p (w t))=(fun p=> ∑ i:I,a t i • B t i p) from funext fun p=> hh (Y t p) _,show (fun p=> Z p v)=(fun p=>∑ i:I,β v i • b i p) from funext fun p=> hh (Z p) v]
    rw [iteratedFDeriv_fun_sum_apply (f:=fun i p=> a t i • B t i p) (fun i _=> (hz i).const_smul _),iteratedFDeriv_fun_sum_apply (f:=fun i p=> β v i • b i p) (fun i _=> (hK i).const_smul _),← Finset.sum_sub_distrib];
    apply (norm_sum_le ..).trans; apply le_trans (b:=∑ _:I, (d+d)) ?_ ?_
    · apply Finset.sum_le_sum; intro i _; simp only[iteratedFDeriv_const_smul_apply' (hz i),iteratedFDeriv_const_smul_apply' (hK i)]; exact ht i _ hx
    rw[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; refine (mul_le_mul_of_nonneg_right (le_max_right 1 _) (by positivity : 0≤d+d)).trans_eq ?_; change m*(d+d)= ε; unfold d;field_simp;ring
end YM.Trace.Sundial
