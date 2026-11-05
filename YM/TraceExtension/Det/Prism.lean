import YM.TraceExtension.Det.Kith

/-! # Charges from returned rooted germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}
    {I:Type} [Fintype I]{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
    {o:Site f}{F:Rays I→ X}{l:I→ Site f}{m n:ℕ}{α β C D A:ℝ}
variable {Y:Gal G f}{Z:Peat G f}
lemma deck_costn [DecidableEq I] (w:I→ℕ)(hw:∀ i,w i=separation o (l i))(h:cost w α n 0 (leaf F 0 m) ≤ C)(hp:0 ≤ α)(v:Fin m → I)(M:ℕ)(hh:(m:ℝ) ≤ (M+1:ℝ)): ‖entry F 0 v‖ ≤ C*Real.exp (-(α/(M+1:ℝ))*spanSites l o v):=by
    let r:= spanSites l o v; let W:=limitN w v
    have hx: r ≤ m*W:=by
       unfold r spanSites; refine (sum_le_sum (fun i _=>?_)).trans_eq (show ∑ _i:Fin m,W=m*W by simp)
       rw [←hw]; exact limitN_ge ..
    have ht: (r:ℝ) ≤ (M+1:ℝ)*W:= by exact (show (r:ℝ) ≤ m*(W:ℝ) by exact_mod_cast hx).trans (mul_le_mul_of_nonneg_right hh (by positivity))
    have he:= mul_le_mul_of_nonneg_left ht (show 0 ≤ α/(M+1:ℝ) by positivity)
    have he':α/(M+1:ℝ)*(r:ℝ) ≤ α*(W:ℝ):=he.trans_eq (by field_simp)
    have hu: Real.exp (α*(W:ℝ)) ≤ spot α n 0 W:=by unfold spot Perfect.shelter; rw [sub_zero,max_eq_right (by positivity)]; exact le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ (show 1 ≤ 1+(W:ℝ) by simp))
    change _≤C*Real.exp (-(α/(M+1:ℝ))*(r:ℝ)); rw [neg_mul, Real.exp_neg,← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),mul_comm]
    have hv: leaf F 0 m v=entry F 0 v:=by unfold Perfect.leaf bank entry; congr 1; ext i j; by_cases he:j=v i<;>simp [bolt,desk,he]
    rw [← hv]; exact (mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr he').trans hu) (norm_nonneg _)).trans ((Finset.single_le_sum (f:=fun i=> spot α n 0 (limitN w i)*‖leaf F 0 m i‖) (fun i _=> mul_nonneg (spot_pos .. |>.le) (norm_nonneg _)) (mem_univ v)).trans h)
lemma estate_charge {W:Acr G f→ ℝ} (h:Estate o W α (fun _=>C))(hc:0≤C)(ha:0≤α)(hw:ContDiffAt ℝ ω W 0)(hx:W 0=0)(hv:fderiv ℝ W 0=0): Pet (af G f) o W (α/5) C 4:=by
    refine ⟨hw,fun i hi q=>?_⟩; match i with
    | 0=> unfold entry; rw[iteratedFDeriv_zero_apply,hx]; simp only [norm_zero]; positivity
    | 1=> unfold entry; rw[iteratedFDeriv_one_apply,hv]; simp; positivity
    | j+2=> have ht:=deck_costn (l:=af G f) (landW o) (a_f G f o) (h.values _ hi (by omega)) ha q 4 (by exact_mod_cast (show j+2 ≤ 4+1 by omega)); norm_num at ht; simpa only [Real.norm_eq_abs,neg_mul] using ht
lemma pea_loom (h:Z∈loom G f)(hp:Estate o (ballX Z) α (fun _=>C))(hc:0≤C)(ha:0≤α): Pet Prod.fst o (Z ∘ input G f) (α/5) C 4:=by
    obtain ⟨hz,hx,hv⟩:=loom_read h; have hh:=estate_charge hp hc ha hv hz hx
    have he:=hh.compL (p:=Sum.inl) (taken G f); refine he.grows (F:= ballX Z ∘ takea G f) (Eventually.of_forall fun x=>?_)
    change Z (input _ _ (bite G f (takea G f x)).1)=_; rw[at_take];rfl
lemma bot_pick (h: Y ∈ rains G f)(y:Lines G f 1):
    (fun z=> fderiv ℝ (bottom Y) (takea G f z) (bolt (.inr y)))=ᶠ[𝓝 0] fun z=> Y (input G f z) y:=by
    filter_upwards [(show Tendsto (takea G f) (𝓝 0) (𝓝 0) from by simpa using (takea G f).continuous.tendsto 0).eventually ((rain_read h).2.2.1.eventually (by simp))] with z hz
    let A:=bottom Y; let B:=takea G f z; let g(s:ℝ):=B+s • bolt (Sum.inr y); have hp: HasDerivAt g (bolt (Sum.inr y)) 0:= (ray_id _).const_add _; have ht : g 0=B:=by simp[g]
    have hx: A ∘ g= fun s:ℝ=> s* Y (input G f z) y:=by
        funext s; unfold A bottom; dsimp only [Function.comp_apply]
        change Y (input G f (aleft G f (g s))) ⬝ᵥ aright G f (g s)=_; unfold g B; rw[map_add,map_add,map_smul,map_smul,al_take,ar_take,bite_lr,bite_r,smul_zero, add_zero,zero_add,dotProduct_smul]; congr 1
        simp [dotProduct,bolt,Pi.single_apply]
    refine HasDerivAt.unique (f:= A ∘ g) ((show HasFDerivAt A (fderiv ℝ A B) (g 0) from ht.symm ▸ (hz.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hp) ?_; rw[hx]; simpa using! (hasDerivAt_id (x:=(0:ℝ))).mul_const (Y (input G f z) y)
lemma pea_rain (h:Y∈ rains G f)(hp:Estate o (bottom Y) α (fun _=>C))(hc:0≤C)(ha:0≤α)(k:Lines G f 1): Pet Prod.fst o (fun z=> Y (input G f z) k) (α/5) (C*Decay (α/5) o k.1) 3:=by
    obtain ⟨hz,hx,hv,_⟩:=rain_read h; have hh:=estate_charge hp hc ha hv hz hx
    have hu:= Pet.halp (m:=3) hh (.inr k); exact (hu.compL (taken G f)).grows (bot_pick h k)
lemma splitp_n : Army (splitp G f) 0:= (Army.powL (aright G f).contDiff.contDiffAt).mul (Army.powL (aleft G f).contDiff.contDiffAt)
lemma splitp_0 : splitp G f 0=1:=by simp[splitp]
lemma cocoa_m (G:Gauge)(m:ℕ): ∃ T:ℝ,0≤T∧∀ (f:Side)(x:Site f)(K:Config G f→X)(a C:ℝ),0≤C→0≤a→ Pet Prod.fst x (K ∘ input G f) a C m → Pet (af G f) x (K ∘ splitp G f) (a/(m+1:ℝ)) (C*T) m:=by
    obtain ⟨A,hA,h⟩:= speak G m
    refine ⟨_,lodge_n (m:=m) (A:=1+A*(Fintype.card (Loc G 1))) (by positivity),fun f x K a C hc ha hp=>?_⟩
    have hf:= hp.rein (h f) (show bchip G f 0=0 by rw[bchip,splitp_0,content_one]) hA hc ha (pay_gate G f); refine hf.grows ?_
    filter_upwards[(show Tendsto (splitp G f) (𝓝 0) (𝓝 1) from splitp_0 ▸ splitp_n.cont.tendsto).eventually content_encodes] with z hz;exact congr_arg K hz
-- no coefficient cost to choose y relative x quadratic issue
lemma color_tale (G:Gauge): ∃ L:ℝ,0≤L ∧ ∀ (f:Side)(K : Gal G f)(x:Site f)(a C:ℝ)(m), 0≤C→(∀ i:Lines G f 1, Pet Prod.fst x (fun z=> K (input G f z) i) a (C*Decay a x i.1) m) → ∀ e:Edge (Site f), Pet Prod.fst x (fun z=> edgeColor (K (input G f z)) e) a (C*L*Decay a x e.1) m:=by
    let L:= (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).symm.toContinuousLinearMap
    refine ⟨‖L‖,norm_nonneg _,fun f K x a C m ha h e=>?_⟩
    let F(z:Link G f):=fun k:G.ColorIndex=>edgeColor (K (input G f z)) e k
    have ht:= (Pet.seven (G:=F) (mul_nonneg ha (decay_pos a x e.1|>.le)) (fun i=>h (e.1,coord e.2,i))).monoL L
    rw [← mul_assoc,mul_comm _ C] at ht; exact ht
-- also no input mix
lemma Pet.left_z {V:Link G f→ X}(h:Pet Prod.fst o V α C m)(hc:0≤C): Pet (af G f) o (V ∘ aleft G f) α C m:=by
    let L:=aleft G f; refine ⟨(show ContDiffAt ℝ ω V (L 0) from (map_zero L).symm ▸ h.1).comp _ L.contDiff.contDiffAt,fun i hi q=>?_⟩
    unfold entry; rw[iter_lin_at ((map_zero (aleft G f)).symm ▸ h.1.of_le le_top),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]
    by_cases he:∀ j:Fin i, ∃ u:Lines G f 1,q j=.inl u
    · choose g hg using he; rw [show (fun j=> aleft _ _ (bolt (q j)))=(fun j:Fin i=>bolt (g j)) from funext fun j=>by rw[hg,bite_l]]; rw[show q=(Sum.inl ∘ g) from funext hg]; exact h.2 _ hi g
    push Not at he; obtain ⟨j,hj⟩:=he
    rw[ContinuousMultilinearMap.map_coord_zero (i:=j),norm_zero]; exact mul_nonneg hc (Real.exp_pos _).le
    cases hv:q j with
    | inl x=> exact False.elim (hj x hv)
    | inr x=> exact bite_lr G f x
end YM.Trace.Det
