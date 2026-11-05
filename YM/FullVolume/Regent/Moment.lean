import YM.FullVolume.Regent.Columns
/-! Meta Norm over Atom & M.L copies. Conv.Variation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Beacon
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Next.Free.Retort Tralis Shade
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:Side}{σ η:ℝ}{t:ℕ}[NeZero t]
def fee (σ η:ℝ)(C:Cameo G t):= ∑' i, (ringT σ C i).budget η
lemma permits (h:η<σ)(C:Cameo G t): SumBudget (fun i=> (ringT σ C i).budget η) (fee σ η C):= let R:= radius σ C h ‖C‖ le_rfl; ⟨R.1,R.2.1,le_rfl⟩
lemma cover_at (h:η<σ)(C:Cameo G t):0≤fee σ η C:= tsum_nonneg (permits h C).1
lemma money {C:Cameo G t}(h:η<σ)(hp: fee σ η C=0): C=0:=by
    apply lp.ext; funext k; rcases k with ⟨i,j⟩
    have hx := permits h C
    have hb : chants t (η-σ) i* ‖C (i,j)‖≤0:=by
       calc
        _ ≤ (ringT σ C i|>.budget η):=by rw [feel]; exact Finset.single_le_sum (f:=fun j=>chants t (η-σ) i * ‖C (i,j)‖) (fun i _=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (Finset.mem_univ j)
        _ ≤ ∑ k∈ ({i}:Finset ℕ), (ringT σ C k).budget η := by simp
        _ ≤ _ := (hx.2.1.sum_le_tsum _ (fun i _=> hx.1 i)).trans_eq hp
    exact norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right hb (Real.exp_pos _)) (norm_nonneg _))
lemma everybody (h:η<σ) (C:Cameo G t)(r:ℝ): fee σ η (r • C)=|r| * fee σ η C:=by
   unfold fee; rw [←tsum_mul_left]; refine tsum_congr fun i=>?_ ; rw [feel,feel, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [lp.coeFn_smul,Pi.smul_apply,norm_smul,Real.norm_eq_abs]; ring
lemma cord {η σ:ℝ}(S T:Cameo G t) (i:ℕ): (ringT σ (S+T) i).budget η ≤ (ringT σ S i).budget η+(ringT σ T i).budget η:=by
   simp_rw [feel,← Finset.sum_add_distrib]; refine Finset.sum_le_sum fun j _=>?_ ; rw [lp.coeFn_add,Pi.add_apply,← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (Real.exp_pos _).le
lemma charge (h:η<σ)(S T:Cameo G t): fee σ η (S+T)≤ fee σ η S+fee σ η T:=by
   unfold fee; have he:=(permits h S).2.1; have ht:=(permits h T).2.1; rw [← he.tsum_add ht]; exact (permits h (S+T)).2.1.tsum_le_tsum (cord S T) (he.add ht)
lemma grime (h:η<σ)(S T:Cameo G t): fee σ η (S-T)≤ fee σ η S+fee σ η T:=by
   rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact (charge h S ((-1:ℝ) • T)).trans_eq (by rw [everybody h]; simp) -- simp risk
lemma lustre {F:Cameo G t}{f:ℕ→ Cameo G t}{b:ℝ}(H:Gleam f F b)(h:η<σ): Tendsto (fun i=> fee σ η (f i)) atTop (𝓝 (fee σ η F)):=by
   unfold fee; simp_rw [feel]; let W(i:ℕ):=(Fintype.card (Ink G (t+1)):ℝ)*b*chants t (-(σ-η)) i
   refine tendsto_tsum_of_dominated_convergence (bound:=W) ((silts t (sub_pos.mpr h)).mul_left _) (fun i=>tendsto_finsetSum _ fun j _=> (H.hinge (i,j)).norm.const_mul _) (H.budget.mono fun i hi x=>?_)
   change ‖∑ j: Ink G (t+1), chants _ _ _*‖(f i) (x,j)‖‖ ≤ _
   rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _=> mul_nonneg (show 0 ≤ chants t (η-σ) x from (Real.exp_pos _).le) (norm_nonneg _))]
   calc
    _ ≤ ∑ _ :Ink G (t+1),chants t (η-σ) x*b:=Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_left ((lp.norm_apply_le_norm (by norm_num) (f i) _).trans hi) (Real.exp_pos _).le
    _ = _:=by unfold W; simp; ring
lemma trinket {F X:Cameo G t}{f u:ℕ→Cameo G t}{b B:ℝ}(H:Gleam f F b)(hp:Gleam u X B)(h:η<σ): Tendsto (fun i=> fee σ η (f i-u i)) atTop (𝓝 (fee σ η (F-X))):= by
    apply lustre (h:=h) (b:=b+B) (f:=fun i=> f i-u i); constructor
    · filter_upwards [H.budget,hp.budget] with i hi hj; exact (norm_sub_le ..).trans (add_le_add hi hj)
    intro i; exact (H.hinge i).sub (hp.hinge i)

lemma compassion {F:Cameo G t}{f:ℕ→ Cameo G t}{b B:ℝ}(H:Gleam f F B)(h:η<σ)(hf:∀ᶠ i in atTop,AtomWall (ringT σ (f i)) η b): AtomWall (ringT σ F) η b:=by
   have hp:= permits h F; refine ⟨⟨hp.1,hp.2.1,le_of_tendsto (lustre H h) (hf.mono fun i hi=> hi.1.2.2)⟩,?_⟩
   intro i u x; let V:= G.adjoint u; let f' (C:Cameo G t) (z:Fin (t+1)→G.Color):=(ringT σ C i).poly z
   have he (x): Tendsto (fun i' => f' (f i') x) atTop (𝓝 (f' F x)):=by unfold f' Atom.poly; exact tendsto_finsetSum _ fun j _=> ((H.hinge (i,j)).div_const _).mul_const _
   exact tendsto_nhds_unique (((he (fun j=> V (x j)))).congr' (hf.mono fun k hi=> hi.2 i u x)) (he x)
lemma brands {R:PathData G} {p:Clip}{w a c:ℝ}(h:R.Bounds p w a c) : Bs G R.loop:=by
   intro i x Q H; have he : Q.loop_coeff i x = R.loop_coeff i x := by funext k; unfold PathData.loop_coeff; rw [H]
   have hz := h.loopTerms i x; have hk := h.loop_normal i x; rw [he]
   exact ⟨hk.1 ▸ hz.1.hasSum, fun l=> hk.2 l ▸ (hz.2 l).hasSum⟩
lemma consulates {F:Cameo G 1}{f:ℕ→Cameo G 1}{b:ℝ}(H:Gleam f F b)(h:0<σ)(ht: ∀ᶠ i in atTop, (Bs G (ringT σ (f i))) ∧ ∀ j,(ringT σ (f i) j).Invariant): Bs G (ringT σ F):=by
    let V:= Shade.cut G σ h; haveI : CompleteSpace V.s:= V.quiet.completeSpace_coe
    apply ((silver h F).1 ?_).1
    suffices hp:F∈V.sᗮᗮ by rwa [Submodule.orthogonal_orthogonal] at hp
    intro x hx
    rw [real_inner_comm]; exact tendsto_nhds_unique_of_eventuallyEq (H.testing x) tendsto_const_nhds (ht.mono fun i h' => hx _ ((silver h _).2 h'))
end YM.Stationary.Beacon
