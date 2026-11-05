import YM.FullVolume.Shroud.Colonnade
import YM.FullVolume.Dusk.Law
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Dusk
open Filter Function Set Extraction
open scoped BigOperators Matrix.Norms.Frobenius Topology ContDiff Classical
variable {X Y Z : Type*}
lemma pebbled {a b:ℕ→ Y}[PseudoMetricSpace Y][CompleteSpace Y] (h:∀ c:ℕ→Y, (∀ i,c i=a i ∨ c i=b i)→CauchySeq c) : Tendsto (fun n=> dist (a n) (b n)) atTop (𝓝 0):=by
    let f(n:ℕ):= if n%2=0 then a n else b n; obtain ⟨x,hx⟩:= cauchySeq_tendsto_of_complete (h a (fun _=> Or.inl rfl)); obtain ⟨y,hy⟩:= cauchySeq_tendsto_of_complete (h b (fun _=> Or.inr rfl)); obtain ⟨z,hz⟩:= cauchySeq_tendsto_of_complete (h f (fun i=>by unfold f; split; exact Or.inl rfl; exact Or.inr rfl))
    let g (n:ℕ):ℕ:=2*n; let u (n:ℕ):=2*n+1; have hfg:Tendsto g atTop atTop:= tendsto_atTop_mono (f:=id) (fun n=>by dsimp [g]; omega) tendsto_id; have hfu:Tendsto u atTop atTop:=tendsto_atTop_mono (f:=id) (fun n=>by dsimp [u]; omega) tendsto_id
    have hpq: dist x z=0:=tendsto_nhds_unique (((hx.comp hfg).dist (hz.comp hfg)).congr' (Eventually.of_forall (p:=fun i=>dist (a (g i)) (f (g i))=(0:ℝ)) fun i=>by unfold g f; rw [if_pos (by omega),dist_self])) tendsto_const_nhds
    have hf: dist y z=0:=tendsto_nhds_unique (((hy.comp hfu).dist (hz.comp hfu)).congr' (Eventually.of_forall (p:=fun i=> dist (b (u i)) (f (u i))=(0:ℝ)) fun i=> by unfold u f; rw [if_neg (by omega),dist_self])) tendsto_const_nhds
    have he:dist x y=0:= le_antisymm (by linarith only [dist_triangle x z y,hpq,hf,dist_comm z y]) dist_nonneg; exact he ▸ hx.dist hy
lemma laurels {t:ℕ→ Y→ ℝ}{x y:ℕ→ Y}{u :ℝ} (P:∀ i,Y → ℂ)(he:Tendsto (fun i=>t i (x i)) atTop (𝓝 u))(hp:Tendsto (fun i=>t i (y i)) atTop (𝓝 u))(h:∀ z:ℕ→Y,Tendsto (fun i=>t i (z i)) atTop (𝓝 u) → CauchySeq (fun i=> P i (z i))): Tendsto (fun i=> dist (P i (x i)) (P i (y i))) atTop (𝓝 0):=by
    refine pebbled (fun f hf=>?_)
    let z (i:ℕ):= if f i=P i (x i) then x i else y i
    have hz: f=fun i=> P i (z i):= funext fun i=>by
                         unfold z; split; assumption
                         next h=> exact (hf i).resolve_left h
    rw [hz]; refine h z (tendsto_iff_forall_eventually_mem.mpr (fun s hs=>?_)); filter_upwards [he.eventually hs,hp.eventually hs] with i hi hk; unfold z; split; exact hi; exact hk
open Extra.Histories
-- variable bounded labels.Mod.L.
variable {G:Gauge}{C:Family G}(d n:ℕ)
set_option quotPrecheck false
local notation "F"=> C.labels.level d
lemma militia (P:ℕ → MultilinearMap ℂ (fun _ :Fin n=> C.label d) ℂ) (v:ℕ→Fin n→ C.label d)(Z:ℝ) (hv:0≤ Z)(hp:∀ i j, ‖v i j‖≤ Z)
    (hf:∀ x,Tendsto (fun i=>P i x) atTop (𝓝 0)):Tendsto (fun i=> P i (v i)) atTop (𝓝 0):=by
    let t (b:Fin n→ (F).Index)(i:ℕ):ℂ:=(∏ j:Fin n,v i j (b j))*P i (fun j=> Extra.Histories.Size.axis (F) (b j));
    have hx(i):P i (v i)=∑ b:Fin n→(F).Index,t b i:=by
       let g(j:Fin n) (b:(F).Index):=v i j b • Extra.Histories.Size.axis F b
       rw [show v i=(fun j=>∑ b,g j b) from funext fun j=> (Extra.Histories.Size.sum_axes F (v i j)).symm,(P i).map_sum g]; refine Finset.sum_congr rfl fun a _=> ?_; exact (P i).map_smul_univ _ _
    have he(b) :Tendsto (t b) atTop (𝓝 0):=by
        rw [tendsto_iff_norm_sub_tendsto_zero]; simp_rw [sub_zero]
        let X j:= Extra.Histories.Size.axis F (b j); have hu:= (hf X).norm.const_mul (Z^n); rw [norm_zero,mul_zero] at hu; refine squeeze_zero (fun i=> norm_nonneg _) (fun i=> ?_) hu
        unfold t; rw [norm_mul,norm_prod]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); exact (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> le_trans (norm_le_pi_norm _ _) (hp i j))).trans_eq (by simp) -- binder cost
    simp_rw [hx]; simpa using! tendsto_finsetSum _ (fun i _=>he i)
end YM.FullVolume.Dusk
#print axioms YM.FullVolume.Dusk.laurels
#print axioms YM.FullVolume.Dusk.militia
