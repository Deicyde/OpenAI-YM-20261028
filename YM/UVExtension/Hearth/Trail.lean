import YM.UVExtension.Wren.Stage
import YM.UVExtension.Steady.Waves
import YM.UVExtension.Span.Egis
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Filter Function Metric Set RG Lattice Wilson MeasureTheory Finset
open Steady Span Push.AbsoluteSums SectorNext.Vacuum
open scoped BigOperators Topology ContDiff Classical
variable {ι κ π A :Type} {v:Filter ι} [v.NeBot] {G:Gauge} {n c d:Side} -- fields
variable {E:Type*}[NormedAddCommGroup E] [CompleteSpace E]
omit [CompleteSpace E] [v.NeBot] in
lemma fixedT {F:A→E}{r:ℝ}(h:∀ x,‖F x‖ ≤ r) : Tune v (fun (_:ι) x=>F x):= ⟨⟨_,Eventually.of_forall fun _=>h⟩,fun ε he=> by simp [he.le]⟩
omit [v.NeBot] in
lemma envelopeT {n:Side}{F:Config G n→ℂ} (h:Envelope F): Tune v (fun (_:ι) x=> F x):=by
   obtain ⟨r,hr⟩:= h.cost; exact fixedT hr
omit [v.NeBot] in
lemma mulT {f g:ι→ A→ℂ}(h:Tune v f)(p:Tune v g) : Tune v (fun n x=>f n x*g n x):= (h.prod p).cont (F:=fun (x : ℂ × ℂ)=> x.1*x.2) continuous_mul
omit [v.NeBot] in
lemma polysT {M:Type*}[NormedCommRing M]{z:κ→ι→A→M} (f:Finset κ)(h:∀ i∈f, Tune v (z i)) [ProperSpace M] : Tune v (fun i x=> ∏ j∈f,z j i x):=by
   induction f using Finset.induction with
   | empty=> simp only [Finset.prod_empty]; exact fixedT (fun x:A=>le_refl ‖(1:M)‖)
   | insert i f hi ih=> simp_rw [Finset.prod_insert hi]; exact ((h i (mem_insert_self ..)).prod (ih (fun i hh=>h i (mem_insert_of_mem hh)))).cont (F:=fun x:M×M=>x.1*x.2) continuous_mul
section
-- Path principal.e valuation at real, unnormalized.
variable {R:ι→ PathData G}{Q:PathData G}{σ:ℝ}(p:Revenues v σ R Q)(t:BudgetPoint)(C:Clip)
include p
lemma ellK (x:Face (Per n)): Tune v (fun i (U:Config G n)=> (R i).ell U x):=by
   let K:= fun i j=> (R i).ellTerms x j; apply Transit.includes (R:=K) _ (fun i j=>i)
   refine ⟨⟨_, (p.fees' x.2).scales 2 zero_le_two, ?_⟩,fun j=> ?_⟩
   · filter_upwards with i j u; unfold K PathData.ellTerms; rw [norm_smul, Real.norm_eq_abs,mul_comm _ ‖_‖]; exact mul_le_mul_of_nonneg_right (Slot.eval_norm ..) (abs_nonneg _)
   simp_rw [K,PathData.ellTerms,p.slots]; exact ((Tune.constant _ _ (p.starts x.2 j)).prod (fixedT (fun U=> (show ‖((Q.row x.2 j).2.atSite (U:Config G n) x.1)‖ ≤ 2 from Slot.eval_norm ..)))).cont (F:=fun x:ℝ × G.Color=> x.1 • x.2) continuous_smul
lemma baseAt (x:Face (Per n)): Tune v (fun i (U:Config G n)=> (R i).baseTerm C t U x):=by
   let D (U:Config G n):= PathData.clipped C t.threshold (G.chord (faceValue U x)); let F i U:=(R i).ell (U:Config G n) x
   obtain ⟨k,hk⟩:= PathData.clip_env (c:=C) t x (G:=G)|>.cost
   exact (fixedT hk).add (((ellK p x).cont (F:=fun y:G.Color=> ‖y‖^2/2) (by fun_prop)).mask (fun U=> PathData.kept C t.threshold x.1 U))
lemma atomsT (x:Site n)(k:ℕ)(f: PathData G→ℕ→Atom G k)(h:Revenues.bulk (σ:=σ) Q v R k f)(he:∀ i j,(f (R i) j).leg=(f Q j).leg): Tune v (fun i (U:Config G n)=> PathData.atomSeries (f (R i)) t U x):=by
   apply Transit.includes (R:=fun i j (U:Config G n)=> (f (R i) j).placed t U x) _ (fun i j=>i)
   refine ⟨⟨_,h.2.scales (2^k) (by positivity),?_⟩,fun j=>?_⟩
   · filter_upwards with i j U; rw [Real.norm_eq_abs,mul_comm (2^k) _]; exact ((f (R i) j).placed_bound t U x).trans (mul_le_mul_of_nonneg_right (Atom.lower_budget _ _ p.pos) (by positivity))
   simp_rw [Atom.placed,masked,Atom.footprint, Atom.stencil, Atom.unmasked, Atom.poly,he]
   apply Tune.mask; apply Tune.term
   intro l _; apply (Tune.constant _ _ (h.1 j l)).mul; apply polysT
   intro z hv; let L j (U:Config G n):=(f Q j).leg z|>.atSite U x; apply fixedT; intro U; change ‖L j U (l z)‖ ≤ (2:ℝ); rw [← EuclideanSpace.basisFun_inner G.ColorIndex (𝕜:=ℝ) (L j U) (l z)]; exact (norm_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one,one_mul]; exact Slot.eval_norm ..) -- refine metav
lemma prills (f:ι→ ℝ)(hx:∃ b,Tendsto f v (𝓝 b)): Tune v (fun i (U:Config G n)=> (R i).principal C t (f i) U):=by
   obtain ⟨b,hb⟩:=hx; let F(j:ι)(k:Site n):=k -- erase
   refine ((Tune.constant f b hb).mul ((Tune.term _ _ (fun i _=> baseAt p t C i)).add (Tune.term _ _ (fun i _=> ?_)))).add (Tune.term _ _ (fun i _=> ?_))
   · exact (atomsT p t i _ _ p.parked₂ (fun i=> (p.layout i).2.1)).add (atomsT p t i _ _ p.parked₃ (fun i=> (p.layout i).2.2))
   exact atomsT p t i _ _ p.parked₁ (fun i=>(p.layout i).1)
lemma turnsK (f:ι→ℝ)(h:∃ b,Tendsto f v (𝓝 b)): Tune v (fun i (U:Config G n)=> (R i).inChannels C t (f i) U):=by
   apply (fixedT (fun (_:Config G n)=> le_refl ‖(Fintype.card Signed:ℝ)⁻¹‖)).mul
   exact Tune.term _ _ (fun i _=> (prills p t C f h).cues (pull i (0:Site n)))
end
section rep
variable {R:ι→ Rep G n}{Q:PathData G}{σ:ℝ}(p:Revenues v σ (fun i=>(R i).path) Q) (h: StableR v R)
include h
omit [v.NeBot] in
lemma addOn : Tune v (fun i U=> (R i).activities.additive (R i).p U):=by
   let V i j:= (R i).activities.regularOccurrence (R i).p j; apply Transit.includes (R:=V) _ (fun x i=>x); obtain ⟨K,hK,hA⟩ := h.alongE
   obtain ⟨r,hr⟩:=hK.books; exact ⟨⟨K,hK,hA⟩,fun i=> ⟨⟨r,(hr.and hA).mono fun n hn x=> (hn.2 _ x).trans (budget_single (hn.1) i)⟩,fun ε he=>(h.right i ε he).mono fun n hn x=> (hn x).2⟩⟩
omit [v.NeBot] in
lemma partK (j:ℕ) : Tune v (fun i U=>(R i).activities.K j U):=by
   obtain ⟨K,hK,hA⟩ := h.alongK; obtain ⟨r,hr⟩:=hK.books; exact ⟨⟨r,(hr.and hA).mono fun n hn x=> (hn.2 _ x).trans (budget_single (hn.1) j)⟩,fun ε he=>(h.right j ε he).mono fun n hn x=> (hn x).1⟩
lemma gasOn : Tune v (fun i U=>(R i).activities.gas (R i).p U):=by
   obtain ⟨K,hK,hV⟩:=h.alongK
   let L:=fun i a=> (R i).activities.gasOccurrence (R i).p a
   apply Transit.includes (R:=L) _ (fun U _=>U)
   obtain ⟨r,hr⟩:=hK.books; refine ⟨⟨_,hK.powerList,?_⟩,fun x=> ?_⟩
   · filter_upwards [hr,hV] with n hn hh x u
     unfold L Activities.gasOccurrence; split
     · rw [Real.norm_eq_abs, Finset.abs_prod]; exact Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=> hh i _)
     rw [norm_zero]; exact Finset.prod_nonneg (fun _ _=> hn.1 _)
   obtain ⟨t,ht⟩:=hr.exists; have hv(i U): (R i).activities.admissible (R i).p U x = (R t).activities.admissible (R t).p U x:=by unfold Activities.admissible; rw [(h.labels i t).1,h.chan i t]
   simp_rw [L,Activities.gasOccurrence,hv]; apply Tune.mask; exact polysT _ (fun i _=>partK h i)
include p
lemma pureOn {C:Clip}(hx:∀ i,(R i).clip=C) : Tune v (fun i U=> (R i).exponent U - (R i).scalar):=by
   obtain ⟨r,hB⟩:=(show ∀ᶠ i:ι in v,True by simp).exists; let t:=(R r).p
   have hh : Tune v (fun i (U:Config G n)=> (R i).path.inChannels (R i).clip (R i).p (R i).beta U):=by
      have hz:∀ i,(R i).p=t:= fun i=> h.chan i r; simp_rw [hx,hz]; exact turnsK p t C _ h.beta
   exact (((Tune.nil.sub hh).sub (addOn h)).switch (Eventually.of_forall fun i=>funext fun x=> by unfold Rep.exponent Rep.scalar; abel)) -- simp loop h.chan
lemma strippedOn {C:Clip}(hx:∀ i,(R i).clip=C) : Tune v (fun i U=>stripped (R i) U) :=by
   let s i U:= (R i).exponent U-(R i).scalar; apply ((Tune.cont (pureOn p h hx) Real.continuous_exp).mul (gasOn h)).switch
   filter_upwards with n; funext U; rw [stripped,Rep.eval, ←mul_assoc,←Real.exp_add]; simp only [sub_eq_add_neg,add_comm]
lemma zPositive {C:Clip}(hx:∀ i,(R i).clip=C)(hz:∀ᶠ i in v, (∃ σ C Λ δ w,(R i).Lawful σ C Λ δ w) ∧ ∀ U,0≤ (R i).eval U): ∃ b:ℝ,0<b ∧ ∀ᶠ i in v,b ≤ ∫ U,stripped (R i) U ∂prior G n:=by
   obtain ⟨r,-⟩:= hz.exists; let t:=(R r).p; let m:= t.threshold
   let Z:=calm G n m; let μ:=prior G n
   obtain ⟨k,hk⟩:=(pureOn p h hx).price
   refine ⟨μ.real Z * Real.exp (-k),mul_pos ?_ (Real.exp_pos _),?_⟩
   · exact lt_of_lt_of_le (pow_pos (pow_pos (div_pos t.threshold_pos (by positivity)) _) _) (RG.space G n m t.threshold_pos t.threshold_le)
   filter_upwards [hk,hz] with i hi hl
   obtain ⟨⟨σ,C,Λ,δ,w,hR⟩,hV⟩:=hl
   rw [show μ.real Z * Real.exp (-k) = ∫ U,Z.indicator (fun _=> Real.exp (-k)) U ∂prior G n by rw [integral_indicator (calm_meas _),setIntegral_const]; rfl]
   apply integral_mono ((integrable_const _).indicator (calm_meas _)) (stripped_int _ hR)
   intro x; by_cases h':x∈Z
   · rw [Set.indicator_of_mem h',stripped,Rep.eval,Activities.gas_one _ _ (voids h' (le_of_eq ?_)),mul_one,←Real.exp_add,Real.exp_le_exp]; have hv: |(R i).exponent x-(R i).scalar|≤k:=hi x; linarith only [(abs_le.mp hv).1]; exact congr_arg BudgetPoint.threshold (h.chan r i)
   rw [Set.indicator_of_notMem h']; exact mul_nonneg (Real.exp_pos _).le (hV x)
end rep
end YM.UVExtension.Hearth
