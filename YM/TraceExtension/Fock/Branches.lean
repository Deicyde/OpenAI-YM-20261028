import YM.TraceExtension.Fock.SpectrumLocal

/-! Open-patch uniqueness removes the spacelike restriction on the other
marks in v-v⁺, giving an independent-leg frequency scaling identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical ContDiff
variable {m n d : ℕ}

def Away (f : Probe Space3) := HasCompactSupport ⇑f ∧ 0∉tsupport f
lemma times_cut (f : Probe Space3) (h : Away f) (g : Space3 → ℂ) (hg : ∀ x≠0,ContDiffAt ℝ ⊤ g x) :
    ∃ p : Probe Space3, Away p ∧ ∀ x,p x=f x*g x := by
    have hv : ContDiff ℝ ∞ (⇑f * g) := contDiff_iff_contDiffAt.mpr fun x => by
        by_cases hp : x=0
        · subst x; refine contDiffAt_const (c:=(0:ℂ)) |>.congr_of_eventuallyEq ?_; filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h.2] with i hi; simp [hi]
        exact (f.smooth _).contDiffAt.mul ((hg x hp).of_le le_top)
    let p := h.1.mul_right.toSchwartzMap hv
    have ht : tsupport p ⊆ tsupport f := tsupport_mul_subset_left (f:=⇑f) (g:=g)
    exact ⟨p,⟨h.1.mul_right,fun e => h.2 (ht e)⟩,fun _=>rfl⟩

lemma branch (q : Wave n) (g : Fin n→ Probe E4) (i : Fin n) (h : ∀ f, data 0 q g i f=0 ∧ data 1 q g i f=0)
    (w : Probe Space3) (hw : Away w) :
    (∫ k,q k*sink 1 (Probe.hat ∘ g) i w k ∂photons n)=0 := by
    obtain ⟨f,hf,hu⟩ := times_cut w hw (fun x=> (↑‖x‖:ℂ)) (fun x hx=> by exact (ofRealCLM.contDiff.contDiffAt).comp _ (contDiffAt_norm ℝ hx))
    have he := (h (Probe.port f)).1
    have hv := (h (Probe.port w)).2
    have ha : dataM 0 q g i (Probe.port f)=dataM 1 q g i (Probe.port w) := by
        unfold dataM sink; rw [Probe.travels,Probe.travels]; simp_rw [hu]; congr! 1; ext a; ring
    have hp : dataP 0 q g i (Probe.port f)=dataP 1 q g i (Probe.port w) := by
        have hi (f : Probe Space3) x : testPlus (Probe.port f) x=f (-x) := by
            have ht := plus_minus (Probe.port f) (-x); rw [neg_neg, Probe.travels] at ht; exact ht.symm
        unfold dataP sink; simp_rw [hi,hu]; congr! 1; ext a; rw [norm_neg]; ring
    unfold data at he hv
    rw [ha,hp,pow_zero,one_mul] at he
    rw [pow_one,neg_one_mul] at hv
    have hy : dataM 1 q g i (Probe.port w)=0 := by linear_combination he / 2 + hv / 2
    rwa [dataM, Probe.travels] at hy

def ahead (b : E4) (f : Probe E4) := Joint.push (Poincare.translation b) f
lemma support_ahead (b : E4) (f : Probe E4) :
    tsupport (ahead b f)=(fun x:E4=>x+(-b)) ⁻¹' tsupport f := by
    let g:= Homeomorph.addRight (-b)
    rw [show ⇑(ahead b f)=f ∘ g from funext (fun x=> by change ahead b f x=f (x+-b); unfold ahead; rw [Joint.push_at]; congr 1),tsupport_comp_eq_preimage _ g]; rfl
lemma compact_ahead (b : E4) (f : Probe E4) (h : HasCompactSupport ⇑f) : HasCompactSupport ⇑(ahead b f) := by
    change IsCompact (tsupport _); rw [support_ahead]; exact (Homeomorph.isCompact_preimage (Homeomorph.addRight (-b))).2 h
lemma ahead_hat (b : E4) (f : Probe E4) (v : E4) : Probe.hat (ahead (-b) f) v=Probe.plane v b* Probe.hat f v := by
    unfold ahead; rw [plus_minus, plus_minus (p:=v),test_trans]; congr 1; simp [Probe.plane]
lemma place_ample (f : Probe E4) (hf : Remote f) : ∀ᶠ b:E4 in 𝓝 0, Remote (ahead (-b) f) := by
    let D := tsupport f; let V := {x : E4×E4 | x.2+ -x.1∈spacelike}
    have he : IsOpen V := open_spacelike.preimage (continuous_snd.add continuous_fst.neg)
    have hm : ({0}: Set E4) ×ˢ D ⊆ V := by rintro ⟨a,b⟩ ⟨rfl,h⟩; simpa only [V,neg_zero, mem_setOf_eq,add_zero] using (hf.2 h)
    obtain ⟨u,v,hu,hv,ha,hb,h⟩ := generalized_tube_lemma isCompact_singleton (show IsCompact D from hf.1) he hm
    filter_upwards [hu.mem_nhds (ha (mem_singleton _))] with b he
    refine ⟨compact_ahead _ _ hf.1, fun x ht=>?_⟩
    rw [support_ahead] at ht
    have hw : x+b∈tsupport f := by simpa using ht
    have hc := h (show (b,x+b) ∈ u ×ˢ v from ⟨he,hb hw⟩); simpa [V] using hc

lemma liftAway (x : Probe Space3) (hx : Away x) (b : E4) :
    ∃ y : Probe Space3, Away y ∧ ∀ p, y p=x p*Probe.plane (momentum p) b := by
    refine times_cut x hx _ fun v h=>?_
    have hv : ContDiffAt ℝ ⊤ momentum v := Mink.divide.symm.contDiff.contDiffAt.comp v
        (contDiffAt_id.prodMk (contDiffAt_norm ℝ h))
    have he : ContDiffAt ℝ ⊤ (fun p : Space3=> ofRealCLM (inner ℝ (momentum p) b)) v := ofRealCLM.contDiff.contDiffAt.comp v (((innerSL ℝ (E:=E4)).flip b).contDiff.contDiffAt.comp v hv)
    exact (he.mul (contDiffAt_const (c:=I))).cexp
lemma supported (q : Wave n) (hp : tempered q d) (i : Fin n)
    (hq : ∀ g : Fin n→Probe E4,(∀ i, Remote (g i)) → ∀ f, data 0 q g i f=0 ∧ data 1 q g i f=0)
    (g : Fin n→ Probe E4) (h : ∀ i, Remote (g i)) (w : Probe Space3) (hw : Away w) :
    (fun k=>q k * sink 1 (Probe.hat ∘ g) i w k) =ᵐ[photons n] 0 := by
    let W (k : Mom n) := q k*sink 1 (Probe.hat ∘ g) i w k
    apply shell_unique W (sink_int _ _ hp ..|>.1)
    have he : ∀ᶠ b : Fin n→E4 in 𝓝 0, ∀ i, Remote (ahead (-b i) (g i)) := eventually_all.mpr fun j=> (show Tendsto (fun x : Fin n→E4=>x j) (𝓝 0) (𝓝 0) from (continuous_apply j).tendsto _).eventually (place_ample _ (h j))
    filter_upwards [he] with b hb
    obtain ⟨v,hv,hV⟩ := liftAway w hw (b i)
    let G j := ahead (-b j) (g j)
    have ht := branch q G i (hq G hb) v hv
    change rapid W b=0; rw [← ht]; unfold rapid
    congr! 1; ext k; unfold W sink beam;
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hV]
    have ht : slot (Probe.hat ∘ G) i k=slot (Probe.hat ∘ g) i k * ∏ j∈Finset.univ.erase i, Probe.plane (momentum (k j)) (b j) := by
        unfold slot; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j hj
        simp only [G, comp_apply,front, ahead_hat]; ring
    rw [ht]; ring

private lemma witnesses : ∃ g : ℕ→Probe E4, (∀ i,Remote (g i)) ∧ ∀ p:E4, ∀ᶠ i:ℕ in atTop, Probe.hat (g i) p≠0 := by
    let b : E4 := position (Ray.fromAxis 0).val 0
    have he : b∈spacelike := by
        apply (lateral _).2; rw [show spatial b= (Ray.fromAxis 0).val from spatial_position ..,(Ray.fromAxis 0).property,show time b=0 from time_position ..]; norm_num
    obtain ⟨r,hr,hp⟩ := Metric.mem_nhds_iff.mp (open_spacelike.mem_nhds he)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually (atom_small E4 hr))
    let g (n:ℕ) := ahead (- -b) (atom E4 ↑(n+N))
    refine ⟨g,fun i=> ?_,fun p=>?_⟩
    · have hx := hN (i+N) (Nat.le_add_left ..); refine ⟨compact_ahead _ _ hx.2,fun x he=>?_⟩
      apply hp; rw [support_ahead] at he; have hu := hx.1 he
      rw [Metric.mem_ball,dist_zero_right] at hu; rw [Metric.mem_ball,dist_eq_norm]; simpa [sub_eq_add_neg] using hu
    have he := (atom_negative p).comp (tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp
          (show Tendsto (fun i:ℕ => i+N) atTop atTop from (strictMono_nat_of_lt_succ (f:=fun i=>i+N) (by intro; omega)).tendsto_atTop))
    filter_upwards [he.eventually_ne one_ne_zero] with i hi; unfold g; rw [ahead_hat]; exact mul_ne_zero (Complex.exp_ne_zero _) hi

private def testAway (i:ℕ) : Probe Space3 :=
    let v := Probe.keeper i
    let b := Probe.tint (Probe.bud (0:Space3) (i+1:ℝ)⁻¹ (by positivity))
    v-Probe.sew b v
private lemma meansAway (i:ℕ) : Away (testAway i) := by
    have he := (Distn.trim_support (X:=Space3) 0 ((i+1:ℝ)⁻¹) (by positivity) (Probe.keeper i))
    have hp : HasCompactSupport ⇑(Probe.keeper (X:=Space3) i) := by
        have ht : HasCompactSupport ⇑(Probe.tint (Probe.stall (X:=Space3))) := by simp only [HasCompactSupport,Probe.tint_support]; apply isCompact_closedBall
        exact ht.comp_homeomorph (Probe.compress i).toHomeomorph
    exact ⟨hp.of_isClosed_subset (isClosed_tsupport _) (he.trans inter_subset_left), fun h=> (he h).2 (Metric.mem_ball_self (by positivity))⟩
private lemma testsAway (x : Space3) (hp : 0< ‖x‖) : ∀ᶠ k:ℕ in atTop,testAway k x≠0 := by
    have he : Tendsto (fun k:ℕ => (k:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    filter_upwards [he.eventually_ge_atTop ‖x‖,((tendsto_inv_atTop_zero.comp he).add (tendsto_inv_atTop_zero.comp he)).eventually (gt_mem_nhds (by rw [zero_add]; exact hp))] with k hk hb
    unfold testAway; let B:= Probe.bud (0:Space3) ((k+1:ℝ)⁻¹) (by positivity)
    have hv : x∉tsupport (Probe.tint B) := by rw [Probe.tint_support,Metric.mem_closedBall,dist_zero_right]; exact not_le_of_gt hb
    change (Probe.keeper k-Probe.sew (Probe.tint B) (Probe.keeper k):Probe Space3) x≠0
    rw [_root_.sub_apply, Probe.sews,image_eq_zero_of_notMem_tsupport hv,Probe.keeper_one _ hk]; simp

lemma annihilator (q : Wave n) (hp : tempered q d) (i : Fin n)
    (he : ∀ g : Fin n → Probe E4,(∀ j,Remote (g j)) → ∀ f,data 0 q g i f=0 ∧ data 1 q g i f=0) : q=0 := by
    obtain ⟨g,hg,h⟩ := witnesses
    apply AEEqFun.ext
    filter_upwards [ae_all_iff.mpr (fun t : ℕ=> supported q hp i he (fun _ => g t) (fun _ => hg t) (testAway t) (meansAway t)), photons_nonzero n,AEEqFun.coeFn_zero (μ:=photons n) (β:=ℂ)] with x hx hp hh
    obtain ⟨k,hk,hp'⟩ := ((testsAway (x i) (hp i)).and (eventually_all.mpr fun j:Fin n=>h (momentum (x j)))).exists
    rw [hh]; apply (mul_eq_zero.mp (hx k)).resolve_right
    unfold sink; refine mul_ne_zero (mul_ne_zero ?_ hk) ?_
    · exact pow_ne_zero _ (ofReal_ne_zero.mpr (hp i).ne')
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    exact mul_ne_zero (ofReal_ne_zero.mpr (hp j).ne') (hp' j)

/-- The necessary dilation identities, in every momentum slot. -/
theorem binds (q : Wave n) (hp : tempered q d) (h : ∀ g, (∀ i,Remote (g i)) → paired_at q g=adjoint_at q g) :
    ∃ k, ∀ i, signalPoly i q k=0 := by
    obtain ⟨k,hk⟩ := dyadic_order q hp h
    exact ⟨k,fun i=> annihilator _ (signal_tempered i q hp _) i (hk i)⟩
end YM.TraceExtension.Photons
