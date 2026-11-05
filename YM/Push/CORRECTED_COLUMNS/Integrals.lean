import YM.Push.CORRECTED_COLUMNS.Tree
import YM.Vac.Shelter


/-!
# Paying the marked numerator and retaining the denominator

Torus uses probability Haar.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Torus
open MeasureTheory Set Lattice Wilson Function
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal
variable {n : Side} {G : Gauge}

section
-- Hexact at the four link arguments.
lemma square_identity (U : Config G n) (x : Site n) (a b : Axis) (h : a<b) :
    faceValue U (x,⟨(a,b),h⟩)=U (x,a)*U (x+step a,b)*(U (x+step b,a))⁻¹*(U (x,b))⁻¹ := by
  unfold faceValue square
  simp only [travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one]
  rw [show x+step a+step b-step a=x+step b by abel,
    show x+step a+step b+ -step a-step b=x by abel]
  group

private lemma parting (X : E n → Prop) [DecidablePred X] (H : Config G n → ℝ) (h : Integrable H (prior G n)) :
    (∫ U, H U ∂prior G n) = ∫ U₁, (∫ U₂,
      H ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E n => G.El) X).symm (U₁,U₂))
       ∂(Measure.pi fun _ => G.probHaar)) ∂(Measure.pi fun _ => G.probHaar) := by
  let μ := (Measure.pi fun _ : {i : E n // X i} => G.probHaar)
  let ν := (Measure.pi fun _ : {i : E n // ¬X i} => G.probHaar)
  let p := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E n => G.El) X)
  have hP : MeasurePreserving p.symm (μ.prod ν) (prior G n) :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : E n => G.probHaar) X).symm _
  have hi : Integrable (fun x => H (p.symm x)) (μ.prod ν) := hP.integrable_comp_of_integrable h
  exact (hP.integral_comp p.symm.measurableEmbedding _).symm.trans (integral_prod _ hi)

private lemma spending (e : E n) (F H : Config G n → ℝ) (hF : Continuous F) (hH : Continuous H) (A : ℝ)
    (hh : ∀ U : Config G n, (∫ x, F (update U e x) ∂G.probHaar) = A)
    (h : ∀ (U : Config G n) (x : G.El), H (update U e x)=H U) :
    (∫ U, F U * H U ∂prior G n) = A * ∫ U, H U ∂prior G n := by
  let p (i : E n) := i≠e
  letI : DecidablePred p := fun i => inferInstanceAs (Decidable (i ≠ e))
  let I := {i : E n // ¬ p i}
  let J := {i : E n // p i}
  let W := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E n => G.El) p
  let v : I := ⟨e,by simp [p]⟩
  let u (s : J → G.El) := W.symm (s,fun _=>1)
  let μ := Measure.pi fun _ : I => G.probHaar
  have hx s (t : I → G.El) : W.symm (s,t) = update (u s) e (t v) := by
    funext i
    by_cases hk : i=e
    · subst i; rw [update_self]
      change (Equiv.piEquivPiSubtypeProd p (fun _ : E n => G.El)).symm (s,t) _=_
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg v.property]
    rw [update_of_ne hk]
    change (Equiv.piEquivPiSubtypeProd p (fun _ : E n => G.El)).symm (s,t) _=(Equiv.piEquivPiSubtypeProd p (fun _ : E n => G.El)).symm _ i
    simp only [Equiv.piEquivPiSubtypeProd_symm_apply,dif_pos (show p i from hk)]
  have hg s : (∫ t : I → G.El,F (W.symm (s,t)) ∂μ) = A := by
    simp_rw [hx s]
    let X (x : G.El) := F (update (u s) e x)
    have hh' : Continuous X := hF.comp (by fun_prop : Continuous (update (u s) e))
    let eval (x : I → G.El) := x v
    have hm : μ.map eval = G.probHaar := by
      change (Measure.pi (fun _ : I => G.probHaar)).map (@Function.eval I (fun _ => G.El) v) = _
      rw [Measure.pi_map_eval]; simp
    have ht := integral_map (φ:=eval) (μ:=μ) (f:=X) (measurable_pi_apply v).aemeasurable hh'.aestronglyMeasurable
    rw [hm] at ht; exact ht.symm.trans (hh _)
  have hp (s : J → G.El) (t : I → G.El) : H (W.symm (s,t)) = H (u s) := hx s t ▸ h _ _
  rw [parting p (fun x => F x * H x) ((hF.mul hH).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    parting p H (hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  change (∫ t : I → G.El,F (W.symm (s,t)) * H (W.symm (s,t)) ∂μ)=A * ∫ t : I → G.El,H (W.symm (s,t)) ∂μ
  simp_rw [hp s]; rw [integral_mul_const,hg]
  dsimp only [μ]; simp
end

private lemma face_untouched (f : G.El → ℝ) (U : Config G n) (p : Face (Per n)) (e : E n) (x : G.El)
    (he : e ∉ reads p) : f (faceValue (update U e x) p)=f (faceValue U p) := by
  obtain ⟨y,⟨⟨a,b⟩,hab⟩⟩ := p
  simp only [reads, Finset.mem_insert,Finset.mem_singleton,not_or] at he
  rw [square_identity,square_identity]
  simp only [update_of_ne (Ne.symm he.1),update_of_ne (Ne.symm he.2.1),update_of_ne (Ne.symm he.2.2.1),
    update_of_ne (Ne.symm he.2.2.2)]

private lemma face_refresh (hn : 2 ≤ n.val) (f : G.El → ℝ) (h : Continuous f)
    (U : Config G n) (p : Face (Per n)) (e : E n) (he : e∈reads p) :
    (∫ x, f (faceValue (update U e x) p) ∂G.probHaar) = ∫ x, f x ∂G.probHaar := by
  obtain ⟨y,⟨⟨a,b⟩,hab⟩⟩ := p
  change a<b at hab
  have hv (q : G.El → G.El) (hp : MeasurePreserving q G.probHaar G.probHaar) :
      (∫ x, f (q x) ∂G.probHaar) = ∫ x, f x ∂G.probHaar := by
    have hi := integral_map (f:=f) hp.aemeasurable h.aestronglyMeasurable
    rw [hp.map_eq] at hi; exact hi.symm
  have hd a : y+step a ≠ y := by
    intro h
    have h' : step a = (0 : Site n) := add_left_cancel (h.trans (add_zero y).symm)
    have hw : (1 : Per n).val=1 := (ZMod.val_eq_one hn _).2 rfl
    have hk := congr_fun h' a
    simp only [step_apply,↓reduceIte,Pi.zero_apply] at hk; rw [hk] at hw
    simp at hw
  simp only [reads, Finset.mem_insert, Finset.mem_singleton] at he
  simp_rw [square_identity _ y a b hab]
  rcases he with he|he|he|he <;> rw [he]
  · simp_rw [update_self,
      update_of_ne (show (y+step a,b)≠(y,a) from fun H => hab.ne' (congr_arg Prod.snd H)),
      update_of_ne (show (y+step b,a)≠(y,a) from fun H => hd b (congr_arg Prod.fst H)),
      update_of_ne (show (y,b)≠(y,a) from fun H => hab.ne' (congr_arg Prod.snd H))]
    simp_rw [mul_assoc]
    exact hv _ (measurePreserving_mul_right G.probHaar _)
  · simp_rw [update_of_ne (show (y,a)≠(y+step a,b) from fun H => hab.ne (congr_arg Prod.snd H)),
      update_of_ne (show (y+step b,a)≠(y+step a,b) from fun H => hab.ne (congr_arg Prod.snd H)),
      update_of_ne (show (y,b)≠(y+step a,b) from fun H => hd a (congr_arg Prod.fst H.symm)), update_self,
      mul_assoc (U (y,a) * _)]
    exact hv _ (G.preserve_two_sided ..)
  · simp_rw [update_of_ne (show (y,a)≠(y+step b,a) from fun H => hd b (congr_arg Prod.fst H.symm)),
      update_of_ne (show (y+step a,b)≠(y+step b,a) from fun H => hab.ne' (congr_arg Prod.snd H)),
      update_of_ne (show (y,b)≠(y+step b,a) from fun H => hab.ne' (congr_arg Prod.snd H)), update_self]
    exact hv _ ((G.preserve_two_sided ..).comp G.preserve_inv)
  simp_rw [update_of_ne (show (y,a)≠(y,b) from fun H => hab.ne (congr_arg Prod.snd H)),
    update_of_ne (show (y+step a,b)≠(y,b) from fun H => hd a (congr_arg Prod.fst H)),
    update_of_ne (show (y+step b,a)≠(y,b) from fun H => hab.ne (congr_arg Prod.snd H)), update_self]
  exact hv _ ((measurePreserving_mul_left G.probHaar _).comp G.preserve_inv)

lemma chosen_product (hn : 2 ≤ n.val) (f : G.El → ℝ) (h : Continuous f)
    (T : E n → Face (Per n))
    (H : ∀ i ∈ paid n, i∈reads (T i) ∧ ∀ u ∈ reads (T i), u ∈ paid n → u ≠ i → index u < index i)
    (s : Finset (E n)) (hs : s ⊆ paid n) :
    (∫ U : Config G n,(∏ i∈s, f (faceValue U (T i))) ∂prior G n) = (∫ x, f x ∂G.probHaar)^s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
  by_cases he : s.Nonempty
  · obtain ⟨e,he',hE⟩ := s.exists_max_image index he
    let t := s.erase e
    have ht : t ⊂ s := Finset.erase_ssubset he'
    let F (i) (U : Config G n) := f (faceValue U (T i))
    have hi i : Continuous (F i) := h.comp (continuous_travel _ _)
    let W (x : Config G n) := ∏ i ∈ t,F i x
    have hh U x : W (update U e x)= W U := by
      apply Finset.prod_congr rfl; intro i hi
      obtain ⟨hne,hI⟩ := Finset.mem_erase.mp hi
      apply face_untouched
      intro hh
      exact (hE _ hI).not_gt ((H _ (hs hI)).2 _ hh (hs he') (Ne.symm hne))
    simp_rw [← Finset.mul_prod_erase _ _ he']
    rw [spending e (F e) W (hi _) (continuous_finsetProd t (fun i _ => hi i)) _
         (fun U => face_refresh hn f h U _ _ (H e (hs he')).1) hh]
    rw [ih t ht (Finset.Subset.trans ht.subset hs),← pow_succ',Finset.card_erase_add_one he']
  simp only [Finset.not_nonempty_iff_eq_empty] at he
  subst s; simp

/-- Before gauge fixing, eliminate all but the tree and four rims. -/
theorem numerator (hn : 2 ≤ n.val) (f : G.El → ℝ) (h : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    (∫ U : Config G n,(∏ p : Face (Per n), f (faceValue U p)) ∂prior G n) ≤
      (∫ x, f x ∂G.probHaar)^(paid n).card := by
  classical
  choose q hq using eliminates hn
  let p₀ : Face (Per n) := (0,⟨(0,1), by decide⟩)
  let q' (i : E n) := if H : i ∈ paid n then q i H else p₀
  have he i (H : i∈paid n) : i∈reads (q' i) ∧ ∀ u∈ reads (q' i), u∈paid n → u≠i → index u < index i := by
    simpa only [q',dif_pos H] using hq i H
  rw [← chosen_product hn f h q' he _ Finset.Subset.rfl]
  have hx (j : Face (Per n)) : Continuous fun U : Config G n => f (faceValue U j) := h.comp (continuous_travel ..)
  have hw (U : Config G n) :
      (∏ p : Face (Per n), f (faceValue U p)) ≤ ∏ i∈paid n, f (faceValue U (q' i)) := by
    let K := (paid n).image q'
    have hi : Set.InjOn q' (paid n:Set (E n)) := by
      intro i hi j hj hh
      by_contra h
      have he' := (he i hi).2 j (hh.symm ▸ (he _ hj).1) hj (Ne.symm h)
      exact he'.not_gt ((he j hj).2 i (hh ▸ (he _ hi).1) hi h)
    let W j := f (faceValue U j)
    have H : ∏ j∈K,W j=∏ i∈paid n, W (q' i) := Finset.prod_image hi
    rw [← show (∏ i∈K,W i) = _ from H]
    change (∏ j, W j)≤∏ j∈K,W j
    rw [← Finset.prod_sdiff (s₁:=K) (s₂:= Finset.univ) (Finset.subset_univ _)]
    apply mul_le_of_le_one_left (Finset.prod_nonneg fun i _ => h0 _)
    exact le_trans (Finset.prod_le_prod (fun i _ => h0 (faceValue U _)) (fun i _ => h1 _)) (by simp)
  exact integral_mono
    ((continuous_finsetProd Finset.univ (fun i _ => hx i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((continuous_finsetProd _ (fun i _ => hx (q' i))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hw

-- Normalize just the tree edges. The root convention is gauge anchored.
private def anc (hn : 2 ≤ n.val) (x : Site n) (h : x ≠ 0) := (from_previous hn x h).choose
private lemma ancestor (hn : 2 ≤ n.val) (x : Site n) (h : x ≠ 0) : Tree (anc hn x h) ∧ arrives (anc hn x h) = x :=
  (from_previous hn x h).choose_spec
private def treeGauge (hn : 2 ≤ n.val) (U : Config G n) (x : Site n) : G.El :=
    if h : x = 0 then 1
    else treeGauge hn U (anc hn x h).1 * U (anc hn x h)
termination_by length x
decreasing_by
  have hx := (ancestor hn x h)
  let e := anc hn x h
  have hu : length (arrives e)=length e.1+1 := grows hn e.1 e.2 hx.1.2
  change length e.1 < length x
  conv_rhs => rw [← hx.2]
  change _ < length (arrives e)
  rw [hu]; omega

private lemma removed (hn : 2 ≤ n.val) (U : Config G n) (e : E n) (h : Tree e) : gauge (treeGauge hn U) U e=1 := by
  let x := arrives e
  change treeGauge hn U e.1 * U e * (treeGauge hn U x)⁻¹ = _
  have he : x≠0 := arrives_ne hn h
  have hG : treeGauge hn U x = treeGauge hn U (anc hn x he).1 * U (anc hn x he) := by
    rw [treeGauge,dif_neg he]
  rw [hG,
    enters_once hn (ancestor hn x he).1 h ((ancestor hn x he).2 : _ = arrives e),mul_inv_cancel]

/-- Only the non-tree links are required to be small *after* conditioning
on the tree values. Do not use any estimate of a density at a null-event
conditional unless given pointwise. -/
theorem denominator (hn : 2 ≤ n.val) (F : Config G n → ℝ) (h : Integrable F (prior G n))
    (hi : GaugeInvariant F) (hw : ∀ U, 0 ≤ F U) (s : ℝ) (hs : 0 < s) (A : ℝ)
    (hp : ∀ U ∈ RG.calm G n s, A ≤ F U) :
    A * (G.probHaar.real (G.shell (s/4)))^(free n).card ≤ ∫ x, F x ∂prior G n := by
  let μ := Measure.pi fun _ : {e : E n // Tree e} => G.probHaar
  let ν := Measure.pi fun _ : {e : E n // ¬Tree e} => G.probHaar
  let W := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E n => G.El) Tree
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hP : MeasurePreserving W.symm (μ.prod ν) (prior G n) :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : E n => G.probHaar) Tree).symm _
  have hv : Integrable (fun x => F (W.symm x)) (μ.prod ν) := hP.integrable_comp_of_integrable h
  let B := A * (G.probHaar.real (G.shell (s/4)))^(free n).card
  rw [parting Tree F h]
  change B ≤ ∫ u,(∫ v,F (W.symm (u,v))∂ν) ∂μ
  have he : (∫ _, B ∂μ)= B := by simp only [integral_const, probReal_univ, one_smul]
  apply he.symm.le.trans
  apply integral_mono_ae (integrable_const _) hv.integral_prod_left
  filter_upwards [hv.prod_right_ae] with u hu
  change B≤ ∫ v,F (W.symm (u,v)) ∂ν
  let T := {e : E n // ¬Tree e}
  let U := W.symm (u,fun _=>1)
  let t := treeGauge hn U
  have hh v (e : E n) (he : Tree e) : gauge t (W.symm (u,v)) e=1 := by
    unfold Lattice.gauge
    have ht : W.symm (u,v) e=U e := by
      change (Equiv.piEquivPiSubtypeProd Tree (fun _ : E n => G.El)).symm _ _=(Equiv.piEquivPiSubtypeProd Tree (fun _ : E n => G.El)).symm _ e
      simp only [Equiv.piEquivPiSubtypeProd_symm_apply,dif_pos he]
    rw [ht]; exact removed hn U e he
  let K := G.shell (s/4)
  let q (i : T) := fun x : G.El => t i.val.1 * x * (t (arrives i.val))⁻¹
  let C i := q i ⁻¹' K
  let Y := Set.pi (univ:Set T) C
  have hm : MeasurableSet Y := MeasurableSet.univ_pi fun i => (G.preserve_two_sided (t i.val.1)
    (t (arrives i.val))⁻¹).measurable (G.shell_meas _)
  have hV : ν.real Y = G.probHaar.real K ^ (free n).card := by
    have hf (i : T) : G.probHaar (C i)=G.probHaar K :=
      (G.preserve_two_sided ..).measure_preimage (G.shell_meas _).nullMeasurableSet
    have ht : Fintype.card T = (free n).card := Fintype.card_subtype _
    unfold ν Measure.real Y
    rw [Measure.pi_pi]; simp_rw [hf]; simp only [Finset.prod_const,Finset.card_univ,ENNReal.toReal_pow]
    rw [show Fintype.card {e : E n // ¬Tree e} = _ from ht]
  have hx v : Y.indicator (fun _ => A) v ≤ F (W.symm (u,v)) := by
    by_cases hh' : v ∈ Y
    · rw [indicator_of_mem hh',← hi t]
      apply hp
      intro e _
      by_cases ht : Tree e
      · rw [hh _ _ ht]
        change G.chord 1 ≤ _; rw [G.chord_one]; positivity
      change gauge t (W.symm (u,v)) e∈K
      have hb : gauge t (W.symm (u,v)) e=q (⟨e,ht⟩:T) (v ⟨e,ht⟩) := by
        unfold Lattice.gauge q
        have hg : W.symm (u,v) e=v ⟨e,ht⟩ := by
          change (Equiv.piEquivPiSubtypeProd Tree (fun _ : E n => G.El)).symm _ e=_
          rw [Equiv.piEquivPiSubtypeProd_symm_apply,dif_neg ht]
        rw [hg]; rfl
      rw [hb]; exact hh' (⟨e,ht⟩:T) (mem_univ _)
    rw [indicator_of_notMem hh']; exact hw _
  have hy := integral_mono ((integrable_const _).indicator hm) hu hx
  rw [integral_indicator hm,setIntegral_const,hV,smul_eq_mul,mul_comm _ A] at hy; exact hy
end YM.Push.Corrected.Torus
