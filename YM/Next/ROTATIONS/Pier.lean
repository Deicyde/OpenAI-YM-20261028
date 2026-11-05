import YM.Next.ROTATIONS.Nodal
import YM.Next.ROTATIONS.Sources
import YM.Next.ROTATIONS.Symbol
import YM.Next.ROTATIONS.Tunnel

/-! # Fixed band estimates from true derivative labels -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L}

def spar (a b : Axis) := fun k => Bool.xor (decide (k=a)) (decide (k=b))
lemma spar_at (a b k : Axis) : signValue (spar a b k)=colorSign (Signed.mirror k) a * colorSign (Signed.mirror k) b := by
  unfold colorSign; simp only [Signed.mirror]; cases h : decide (k=a) <;> cases H : decide (k=b) <;> simp only [spar,h,H] <;> norm_num [signValue]
lemma mix_if_both (Q : Finset Axis) (e : Axis→Bool) (x y) (hx : x∈Q) (hy : y∈Q) (h : e x≠e y) : Mixed Q e := by
  intro i hi; by_cases H:e i=e x
  · exact ⟨y,hy,H ▸ h⟩
  exact ⟨x,hx,H⟩
lemma exists_another (x y : Axis) : ∃ z : Axis, z≠x ∧ z≠y := by
  have : ∀ x y : Axis, ∃ z : Axis,z≠x ∧ z≠y := by decide
  exact this x y
lemma spar_both (a b : Axis) (h : a≠b) : Mixed Finset.univ (spar a b) := by
  obtain ⟨p,hp,hq⟩ := exists_another a b
  exact mix_if_both Finset.univ (spar a b) a p (Finset.mem_univ _) (Finset.mem_univ _) (by simp [spar,h,hp,hq])
lemma shines (J : Stress S) (H : S.Hierarchy) (hp : RawTensor H.spin J) (a b) : Enters H (spar a b) (J a b) := by
  intro i; rw [spar_at]; exact tensor_signed J H hp a b (Signed.mirror i)


def dig (a b i : Axis) (J : Stress S) (P : DiffPlan S) : S.Tag := if a=b then rise P i (tag J a b) else tag J a b
def signsD (a b i : Axis) (j : Axis) := if a=b then decide (j=i) else spar a b j
lemma signD_both (a b i : Axis) : Mixed Finset.univ (signsD a b i) := by
  by_cases h:a=b
  · obtain ⟨j,hj⟩ := exists_ne i
    exact mix_if_both Finset.univ (signsD a b i) i j (Finset.mem_univ i) (Finset.mem_univ j) (by simp [signsD,h,hj])
  rw [show signsD a b i=spar a b from funext fun j => by simp [signsD,h]]; exact spar_both a b h
lemma signD_at (H : S.Hierarchy) (J : Stress S) (h : RawTensor H.spin J) (P : DiffPlan S) (hp : P.Orientation H.spin)
    (a b i) : Enters H (signsD a b i) (dig a b i J P).2 := by
  by_cases hq : a=b
  · subst b; rw [show dig a a i J P=_ from if_pos rfl]
    intro j; change S.mirror H.spin 5 _ (P.deriv 4 i (J a a)) = signValue (signsD a a i j) • P.deriv 4 i (J a a); rw [hp.mirrorDer 4, tensor_signed J H h]
    dsimp only [Signed.mirror,Equiv.refl_apply]; rw [sign_sq]; simp only [one_smul]
    rw [Finset.sum_eq_single i]
    · simp only [signValue,Signed.matrix_at]; by_cases h:j=i <;> simp [h,signsD]
    · intro k _ hk; simp [Signed.matrix_at, Ne.symm hk]
    simp
  rw [show dig a b i J P=tag J a b from if_neg hq, show signsD a b i=spar a b from funext fun i => by simp [signsD,hq]]; exact shines J H h a b
lemma signD_real (H : S.Hierarchy) (J : Stress S) (P : DiffPlan S) (h : Conserved P H.spin J) (hp : P.Orientation H.spin)
    (a b i) : S.conj H.spin _ (dig a b i J P).2=(dig a b i J P).2 := by
  by_cases he : a=b
  · rw [show dig a b i J P=rise P i (tag J a b) from if_pos he]
    change S.conj H.spin 5 (P.deriv 4 i (J a b))=P.deriv 4 i (J a b); rw [hp.realDer 4,h.real]
  rw [show dig a b i J P=tag J a b from if_neg he]; exact h.real ..

private def lease (u v : S.Tag) (f : Grouping) := ∫ x, pair u v x*tensor (polar f) x
private lemma liftIt (f : Grouping) (i : Axis) (F : Profile) (hF : Far F) (hf : f i=F) :
    stepAt 1 (update f i (slash 1 F)) i=f := by unfold stepAt; rw [update_self,pump_back 1 F hF]; rw [update_idem,← hf, update_eq_self]
private lemma first_lift (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (v w : S.Tag) (i : Axis) : ∃ D : ℕ,
    ∀ (F : Profile) (_ : Far F) f, f i=F → ∀ j : Axis,j≠i → Centred D (f j) →
    lease v w f=(-I)*lease (rise P i v) w (update f i (slash 1 F)) := by
  obtain ⟨D,hD⟩ := pair_bound H v w; obtain ⟨E,hE⟩ := pair_bound H (rise P i v) w
  let d := max D E
  refine ⟨d,fun F hF f he j hj ht => ?_⟩
  let g := update f i (slash 1 F)
  have hv : flat d (polar g j) := polar_flat g j _ (by unfold g; rw [update_of_ne hj ..]; exact ht)
  have hw : flat d (moved i (polar g) j) := by unfold moved; rw [update_of_ne hj ..]; exact hv
  have hh := integrate_both (pair v w) (tensor (polar g)) (pair (rise P i v) w) (tensor (moved i (polar g))) i
    (radical _ d j hv _ (hD.loosen (le_max_left ..)) (pair_meas H ..))
    (radical _ d j hw _ (hD.loosen (le_max_left ..)) (pair_meas H ..))
    (radical _ d j hv _ (hE.loosen (le_max_right ..)) (pair_meas H ..)) (pair_dif H v w P hp i) fun x _ => moved_deriv i _ x
  simp_rw [hat_rhs, show stepAt 1 g i=f from liftIt f i F hF he] at hh
  simp_rw [mul_left_comm _ (-I), integral_const_mul] at hh; unfold lease
  rw [show (∫ x, pair (rise P i v) w x*tensor _ x)= -(-I*∫ x,pair v w x*tensor (polar f) x) from neg_injective (by simpa using hh.symm)]
  simp [← mul_assoc]
private lemma second_lift (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (v w : S.Tag) (i : Axis) : ∃ D : ℕ,
    ∀ (F : Profile) (_ : Far F) f, f i=F → ∀ j : Axis,j≠i → Centred D (f j) →
    lease v w f=I*lease v (rise P i w) (update f i (slash 1 F)) := by
  obtain ⟨D,hD⟩ := pair_bound H v w; obtain ⟨E,hE⟩ := pair_bound H v (rise P i w)
  let d := max D E
  refine ⟨d,fun F hF f he j hj ht => ?_⟩
  let g := update f i (slash 1 F)
  have hv : flat d (polar g j) := polar_flat g j _ (by unfold g; rw [update_of_ne hj ..]; exact ht)
  have hw : flat d (moved i (polar g) j) := by unfold moved; rw [update_of_ne hj ..]; exact hv
  have hl := (radical _ d j hv _ (hE.loosen (le_max_right ..)) (pair_meas H ..)).neg
  have hh := integrate_both (pair v w) (tensor (polar g)) (fun y => -pair v (rise P i w) y) (tensor (moved i (polar g))) i
    (radical _ d j hv _ (hD.loosen (le_max_left ..)) (pair_meas H ..))
    (radical _ d j hw _ (hD.loosen (le_max_left ..)) (pair_meas H ..)) (by simpa [Pi.neg_def] using hl) (pair_dif_neg H v w P hp i) fun x _ => moved_deriv i _ x
  simp_rw [hat_rhs, show stepAt 1 g i=f from liftIt f i F hF he, mul_left_comm _ (-I), integral_const_mul, neg_mul, integral_neg,neg_neg] at hh
  change _ = I* (∫ x,pair v (rise P i w) x*tensor (polar g) x); unfold lease; rw [← hh]; simp [← mul_assoc]

private lemma expenses (H : S.Hierarchy) (P : DiffPlan S) (h : P.Derivatives S) (J : Stress S) (a b c d i)
    (F : Profile) (hF : Far F) :
    ∃ (y : ℕ) (g : Profile) (z : ℂ), Ends g ∧ ∀ f : Grouping, f i=F → ∀ j : Axis,j≠i → Centred y (f j) →
    lease (tag J a b) (tag J c d) f=z*lease (dig a b i J P) (dig c d i J P) (update f i g) := by
  have HA : ∃ m Q u, Far Q ∧ ∀ f : Grouping,f i=F → ∀ j : Axis,j≠i → Centred m (f j) →
      lease (tag J a b) (tag J c d) f=u*lease (dig a b i J P) (tag J c d) (update f i Q) := by
    unfold dig
    split_ifs
    · obtain ⟨m,hm⟩ := first_lift H P h (tag J a b) (tag J c d) i
      exact ⟨m,_,_, slash_far hF _,hm F hF⟩
    exact ⟨0,F,1,hF,fun f he j _ _ => by rw [← he,update_eq_self,one_mul]⟩
  obtain ⟨m,Q,u,hQ,hA⟩ := HA
  by_cases hx : c=d
  · obtain ⟨k,hk⟩ := second_lift H P h (dig a b i J P) (tag J c d) i
    refine ⟨max m k,_,u*I,(slash_far hQ 1).1,fun f hf j hj hv => ?_⟩
    rw [hA f hf j hj (fun x hh => hv x (hh.trans_le (le_max_left ..))), hk Q hQ (update f i Q) (update_self ..) j hj ?_,
      update_idem, show dig c d i J P=_ from if_pos hx, mul_assoc]
    rw [update_of_ne hj ..]; exact fun x he => hv x (he.trans_le (le_max_right ..))
  exact ⟨m,_,_,hQ.1,by rwa [show dig c d i J P=tag J c d from if_neg hx]⟩

def axes (a b c d i : Axis) := Bool.xor (spar a b i) (spar c d i)

variable (V : ∀ i,Chamber S i)
include V
lemma fixed (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation H.spin)
    (J : Stress S) (C : Conserved P H.spin J) (Y : RawTensor H.spin J)
    {D : ℕ} {R : Series} (hR : Portrait J D R) (a b c d i) (f : Grouping)
    (hf : Far (f i)) (hF : ∀ j, Ends (f j)) (hv : ∀ j, j≠i → Reflects (axes a b c d j) (f j))
    (w : Axis → ℝ) (he : w i=0) (hw : ∀ i,w i ≤ 0) (δ : ℝ) (hδ : 0<δ) :
    Budget δ (fun n => sent (R a b c d) (mails w f n)) := by
  let e := signsD a b i
  let e' := signsD c d i
  let t := dig a b i J P; let u := dig c d i J P
  obtain ⟨A,H₁,H₂,H₃⟩ := enters_weights H e t.2 (signD_at H J Y P ho a b i)
  obtain ⟨B,h₁,h₂,h₃⟩ := enters_weights H e' u.2 (signD_at H J Y P ho c d i)
  obtain ⟨j,g,z,hu,hz⟩ := expenses H P hp J a b c d i (f i) hf
  let W := sent (R a b c d)
  let ε k := Bool.xor (e k) (e' k)
  have hK k : signValue (ε k)=signValue (e' k)*signValue (e k) := by unfold ε; cases e k <;> cases e' k <;> norm_num [signValue]
  refine fix_cost V H i B A e' e (signD_both c d i) (signD_both a b i) h₂ H₂ h₃ H₃ W
    (fun k y => ⟨W.toLinearMap y k,fun h => rfl⟩) ε hK δ hδ (f i) g hu z (max D j) ?_ (other i) (by simp [other])
    w hw (fun k hl => ?_) f hF (fun k hn => ?_) rfl
  · intro l _ hg k hk h
    change R a b c d (polar l)= _
    rw [hR.agrees a b c d _ k (polar_flat l _ _ (fun r hh => h r (hh.trans_le (le_max_left ..))))]
    change lease (tag J a b) (tag J c d) l = _
    rw [hz _ hg k hk (fun r hh => h r (hh.trans_le (le_max_right ..)))]
    congr 1
    have HH : ∀ᵐ p : E4,p≠0 := by simp only [ae_iff]; simp
    refine integral_congr_ae (HH.mono fun p hh => ?_)
    dsimp only [mixPlot]
    rw [pair_reply H A B t.2 u.2 H₁ h₁ p hh, show S.conj _ _ u.2=u.2 from signD_real H J P C ho c d i]; rfl
  · by_contra hh; have he : k≠i := by intro h; subst k; contradiction
    exact hl (apart he)
  · have hx := hv k (Finset.mem_erase.mp hn).1
    have hy : k≠i := (Finset.mem_erase.mp hn).1
    rw [show ε k=axes a b c d k by
      unfold ε axes e e' signsD spar; by_cases hk : a=b <;> by_cases hl : c=d <;> simp [hk,hl, hy]]; exact hx
end YM.Outer
