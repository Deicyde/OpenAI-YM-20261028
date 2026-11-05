import YM.Next.RANK.LedgerGate

/-!
# Moving a pure layer to assigned masks and debiting the K graph
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V ι κ X : Type} [Fintype ι] [Fintype κ]
section
variable [Fintype V] [DecidableEq V] {p : BudgetPoint} {ζ : V→Site n}
variable (H : ι→ SourceAt G ζ) (W : κ→SourceAt G ζ) (v : ι→κ) (a : ∀ i,(H i).fires = (W (v i)).fires) (hv : ∀ i,(H i).extent⊆(W (v i)).extent)

def messages (i : ι) (τ : ℝ) : Refusal G ζ τ:= by
  let X:= H i; let Y:= W (v i)
  let P:= fun U=> masked τ X.extent X.value U- masked τ Y.extent X.value U
  have hY: LocalOn Y.extent X.value:= fun U V H=> X.loc U V (agrees_mono H (fun _ h=> hv i h))
  have ht (P : Support n) (F : Config G n→ℂ) (hp : LocalOn ↑P F) : UsesFinal τ P (masked τ P F):=by
    intro u v hQ hh; have hz:Healthy τ P u ↔ Healthy τ P v:= by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,hh]
    by_cases hx:Healthy τ P u
    · rw [masked_eq _ _ _ _ hx,masked_eq _ _ _ _ (hz.1 hx)]; exact hp _ _ hQ
    rw [masked_ne _ _ _ _ hx,masked_ne _ _ _ _ (mt hz.2 hx)]
  refine ⟨Y.extent,X.fires,X.chosen,fun j hj=> hv i (X.remembers j hj), P, (masked_measurable _ _ _ X.meas).sub (masked_measurable _ _ _ X.meas),?_,?_,?_⟩
  · intro U h hh; apply h; unfold P; rw [masked_eq _ _ _ _ (Disjoint.mono_left (hv i) hh),masked_eq _ _ _ _ hh,sub_self]
  · intro U V he hr; unfold P; rw [Work.H03.reads_larger (hv i) (ht _ _ X.loc) U V he hr, ht _ _ hY U V he hr]
  exact fun k U=> congr_arg₂ (·-·) (sails τ _ _ X.inv k U) (sails τ _ _ X.inv k U)

def displaying (x : κ) (U : Config G n) := ∑ i, if v i=x then (H i).value U else 0

def partnerW (x : κ) : SourceAt G ζ:= by
  let X:= W x; let ℵ (U):= displaying H v x U-X.value U
  refine ⟨X.extent,X.fires,X.chosen,X.remembers,ℵ,Measurable.sub ?_ X.meas,?_,?_⟩
  · unfold displaying; apply Finset.measurable_fun_sum; intro i _; split
    · exact (H i).meas
    exact measurable_const
  · intro U V h
    refine congr_arg₂ (·-·) (sum_congr rfl (fun i _=>?_)) (X.loc U V h);split
    · rename_i ht; refine (H i).loc U V (agrees_mono h (fun x hx=> ?_)); apply (show (H i).extent⊆ X.extent from by unfold X; rw [← ht]; exact hv i);exact hx
    rfl
  intro k U; refine congr_arg₂ (·-·) (sum_congr rfl fun i _=>?_) (X.inv k U); split; exact (H _).inv ..; rfl

include a in
lemma amount_sum (U : Config G n) (τ):
    ∑ i,(H i).amount τ U=(∑ j,(partnerW H W v hv j).amount τ U)+(∑ i,(W i).amount τ U)+∑ i, (messages H W v hv i τ).amount U := by
  classical
  let F x:=(W x).fires; let q x:=(W x).extent
  let φ i:= Poly.send (F (v i)) (masked τ (q (v i)) (H i).value U)
  let z k:= partnerW H W v hv k
  have he: ∑ i,(H i).amount τ U= (∑ i, φ i)+∑ i,(messages H W v hv i τ).amount U:= by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro i _
    unfold messages SourceAt.amount Refusal.amount φ; simp only; rw [a, ← send_plus, add_comm, sub_add_cancel]
  rw [he]; congr 1
  let δ j i:=if v i=j then φ i else 0
  rw [show ∑ i,φ i= ∑ i,∑ j,δ j i by simp [δ], sum_comm, ←sum_add_distrib]
  apply sum_congr rfl; intro j hJ
  let A : veil V:= (z j).amount τ U
  change (∑ i,δ j i)= A+_
  unfold A z partnerW SourceAt.amount; simp only; rw [← send_plus]
  by_cases hb : Healthy τ (q j) U
  · rw [masked_eq _ _ _ _ hb,masked_eq _ _ _ _ hb,sub_add_cancel]; unfold displaying
    have ht(a : Finset ι) : ∑ i∈a,δ j i= Poly.send (F j) (∑ i∈ a, if v i=j then (H i).value U else 0):= by
      induction a using Finset.induction_on with
      | empty=> rw [sum_empty,sum_empty,Poly.send_zero]
      | @insert i s hi HH=>
        rw [sum_insert hi,sum_insert hi,send_plus, HH]; congr 1; unfold δ;split_ifs with hw; unfold φ;rw [hw,masked_eq _ _ _ _ hb]
        rw [Poly.send_zero]
    exact ht _
  rw [masked_ne _ _ _ _ hb,masked_ne _ _ _ _ hb,add_zero,Poly.send_zero]
  apply sum_eq_zero; intro i _; unfold δ;split_ifs with h
  · unfold φ; rw [h,masked_ne _ _ _ _ hb,Poly.send_zero]
  rfl

variable (P : Rep G n) (K : X → Lifted G ζ P.p.threshold) [Fintype X]
private lemma alter {μ α : Type} [Fintype μ] [Fintype α] (R : α→ SourceAt G ζ) (Y : μ→SourceAt G ζ)
    (Z : ι → Refusal G ζ P.p.threshold) (U) (he : ∑ i,(R i).amount P.p.threshold U=∑ j,(Y j).amount P.p.threshold U + ∑ i, (Z i).amount U):
    dust P R K U=dust P Y (merged K Z) U:= by
  let Q:= ∑ j,(Y j).amount P.p.threshold U
  have hv i : ((Z i).amount U).part (quiet _)=0:= send_zero _ _ (Z i).chosen
  have hF : Q.part (quiet _)=0:= by rw [show Q.part _ = _ from Poly.part_sum ..];exact sum_eq_zero fun i _=> send_zero _ _ (Y i).chosen
  have hp:= Exponential.pass_sum Finset.univ (fun i=>(Z i).amount U) (fun i _=> hv i)
  have hx: Poly.pass (∑ i,(Z i).amount U)=∏ i,((Z i).amount U+1):= hp.trans (Finset.prod_congr rfl fun i _=> solo_pass _ _ (Z i).chosen)
  unfold Value.dust; apply congr_arg (_ • ·)
  rw [he,pass_add _ _ hF (by rw [Poly.part_sum]; exact sum_eq_zero fun i _=>hv i),hx,← coins K Z U]; ring

include a hv
lemma enact {α : Type} [Fintype α] (R : α→SourceAt G ζ) (U) :
    dust P (Sum.elim R H) K U=dust P (Sum.elim (Sum.elim R (partnerW H W v hv)) W)
                                  (merged K (fun i=> messages H W v hv i P.p.threshold)) U := by
  let η:=P.p.threshold
  let V':=fun i : ι=> messages H W v hv i η; let k:= Sum.elim (Sum.elim R (partnerW H W v hv)) W
  let A:= fun x:SourceAt G ζ=>x.amount η U
  have he : ∑ i, A ((Sum.elim R H) i)=∑ i,A (k i)+∑ i,(V' i).amount U:= by
    rw [Fintype.sum_sum_type, show ∑ i,A (k i)= _ from Fintype.sum_sum_type _, show ∑ i,A (k (.inl i))= _ from Fintype.sum_sum_type _]
    dsimp only [Sum.elim_inl,Sum.elim_inr,k]; rw [show ∑ i, A (H i)=_ from amount_sum H W v a hv ..]; unfold A V'; abel
  exact alter P K _ k V' U he

omit a

-- value fees at OLD PU θ. simple attachments (no radius inflation). enlargements require cover hits.
section
variable {e z f : ℝ} {c : ι→ℝ} {r : V→ℝ}
omit [Fintype ι] [Fintype κ] in
private lemma grains (h : ∀ i, 0 ≤ r i) (hp : ∀ i,(H i).pays p r e (c i)) (hz:0≤e) (i U) :
    let F:= messages H W v hv i p.threshold
    Poly.price r (F.amount U) ≤ c i:= by
  let s:= p.threshold; intro f
  rw [Refusal.amount, Poly.solo]; unfold f messages; dsimp only
  by_cases ht : Healthy s (W (v i)).extent U
  · rw [masked_eq _ _ _ _ ht,masked_eq _ _ _ _ (Disjoint.mono_left (hv _) ht),sub_self,norm_zero,mul_zero]; exact (hp _).1
  rw [masked_ne _ _ _ _ ht,sub_zero]; by_cases hs: Healthy s (H i).extent U
  · rw [masked_eq _ _ _ _ hs]; apply le_trans _ ((hp i).2 U hs); rw [mul_assoc]; apply le_mul_of_one_le_left _ (charged p _ hz _); apply mul_nonneg _ (norm_nonneg _); apply Finset.prod_nonneg; exact fun i _=>h i
  rw [masked_ne _ _ _ _ hs,norm_zero,mul_zero]; exact (hp _).1
omit [Fintype κ] in
lemma landed (hr : ∀ i,0 < r i) (J : κ→ℝ) {C x : ℝ} (hx : 0≤x) (he : 0 ≤ e) (hF : ∀ i,(H i).pays P.p r e (c i))
    (hJ : Stripes P.p K r (e+1) z) (he' : ∀ i,Value.charge P.p (e+1) (W i).extent=J i)
    (hc : ∀ p : Site n,(∑ i,if p∈(W (v i)).extent then c i * J (v i) else 0) ≤ C)
    (hw : Real.exp f *z+C ≤ x) (hv' : (P.p.B+P.p.B+1:ℕ)^4*(x:ℝ) ≤ 1) (hL : 0≤ f):
    Stripes P.p (merged K (fun i=> messages H W v hv i P.p.threshold)) r e (Real.exp (-f)*(Real.exp x-1)):= by
  obtain ⟨y,hy,hI⟩:=hJ
  let D:= P.p
  let A i:= messages H W v hv i D.threshold
  let g i:= Real.exp f * y i / Value.charge D (e+1) (K i).extent
  let C' : X⊕ι→ℝ:= Sum.elim g c
  have hZ i:0≤ C' i:= by cases i with
    | inl i=> exact div_nonneg (mul_nonneg (Real.exp_pos _).le (hy i|>.1)) (Real.exp_pos _).le
    | inr i=>exact (hF i).1
  have h₁ (i U) : Poly.price r (hook K A i U) ≤ Real.exp (landing K A 0 f i) * C' i:= by
    cases i with
    | inr i=> exact le_trans (show Poly.price r ((A i).amount U) ≤ c i from grains H W v hv (fun i=> (hr i).le) hF he i U) (le_of_eq (show c i=_ from (by simp [C',landing])))
    | inl i=>
      obtain ⟨_,hx⟩:=hy i; let b:= Poly.toll r (K i).fires
      rw [hook, Poly.solo]; dsimp only [landing,C',Sum.elim_inl,g]; rw [zero_mul, zero_add,← mul_div_assoc, ← mul_assoc (Real.exp (-f)), ← Real.exp_add, neg_add_cancel, Real.exp_zero,one_mul]
      apply (le_div_iff₀ (Real.exp_pos _)).2; exact (mul_comm ..).trans_le ((mul_assoc ..).symm.trans_le (hx _))
  have hE : Ac.Hit (area K A) D.B C' (e+1) x := by
    intro i; let E j:= if i∈ area K A j then C' j*Value.charge D (e+1) (area K A j) else 0
    have hi j: 0 ≤ E j:= by unfold E; split;exact mul_nonneg (hZ _) (Real.exp_pos _).le;exact le_rfl
    have he k: E (.inl k)= Real.exp f*(if i∈(K k).extent then y k else 0):= by unfold E area C';dsimp only [Sum.elim_inl]; split_ifs; dsimp only [g]; field_simp [Value.charge]; rw [mul_zero]
    refine ⟨hi, summable_of_hasFiniteSupport (Set.toFinite _),?_⟩
    -- instances canonical
    change ∑' j,E j≤ _; rw [tsum_fintype,Fintype.sum_sum_type]; simp_rw [he,← mul_sum]; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (hI _) (Real.exp_pos _).le) ?_) hw
    have ht j:E (.inr j)=if i∈(W (v j)).extent then c j *J (v j) else 0:= by unfold E area; change (if i∈(W _).extent then c j*Value.charge P.p (e+1) (W (v j)).extent else _) =_; split_ifs; rw [he' _]; rfl
    simp_rw [ht]; exact hc i
  refine ⟨fun i=> owed K A i C' f e, pays K A 0 f hZ (le_refl _) hL hr h₁, held_over K A f hZ hE he hv' hx⟩
end
end
end YM.Next.Rank.Tapes
