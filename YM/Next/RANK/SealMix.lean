import YM.Next.RANK.ArraySpace
import YM.Next.RANK.Patchable

/-!
# Multi pack prices

Inputs billed at their marker root and ORIGINAL receipt, before weakening threshold.
Even though calls may use the same U for all marks of a cell, don't recover
root v budgets without charging the old geometry. We can afford even at
unweighted radius from mixed reads, thanks to actual positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V ι κ : Type} [DecidableEq V] [Fintype V]
variable {ζ : V→ Site n} {r p : BudgetPoint} {d e u v t : ℝ}

-- currency per marker. applies even to K mixtures multi. weights outside.

def stars (r : BudgetPoint) (F : ι→modes V) (X : ι→Support n) (e : ℝ) (c : ι→ℝ) (t : ℝ) := ∀ x : V, Point X r.B c e (fun i=> x∈(F i).val) t

lemma roots_hits (X : ι→Support n) (F : ι→modes V) (K : V→Site n) (h : Function.Injective K) (hf : ∀ i,(F i).val.Nonempty) (hX : ∀ i j,j∈ (F i).val→ K j∈X i)
    {c : ι→ℝ} {p : BudgetPoint} (he : ∀ i,0 ≤c i) {e d : ℝ} (hp : 0≤ d) (hz : stars p F X (e+1) c d) : Incur X p.B c e (wilt p.B*d):= by
  let f i:=Classical.choose (hf i); have hu i : f i∈(F i).val:= Classical.choose_spec (hf i)
  apply circle X _ (K∘f) (fun i=>hX i _ (hu i)) _ _ p.B_pos he _
  intro x; let a := pay (fun i=> c i*debt p.B (e+1) (X i)) (fun j=>K (f j)=x)
  have ha i:0≤a i:= by unfold a pay;split;exact mul_nonneg (he i) (Real.exp_pos _).le; exact le_rfl
  change SumBudget a d
  by_cases hv:∃ i,K i=x
  · obtain ⟨i,hi⟩:=hv; have hx:= hz i
    have hv (j) : a j ≤ pay (fun i=> c i*debt p.B (e+1) (X i)) (fun k=> i∈ (F k).val) j := by
      by_cases hQ:K (f j)=x
      · have hT:f j=i:=h (hQ.trans hi.symm); unfold a pay; rw [if_pos hQ, if_pos (show i∈ (F j).val from hT ▸ hu j)]
      refine le_trans (le_of_eq ?_) (hx.1 j); exact if_neg hQ
    have hb:=hx.2.1.of_nonneg_of_le ha hv; exact ⟨ha,hb,(hb.tsum_le_tsum hv hx.2.1).trans hx.2.2⟩
  have hX:a=fun _=>0:= funext fun i=> if_neg (fun h=>hv ⟨_,h⟩); rw [hX];exact ⟨fun i=>le_rfl,summable_zero,tsum_zero.le.trans hp⟩

-- lots of mass currency, dual W/R long not here

def transported (H : SourceAt G ζ) (τ : ℝ) (r : V→ℝ) (a : ℝ) := 0 ≤ a ∧ ∀ U,Healthy τ H.extent U→ Poly.price r (H.amount τ U) ≤ a
lemma transferD (H : SourceAt G ζ) (τ : ℝ) (r : V→ℝ) (a : ℝ) : transported H τ r a ↔ 0 ≤ a ∧ ∀ U, Healthy τ H.extent U→ Poly.toll r H.fires* ‖H.value U‖ ≤ a:=by
  refine and_congr_right fun h=> forall_congr' fun U=> imp_congr_right fun hu=> ?_; rw [SourceAt.amount,Poly.solo,masked_eq _ _ _ _ hu]

def Unpacks (H : ι→SourceAt G ζ) (p : BudgetPoint) (r : V→ℝ) (e t : ℝ) := ∃ b : ι→ℝ,(∀ i,transported (H i) p.threshold r (b i)) ∧
    stars p (fun i=> (H i).fires) (fun i=> (H i).extent) e b t

def Unfold (A : ι→Lifted G ζ p.threshold) (r : V→ℝ) (v e : ℝ) := ∃ b : ι→ℝ,(∀ i,heavy (A i) r (b i)) ∧
    stars p (fun i=> (A i).fires) (fun i=> (A i).extent) v b e

lemma count_cost (p : BudgetPoint) (Z : Support n) (x : modes V) (hf : Spaced p.B ζ) (h : 2≤ x.val.card) (hp : ∀ j, j∈x.val → ζ j∈Z) (hu : 8 ≤ p.B) :
    p.B*x.val.card ≤ 64*coverNumber p.B Z := YM.Work.I01.answer n V ζ p.B hu x.val (fun i hi j hj hh=> hf i j hh) h Z (by intro z hz; obtain ⟨j,hj,rfl⟩:= mem_image.mp hz; exact hp j hj)

-- gate relation: v paid exponent B source into q tests incl halo8 enlargements
structure BudgetMix (p q : BudgetPoint) (s r : ℝ) (e δ : ℝ) where
  u : ℝ
  grows : 0 ≤ u
  fee : 0 ≤ δ
  value : 0 ≤ e
  body : 8≤p.B
  width : Lower p q
  grant : 100000*(p.B:ℝ)*e ≤ q.B*(p.supportExponent/2)
  worth : r ≤ Real.exp u * s
  wt : 64*(u+δ+100000*e) ≤ p.B * (p.supportExponent/2)

lemma charges (h : BudgetMix p r t u e d) (ht : 0 ≤ u) {Q : Support n} {J : modes V} (hi : Spaced p.B ζ) (hj : 2 ≤ J.val.card) (hv : ∀ i,i∈J.val → ζ i∈ Q) :
    Poly.toll (fun _=> u) J * debt r.B e (halo 8 Q)≤ Real.exp (-d)*(Poly.toll (fun _=> t) J * debt p.B p.supportExponent Q) := by
  have ht' : 0≤ Real.exp h.u * t:= ht.trans h.worth
  have he : 0≤ t:= nonneg_of_mul_nonneg_right ht' (Real.exp_pos _)
  let W:= coverNumber r.B (halo 8 Q); let X:= coverNumber p.B Q; let C:= J.val.card
  have hL : e* W≤ 100000*e + X*(p.supportExponent/2):= by
    have hy := h.width
    have hz : (r.B:ℝ)*W≤ 100000*(r.B+(p.B:ℝ)*X):= by exact_mod_cast widen p.B r.B 8 p.B_pos hy.grows hy.size Q
    apply le_of_mul_le_mul_left _ (show 0<(r.B:ℝ) by exact_mod_cast r.B_pos)
    linarith only [mul_le_mul_of_nonneg_right hz h.value, mul_le_mul_of_nonneg_right h.grant (Nat.cast_nonneg (α:=ℝ) X)]
  have hp : (C:ℝ)*h.u + e*W ≤ -d+p.supportExponent*X := by
    have hC : (1:ℝ) ≤ C:= by exact_mod_cast (le_trans (by decide) hj : 1 ≤ C)
    have hx : (p.B:ℝ)*C≤ 64* X:= by exact_mod_cast count_cost p Q J hi hj hv h.body
    have hh := mul_le_mul_of_nonneg_left hC h.fee; have ht := mul_le_mul_of_nonneg_right h.wt (Nat.cast_nonneg (α:=ℝ) C)
    linarith only [hh,hL,mul_le_mul_of_nonneg_left hC h.value,ht,mul_le_mul_of_nonneg_right hx p.exponent_pos.le]
  simp only [Poly.toll, prod_const]; apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht h.worth C) (Real.exp_pos _).le).trans
  change (Real.exp h.u*t)^C * debt r.B e (halo 8 Q) ≤ _; rw [mul_pow,← Real.exp_nat_mul]; unfold debt
  have hg:= mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) (pow_nonneg he C)
  simp only [Real.exp_add] at hg; change _*t^C * Real.exp (e*W) ≤ Real.exp (-d)*(t^C*Real.exp (p.supportExponent*X)); linarith only [hg]

lemma bill_changed (H : BudgetMix p r t u e d) (hu : 0<u) (ht : 0<t) (F : ι→modes V) (X : ι→Support n) {c : ι→ℝ} (hx : ∀ i,0≤ c i)
    (hi : Spaced p.B ζ) (hs : ∀ i, 2≤(F i).val.card) (hX : ∀ i,∀ j,j∈(F i).val→ζ j∈X i) (h : stars p F X p.supportExponent c v) :
    stars r F (fun i=> halo 8 (X i)) e (fun i=> c i * (Poly.toll (fun _=>u) (F i)/ Poly.toll (fun _=>t) (F i))) (Real.exp (-d)*v) := by
  let α i := Poly.toll (fun _=>u) (F i); let β i:= Poly.toll (fun _=>t) (F i)
  have ha i:0<α i:= Poly.worth (fun _=> hu) _; have hb i:0<β i:= Poly.worth (fun _=> ht) _
  intro x
  let f:=pay (fun i=> c i*(α i/β i)* debt r.B e (halo 8 (X i))) (fun j=> x∈(F j).val)
  let z i:= pay (fun i=> c i*debt p.B p.supportExponent (X i)) (fun j=> x∈(F j).val) i; change SumBudget f _
  have hf i:0≤ f i:= by unfold f pay;split; exact mul_nonneg (mul_nonneg (hx _) (div_nonneg (ha i).le (hb i).le)) (Real.exp_pos _).le; exact le_rfl
  have hz:= h x; let Q:= Real.exp (-d); have hQ:=Real.exp_pos (-d)
  have hm i:f i ≤ Q*z i:= by
    unfold f z pay; split_ifs
    · have hg:=charges H hu.le hi (hs i) (hX i)
      apply le_of_mul_le_mul_right _ (hb i)
      have ht:(c i*(α i/β i)*debt r.B e (halo 8 (X i)))*(β i)=c i*(α i*debt r.B e (halo 8 (X i))) := by have ht:β i≠0:=(hb i).ne'; field_simp
      rw [ht]; refine (mul_le_mul_of_nonneg_left hg (hx i)).trans_eq ?_; unfold Q β; ring
    rw [mul_zero]
  have hp : Summable (fun i=> Q*z i):= hz.2.1.mul_left _; have he:= hp.of_nonneg_of_le hf hm
  refine ⟨hf,he,(he.tsum_le_tsum hm hp).trans ?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hz.2.2 hQ.le

lemma ratios {X Y z a : ℝ} (hp : 0< Y) (hX : 0≤X) (h : Y*z≤a) : X*z ≤ a*(X/Y):= by
  refine le_trans (b:= X*(a/Y)) ?_ (le_of_eq ?_)
  · exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hp).2 (by rwa [mul_comm])) hX
  ring
lemma rooted_interest {Y : ι→Lifted G ζ p.threshold} (h : Unfold (p:=p) Y (fun _=>t) p.supportExponent v) (hs : ∀ i,2≤(Y i).fires.val.card)
    (H : BudgetMix p r t u (e+1) d) (hz : 0<t) (hh : 0<u) ( _ : 0≤e) (hy : 0 ≤ v) (hi : Spaced p.B ζ) :
    Burden Y r (fun _=>u) e (wilt r.B*(Real.exp (-d)*v)):= by
  obtain ⟨c,hf,hr⟩:=h
  let m i:= Poly.toll (fun _=>u) (Y i).fires; let P i:=Poly.toll (fun _=>t) (Y i).fires
  have hm i:0<m i:= Poly.worth (fun _=>hh) _; have hp i:0<P i:=Poly.worth (fun _=>hz) _
  let f i:= c i*(m i/P i)
  have ht i:0≤ f i:=mul_nonneg (hf i|>.1) (div_nonneg (hm i|>.le) (hp i|>.le))
  have hx:= bill_changed H hh hz _ _ (fun i=> (hf i).1) hi hs (fun i j=> (Y i).remembers j) hr
  refine ⟨f,fun i=>⟨ht i,fun U=> ratios (hp i) (hm i|>.le) (hf i|>.2 U)⟩,
    roots_hits _ (fun i=> (Y i).fires) ζ (injected _ ζ p.B_pos hi) ?_ ?_ ht (mul_nonneg (Real.exp_pos _).le hy) hx⟩
  · exact fun i=> card_pos.mp (lt_of_lt_of_le (by norm_num) (hs _))
  exact fun i j hj=> halo_subset _ _ ((Y i).remembers j hj)

/-- BOTH carried and attachment estimates still in OLD t for H. -/
def Credit (W : ι→SourceAt G ζ) (p q : BudgetPoint) (r : V→ℝ) (e t : ℝ) := ∃ b : ι→ℝ,(∀ i,transported (W i) p.threshold r (b i)) ∧
    stars q (fun i=>(W i).fires) (fun i=> halo 8 (W i).extent) e b t
lemma transfer (W : ι→SourceAt G ζ) (h : Unpacks W p (fun _=>t) p.supportExponent v) (hs : ∀ i,2≤ (W i).fires.val.card)
    (H : BudgetMix p r t u e d) (hz : 0<t) (hh : 0<u) (hi : Spaced p.B ζ) : Credit W p r (fun _=>u) e (Real.exp (-d)*v):= by
  obtain ⟨b,hb,hL⟩:=h
  let m i:= Poly.toll (fun _=>u) (W i).fires; let P i:=Poly.toll (fun _=>t) (W i).fires
  have hm i:0<m i:=Poly.worth (fun _=>hh) _; have hp i:0<P i:=Poly.worth (fun _=>hz) _
  let f i:= b i*(m i/P i)
  refine ⟨f,fun i=> (transferD ..).2 ⟨mul_nonneg (hb i|>.1) (div_nonneg (hm i|>.le) (hp i|>.le)),fun U hU=>?_⟩,
    bill_changed H hh hz _ _ (fun i=> (hb i).1) hi hs (fun i j=> (W i).remembers j) hL⟩
  exact ratios (hp i) (hm i|>.le) (((transferD ..).1 (hb i)).2 U hU)
end YM.Next.Rank.Edition
