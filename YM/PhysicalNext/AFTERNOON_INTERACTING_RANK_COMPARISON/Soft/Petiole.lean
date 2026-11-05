import YM.AnalyticNext.QUARTIC_MATCH.Radius.Fruit
import YM.Further.QUANTUM_RATES_PORT.Accounts
import YM.Next.WARD_BIN.LabelEst
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Pattern
import YM.PhysicalNext.GRADED_QUARTIC_RATE.Stamp
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.STRESS_FLUX.Low
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free

/-!
# Anchored support economy of the soft basis

Base *at the same beta* carries the clipped ell and linear charges.
The ancillary output E may actually contain negatives of the canonical
atom channels, also paying their FULL-LENGTH supports & original masks.
Don't conflate this with real projection of a Hessian or bounds to
be used for beta renormalization. Here it's a different, value-only step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Next.Rank RankCovariance Thirst Pump
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι κ : Type} {k : ℕ} {P : BudgetPoint} {σ d L u τ A : ℝ}
section
variable (F : ℕ → Atom G k) (hf : ∀ i,(F i).Invariant) (P : BudgetPoint)

def juke (x : Site n × ℕ) : Piece G n P.threshold where
  atWay:= ⟨x.1,(F x.2).footprint x.1,mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩⟩
  value:=fun U=> (F x.2).placed P U x.1
  gauge:= Alarm.scorn (F x.2) P (hf x.2) x.1
  probes:= masked_measurable _ _ _ ((F x.2).unmasked_cont _).measurable
  look:= masksLook (Alarm.unmasked_space (F x.2) _)
  leave _ h:= Classical.byContradiction fun hp=>h (masked_ne _ _ _ _ hp)
def detail (P : BudgetPoint) (k : ℕ) (A : ℝ):=Real.exp (P.supportExponent*(1+2*k:ℝ))*P.threshold^k*A
-- price in true length accommodates native cover even for all winding supports.
lemma juke_cost (n : Side) (hs : SumBudget (fun i=> (F i).budget σ) A) (hw : P.supportExponent/P.B≤ σ) : Pieces (p:=P) (n:=n) (juke F hf P) (detail P k A):= by
  let C :ℝ:=P.supportExponent*(1+2*k:ℝ)
  let t':= Real.exp C * P.threshold^k; let v (i:ℕ):=(F i).magnitude*P.threshold^k
  have ht : 0≤t':= mul_nonneg (Real.exp_pos _).le (pow_nonneg P.threshold_pos.le _)
  have hv i : 0≤v i := mul_nonneg (by unfold Atom.magnitude; positivity) (pow_nonneg P.threshold_pos.le _)
  have he (x : Site n) (i : ℕ) : P.mass ((F i).footprint x) (v i) ≤ t'*(F i).budget σ:= by
    let M:=P.B; let d:= coverNumber P.B ((F i).footprint x); let l:= (F i).length
    have hp:0<(M:ℝ):=by exact_mod_cast P.B_pos
    have hz : (M:ℝ)*d ≤ M+(k*(2*(M:ℝ))+l):= by
      exact_mod_cast Next.Scheduling.Wages.traversed (F i) x M (show 0<M from P.B_pos)
    have hh: (d:ℝ) ≤ (1+2*k:ℝ)+(l:ℝ)/M:= by field_simp; linarith only [hz]
    have hb:P.supportExponent * d ≤ C+σ*l:= by
      refine (mul_le_mul_of_nonneg_left hh P.exponent_pos.le).trans ?_
      unfold C; rw [mul_add]; refine add_le_add_right ?_ _; calc
          _ = (P.supportExponent/P.B)*(l:ℝ):= by unfold M; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hw (by positivity)
    change Real.exp _ * _ ≤ _*_
    have hA := mul_le_mul_of_nonneg_right (Real.exp_monotone hb) (hv i); apply hA.trans_eq
    rw [Real.exp_add]; unfold t' Atom.budget v; ring
  refine ⟨fun i=>v i.2,fun i=> ⟨hv _,fun U=> healthy_atom (F i.2) P U i.1⟩,fun x=> ?_⟩
  let f (i : Site n × ℕ):= if i.1=x then P.mass ((F i.2).footprint i.1) (v i.2) else 0
  have h (i : Site n × ℕ):0≤f i:= by unfold f; split; exact mul_nonneg (Real.exp_pos _).le (hv _); exact le_rfl
  let g (i : Site n × ℕ):= if i.1=x then t'*(F i.2).budget σ else 0
  have hL (i): f i ≤ g i:= by unfold f g; split; exact he _ _; exact le_rfl
  have hp : Summable g:= (summable_prod_of_nonneg (fun i=> (h i).trans (hL i))).2 ⟨fun i=> by
    unfold g; by_cases he:i=x; simpa only [he,↓reduceIte] using hs.2.1.mul_left t'; simp only [he,↓reduceIte]; exact summable_zero,(hasSum_fintype _).summable⟩
  change SumBudget f _; have hM:= hp.of_nonneg_of_le h hL
  refine ⟨h,hM, (hM.tsum_le_tsum hL hp).trans ?_⟩
  rw [hp.tsum_prod,tsum_fintype,sum_eq_single x];
  · unfold g; simp only [↓reduceIte]; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hs.2.2 ht
  · intro i _ hv; simp only [g,hv,↓reduceIte,tsum_zero]
  simp
end
-- use after pricing; keeps every channel
section
variable (Q : Rep G n) (H : Q.path.Bounds Q.clip σ A L)
abbrev ix (n : Side):= Site n × ℕ
def anthology (i : (Site n × ℕ) ⊕ ((Site n × ℕ) ⊕ (Site n × ℕ))) : Piece G n Q.p.threshold := Sum.elim
    (fun j=> (juke Q.path.cubic (fun i=> (H.invariant i).2.1) _ j).reweight (-Q.beta))
    (Sum.elim (fun j=>(juke Q.path.quartic (fun i=> (H.invariant i).2.2) _ j).reweight (-Q.beta)) (fun j=> (juke Q.path.loop (fun i=> (H.invariant i).1) _ j).reweight (-1))) i

def boxesCost (P : BudgetPoint) (β A L : ℝ):=|β| *detail P 3 A+(|β| *detail P 4 A+detail P 2 L)
lemma box_paid (hp : Q.p.supportExponent/Q.p.B≤σ) : Pieces (p:=Q.p) (anthology Q H) (boxesCost Q.p Q.beta A L):= by
  let P:= Q.p;let T:= Q.path
  let X:= fun j:ix n=>juke T.cubic (fun i=> (H.invariant i).2.1) P j; let Y:= fun j:ix n=>juke T.quartic (fun i=>(H.invariant i).2.2) P j; let Z:= fun j:ix n=>juke T.loop (fun i=>(H.invariant i).1) P j
  have hx: Pieces (p:=P) X (detail P 3 A):= juke_cost _ _ P n H.three hp
  have hy: Pieces (p:=P) Y (detail P 4 A):= juke_cost _ _ P n H.four hp
  have hz: Pieces (p:=P) Z (detail P 2 L):= juke_cost _ _ P n H.two hp
  simpa only [anthology,boxesCost,abs_neg,abs_one,one_mul] using! (hx.scaling (-Q.beta)).combine ((hy.scaling (-Q.beta)).combine (hz.scaling (-1)))
def mounts (W : Signed × (ix n⊕ix n⊕ix n)): Piece G n Q.p.threshold:=
    ((anthology Q H W.2).turn (W.1,0)).reweight (Fintype.card Signed:ℝ)⁻¹
lemma mount_cost (hp : Q.p.supportExponent/Q.p.B≤σ) : Pieces (p:=Q.p) (mounts Q H) (boxesCost Q.p Q.beta A L):=by
  let r:ℝ:=Fintype.card Signed; let v:=boxesCost Q.p Q.beta A L
  apply (Pieces.eachAxis (p:=Q.p) (fun _ : Signed=> |r⁻¹| *v) (fun i=> ((box_paid Q H hp).turn (i,0)).scaling r⁻¹)).across
  have hr:0<r:= by unfold r; positivity
  simp only [sum_const,card_univ,nsmul_eq_mul,abs_of_nonneg (inv_pos.mpr hr).le]; rw [show (Fintype.card Signed:ℝ)=r from rfl,← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul]

def basis (Q : Rep G n) (V : Config G n):= (Fintype.card Signed:ℝ)⁻¹*∑ s:Signed,∑ i,Q.path.baseTerm Q.clip Q.p (pull s 0 V) i
lemma mount_price (hp : Q.p.supportExponent/Q.p.B ≤ σ) (V : Config G n) :
    Q.path.inChannels Q.clip Q.p Q.beta V + (∑' i,(mounts Q H i).value V) = Q.beta*basis Q V := by
  let b:=Q.beta; let T:=Q.path; let p:=Q.p; let K:ℝ:=Fintype.card Signed; let l:=Q.clip
  have hx P (r : ℝ) (k : ℕ) (F : ℕ→ Atom G k) (g : ℝ) (hf : SumBudget (fun i=> (F i).budget σ) g) (h : ∀ i,(F i).Invariant) :
      let j := fun i : ix n=> (juke F h p i).reweight r
      Summable (fun i=> (j i).value P) ∧ (∑' i,(j i).value P) =r*∑ i,PathData.atomSeries (n:=n) F Q.p P i := by
    intro j; have he : Summable (fun i=> (j i).value P):= ((juke_cost F h p n hf hp).scaling r).all P
    refine ⟨he,?_⟩; rw [he.tsum_prod,tsum_fintype,mul_sum]
    exact sum_congr rfl fun i _=> tsum_mul_left ..
  have he (W : Config G n) (i : Signed) :
      let V:= pull i 0 W
      T.principal l p b V + (∑' j,(anthology Q H j).value V) = b*∑ i, T.baseTerm l p V i:= by
    intro V
    let h (i: ix n⊕ix n⊕ix n):=(anthology Q H i).value V
    obtain ⟨hx',h1⟩:=hx V (-b) 3 _ _ H.three (fun i=>(H.invariant i).2.1)
    obtain ⟨hy',h2⟩:=hx V (-b) 4 _ _ H.four (fun i=>(H.invariant i).2.2); obtain ⟨hz,h3⟩:=hx V (-1) 2 _ _ H.two (fun i=>(H.invariant i).1)
    rw [Summable.tsum_sum (f:=h) hx' (Summable.sum (h ∘ Sum.inr) hy' hz)]
    rw [Summable.tsum_sum (f:=fun i=> h (Sum.inr i)) hy' hz]
    change T.principal l p b V + _ = _
    unfold PathData.principal
    rw [sum_add_distrib]
    change ∑' (x:ix n), h (.inl x) = -b*∑ i,PathData.atomSeries T.cubic p V i at h1
    change ∑' (x:ix n), h (.inr (.inl x))= -b*∑ i,PathData.atomSeries T.quartic p V i at h2
    change ∑' (x:ix n), h (.inr (.inr x))= (-1)*∑ i,PathData.atomSeries T.loop p V i at h3
    change b*_+_+ ((∑' x,h (.inl x))+((∑' x,h (.inr (.inl x)))+∑' x,h (.inr (.inr x)))) = _
    rw [h1,h2,h3]; ring
  rw [((mount_cost Q H hp).all V).tsum_prod,tsum_fintype]; unfold PathData.inChannels basis
  change K⁻¹* ∑ i:Signed, T.principal l p b (pull i 0 V) + (∑ i:Signed,∑' j,K⁻¹ * (anthology Q H j).value (pull i 0 V))= b*_
  simp_rw [tsum_mul_left]; rw [← mul_sum,← mul_add, ← sum_add_distrib, mul_left_comm b];
  refine congr_arg (K⁻¹*·) ?_; rw [mul_sum]; refine sum_congr rfl fun i _=> he _ _

omit H in
lemma basis_turn (e : Wheel n) (V : Config G n): basis Q (pull e.1 e.2 V) = basis Q V := by
  let K (V : Config G n):= ∑ i : PlaqAxes, Q.path.baseTerm Q.clip Q.p V (0,i)
  have he (V : Config G n) : basis Q V= Next.Rank.Alarm.rag K V:= by
    unfold basis Next.Rank.Alarm.rag; apply congr_arg ((Fintype.card Signed:ℝ)⁻¹ *·)
    refine sum_congr rfl fun i _=>?_; rw [← Next.Rank.Alarm.spin_shift]; rw [Fintype.sum_prod_type]; exact sum_congr rfl fun x _ => sum_congr rfl fun j _ => Next.Rank.Edition.base_at _ _ _ _
  rw [he,he, Next.Rank.Edition.rag_rip]

end
end YM.PhysicalNext.InteractingRank.Soft
