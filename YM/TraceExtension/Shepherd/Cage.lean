import YM.TraceExtension.Shepherd.Slide
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Gauge Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n)
local notation "W!"=> R.path
local notation "b!"=> R.p.threshold
local notation "M!"=> R.p.B
local notation "d!"=> R.p.supportExponent
variable {σ A v δ t:ℝ}(h:R.Lawful σ A v δ t)(H:Geo.Width R.p R.clip σ)
private lemma comes (S:Badge n→Support n)(a e:ℝ)(f:Badge n→ℝ)(he:0 ≤ e)(hp:∀ i,(S i).Nonempty)(hf:∀ i,0 ≤ f i)(h:Hit S M! f e a):Summable f:=by
    let V(x : Site n)(i):= if x∈ S i then f i*Real.exp (e*coverNumber M! (S i)) else 0
    refine Summable.of_nonneg_of_le (f:=fun i=>∑ x,V x i) hf (fun i=> ?_) (summable_sum fun i _=> (h i).2.1)
    obtain ⟨x,hx⟩:=hp i; refine le_trans ?_ (single_le_sum (f:=fun x=> V x i) (fun x _=> (h x).1 i) (mem_univ x)); unfold V; rw[if_pos hx]; exact le_mul_of_one_le_right (hf _) (Real.one_le_exp (by positivity))
lemma sprang (i:Badge n): (boothC R i).Nonempty:= match i with| .inl i=>⟨_,(i.1.reg _ (sloop R i.2)).anchor⟩| .inr i=> ⟨_,(R.activities.reg i).anchor⟩
-- absolute costA/B; `B` only for Brink diffs.
def tariff (b c :ℝ):= Fintype.card Signed * siteFactor R.p.B * (factor*b) + c*siteFactor R.p.B
abbrev leaseC (σ A v:ℝ):= (2*b!*|R.beta|)* crown R σ A+ bedste R A v
abbrev wingC (d σ A v:ℝ):= (|R.beta| *((2*kindle G) * d * b!))*crown R σ A+ 2*bedste R A v
include h H
lemma cans (he:0 ≤ d!-1): ∃ b: Support n→ℝ,(∀ i,0 ≤ b i ∧ ∀ U,|stockC R i U| ≤ b i)∧ Hit id M! b (d!-1) (tariff R (leaseC R σ A v) δ):=by
    obtain ⟨c,hc,hm⟩:= h.labels.boundE; have hc'(i U): |R.activities.regularOccurrence R.p i U|≤ c i:=by unfold Activities.regularOccurrence; by_cases ht:Healthy b! (R.activities.reg i).support U; rw [masked_eq _ _ _ _ ht]; exact (hc i).2 U ht [] (Nat.zero_le _) (by simp); rw [masked_ne _ _ _ _ ht,abs_zero]; exact (hc i).1
    let f: Badge n→ℝ:= Sum.elim (fun i=> factor * bingo R i.2) c
    have hy(i):0 ≤ f i:= match i with| .inl i=>mul_nonneg factor_pos.le ((abs_nonneg _).trans (canto R _ 1))| .inr i=>(hc i).1
    have hζ : Hit (boothC R) M! f (d!-1) (tariff R (leaseC R σ A v) δ):=by unfold tariff; rw [mul_comm δ]; exact hitting (boothC R ∘ Sum.inl) (boothC R ∘ Sum.inr) (boothC R) rfl rfl _ _ _ (rawHit R (fun i=> (abs_nonneg _).trans (canto R i 1)) (grand R h H)) (regHit R h.labels.boundE (fun i=>(hc i).1) hm)
    have he':=comes R (boothC R) _ _ _ he (sprang R) hy hζ; refine ⟨cram (boothC R) f,fun i=>⟨tsum_nonneg (fun i=> hy _),fun U=>?_⟩,pass_hit _ _ _ hζ he'⟩
    let p := pieceC R; unfold stockC; apply le_trans (norm_tsum_le_tsum_norm ((songE R h H U).norm.comp_injective (i:=Subtype.val (p:=fun p=>boothC R p=i)) Subtype.val_injective)); refine Summable.tsum_le_tsum (fun i=>?_) ((songE R h H U).norm.comp_injective Subtype.val_injective) (he'.comp_injective Subtype.val_injective)
    rcases i with ⟨i|i,hi⟩; change |_| ≤ factor*_; rw [pieceC]; change |-factor*(_ : ℝ)| ≤ _; rw [abs_mul,abs_neg,abs_of_pos factor_pos]; exact mul_le_mul_of_nonneg_left (canto R _ _) factor_pos.le
    change |- _| ≤ c i; rw[abs_neg]; exact hc' i U
lemma wings (he:0 ≤ d!-1)(p:ℝ)(hp:0 ≤ p): ∃ b: Support n→ℝ,(∀ i,0 ≤ b i ∧ ∀ U V:Config G n, Brink R p U V → |stockC R i U-stockC R i V| ≤ b i) ∧ Hit id M! b (d!-1) (tariff R (wingC R p σ A v) (2*δ)):=by
    obtain ⟨c,hc,hm⟩:= h.labels.boundE; have hc'(i U): |R.activities.regularOccurrence R.p i U|≤ c i:=by unfold Activities.regularOccurrence; by_cases ht:Healthy b! (R.activities.reg i).support U; rw [masked_eq _ _ _ _ ht]; exact (hc i).2 U ht [] (Nat.zero_le _) (by simp); rw [masked_ne _ _ _ _ ht,abs_zero]; exact (hc i).1
    have hU:=salary R h H p hp; have hf (i) : 0 ≤ balm R i p:= by apply nonneg_of_mul_nonneg_left (hU.1 i) (Real.exp_pos (d!*coverNumber M! (fort R i)))
    let f: Badge n→ℝ:= Sum.elim (fun i=> factor*balm R i.2 p) (fun i=>2*c i)
    have hy(i):0 ≤ f i:= match i with| .inl i=>mul_nonneg factor_pos.le (hf i.2)| .inr i=>mul_nonneg zero_le_two (hc i).1
    have hE:=rawHit R hf hU; have hτ:= regHit R h.labels.boundE (fun i=>(hc i).1) hm
    have hz : Hit (boothC R ∘ Sum.inr) M! (fun i=>2*c i) (d!-1) (2*(siteFactor M!*δ)) := by
        intro x; convert! budget_scale (by norm_num : (0:ℝ) ≤ 2) (hτ x) using 1; funext i; split <;> ring
    have hζ : Hit (boothC R) M! f (d!-1) (tariff R (wingC R p σ A v) (2*δ)):=by unfold tariff; rw [show 2*δ*siteFactor M! =2*(siteFactor M!*δ) from by ring]; exact hitting (boothC R ∘ Sum.inl) (boothC R ∘ Sum.inr) (boothC R) rfl rfl _ _ _ hE hz
    have he':=comes R (boothC R) _ _ _ he (sprang R) hy hζ; refine ⟨cram (boothC R) f,fun i=>⟨tsum_nonneg (fun i=> hy _),fun U V H'=>?_⟩,pass_hit _ _ _ hζ he'⟩
    let p' W:= (songE R h H W).comp_injective (i:=Subtype.val (p:=fun p=>boothC R p=i)) Subtype.val_injective; change |∑' x:{u// boothC R u=i}, ((fun t=>pieceC R t U) ∘ Subtype.val) x-∑' x:{u//boothC R u=i}, ((fun t=>pieceC R t V) ∘ Subtype.val) x| ≤ _; rw [← Summable.tsum_sub (p' U) (p' V)]; let v':=((p' U).sub (p' V)).norm
    apply (norm_tsum_le_tsum_norm v').trans; apply Summable.tsum_le_tsum _ v' (he'.comp_injective Subtype.val_injective); rintro ⟨i|i,hi⟩
    · change |-factor*(_ :ℝ)- -factor*_| ≤ factor*_; rw [← mul_sub,abs_mul,abs_neg,abs_of_pos factor_pos]; exact mul_le_mul_of_nonneg_left (casto R H' i.1 _) factor_pos.le
    change |- _ - - _| ≤ 2*c i; rw [two_mul]; exact (abs_sub ..).trans (add_le_add ((abs_neg _).trans_le (hc' i U)) ((abs_neg _).trans_le (hc' i V)))
-- truncate with p.support shift by 1
abbrev SheetL (d:ℕ):= {v:Support n// d < coverNumber R.p.B v}
lemma tallL (he:0 ≤ d!-1)(p :ℕ):∃ b: SheetL R p → ℝ,(∀ i,0 ≤ b i ∧ ∀ U,|stockC R i.val U| ≤ b i) ∧ Hit Subtype.val M! b (d!-2) (Real.exp (-(p:ℝ))*tariff R (leaseC R σ A v) δ):=by
    obtain ⟨b,hb,hp⟩:= cans R h H he; refine ⟨_,fun i=> hb i.val,fun i=>?_⟩
    refine Budget.pull_le (p:=fun _=>True) (q:=Subtype.val) (budget_scale (Real.exp_pos _).le (hp i)) (fun j=> by split; exact mul_nonneg (hb _|>.1) (Real.exp_pos _).le; rfl) (fun _ _=>trivial) Subtype.val_injective.injOn fun j _=>?_
    split
    next ht=>
        rw[if_pos (show i∈id j.val from ht),mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (hb _|>.1); apply Real.exp_monotone; change (d!-2)*coverNumber M! j.val ≤ -(p:ℝ)+(d!-1)*coverNumber M! j.val; linarith only [show (p:ℝ) ≤ coverNumber M! j.val from Nat.cast_le.mpr j.property.le]
    next ht=> rw[if_neg (show i∉id j.val from ht),mul_zero]
end YM.Trace.Shepherd
