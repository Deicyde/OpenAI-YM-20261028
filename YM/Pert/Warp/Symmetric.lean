import YM.Pert.Warp.PairIds
/-! Symmetrization of the deletion law on real centered linear probes. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Pert.Warp
open MeasureTheory ProbabilityTheory Function Tensor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsGaussian μ]
variable {K : Type*} [RCLike K] {I J : Type*} [Fintype J] [DecidableEq J] [DecidableEq I] [Fintype I] {n : ℕ}

def packet (μ : Measure E) (p : I→E→K) := Fintype.card I • scan μ ∅ p
def nullPay (i j : I) (p : I→E→K) : K := if i=j then 0 else scan μ {i,j} p
def refund (p : I→E→K) := ∑ i,∑ j,nullPay μ i j p

lemma packet_mean (p : I→E→K) : packet μ p = Fintype.card I • price μ p := by simp [packet,scan,price,kick,fake]
lemma packet_permute (p : I→E→K) (s : Equiv.Perm I) : packet μ (p∘s)=packet μ p := by
  rw [packet_mean,packet_mean,price,kick,price,kick];congr 1; apply congrArg (fun F:E→K=>∫ x,F x ∂μ); funext x; exact Equiv.prod_comp s (fun i=>p i x)
lemma pay_permute (p : I→E→K) (s : Equiv.Perm I) (i j) : nullPay μ i j (p∘s) = nullPay μ (s i) (s j) p := by
  unfold nullPay; simp only [EmbeddingLike.apply_eq_iff_eq]; split; rfl
  apply congrArg (fun A : E→E→K => ∫ x,(∫ y,A x y ∂μ) ∂μ); funext x y
  unfold fake; convert! Equiv.prod_comp s (fun k => p k (if k∈({s i, s j}: Finset I) then x else y)) using 1
  simp only [Finset.mem_insert,Finset.mem_singleton,EmbeddingLike.apply_eq_iff_eq]
  rfl
lemma refund_permute (p : I→E→K) (s : Equiv.Perm I) : refund μ (p ∘ s)=refund μ p := by
  simp only [refund,pay_permute]
  calc _ = ∑ i:I, ∑ j:I, nullPay μ (s i) j p := Finset.sum_congr rfl fun i _ => Equiv.sum_comp s (fun j=>nullPay μ (s i) j p)
       _ = _ := Equiv.sum_comp s (fun i=>∑ j, nullPay μ i j p)

def patt (f : Fin n→J) : T (J→ℝ) ℝ n := (ContinuousMultilinearMap.mkPiAlgebra ℝ _ _).compContinuousLinearMap (ContinuousLinearMap.proj ∘ f)
lemma patt_eq (f : Fin n→J) (z) : patt f z = ∏ i,z i (f i) := rfl

def scanning (t : Finset (Fin n)) (F : J→E→ℝ) : T (J→ℝ) ℝ n := ∑ v : Fin n→J, scan μ t (F∘v) • patt v
lemma scanning_eq (t : Finset (Fin n)) (F : J→E→ℝ) (hF : ∀ i, Orb.Tame (F i)) (z) : scanning μ t F z = scan μ t (charge F z) := by simp [scanning,scan_tab μ t F z hF,tab,patt_eq]

def sourceT (n : ℕ) (F : J→E→ℝ) : T (J→ℝ) ℝ n := Fintype.card (Fin n) • scanning μ ∅ F
def refundT (n : ℕ) (F : J→E→ℝ) : T (J→ℝ) ℝ n := ∑ i:Fin n,∑ j : Fin n, if i=j then 0 else scanning μ {i,j} F
lemma source_eq (F : J→E→ℝ) (hF : ∀ i, Orb.Tame (F i)) (z) : sourceT μ n F z = packet μ (charge F z) := by rw [sourceT, packet, show (Fintype.card (Fin n) • scanning _ _ F : T _ _ n) z = Fintype.card (Fin n) • (scanning μ ∅ F z) from rfl, scanning_eq _ _ _ hF]
lemma refund_eq (F : J→E→ℝ) (hF : ∀ i, Orb.Tame (F i)) (z) : refundT μ n F z = refund μ (charge F z) := by
  rw [refundT, refund, ContinuousMultilinearMap.sum_apply]; refine Finset.sum_congr rfl (fun i _=>?_); rw [ContinuousMultilinearMap.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_
  by_cases h : i=j <;> simp only [h,nullPay, reduceIte]
  exacts [rfl, scanning_eq μ _ F hF z]
lemma source_sym (F : J→E→ℝ) (hF : ∀ i, Orb.Tame (F i)) : Sym (sourceT μ n F) := fun z s=> (source_eq _ _ hF _).trans ((packet_permute μ (charge F z) s).trans (source_eq _ _ hF _).symm)
lemma refund_sym (F : J→E→ℝ) (hF : ∀ i, Orb.Tame (F i)) : Sym (refundT μ n F) := fun z s=> (refund_eq _ _ hF _).trans ((refund_permute μ (charge F z) s).trans (refund_eq _ _ hF _).symm)

lemma packet_zero (f : E→K) (hn : n=0) : packet μ (fun _ : Fin n => f) = refund μ (fun _ : Fin n=>f) := by subst n; unfold packet refund; simp
lemma pay_gen (f : E→K) (i j : Fin (n+1)) (h : i≠j) : nullPay μ i j (fun _ => f) = (∫ x,f x^2 ∂μ)*(∫ x,f x^(n-1) ∂μ) := by
  rw [nullPay,if_neg h,scan_exact]; have hp : ({i,j}:Finset (Fin (n+1))).card=2 := by simp [Finset.card_insert_of_notMem, h]
  have hc : (({i,j}:Finset (Fin (n+1)))ᶜ).card=n-1 := by rw [Finset.card_compl,Fintype.card_fin,hp]; omega
  simp only [kick,Finset.prod_const,hp,hc]
lemma refund_entry (f : E→K) (i : Fin (n+1)) : ∑ j : Fin (n+1),nullPay μ i j (fun _=>f) = n • ((∫ x,f x^2 ∂μ)*(∫ x,f x^(n-1) ∂μ)) := by
  rw [← Finset.sum_erase_add (h:=Finset.mem_univ i)]
  rw [show nullPay μ i i (p:=fun _=>f)=0 from if_pos rfl,add_zero]
  let A := (∫ x,f x^2 ∂μ)*(∫ x,f x^(n-1) ∂μ)
  rw [Finset.sum_congr rfl (g:=fun j:Fin (n+1)=>A) (fun x (hx : x∈Finset.univ.erase i)=>pay_gen μ f i x (Finset.ne_of_mem_erase hx).symm)]
  rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,Nat.add_sub_cancel]

lemma charge_diag (F : J→E→ℝ) (L : E→L[ℝ] ℝ) (z : J → ℝ) (h : charge F (fun _ : Fin (n+1) => z) = fun _ => (L : E → ℝ)) (hL : ∫ x,L x ∂μ=0) : packet μ (charge F (fun _ : Fin (n+1)=>z)) = refund μ (charge F (fun _ : Fin (n+1)=>z)) := by
  have he := diagonal_walk μ L hL n
  have h' (i : Fin (n+1)) := refund_entry μ ((L: E→ℝ)) i
  rw [h,packet,scan_exact,refund,kick,kick]; simp_rw [h',Finset.sum_const,Finset.card_univ]
  rw [Finset.compl_empty]; simp only [Finset.prod_empty, Finset.card_empty,pow_zero,integral_const,probReal_univ,smul_eq_mul,one_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin,he,nsmul_eq_mul];ring
lemma charge_center (F : J→E→L[ℝ] ℝ) (h : ∀j, ∫ x,F j x ∂μ=0) (z : J→ℝ) : packet μ (charge (fun j=>(F j: E→ℝ)) (fun _ : Fin n=>z)) = refund μ (charge (fun j=>(F j: E→ℝ)) (fun _ : Fin n=>z)) := by
  let L := ∑ j:J,z j • F j
  cases n with
  | zero=> exact packet_zero μ (charge (fun j=>(F j:E→ℝ)) (fun _:Unit=>z) ()) rfl
  | succ n =>
    have e : charge (fun j=>(F j:E→ℝ)) (fun _ : Fin (n+1)=>z) = fun _=>(L:E→ℝ) := by funext i x; simp [charge,L]
    apply charge_diag μ _ L z e
    simp only [L,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [integral_finsetSum _ (fun i (_:i∈Finset.univ) => (IsGaussian.integrable_dual μ (F i)).const_mul _)]
    simp_rw [integral_const_mul,h,mul_zero,Finset.sum_const_zero]
lemma packet_cancel (F : J→E→L[ℝ] ℝ) (h : ∀j, ∫ x,F j x ∂μ=0) (z : Fin n→J→ℝ) : packet μ (charge (fun j=>(F j: E→ℝ)) z) = refund μ (charge (fun j=>(F j: E→ℝ)) z) := by
  let P j := (F j:E→ℝ)
  have hF (j) := Orb.Tame.clm (F j)
  have e : sourceT μ n P = refundT μ n P := Tensor.ext_diag _ _ (source_sym μ P hF) (refund_sym μ P hF) (funext fun t:J→ℝ=>by unfold diagonal; rw [source_eq μ P hF,refund_eq μ P hF]; exact charge_center μ F h t)
  rw [←source_eq μ P hF,e,refund_eq μ P hF]
end YM.Pert.Warp
