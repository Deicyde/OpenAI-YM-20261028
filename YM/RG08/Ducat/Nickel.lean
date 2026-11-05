import YM.RG08.Ducat.Shines

/-! # Scalar coupling prices and variation after reclosure. Won't repeat any without charging gain. -/
noncomputable section
namespace YM.RG08.Ducat
open Filter Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat
open scoped Classical BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type}(D:Exchange O)(d:O→ℝ)
def Weigh (f g:O→ℝ):Prop:=∃ p,D.Good p∧∀ i,|f i| ≤ p i∧|g i| ≤ p i∧|f i-g i|≤p i*d i
namespace Weigh
variable {f g f' g':O→ℝ}
lemma flat (c:ℝ)(hd:∀ i,0≤d i):Weigh D d (fun _=>c) (fun _=>c):= ⟨_,D.steady _ (abs_nonneg c),fun i=>⟨le_rfl,le_rfl,by simp only [sub_self,abs_zero];exact mul_nonneg (abs_nonneg _) (hd i)⟩⟩
variable {D d}
lemma sum (h:Weigh D d f g)(he:Weigh D d f' g'):Weigh D d (fun i=> f i+f' i) (fun i=>g i+g' i):=by
 obtain ⟨p,hp,h⟩:=h;obtain ⟨v,hv,H⟩:=he
 refine ⟨_,D.hear _ _ hp hv,fun i=>?_⟩;obtain ⟨he,ht,h⟩:=h i;obtain ⟨hx,hm,H⟩:=H i;refine ⟨(abs_add_le ..).trans (add_le_add he hx),(abs_add_le ..).trans (add_le_add ht hm),?_⟩; dsimp only; rw [add_sub_add_comm,add_mul];exact (abs_add_le ..).trans (add_le_add h H)
lemma neg (h:Weigh D d f g):Weigh D d (fun i=> -f i) (fun i=> -g i):=by obtain ⟨p,h,H⟩:=h;refine ⟨p,h,fun i=>?_⟩;simp only [show -f i - -g i= -(f i-g i) by ring,abs_neg];exact H i
lemma minus (h:Weigh D d f g)(he:Weigh D d f' g'):Weigh D d (fun i=>f i-f' i) (fun i=>g i-g' i):=by simpa only [sub_eq_add_neg] using h.sum he.neg
lemma mul (h:Weigh D d f g)(he: Weigh D d f' g'):Weigh D d (fun i=>f i*f' i) (fun i=>g i*g' i):=by
 obtain ⟨p,hp,h⟩:=h;obtain ⟨q,hq,H⟩:=he;refine ⟨fun i=>2*p i*q i,D.moreover _ _ (D.moreover _ _ (D.steady _ zero_le_two) hp) hq,fun i=>?_⟩
 obtain ⟨ha,hA,hT⟩:=h i;obtain ⟨hb,hB,hM⟩:=H i;have hp:=D.safe _ hp i;have hq:=D.safe _ hq i
 have ht:p i*q i ≤ 2*p i*q i:=by nlinarith [mul_nonneg hp hq]
 dsimp only;rw [abs_mul,abs_mul]; refine ⟨(mul_le_mul ha hb (abs_nonneg _) hp).trans ht,(mul_le_mul hA hB (abs_nonneg _) hp).trans ht,?_⟩
 rw [show f i*f' i-g i*g' i=(f i-g i)*f' i+g i*(f' i-g' i) by ring]
 apply (abs_add_le ..).trans
 rw [abs_mul,abs_mul];nlinarith only [mul_le_mul hT hb (abs_nonneg _) ((abs_nonneg _).trans hT),mul_le_mul hA hM (abs_nonneg _) hp]
lemma lump {I:Type}(s:Finset I)(f g:I→O→ℝ)(h:∀ i∈s,Weigh D d (f i) (g i))(hd:∀ x,0≤d x):Weigh D d (fun x=>∑ i∈s,f i x) (fun x=>∑ i∈s,g i x):=by
 induction s using Finset.induction_on with
 | empty=> simpa only [sum_empty] using flat D d 0 hd
 | insert a s ha hi=>simpa only [sum_insert ha] using sum (h a (mem_insert_self ..)) (hi (fun i hi=>h _ (mem_insert_of_mem hi)))
end Weigh
variable {D d}(hd:∀ i,0≤d i)
def Scale (D:Exchange O)(d:O→ℝ)(n:ℕ)(f g:O→Nacre.Essence):Prop:=∀ i ≤ n, Weigh D d (fun x=>coeff i (f x)) (fun x=>coeff i (g x))
namespace Scale
variable {f g f' g':O→Nacre.Essence}{n:ℕ}
 include hd
lemma particular (p:Nacre.Essence):Scale D d n (fun _=>p) (fun _=>p):=fun _ _=>Weigh.flat D d _ hd -- include hd
 omit hd
lemma lower (h:Scale D d n f g){a:ℕ}(hp:a≤n):Scale D d a f g:=fun i hi=>h i (hi.trans hp)
include hd
-- include earlier
lemma fusion (h:Scale D d n f g)(H:Scale D d n f' g'):Scale D d n (fun x=> f x*f' x) (fun x=>g x*g' x):=by
 intro i hi;simp_rw [coeff_mul];apply Weigh.lump (HasAntidiagonal.antidiagonal i) (fun y x=>coeff y.1 (f x)*coeff y.2 (f' x)) (fun y x=>coeff y.1 (g x)*coeff y.2 (g' x)) _ hd;intro x hx; obtain ht:=HasAntidiagonal.mem_antidiagonal.mp hx;apply Weigh.mul (h _ (by omega)) (H _ (by omega))
lemma power (h:Scale D d n f g)(p:ℕ):Scale D d n (fun x=>f x^p) (fun x=>g x^p):=by
 induction p with
 | zero=>simp only [pow_zero];apply particular hd
 | succ p hp=> simpa only [pow_succ] using hp.fusion hd h
end Scale
-- ratio lag. Need coefficients including Ω for every i < requested, for ratio⁻¹^-1. truncation comparison both numerator histories.
 include hd
lemma ratios {w w':O→ℕ→ℝ} (n:ℕ)(h:∀ i : ℕ,i ≤ n → 0 < i → Weigh D d (fun x=>w x i) fun x=>w' x i):Scale D d n (fun x=>Nacre.ratio (w x)) (fun x=>Nacre.ratio (w' x)):=by
 have Hs {f:ℕ→ℝ}{i:ℕ}(h:0 < i): coeff i (Nacre.ratio f)= (Nacre.boost f (Nacre.ratio f) i - Nacre.contour (Nacre.ratio f) i)/2:=by
    have H:=fixed f i;rw [birch (hasHead f) h,Nacre.boost] at H; rw [if_neg h.ne',zero_add] at H;unfold Nacre.boost;linarith
 induction n with
 | zero=>intro i hi; obtain rfl:i=0:=by omega
         simp_rw [hasHead];exact Weigh.flat D d 1 hd
 | succ n ih=>
   have he:=ih (fun i hi=> h _ (by omega));intro i hi;rcases lt_or_eq_of_le hi with hv|rfl; exact he i (by omega)
   simp_rw [Hs (by omega:0<n+1),div_eq_mul_inv]
   refine (Weigh.mul ?_ (Weigh.flat D d _ hd));refine Weigh.minus ?_ ?_
   · unfold Nacre.boost;apply Weigh.lump _ _ _ _ hd;intro i hi
     obtain ⟨hi,ht⟩:=mem_erase.mp hi;have hx:i ≤ n+1:=by simpa using ht
     -- function eta
     change Weigh D d (fun x=>coeff _ (factor (w x) _ i)) (fun x=>coeff _ (factor (w' x) _ i))
     simp_rw [Nacre.factor,coeff_X_pow_mul',if_pos hx,coeff_smul,smul_eq_mul];exact (h _ hx (by omega)).mul ((he.power hd i) _ (by omega))
   unfold Nacre.contour;apply Weigh.lump _ _ _ _ hd; intro i hi
   by_cases hx:i.1<n+1 ∧ i.2<n+1
   · -- goals with implicit K array; from
     simp only [if_pos hx];exact (he i.1 (by omega)).mul (he i.2 (by omega))
   simp only [if_neg hx];apply Weigh.flat D d _ hd

lemma reciprocals {X Y:O→Nacre.Essence}(hx:∀ i,constantCoeff (X i)=1)(hy:∀ i,constantCoeff (Y i)=1){n:ℕ}(h:Scale D d n X Y):Scale D d n (fun i=>(X i)⁻¹) (fun i=>(Y i)⁻¹):=by
 induction n with
 | zero=>intro i hi;obtain rfl:i=0:=by omega
         simp_rw [coeff_zero_eq_constantCoeff_apply,PowerSeries.constantCoeff_inv,hx,hy]; exact Weigh.flat D d _ hd
 | succ n ih=>
   have H:=ih (h.lower (Nat.le_succ n)); intro i hi;rcases lt_or_eq_of_le hi with Hn|rfl;exact H _ (by omega)
   let f (X:O→Essence) (i:ℕ×ℕ) (x:O):= if i.2<n+1 then coeff i.1 (X x)*coeff i.2 (X x)⁻¹ else 0
   have he i (hi:i∈HasAntidiagonal.antidiagonal (n+1)):Weigh D d (f X i) (f Y i):=by
      by_cases hx:i.2<n+1
      · simp only [f,if_pos hx];have hu:= HasAntidiagonal.mem_antidiagonal.mp hi;exact (h _ (by omega)).mul (H _ (by omega))
      simp only [f,if_neg hx];exact Weigh.flat D d _ hd
   simp_rw [coeff_inv (n+1),if_neg (Nat.succ_ne_zero n),hx,hy,inv_one,neg_one_mul]
   exact (Weigh.lump _ _ _ he hd).neg

lemma sizes {w w':O→ℕ→ℝ}(e i r:ℕ)(h:∀ n ≤ e-i,0<n→Weigh D d (fun x=>w x n) (fun x=>w' x n)):Weigh D d (fun x=>dues (w x) i r e) (fun x=>dues (w' x) i r e):=by
 unfold dues;by_cases ht:i ≤ e
 · simp only [if_pos ht];unfold Nacre.shift;let n:=e-i
   have hh:=ratios hd n h
   have hs(f:O→ℕ→ℝ)(x:O):constantCoeff (Nacre.ratio (f x))=1:=(coeff_zero_eq_constantCoeff_apply _).symm.trans (hasHead _)
   exact ((hh.power hd i).fusion hd ((reciprocals hd (hs _) (hs _) hh).power hd r)) n le_rfl
 simp only [if_neg ht];exact Weigh.flat D d _ hd
end YM.RG08.Ducat
