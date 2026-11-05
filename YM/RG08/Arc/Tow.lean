import YM.RG08.Arc.Mimic
/-! # Analytic germs and pulses. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter Metric MeasureTheory YM.PertExtension.Series YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial
open Finset Function Analysis
open scoped BigOperators Topology Real ContDiff Classical
variable {f g p q r : ℝ→ℝ} {n k m : ℕ} {ι : Type*} {x y z : ℕ→ℝ}
lemma aspireNeg (h : Aspiration f x) : Aspiration (-f) (-x) := by
  intro n; have hx : (peval (-x) n)= -(peval x n) := by funext t; simp [peval, Zone.eval,Finset.sum_neg_distrib];
  rw [hx,show -f - -(peval x n)= -(f-peval x n) by abel]; exact bill_neg (h n)
lemma aspireLess (h : Aspiration f x) (he : Aspiration g y) : Aspiration (f-g) (x-y) := by simpa only [sub_eq_add_neg] using! h.add (aspireNeg he)
lemma aspireCoin (h : Aspiration f x) (c : ℝ) : Aspiration (c • f) (c • x) := by
  intro n; have he : peval (c • x) n=c • peval x n := by funext t; unfold peval Zone.eval; rw [Pi.smul_apply,Finset.smul_sum]; apply sum_congr rfl; intro i _; exact smul_comm (t^i) c (x i)
  rw [he]; exact Fit.scale (h n) _
lemma aspiredV (H : Fit (n+1) f g) (h : Aspiration f x) (p : Aspiration g y) (hx : k≤n) : x k=y k := sub_eq_zero.mp ((aspireLess h p).vanish H (by omega))
lemma aspiredH (H : Fit (n+1) f (peval y n)) (h : Aspiration f x) (hx : k≤n) : x k=y k :=
  (aspiredV H h (Aspiration.polynomial y n) hx).trans (if_pos hx)

def ink (f : ℝ→ℝ) (i : ℕ) := jet f i (1:ℝ)
lemma ink_aspire (h : ContDiffAt ℝ ∞ f 0) : Aspiration f (ink f) := by simpa only [smul_eq_mul, mul_one, ink] using! directions h (1:ℝ)
lemma ink_add (h : ContDiffAt ℝ ∞ f 0) (p : ContDiffAt ℝ ∞ g 0) : ink (f+g)=ink f+ink g :=
  (ink_aspire (h.add p)).unique ((ink_aspire h).add (ink_aspire p))
lemma ink_less (h : ContDiffAt ℝ ∞ f 0) (p : ContDiffAt ℝ ∞ g 0) : ink (f-g)=ink f-ink g :=
  (ink_aspire (h.sub p)).unique (aspireLess (ink_aspire h) (ink_aspire p))
lemma ink_c (c : ℝ) (h : ContDiffAt ℝ ∞ f 0) : ink (c • f)= c • ink f :=
  (ink_aspire (h.const_smul c)).unique (aspireCoin (ink_aspire h) c)
@[simp] lemma ink_z : ink (0:ℝ→ℝ)=0 := funext fun i=> by
  apply (aspiredH (n:=i) (y:=0) ?_ (ink_aspire contDiffAt_const) le_rfl)
  rw [show peval (0:ℕ→ℝ) i=0 from funext fun t=> by simp [peval,Zone.eval]]; exact Fit.same ..
lemma ink_0 (f : ℝ→ℝ) : ink f 0=f 0 := jet_zero ..
lemma pulse_c (h : ContDiffAt ℝ ∞ f 0) (u : ℝ) : ink (fun t=> f (t*u)) k= u^k * ink f k := by
  rw [show ink (fun t=>f (t*u)) k= jet f k u from congr_fun ((ink_aspire (f:=fun t=>f (t*u)) ?_).unique (directions h u)) k,ink, ← jet_smul]; simp only [smul_eq_mul,mul_one] -- fix syntax
  exact ((zero_mul u).symm ▸ h).comp (f:=fun t=> t*u) (0:ℝ) (contDiffAt_id.mul contDiffAt_const)
lemma pulse_bound (h : ∀ i∈range (k+1), ink f i = ink g i) (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) : Fit (k+1) f g := by
  have he : peval (ink f) k=peval (ink g) k := funext (fun t=> sum_congr rfl (fun i hi=>by change _ • ink f i=_ • ink g i; rw [h i hi]))
  exact Fit.join (he ▸ (ink_aspire hf k)) ((Fit.turn (ink_aspire hg k))) -- defeq
lemma ink_product (h : ContDiffAt ℝ ∞ f 0) (he : ContDiffAt ℝ ∞ g 0) : ink (f*g)=conv (ink f) (ink g) :=
  (ink_aspire (h.mul he)).unique ((ink_aspire h).prod (ink_aspire he))
@[simp] lemma ink_single (c : ℝ) : ink (fun t:ℝ=>t^n*c) k= if k=n then c else 0 :=
  congr_fun ((ink_aspire (f:=fun t:ℝ=>t^n*c) ((contDiffAt_id.pow n).mul contDiffAt_const)).unique (Aspiration.single c n)) _
lemma ink_t_pow (f : ℝ→ℝ) (h : ContDiffAt ℝ ∞ f 0) (i k : ℕ) :
    ink (fun t:ℝ=> t^i * f t) k= if i≤k then ink f (k-i) else 0 := by
  let g:= fun t : ℝ=>t^i * 1
  have hp : ContDiffAt ℝ ∞ g 0 := (contDiffAt_id.pow i).mul contDiffAt_const
  rw [show (fun t:ℝ=>t^i*f t)=g*f from funext fun t=> by simp [g],ink_product hp h]; unfold conv term
  simp_rw [PowerSeries.coeff_mul,PowerSeries.coeff_mk, show ∀ j, ink g j= if j=i then 1 else 0 from fun _=>ink_single 1]; split; next h=>
    rw [sum_eq_single_of_mem (i,k-i) (Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le h))]; simp
    intro a ha hh; have hd : a.1≠i := fun H=> hh (Prod.ext H (by have ht:=mem_antidiagonal.mp ha; dsimp; omega)); simp [hd]
  next H=> apply sum_eq_zero; intro j hj; have hV:j.1≠i:=by have hx:=mem_antidiagonal.mp hj; omega
           simp [hV]
lemma smooth_sum {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] (s : Finset ι) {F : ι→ E→E'} {n : WithTop ℕ∞} {z : E} (h : ∀ i∈s,ContDiffAt ℝ n (F i) z) : ContDiffAt ℝ n (∑ i∈s,F i) z := by
  rw [show (∑ i∈s,F i)=(fun t=>∑ i∈s,F i t) from funext fun t=> Finset.sum_apply t ..]; exact ContDiffAt.sum h
lemma ink_sums (s : Finset ι) {F : ι→ ℝ→ℝ} (h : ∀ i∈s,ContDiffAt ℝ ∞ (F i) 0) : ink (∑ i∈s,F i)=∑ i∈s,ink (F i) :=
  (ink_aspire (smooth_sum _ h)).unique (Aspiration.sum s F _ (fun i hi=> ink_aspire (h i hi)))
lemma ink_list (s : Finset ι) (F : ι→ ℝ→ℝ) (h : ∀ i∈s,ContDiffAt ℝ ∞ (F i) 0) (j : ℕ) : ink (fun t : ℝ=>∑ i∈s,F i t) j=∑ i∈s, ink (F i) j := by
  rw [show (fun t : ℝ=>∑ i∈s,F i t)=(∑ i∈s,F i) from Eq.symm (funext fun t=>Finset.sum_apply t ..),ink_sums s h]; exact Finset.sum_apply _ _ _

section jet
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma jet_coefficient (f : E→ℝ) (j) : jet f j= Tensor.diagonal (Tensor.coeff f j 0) := rfl
lemma jet_path (f : E→ℝ) (v : ℝ→E) (h : Bill 0 v) (hp : ContDiffAt ℝ ∞ f 0) (n : ℕ) : Fit (n+1) (fun t=>f (t•v t)) (fun t=>∑ j∈ range (n+1), t^j • jet f j (v t)) := by
  obtain ⟨C,hC,he⟩:=h; obtain ⟨δ,B,hδ,hB,H⟩:=deposition _ n hp
  refine ⟨B*C^(n+1),by positivity,?_⟩; filter_upwards [he,eventually_small (show 0<δ/(C+1) by positivity)] with t he ht
  have hv : ‖v t‖ ≤ C:= by simpa using he
  apply (H (v t) t ht.1 _).trans
  · have H : 0≤t:=ht.1.le; gcongr
  exact (mul_le_mul_of_nonneg_left hv ht.1.le).trans ((by have h:=(lt_div_iff₀ (show 0<C+1 by positivity)).mp ht.2; linarith [ht.1]: t*C≤δ))
lemma pulse_ray (F : E→ℝ) (k : ℕ)(h : ContDiffAt ℝ ∞ F 0)(v : E) :
    ink (fun t:ℝ=> F (t • v)) k= jet F k v := by
  have hp : ContDiffAt ℝ ∞ (fun t:ℝ=> F (t • v)) 0 := ((zero_smul ℝ v).symm ▸ h).comp (f:=fun t : ℝ=> t•v) 0 (contDiffAt_id.smul contDiffAt_const)
  exact congr_fun ((ink_aspire hp).unique (directions h v)) _
end jet
lemma peval_stop (k : ℕ) (u : ℕ→ℝ) : ContDiff ℝ ω (peval u k) := ContDiff.sum (s:=range (k+1)) (f:=fun i t=> t^i • u i) (fun i _=> (contDiff_id.pow i).mul contDiff_const)
end YM.RG08.Reflect
