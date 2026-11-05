import YM.FullVolume.Spiral.Chrome
/- elementary continuation estimate proof via finite Lagrange tables; horizontal norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset Set RG Push.AbsoluteSums Ray Asymptotics
open PhysicalNext.Repeat.Muse
open scoped Topology BigOperators Classical ContDiff
variable {n m:ℕ}{r:ℝ}
section sep
variable {Y : Type*}[NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
-- compression. No norm quotient
variable (v:sun) (X:Beam Y)
def fit :Beam Y:= by
    refine ⟨fun i=>v.val^i • X i, memℓp_gen (by simp only [ENNReal.toReal_one, Real.rpow_one]; exact (at_flight v.val (abs_le.mpr v.2) (togg X)).2.1)⟩
lemma fitN : ‖fit v X‖≤‖X‖:= (paid (fit v X)).tsum_eq.symm.trans_le (at_flight v.val (abs_le.mpr v.2) (togg X)).2.2
lemma fitL (s:sun): read Y s (fit v X)=read Y (slash v.val v.property s) X:=by change ∑' i:ℕ,s.val^i • (v.val^i • X i)=∑' i:ℕ,(s.val*v.val)^i • X i; simp_rw [mul_pow,smul_smul]
lemma fitD (Z:Beam Y): fit v (X-Z)=fit v X-fit v Z:=by apply lp.ext; funext k; exact smul_sub ..
lemma lawn (k:ℕ): ‖fit v X k‖=|v.val|^k*‖X k‖:=by change ‖v.val^k • X k‖= _; rw [norm_smul,Real.norm_eq_abs,abs_pow]
def stem (n:ℕ):Beam Y:= by
   let f (k:ℕ):= if k≤ n then X k else 0
   refine ⟨f,memℓp_gen ?_⟩; simp only [ENNReal.toReal_one,Real.rpow_one]; apply Summable.of_nonneg_of_le (fun i=> norm_nonneg _) _ (paid X).summable; intro i; unfold f; split; rfl; simp only [norm_zero,norm_nonneg]
lemma stemK (n k:ℕ): stem X n k= if k≤ n then X k else 0 :=rfl
lemma stemSize (n:ℕ): ‖fit v X - stem (fit v X) n‖ ≤ |v.val|^(n+1)*‖X‖:=by
    let P:= fit v X; let Q:=P-stem P n
    have ht(k:ℕ): ‖Q k‖≤ |v.val|^(n+1)*‖X k‖:=by
       change ‖P k-stem P n k‖≤ _; rw [stemK]; split_ifs with h
       · rw [sub_self,norm_zero]; positivity
       rw [sub_zero,lawn]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) (abs_le.mpr v.2) (by omega)) (norm_nonneg _)
    exact ((paid Q).tsum_eq.symm).trans_le ((budget_mono (budget_scale (pow_nonneg (abs_nonneg _) _) (togg X)) (fun _=>norm_nonneg _) ht).2.2)
abbrev Crop (X:Beam Y)(n:ℕ): Prop:= ∀ k:ℕ,n<k→ X k=0
namespace Crop
lemma still (h:Crop X n) (s:sun):read Y s X=∑ k∈Finset.range (n+1),s.val^k • X k:= tsum_eq_sum (fun k hk=>by rw [h k (by simp at hk; omega),smul_zero])
lemma shoots (x:Y): Crop (arm x) n:=fun k hk=> by simp [arm,lp.single_apply,show k≠0 by omega]
lemma cropped(n): Crop (stem X n) n:=fun k hk=> by rw [stemK,if_neg (by omega)]
lemma play (h:Crop X n)(Y':Beam Y)(hp:Crop Y' n):Crop (X-Y') n:= fun i hi=> sub_eq_zero.mpr (by rw [h _ hi,hp _ hi])
lemma timesP (h:Crop X n)(x:ℝ): Crop (x • X) n:= fun i hi=>by change x • X i=0; rw [h _ hi,smul_zero]
lemma higher (h:Crop X n): Crop X (n+1):=fun i hi=> h _ (by omega)
end Crop
private def springF (i:ℕ): Y:= Nat.casesOn i 0 (fun i=> X i)
def sprang : Beam Y:= ⟨fun i=>springF X i,memℓp_gen (by simp only [ENNReal.toReal_one,Real.rpow_one]; exact (summable_nat_add_iff 1).1 (paid X).summable)⟩
lemma sprangN: ‖sprang X‖=‖X‖:=by rw [← (paid _).tsum_eq,← Summable.sum_add_tsum_nat_add 1 (paid _).summable]; rw [Finset.sum_range_one, show sprang X 0=0 from rfl,norm_zero,zero_add]; exact (paid X).tsum_eq
lemma sprangL(s:sun): read Y s (sprang X)=s.val • read Y s X:=by
    change ∑' i:ℕ,s.val^i • sprang X i= s.val • read Y s X; rw [← Summable.sum_add_tsum_nat_add 1 ((sprang X).spar (abs_le.mpr s.2)).summable]
    have h(i:ℕ): sprang X (i+1)=X i:=rfl
    rw [Finset.sum_range_one,show sprang X 0=0 from rfl,smul_zero,zero_add]
    simp_rw [h,pow_succ',mul_smul]; exact ((spar X (abs_le.mpr s.2)).const_smul s.val).tsum_eq
lemma Crop.inc (h:Crop X n): Crop (sprang X) (n+1):=by
    intro k hk; cases k with
    | zero=> omega
    | succ k=> exact h k (by omega)
abbrev arms:= v.val • X-sprang X
lemma armsL (s:sun) : read Y s (arms v X)=(v.val-s.val) • read Y s X:=by unfold arms; rw [map_sub,map_smul,sprangL,sub_smul]
lemma armsN : ‖arms v X‖≤ 2*‖X‖:=by unfold arms; refine (norm_sub_le ..).trans ?_; rw [norm_smul,sprangN]; nlinarith only [show ‖v.val‖≤1 from abs_le.mpr v.2, norm_nonneg X]
lemma Crop.marsh (h:Crop X n): Crop (arms v X) (n+1):=Crop.play _ (Crop.timesP _ (Crop.higher _ h) v.val) _ (Crop.inc _ h)
end sep
end YM.FullVolume.Amp.Beam
#print axioms YM.FullVolume.Amp.Beam.armsL
