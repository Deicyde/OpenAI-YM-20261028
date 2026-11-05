import YM.FullVolume.Amp.Blank
/-! ℓ¹ germ Banach algebra Kapstone. Strict comparisons. We compose via equality of evaluations to see distribution. Whole closed real disk as coefficient space extracts Hol endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type*} [NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] [NormedAddCommGroup I][NormedSpace ℝ I][CompleteSpace I]
variable {s:ℝ}{n j:ℕ}
abbrev Beam (X:Type*) [NormedAddCommGroup X]: Type _:= lp (fun _ : ℕ=>X) 1
variable (x:Beam X)(v:sun)
lemma paid (x:Beam X): HasSum (fun n=> ‖x n‖) ‖x‖:=by simpa using lp.hasSum_norm (by norm_num) x
lemma togg (x:Beam X): SumBudget (fun n=> ‖x n‖) ‖x‖:= ⟨fun n=>norm_nonneg _,(paid x).summable,(paid x).tsum_eq.le⟩
namespace Beam
def arc (x:Beam X)(a:ℝ):=∑' n:ℕ,a^n • x n
lemma spar (ht: |s|≤1):HasSum (fun i:ℕ=>s^i • x i) (x.arc s) := (at_flight s ht (togg x)).2.1.of_norm.hasSum
lemma price : ‖x.arc v‖≤‖x‖:= let h:=at_flight v.val (abs_le.mpr v.2) (togg x); (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
variable (X) in
def read (v:sun): Beam X →L[ℝ] X:= by
   have ht:|v.val|≤1:= abs_le.mpr v.2
   let f:Beam X →ₗ[ℝ] X:={ toFun := fun x=> arc x v,
                            map_add' := fun x y=> by unfold arc; simp [lp.coeFn_add,smul_add, Summable.tsum_add (x.spar ht).summable (y.spar ht).summable],
                            map_smul' := fun a x=> by unfold arc; rw [show (fun i:ℕ=> (v.val)^i • (a • x) i)=fun i:ℕ=>a • v.val^i • x i from funext fun i=> smul_comm ..]; exact ((spar x ht).const_smul a).tsum_eq }
   exact f.mkContinuous 1 (fun x=>by rw [one_mul]; exact price x v)
lemma tippy : Tip (⇑x) x.arc:=by
   have ht:=signpost 1 (togg x) (B:=x.arc) (by filter_upwards [sprite 1] with t h; rw [one_mul] at *; exact spar x h)
   simpa only [one_pow,one_smul] using ht
lemma soul (y:Beam X)(he:∀ v:sun,arc x v=arc y v): x=y:= by
   have hf:Tip (⇑x) y.arc:=by intro n; apply (tippy x n).congr'; exact ((sprite 1).mono fun t ht=>congr_arg (fun z=> z-shell _ n t) (he ⟨t,abs_le.mp (show |t|≤1 by rwa [one_mul] at ht)⟩)); rfl
   exact lp.ext (sole hf y.tippy)
-- operations
def arm (a:X) : Beam X:= lp.single 1 0 a
def spark (a:X): Beam X:=lp.single 1 1 a
lemma armN (a:X): ‖arm a‖= ‖a‖:= lp.norm_single (by norm_num) ..
lemma armL (a:X): read X v (arm a)=a:= by
  change ∑' n:ℕ, v.val^n • lp.single (E:=fun _=>X) 1 0 a n=a; rw [tsum_eq_single 0 (fun i hi=> by simp [lp.single_apply,Pi.single_eq_of_ne hi])]; simp
lemma sparkN (a:X): ‖spark a‖= ‖a‖:=lp.norm_single (by norm_num) ..
lemma sparkL (a:X): read X v (spark a)= v.val • a:=by
  change ∑' n:ℕ, v.val^n • lp.single (E:=fun _=>X) 1 1 a n=_; rw [tsum_eq_single 1 (fun i hi=>by simp [lp.single_apply,Pi.single_eq_of_ne hi])]; simp
-- lift bilinear by SUM of singles at addresses preadd
section bilinear
variable (P:X→L[ℝ] Y →L[ℝ] I)(a:Beam X)(b:Beam Y)
def sparkW (p:ℕ × ℕ): Beam I := lp.single 1 (p.1+p.2) (P (a p.1) (b p.2))
lemma weightB : SumBudget (fun i=> ‖sparkW P a b i‖) (‖P‖*(‖a‖*‖b‖)):=by
   apply budget_mono (budget_scale (norm_nonneg P) (budget_prod (togg a) (togg b))) (fun i=>norm_nonneg _) (fun i=>?_)
   unfold sparkW; rw [lp.norm_single (by norm_num)]; exact ((P _).le_of_opNorm_le (P.le_opNorm _) _).trans_eq (mul_assoc ..)
def brave : Beam I:=∑' i, sparkW P a b i
lemma braveN : ‖brave P a b‖ ≤ ‖P‖*(‖a‖*‖b‖):= let h:=weightB P a b; (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
lemma harp : read I v (brave P a b)=P (read X v a) (read Y v b):=by
   have ht:=(weightB P a b).2.1.of_norm; have hp:|v.val| ≤1:=abs_le.mpr v.2; let Y j:= v.val^j • b j; let X' i:=v.val^i • a i
   have hs := (read I v).hasSum ht.hasSum
   have hZ(p:ℕ×ℕ) : read I v (sparkW P a b p)= P (X' p.1) (Y p.2):=by
     change ∑' n:ℕ, v.val^n • sparkW P a b p n=_; rw [tsum_eq_single (p.1+p.2)]; unfold sparkW X' Y; rw [lp.single_apply, Pi.single_eq_same,map_smul,map_smul,smul_apply,pow_add,smul_smul,mul_comm (v.val^p.snd)]
     intro j hj; unfold sparkW; rw [lp.single_apply, Pi.single_eq_of_ne hj, smul_zero]
   change _=_; simp_rw [hZ] at hs
   let B:=b.arc v; change read I v (brave P a b)=P (a.arc v) B
   rw [← show _= read I v (brave P a b) from hs.tsum_eq, hs.summable.tsum_prod]; have he i:(∑' j,P (X' i) (Y j))= P (X' i) B := ((P _).hasSum (b.spar hp)).tsum_eq
   simp_rw [he]; exact ((ContinuousLinearMap.flip P B).hasSum (a.spar hp)).tsum_eq
end bilinear
-- pair concatenation to lp ℓ¹ sum
variable (a:Beam X)(b:Beam Y)
def lay : Beam (X × Y):= by
  let f i:=(a i,b i); refine ⟨f,memℓp_gen ?_⟩
  simp only [ENNReal.toReal_one,Real.rpow_one]
  apply (budget_mono (budget_plus (togg a) (togg b)) (fun i=> norm_nonneg (f i)) ?_).2.1
  exact fun i=> max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
lemma layN: ‖lay a b‖≤ ‖a‖+‖b‖:= by
   have hh:= budget_mono (budget_plus (togg a) (togg b)) (g:=fun i=> ‖lay a b i‖) (fun i=>norm_nonneg _) (fun i=> max_le (le_add_of_nonneg_right (norm_nonneg (b i))) (le_add_of_nonneg_left (norm_nonneg (a i))))
   exact (paid (lay a b)|>.tsum_eq.symm).trans_le hh.2.2
lemma layL : read (X×Y) v (lay a b)=(read X v a,read Y v b):=by
   have hp:|v.val| ≤1:=abs_le.mpr v.2; exact ((a.spar hp).prodMk (b.spar hp)).tsum_eq -- pairing
lemma layD (a':Beam X)(b':Beam Y): ‖lay a b-lay a' b'‖≤‖a-a'‖+‖b-b'‖:=by rw [show lay a b-lay a' b'=lay (a-a') (b-b') from (by ext <;>rfl)]; exact layN ..
end Beam
end YM.FullVolume.Amp
