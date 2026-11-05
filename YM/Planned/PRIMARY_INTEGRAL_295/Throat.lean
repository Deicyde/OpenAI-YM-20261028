import YM.Planned.PRIMARY_INTEGRAL_295.Bazaars

/-! # Wrap-remnant cost on retained stencil, current directions

Estimate on discarded/coarse positions beyond common chart. Here the kernel
row queries an input on true c lattice. Lemma needs both derivatives have
polynomial moment costs *through all Cover* (provided by lamps), not just in
current local domain. Localization expense held at full w, M. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Throat
open Function Filter Set Metric Labels Lattice RG Wilson Source Source.Drops
open Place Streets Bazaars   Carrier Precision Exterior Bloch Laurent Next.Free
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {d k l n j : ℕ} {G : Gauge} {T : Finset Cover} {L : Side}
variable {A B C σ : ℝ}

section
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private def deposit (M:ℕ) (n:ℕ) (y:Cover) (σ C : ℝ) := C * (Real.exp (-(σ/2)*M) * liftCost n y * Real.exp (σ/2*size y) * widthCost (σ/2) n)


-- all integral shifts including y nonzero stencil cost.
lemma spared {f g : Window E} {w:Cover→ℝ} (hσ : 0<σ) (_hC:0≤C) (hW: Laurent.Width σ C w)
    (n M:ℕ) (hf: Carries f n A) (hg: Carries g n B) (h : ∀ x, size x ≤ M → f x=g x) (y:Cover) (i:Axis) :
    ‖stream w y (fun x=>f x i)-stream w y (fun x=> g x i)‖ ≤ (A+B)*deposit M n y σ C := by
  let a:= σ/2; have ha : 0<a := half_pos hσ
  let q:=Real.exp (-a*M)*liftCost n y*Real.exp (a*size y) * widthCost a n
  have Hx:=liftCost_ge n y; have ht := widthCost_ge ha n
  have hf' :=hf.1; have hg':= hg.1; have hp : 0 ≤ (A+B)*q := mul_nonneg (add_nonneg hf' hg') (by unfold q; positivity)
  have hs:=hW.2.1; have hP:=hW.2.2
  let P (x:Cover):=((A+B)*q)*(Real.exp (σ*size x)*‖w x‖)
  have hP' : SumBudget P (((A+B)*q)*C) := by
    refine ⟨fun i=>mul_nonneg hp (by positivity),hs.mul_left _,?_⟩; unfold P; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hP hp
  let V (x:Cover):= w x • f (y+x) i - w x • g (y+x) i
  have hN (x:Cover): ‖V x‖ ≤ P x := by
    by_cases hc:size (y+x) ≤ M
    · unfold V; rw [h _ hc,sub_self,norm_zero]; exact hP'.1 x
    have he : 1 ≤ Real.exp (-a*M)*Real.exp (a*size y)*Real.exp (a*size x) := by
      rw [← Real.exp_add,← Real.exp_add]; apply Real.one_le_exp
      have hh : (M:ℝ) ≤ size y + size x := by exact_mod_cast (show M≤ _ from (by omega : M ≤ size (y+x)).trans (size_add ..))
      nlinarith
    have hn : liftCost n x ≤ widthCost a n * Real.exp (a * size x) := widthBill _ ha _ (size x) (by positivity)
    have hv : ‖V x‖ ≤ (A+B)*liftCost n (y+x) * ‖w x‖ := by
      unfold V; apply (norm_sub_le ..).trans; rw [norm_smul,norm_smul,←mul_add,add_mul,mul_comm (A*liftCost n (y+x)+B*liftCost n (y+x))]
      exact mul_le_mul_of_nonneg_left ((add_le_add (hf.2 _ i) (hg.2 _ i))) (norm_nonneg (w x))
    apply hv.trans
    calc
     _ ≤ (A+B)*(liftCost n y*liftCost n x)*‖w x‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (liftCost_add n ..) (by positivity)) (norm_nonneg _)
     _ ≤ (A+B)*(liftCost n y*(widthCost a n*Real.exp (a*size x)))*‖w x‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hn (liftCost_pos ..)) (by positivity)) (norm_nonneg _)
     _ ≤ _ * (Real.exp (-a*M)*Real.exp (a*size y)*Real.exp (a*size x)) := le_mul_of_one_le_right (by positivity) he
     _ = P x := by
       unfold P q; rw [show σ*(size x)=a*size x+a*size x by unfold a; ring,Real.exp_add]; ring
  have hd := Work.F08.budget_minor hP' (fun i=> norm_nonneg (V i)) hN
  have he : stream w y (fun x=>f x i)-stream w y (fun x=>g x i) = ∑' x,V x := by
    exact ((stream_income hσ ⟨hW.1,hs,hP⟩ y n hf' (fun x=>hf.2 x i)).2.1.of_norm.tsum_sub
      (g:=fun x=> w x • g (y+x) i) (stream_income hσ hW y n hg' (fun x=>hg.2 x i)).2.1.of_norm).symm
  rw [he]; exact ((norm_tsum_le_tsum_norm hd.2.1).trans hd.2.2).trans_eq (by unfold q a deposit; ring)
end

def stomach (S:Finset Cover) (n:ℕ) (σ C:ℝ) :=
    let a:=σ/2
    ∑ p:Spot S, 4 * (C * liftCost n (first p).val * Real.exp (a* size (first p).val) * widthCost a n)
lemma stoop (S:Finset Cover) (n:ℕ) (hσ:0<σ) (hC:0≤C) : 0 ≤ stomach S n σ C := Finset.sum_nonneg (fun i _=>by
  have h:=widthCost_ge (half_pos hσ) n; have := liftCost_pos n (first i).val; positivity)

lemma tribes (T:Finset Cover) {f g : Window G.Color} (W : Lines L) (hσ:0<σ) (hC:0≤C) (hW : W.strip σ C)
    (n M:ℕ) (hf: Carries f n A) (hg:Carries g n B) (h : ∀ x, size x≤M → f x=g x) :
    ‖Units.inView T (applyLine W f)-Units.inView T (applyLine W g)‖ ≤ (A+B)*stomach T n σ C * Real.exp (-(σ/2)*M) := by
  classical
  have hp:=stoop T n hσ hC; have ha:=hf.1; have hb:=hg.1
  let u(y:Cover):= C*liftCost n y * Real.exp (σ/2*size y)*widthCost (σ/2) n
  have ht:=widthCost_ge (half_pos hσ) n
  have hu (y : Cover) := show 0≤u y by unfold u; have := liftCost_pos n y; positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i
  let x := (first i).val; let z:= cellar L x; let v:=beam i
  have hx : size z ≤ size x := Work.F08.carry_size (0:Site L) _
  have hu' : u z ≤ u x := by
    unfold u
    have hf := liftCost_pos n z
    have hr := liftCost_cellar L n x
    have hP := liftCost_pos n x
    gcongr
  let p := Real.exp (-(σ/2)*M)
  change ‖applyLine W f x v-applyLine W g x v‖ ≤ _; unfold applyLine; rw [← Finset.sum_sub_distrib]
  have he b:= spared hσ hC (hW (wrap L x,Exterior.coord v) (Exterior.coord b)) n M hf hg h z b
  apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun b _=> he b)).trans _)
  have hi : 4*u x≤stomach T n σ C:=Finset.single_le_sum (f:=fun i:Spot T=> 4*u (first i).val) (fun i _=> by have := hu (first i).val; positivity) (Finset.mem_univ i)
  calc
   _ = (A+B)*(4*u z)*p := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,Axis]; unfold p u deposit; push_cast; ring
   _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hu' (by norm_num : (0:ℝ)≤4)).trans hi) (by positivity)) (Real.exp_pos _).le
end YM.Planned.PrimaryIntegral295.Throat
