import YM.RG08.Plot.Profit
/-!
# All subsets of birth fees. Geometric tails true powers and both cutoffs
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings High
open scoped BigOperators Topology Real ContDiff Classical
variable {I J:Type} {u:I→Windows}{n k i M N r l:ℕ}{X:Chain}{G:Gauge}{θ v C: ℝ}{b:J→Dial u}{y φ:J→ℝ}
section tolls
lemma gain_comp (t:ℕ) (S:Schedule) (i j:ℕ)(Z:ℝ): (gain S Z i j)^t=gain S (t*Z) i j:=by rw [gain,←Real.exp_nat_mul,gain]; ring_nf
lemma gain_pair (S:Schedule)(u v:ℝ)(i j:ℕ): gain S (u+v) i j=gain S u i j*gain S v i j:= by unfold gain; rw [← Real.exp_add]; ring_nf
lemma gamma_s (S:Schedule) k: gain S (1/8) k (k+1) ≤ gammaR := Real.exp_monotone (by rw [neg_div]; exact mul_le_mul_of_nonpos_left (downGill k S) (by norm_num))
private def stockQ : ℝ:= (1-gammaR)⁻¹
private lemma stock_ne : 0≤ stockQ:= inv_nonneg.mpr (sub_nonneg.mpr gamma_range.2.le)
lemma gain_cover (S:Schedule) (h:k≤ M): (∑ i∈Ico k M, gain S (1/8) k i) ≤ stockQ:= by
   induction h using Nat.decreasingInduction with
   | self=> rw [Ico_self,sum_empty]; exact stock_ne
   | of_succ k hk ih=>
     rw [← Finset.insert_Ico_succ_left_eq_Ico hk, sum_insert (by simp), gain_zero]
     rw [show Order.succ k=k+1 from rfl,show (∑ i∈Ico (k+1) M, gain S (1/8) k i)=gain S (1/8) k (k+1)*∑ i∈Ico (k+1) M,gain S (1/8) (k+1) i from (sum_congr rfl (fun i _=> gain_trans S (1/8) k (k+1) i)).trans (Finset.mul_sum ..).symm]

     calc
       _ ≤ 1+gammaR*stockQ:= add_le_add (le_refl _) (mul_le_mul (gamma_s S k) ih (sum_nonneg (fun _ _=>(gain_pos ..).le)) gamma_range.1.le)
       _ = _:= by have h:=gamma_range.2; unfold stockQ; field_simp [sub_ne_zero.mpr h.ne']; ring
lemma car_ride (θ ζ:ℝ)(h:0 ≤ θ)(hh:θ ≤ 1/2)(j:ℕ)(C:ℝ)(hp:0≤C) (l : ℕ)(hv:1 ≤ l): ∃ D:ℝ,0≤D ∧
   ∀ (S:Schedule){Z:ℝ}(K i N M:ℕ), 0 ≤ Z → K ≤ i → i≤ M →
   (∑ b∈ Ico i M, C*age S Z K b^j*gain S 1 K b^l*gain S θ b N) ≤ D*age S Z K i ^ j*gain S 1 K i ^l*gain S θ i N := by
   obtain ⟨D,hD,H⟩:= gain_poly (l-θ) (1/8:ℝ) (by have he: (1:ℝ) ≤ l:= (by exact_mod_cast hv); linarith) j
   refine ⟨C*D*stockQ,mul_nonneg (mul_nonneg hp hD) stock_ne,fun S Z K i N M hZ hK hI=>?_⟩
   let A:= C*D*age S Z K i ^ j*gain S 1 K i ^ l*gain S θ i N; have hA:0≤A:= mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp hD) (pow_nonneg (zero_le_one.trans (age_one hZ K i)) j)) (pow_nonneg (gain_pos ..).le _)) (gain_pos ..).le
   calc
    _ ≤ A* ∑ z∈ Ico i M, gain S (1/8) i z := by
      rw [Finset.mul_sum]; refine sum_le_sum ?_; intro v hv
      have hG:= H S Z K i v hZ (mem_Ico.mp hv).1; let T:= gain S 1 K i
      have hx:T= gain S 1 K i:=rfl
      have hw: gain S 1 K v^l = T^l*gain S θ i v*gain S ((l:ℝ)-θ) i v := by
         rw [mul_assoc, ← gain_pair, gain_trans S 1 K i v,mul_pow,gain_comp,gain_comp]; rw [mul_one, add_sub_cancel]
      rw [hw]; calc
        _ = (C*T^l*gain S θ i N)*(age S Z K v ^ j*gain S (l-θ) i v) := by rw [gain_trans S θ i v N]; ring
        _ ≤ _ := by
          apply (mul_le_mul_of_nonneg_left hG (mul_nonneg (mul_nonneg hp (pow_nonneg (gain_pos ..).le _)) (gain_pos ..).le)).trans_eq; unfold A; ring
    _ ≤ A*stockQ := mul_le_mul_of_nonneg_left (gain_cover S hI) hA -- Chain mismatch S
    _ = _:= by unfold A; ring
end tolls
section calls
variable {F:High b 0→ℕ→Shale (Loc G 1) r}
lemma lineG (h:0≤θ)(hx: θ ≤1/2)(hp:1 ≤ l)(hv:0≤ y)(hF: Card k (fun i:Heatline b=> glass X i.warm) (fun i=> y i.warm.z * material X i.warm ^ l*gain X.S θ i.warm.i i.warm.appr.N) (fun t=> F t.main t.j) (fun i=>material X i.main))(u0:High b 0→ Finset ℕ)(hu:∀ i,u0 i⊆ Ico i.i (b i.z).N) : Card k (glass X) (fun i:High b 0=> y i.z * material X i ^l*gain X.S θ i.i (b i.z).N) (fun i=> ∑ j∈u0 i,F i j) (material X):= by
   obtain ⟨A,⟨B,n,hB,H⟩,HP⟩:=hF.money; obtain ⟨C,hC,hG⟩:= car_ride θ 0 h hx n B hB l hp
   refine ⟨(fun i=>C*i.glass X ^ n), (Weighed.constant (High.glass X) hC).times (Weighed.power _ (glint X b 0) n), fun i=> ?_⟩
   let y' := y i.z; let Z:= (b i.z).W; let a t:= age X.S Z i.K t; let T j:= B*(a j)^n*gain X.S 1 i.K j^l*gain X.S θ j (b i.z).N
   apply Ink.raise (Ink.additions (f:=fun j=> F i j) (g:=fun j=>y'* T j) (s:=u0 i) ?_ (zero_le_one.trans (tailp (spanP_pos X i.K i.i|>.le)))) ?_
   · intro j hj; let v:Heatline b:=⟨i,j,mem_Ico.mp (hu i hj)|>.1,mem_Ico.mp (hu i hj)|>.2⟩
     have hh:A v≤B*a j^n:=(H v).2; have ht:glass X v.warm=a j:= rfl
     apply Ink.raise (HP v)
     have hx(y:Heatline b):0≤ (material X y.warm)^l:= pow_nonneg (spanP_pos ..|>.le) _
     apply (mul_le_mul_of_nonneg_right hh (mul_nonneg (mul_nonneg (hv _) (hx _)) (gain_pos ..).le)).trans_eq
     rw [matL]; change _*(y'*gain X.S 1 i.K j ^l *gain X.S θ j (b i.z).N)= y'*T j; unfold T; ring
   rw [← Finset.mul_sum,matL]; let v := Ico i.i (b i.z).N
   have ht : ∀ j,0≤ T j := fun j=> mul_nonneg (mul_nonneg (mul_nonneg hB (pow_nonneg (zero_le_one.trans (age_one (u (b i.z).a).pos ..)) _)) (pow_nonneg (gain_pos ..).le _)) (gain_pos ..).le
   apply (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (t:=v) (f:=T) (hu i) (fun j _ _=>ht j)).trans (hG X.S (Z:=Z) i.K i.i (b i.z).N (b i.z).N (u _|>.pos) i.heap i.scope)) (hv i.z)).trans_eq
   change y'*(C*a i.i^n*gain X.S 1 i.K i.i^l*gain X.S θ i.i (b i.z).N)=(C*a i.i^n)*(y'*_*_); ring
end calls
end YM.RG08.Plot
