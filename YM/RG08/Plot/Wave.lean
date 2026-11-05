import YM.RG08.Plot.Sterling
/-!
# Aggregate whole product through arbitrary fine mesh window

`♮` denotes norm in test profiles and source seeds before root-sums. Births
still leave such factor even after suppressing unchanged channels.
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
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{z a:M→ℕ}{p:List M} {U V: J→ M→ ℕ→ BoardU D R G}{s q :M→ J→ℝ}{C B:J→ℝ}{φ:M→J→Profile D}{x:J→ E4}
section powers
local notation "♭" => glass X
local notation "♮" => material X
local notation "⚡" => defect X
variable {N M: High b 0→ℕ→Shale (Loc G 1) r}{w:J→ℝ}
lemma buds_(hp:1 ≤ l) (h:Card k (fun i:Heatline b=> ♭ i.warm) (fun i=> w i.warm.z*(♮ i.warm)^l) (fun i=>N i.main i.j) (fun i=>♮ i.main))(hz:0≤w): Card k ♭ (fun i=> w i.z*(♮ i)^l) (fun i=>∑ j∈Ico i.i (b i.z).N,N i j) ♮:= by
   have hx:= lineG (k:=k) (θ:=0) le_rfl (by norm_num) hp hz (X:=X) (F:=N) ?_ (fun i=> Ico i.i (b i.z).N) (fun _=>le_rfl) -- simplification
   · simpa only [gain,neg_zero,zero_mul,Real.exp_zero,mul_one] using! hx
   simpa only [gain,neg_zero,zero_mul,Real.exp_zero,mul_one] using! h
lemma stemsG (hp:1≤ l)(h: Drum k (fun i:Heatline b=> glass X i.warm) (fun i=>⚡ i.warm) (fun i=>w i.warm.z*material X i.warm^l) (fun i=>N i.main i.j) (fun i=>M i.main i.j) (fun i=>material X i.main))(hv:0≤w): Drum k ♭ ⚡ (fun i=>w i.z*(♮ i)^l) (fun i=>∑ j∈Ico i.i (b i.z).N,N i j) (fun i=>∑ j∈ Ico i.i (b i.z).N,M i j) ♮:= by
   refine ⟨buds_ hp h.first hv,buds_ hp h.second hv,?_⟩
   let S i:= (Ico (High.i (b:=b) (n:=0) i) (b i.z).N); rw [show _-_= (fun i:High b 0=>∑ j∈ S i,(N-M) i j) from funext fun i=>by simp only [Pi.sub_apply,Finset.sum_sub_distrib]; rfl] -- may fail
   convert lineG (θ:=1/4) (by norm_num) (by norm_num) hp hv (X:=X) (F:=N-M) ?_ S (fun _=>le_rfl) using 1
   · funext i; exact mul_comm ..
   convert h.funds using 1; funext i; exact mul_comm ..
   rfl
-- gain for the N' window contribution without independent $∆$ beyond N
lemma fore (he:1 ≤ l)(F: High b 0→ ℕ→ Shale (Loc G 1) r)(T:Heatline (rightT b)→ Shale (Loc G 1) r)(hp:Card k (fun i:Heatline (rightT b)=> ♭ i.warm) (fun i=> w i.warm.z*(♮ i.warm)^l) T (fun i=>material X i.main))
   (hk:∀ (i:High b 0) j (ht:j∈ Ico (b i.z).N (b i.z).M)(hm:Heatline (rightT b)), hm.main.z=i.z→ hm.main.i=i.i→ hm.j=j→F i j=T hm) (hx:0 ≤ w): Card k ♭ (fun i=> ⚡ i *(w i.z*(♮ i)^l)) (fun i=> ∑ j∈ Ico (b i.z).N (b i.z).M,F i j) ♮:= by
   obtain ⟨A,⟨B,p,hB,H⟩,Hq⟩:=hp.money
   obtain ⟨C,hC,hP⟩:= car_ride (1/4) 0 (by norm_num) (by norm_num) p B hB l he
   refine ⟨_, (Weighed.constant (High.glass X) hC).times (Weighed.power _ (glint X b 0) p),fun i=>?_⟩
   let m:= b i.z; let N:= m.N
   let Z:=m.W; let S (j:ℕ):= B*age X.S Z i.K j ^p * gain X.S 1 i.K j ^l*gain X.S (1/4) j N; let p':= (w i.z); let A':=(Ico N m.M)
   have hS(j):0≤S j:= mul_nonneg (mul_nonneg (mul_nonneg hB (pow_nonneg (zero_le_one.trans (age_one (u m.a|>.pos) ..)) _)) (pow_nonneg (gain_pos ..).le _)) (gain_pos ..).le
   have hp j (hj:j∈A') : cis k (♮ i) (F i j) (p'*S j):= by
      let o:High (rightT b) 0:=⟨i.z,i.i,i.heap,i.scope.trans (b i.z).ripe⟩; let V:Heatline (rightT b):= ⟨o,j,i.scope.trans (mem_Ico.mp hj|>.1),(mem_Ico.mp hj).2⟩
      rw [hk i j hj V rfl rfl rfl]; apply Ink.raise (Hq V)
      have he:1≤gain X.S (1/4) j N:= Real.one_le_exp_iff.mpr (mul_nonneg_of_nonpos_of_nonpos (by norm_num) (sub_nonpos.mpr (age_scale_mono _ ((mem_Ico.mp hj).1))))
      rw [matL]; change A V * (p'*gain X.S 1 i.K j ^l) ≤ _; apply le_trans (mul_le_mul_of_nonneg_right ((H V).2) (mul_nonneg (hx _) (pow_nonneg (gain_pos ..).le _)))
      unfold S; change B*age X.S Z i.K j ^p*(p'*_) ≤ _
      let oW := B*age X.S Z i.K j ^p; change oW*(p'* _) ≤ _
      calc
         _ = p'*(oW*gain X.S 1 i.K j ^l):=by ring
         _ ≤ _:= by -- unify
           refine (le_mul_of_one_le_right (mul_nonneg (hx i.z) (mul_nonneg (mul_nonneg hB (pow_nonneg (zero_le_one.trans (age_one (u m.a|>.pos) ..)) _)) (pow_nonneg (gain_pos ..).le _))) he).trans_eq ?_; exact mul_assoc ..
   apply Ink.raise (Ink.additions hp (zero_le_one.trans (tailp (spanP_pos ..|>.le))))
   rw [← Finset.mul_sum]; refine (mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (s:=A') (t:=Ico i.i m.M) (fun j hj=>?_ ) (fun j _ _=>hS j)).trans (hP X.S (Z:=Z) i.K i.i N m.M (u m.a|>.pos) i.heap (i.scope.trans (b i.z).ripe))) (hx i.z)).trans_eq ?_
   · exact mem_Ico.mpr ⟨le_trans i.scope ((mem_Ico.mp hj).1), (mem_Ico.mp hj).2⟩
   rw [matL]; change p'*(C*(age X.S Z i.K i.i)^p*gain X.S 1 m.K i.i^l*gain X.S (1/4) i.i N)= (C*age X.S Z i.K i.i^p)*(gain X.S (1/4) i.i N * (p'*_)); ring
end powers
end YM.RG08.Plot
