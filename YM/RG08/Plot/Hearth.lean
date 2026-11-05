import YM.RG08.Plot.Sands
/-!
# Exact product discrepancy estimates with unconditional moment contracts
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff
variable {I J M: Type}{v δ q y C B:I→ℝ}{u:List J} {a ℓ:I→ℕ}{x:I→E4}{r n k E D τ i j b:ℕ}{s t':J→I→ℝ}{h z:J→ℕ}{G:Gauge}{R:ℝ}{φ:J→I→Profile D}{X:Chain}
section rake
lemma accrued_y (hp:Audience y)(hz:∀ j∈u, Weighed y (s j)): Weighed y (accrues s u):= by
   induction u with
   | nil=> exact Weighed.one
   | cons i p ih=> exact (hz i (by simp)).times (ih fun i hi=> hz i (List.mem_cons_of_mem _ hi))
lemma accrued_m {s t:J→I→ℝ}: accrues (s*t) u= accrues s u * accrues t u:= by
   induction u with
   | nil=> change (1:I→ℝ)=1*1; simp
   | cons i p ih=> change s i*t i*accrues (s*t) p=(s i*accrues s p)*(t i*accrues t p); rw [ih,mul_mul_mul_comm]
lemma accrued_wP (v:I→ℝ) (A:J→ℕ)(u): accrues (fun i=> v^A i) u=v^(loadᵣ A u):= by
   induction u with | nil=> simp [accrues,loadᵣ] | cons i p ih=> change v^A i*accrues _ p=v^(A i+_); rw [ih,pow_add]; rfl
lemma accrued_div (s t:J→I→ℝ)(u): accrues (s/t) u= accrues s u / accrues t u:= by
   induction u with
   | nil=> change (1:I→ℝ)=1/1; simp
   | cons i p ih=>
      funext j; change s i j/t i j*accrues (s/t) p j= (s i j * accrues s p j)/(t i j * accrues t p j); rw [ih]; exact div_mul_div_comm ..
lemma accrues_pull (u:List I)(s:I→J→ℝ)(i:J)(v:M→J) : accrues (fun j=> s j∘v) u = accrues s u ∘ v:= by
   induction u with | nil=> rfl| cons j u ih=> change (s j∘v)*accrues _ u= (s j*accrues s u) ∘ v; rw [ih]; rfl
variable [Fintype J][DecidableEq J]
lemma accrued_count {s:J→I→ℝ}(h:u.Nodup)(hp:∀ i,i∈u)(i): accrues s u i=∏ j,s j i:= by
   have hx u : accrues s u i=(u.map (fun j=>s j i)).prod:= by induction u with | nil=> rfl| cons b u ih=> rw [List.map_cons,List.prod_cons,←ih]; rfl
   rw [hx,← List.prod_toFinset _ h, eq_univ_of_forall (fun i=> List.mem_toFinset.mpr (hp i))]
end rake
section shelter
variable [Fintype J][DecidableEq J]
variable {P Q:∀ i,StripU G (X.S.block (ℓ i))} {U V: J→I→ BoardU D R G}
local notation "♭" => WidthP X a ℓ
local notation "♯" => WidthP X a (fun i=>ℓ i+1)
-- canon vertices evaluated at level i+1, not chart expansion in p. Restore literal funding.
def burned (h k n:ℕ)(φ:Profile D)(X:Chain)(x:E4)(V:BoardU D R G): Tale G:= Town.season (-arcT X k n x) (collect X h k n φ x V)
def shout (u:List J)(h z:J→ℕ)(P:StripU G (X.S.block i))(φ:J→Profile D)(k:ℕ)(x:E4)(U:J→ BoardU D R G): Tale G:= jamT P (fun j=>burned (h j) k (i+1) (φ j) X x (U j)) (shrinkP X k i x) z u -- bug binder i' remove
variable {p0 p qM: I→ℝ}{l:I→ℕ}
lemma Accum (he:Mats u y C B s φ)(hH:1/2≤ R)(hδ:u.Nodup)(hc:∀ i,i∈u)(hm:loadᵣ z u≤τ)(hC:∀ i∈u,z i≤τ)(ht: ∀ i∈u,∀ j,Marvel (z i) (U i j))(hp:∀ i∈u,∀ j,Marvel (z i) (V i j))(hP:LensP (k+b) E τ y δ v P Q)(hS: LensP b E τ y δ v P Q)(hQ:LensP k E τ y δ v P Q) (hv:∀ i,Vily (veiled (P i).cv))(hw:∀ i,Vily (veiled (Q i).cv))(hf:∀ j∈u,0≤t' j)(hz:∀ j∈u,∀ i≤E,∀ r, Drum (k+b) y δ (t' j) (fun t=> U j t i r) (fun t=> V j t i r) 1)
    (hD:♭ ≤1) (hh:n≤E)(x:I→E4): Drum k y δ ((accrues (t'*s) u)/(♯ ^loadᵣ h u)*♭^b) (fun i=>shout u h z (P i) (fun j=>φ j i) (a i) (x i) (fun j=>U j i) n r) (fun i=>shout u h z (Q i) (fun j=>φ j i) (a i) (x i) (fun j=>V j i) n r) (WidthP X a ℓ) := by
   let H i:=shrinkP X (a i) (ℓ i) (x i); let W i:= arcT X (a i) (ℓ i+1) (x i); let S i:=arcT X (a i) (ℓ i) (x i)
   let Y (U:J→ I→ BoardU D R G) (i:I) j v := unitA X (h j) (a i) (ℓ i+1) (φ j i).val (x i) (U j i) v
   let F (U:J→ I→BoardU D R G) (i:I) j (v:J→Cover) := Town.season (v j-W i) (Y U i j (v j)); let L i j:= noses X i a ℓ (φ j) x R
   let L' i:= Fintype.piFinset (L i); let M (P:∀ i:I,StripU G (X.S.block (ℓ i))) (U:J→ I→BoardU D R G)(i)(v:J→Cover):= jamT (P i) (fun j=>F U i j v) (H i) z u
   let T : J→I→ℝ:=fun j i=> (t' j*s j) i * tariff (h j) (♯ i) -- typo
   let a' := accrues T u; have hZ i hi:0 ≤ T i:= fun j=>mul_nonneg (mul_nonneg (hf _ hi _) (he.zero _ hi _)) (permit_pos (a:=a) (ℓ:=fun i=> ℓ i+1) (X:=X) (h i) j) -- spaces
   have hmP (K:∀ i:I,StripU G (X.S.block (ℓ i))) (U:J→ I→BoardU D R G)(ht:∀ i, Fair (K i))(hp:∀ i∈u,∀ j,Marvel (z i) (U i j))(i:I): shout u h z (K i) (fun j=>φ j i) (a i) (x i) (fun j=>U j i) =∑ j∈L' i,M K U i j:= by
      unfold shout burned; simp_rw [move_collect]; refine jam_grows (J:=fun _=>Cover) (K i) (ht i) hδ hc (L i) (fun j y=> Town.season (y-W i) (Y U i j y)) (fun j v=> (charge_t _ (x i) (a i) (ℓ i+1) (hp j (hc j) i) (h j) X v).transport _) (H i)
   simp_rw [hmP P U hP.one ht,hmP Q V hP.two hp,Finset.sum_apply]
   have hw': ♯ ≤ 1:= spinTick a ℓ X hQ.age hQ.pay hD
   have hv : Drum k y δ (fun i=> (↑(L' i).card:ℝ)*(a' i* ((♭ i)^b))) (fun i=>∑ j∈ L' i, M P U i j n r) (fun i=>∑ j ∈ L' i, M Q V i j n r) (WidthP X a ℓ):= by
      let D':= accrues T u * ♭^b
      refine Drum.club (V:=fun i j=>M P U i j n r) (W:=fun i j=>M Q V i j n r) (s:=L') hP.age hP.rent (p:= D') (fun i=>mul_nonneg (pow_pr (q':=T) hZ i) (pow_nonneg (spanP_pos ..|>.le) b)) (fun _=>spanP_pos ..|>.le) ?_
      let src (i:Club L') := i.1; let t j (i:Club L'):= i.2.val j -- type
      let Z j (i:Club L'):= growP (X.S.block (ℓ i.1)) (t j i)-S i.1; let Z' j (i:Club L'):= t j i-W i.1
      have hW j (i: Club L'): t j i ∈ L i.1 j:= Fintype.mem_piFinset.mp i.2.property j
      have H' (j i): Lattice.lift (H (src i))+Z' j i= (X.S.block (ℓ i.1)).val • Z j i + Lattice.lift (growL (X.S.block (ℓ i.1)) (t j i)):= royalty ..
      let Y' (U:J→ I→BoardU _ R G) j (v:Club L'):= Y U v.1 j (t j v)
      rw [show (fun i:Club L'=>D' i.1)=(accrues (fun i=> T i ∘src) u)*(♭∘src)^b from ?_]; swap
      · funext i; rw [Pi.mul_apply, accrues_pull u T i.1 src]; rfl
      refine steps_l (u:=u) (K:=fun i=> Q (src i)) (P:=fun i=>P (src i)) (U:=Y' U) (B:=Y' V) (A:=z) (x:=fun i:Club L'=> B (src i)*(1+8*R)) (t':=Z') (z:=Z) (f:=fun j i=>growL (X.S.block (ℓ i.1)) (t j i)) (drum_w hP src) (drum_w hQ src) (fun i=>hv i.1) (fun i=>hw i.1) hm hC (fun i hi j=> ?_ ) (fun i hi j=>?_) (fun i hi m hm k=> ?_) (fun j _ i=>H' j i) (leaves_from (X:=X) (x:=x ∘src) (a:=a ∘src) (ℓ:=ℓ∘src) hH (drum_w hS src) (fun i=>hD i.1) (mats_hood he src) (fun i hi j=>hW i j)) (fun i hi j=>hZ i hi j.1) hδ hh
      · exact charge_t _ _ _ _ (ht _ hi _) ..
      · exact charge_t _ _ _ _ (hp _ hi _) ..
      let f(j: Club L'):= (φ i (src j)).val
      exact colorUp (u:=t i) (A:=s i ∘src) (x:=x∘src) (φ:=f) (a:=a∘src) (ℓ:=fun i=>ℓ i.1+1) (X:=X) ((hz _ hi _ hm k).mold src) (fun j=> he.zero _ hi _) (fun j=> he.mass _ hi _) (fun j=>hw' j.1) (n:=h i)
   have hR:0≤R := le_trans (by norm_num : (0:ℝ)≤1/2) hH
   let q j i:= ((L i j).card:ℝ)*(♯ i)^4
   have he i hi:= posted (a:=a) (ℓ:=fun i=>ℓ i+1) he.spanH hR (he.space i hi) hw' hP.age x
   apply Drum.cheap (p:=accrues q u) _ (accrued_y hP.age he)
   rw [show (fun i=> (↑(L' i).card:ℝ)* (a' i* ((♭ i)^b)))= accrues q u * (accrues (t'*s) u / ♯^loadᵣ h u * ♭^b) from ?_] at hv; exact hv
   funext i; rw [← accrued_wP]; let v j i:= (↑((L i j).card):ℝ); have hC: (↑(L' i).card:ℝ)=accrues v u i:= by unfold L'; rw [Fintype.card_piFinset]; push_cast; rw [accrued_count hδ hc]
   change (↑(L' i).card:ℝ)* (accrues T u i * (♭ i)^b)= accrues q u i * (accrues _ u i / accrues _ u i* _); rw [hC]
   simp_rw [fun (s:J→I→ℝ)=>accrued_count (s:=s) hδ hc]; unfold q v T tariff; simp only [Pi.mul_apply, Pi.div_apply,Pi.pow_apply,prod_div_distrib,prod_mul_distrib]; ring
end shelter
end YM.RG08.Plot
