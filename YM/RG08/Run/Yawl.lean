import YM.RG08.Run.Ships
/-!
# Transfer lemma on subset calls. Explicit lease and amplitude.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill
open scoped BigOperators Topology Real ContDiff
open Wings
variable {I J α Y:Type}{u:I→Windows}{b:J→ShoreP u}{n k r:ℕ}{X:Chain}{θ : ℝ}
def strideP (X:Chain)(b:J→ShoreP u) (p:J→ℝ) (i:Wall b n):= p i.a*gain X.S (1/4) i.i (b i.a).next.i
lemma stride_tick (t:Wall b 1)(p:J→ℝ) : strideP X b p t=strideP X b p t.roof *gain X.S (1/4) t.i (t.i+1):= by
   unfold strideP; conv_lhs=> rw [gain_trans _ _ _ (t.i+1)]
   change _=p t.a*gain X.S (1/4) (t.i+1) (b t.a).next.i * _; ring
local notation "Ⓨ" => wallY (b:=b) X
local notation "Δ" => tiltP (b:=b) X
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] {P : Wall b 0→Quire.Rooted Y α r} {Q : Wall b 1→ Quire.Rooted Y α r}{p : J→ℝ}{v : Wall b 0 →ℝ}
lemma Card.up (h:Card k Ⓨ (strideP X b p) P v)(hv:Weighed (wallY X (b:=b) (n:=1)) (fun i=> ((X.S.block i.i).val:ℝ)))(hp:0≤p): Card k Ⓨ (strideP X b p) (fun i:Wall b 1=> P i.roof) (fun i=>v i.roof) := by
   have ht(t:Wall b 1): strideP X b p t.roof ≤ (X.S.block t.i).val *strideP X b p t := by
     rw [stride_tick]; have hg:0≤strideP X b p t.roof:=mul_nonneg (hp _) (gain_pos ..).le
     rw [mul_left_comm _ (strideP X b p t.roof)]; apply le_mul_of_one_le_right hg; let f:= X.S.block t.i; let a:=(f.val:ℝ); have ha: 1 ≤ a:= by unfold a; exact_mod_cast f.property
     have hz:0<a:= by positivity
     apply le_trans _ (mul_le_mul_of_nonneg_left (Wall.gain_fewer X (by norm_num) t) (Nat.cast_nonneg (f.val)))
     rw [gain_succ_half, ← mul_div_assoc,mul_one]
     apply (one_le_div (Real.sqrt_pos.mpr hz)).2
     nlinarith [Real.sq_sqrt hz.le,Real.sqrt_nonneg a]
   exact Card.lesser (Card.raise (z:=(fun i:Wall b 1=> ((X.S.block i.i).val:ℝ))*strideP X b p) (h.mold Wall.roof) ht) hv
set_option linter.unusedSectionVars false in
lemma traverse (hp:0≤p)(he:0≤v)(hk:Card k (fun t=>Ⓨ (Wall.tip b t)) p (fun t=>P (Wall.tip b t)) (fun t=>v (Wall.tip b t)))(h: ∀ (t:Wall b 1)(C:ℝ), cis k (v t.roof) (P t.roof) C → cis k (v t.low) (Q t) (C*gain X.S (1/2) t.i (t.i+1)))(hz: Card k Ⓨ (strideP X b p) (fun t:Wall b 1=> P t.low-Q t) (fun t=>v t.low)) : Card k Ⓨ (strideP X b p) P v := by
  obtain ⟨u,⟨A,n,hA,Ha⟩,hM⟩:=hk.money; obtain ⟨C,⟨B,s,hB,Hb⟩,hQ⟩:=hz.money
  let M t:=(b (Wall.a (b:=b) (n:=0) t)).city; have hv:Weighed (wallY X (b:=b) (n:=0)) (fun i=> (M i:ℝ)):= (subsegment (u:=_) X).transfer (fun i:Wall b 0=> b i.a)
  refine ⟨_,((Weighed.constant (wallY X) hA).times (Weighed.power (wallY X (n:=0)) (Wall.plusOne X) n)).plus ((hv.times (Weighed.constant (wallY X) hB)).times (Weighed.power (wallY X) (Wall.plusOne X) s)) (Wall.plusOne X),fun t=>?_⟩
  let N:=(b t.a).next.i; let L:=(b t.a).low; let y:=wallY X t; have hh:1≤ y:= Wall.plusOne X _
  let W k (ht:L≤ k) (hj:k≤ N): Wall b 0:=⟨t.a,k,ht,hj⟩; let a:=A*y^n; let b':= B*y^s
  have hy i (ht:i≤ N) (hh:L≤ i): cis k (v (W i hh ht)) (P (W i hh ht)) ((a+(↑(N-i):ℝ)*b')*strideP X _ p (W i hh ht)) := by
    induction ht using Nat.decreasingInduction with
    | self=>
       have hz: Wall.tip b t.a= W N hh (le_refl N):=rfl
       rw [← hz]; apply Ink.raise (hM t.a)
       rw [show strideP X b p (Wall.tip b t.a)=p t.a from (by simp only [strideP,Wall.tip,gain_zero,mul_one]), Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]
       exact mul_le_mul_of_nonneg_right (Ha t.a|>.2) (hp t.a)
    | of_succ i hi ih =>
       let v': Wall b 1:=⟨t.a,i,hh,hi⟩
       have hX:= ih (Nat.le_trans hh (Nat.le_succ i))
       have he':= h v' _ hX; have hz:= hQ v'
       have hw : 0≤strideP X b p v':=mul_nonneg (hp _) (gain_pos ..).le
       apply Ink.raise (cast (congr_arg (fun (F:Quire.Rooted Y α r)=> cis k (v v'.low) F _) (show Q v'+(P v'.low-Q v')=P v'.low from add_sub_cancel ..)) (Ink.plus he' hz (fun i=> zero_le_one.trans (tailp (he v'.low) i))))
       apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (Wall.gain_fewer X (by norm_num : (1/4:ℝ)≤1/2) v') hX.nonneg) (mul_le_mul_of_nonneg_right (Hb v'|>.2) hw)); apply le_of_eq
       change ((a+↑(N-(i+1))*b')*strideP X b p v'.roof)* gain X.S (1/4) v'.i (v'.i+1)+b'*strideP X b p v'= (a+↑(N-i)*b')*strideP X b p v'; rw [stride_tick v',show N-i=N-(i+1)+1 by omega]; push_cast; ring
  apply Ink.raise (hy t.i t.last t.first); simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply]; change _ ≤ (a+(↑(M t):ℝ)*B*y^s) * strideP X b p t
  rw [mul_assoc (↑(M t):ℝ)]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hp _) (gain_pos ..).le); refine add_le_add_right ?_ a -- side error
  · have hy:L≤t.i:=t.first; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (show N-t.i≤ N-L from by omega)) (show 0≤ b' by unfold b'; positivity)
end YM.RG08.Run
