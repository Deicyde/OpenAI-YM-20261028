import YM.RG08.Bands.Majesty
/-!
# Cost first contact in thermal inequality.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Bands
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {α:Type}{n k b r s:ℕ}
section sew
variable {u v:Cover}{σ η p A B C:ℝ}{F: Shale α (r+1)}{W:Shale α (s+1)}{K:Row α α}
private lemma casks_p (F:Beads α r)(V:Beads α s) : girth (aboardB (F,V))=girth F+girth V := by unfold girth aboardB; rw [Fin.sum_univ_add]; simp
lemma groovy_p (u:Cover)(P: Beads α r)(he:0≤ η)(hx:η≤1): tailP k η (gang u P) ≤ (1+(r:ℝ)*(η*size u))^k * tailP k 1 P:= by
   unfold tailP; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity)
   let v:=(size u:ℝ); have hv:0≤v:=Nat.cast_nonneg _
   have hz:(girth (gang u P):ℝ) ≤ girth P+(r:ℝ)*size u:= by exact_mod_cast roam_grows P u
   nlinarith only [mul_le_mul_of_nonneg_left hz he,mul_le_of_le_one_left (show 0 ≤ (girth P:ℝ) by positivity) hx, show 0≤ (girth P:ℝ) from Nat.cast_nonneg _,show 0 ≤ (r:ℝ)*η*size u*(girth P:ℝ) by positivity]
lemma count_l (h:cis (k+b) 1 F A)(hw:cis (k+b) 1 W B)(hp:K.strip σ C)(he:0<σ)(hC:0≤C)(hv:0≤η)(hy:η≤1)(ho:1 ≤ p*(1+(size (u-v):ℝ)))(hP:0≤p):
   cis k η (countP none K (roam u F) (roam v W)) (‖syl r s‖*((((1+((r+1:ℕ):ℝ)*(η*size u))^k*(1+((s+1:ℕ):ℝ)*(η*size v))^k)*p^b*(Run.utter b σ*C))*(A*B))) := by
   let U:=fun (i:ℕ)(v:Cover)=>(1+ ((i+1:ℕ):ℝ) * (η*size v))^k; have hu i x : 0 ≤ U i x:= by unfold U; positivity
   let M:=U r u*U s v; have hM:0 ≤ M:= mul_nonneg (hu ..) (hu ..); let N:=(Run.utter b σ*C); have hN:0≤N:=mul_nonneg (utter_pos he) hC
   unfold countP; refine sew_cis (Ink.scale (Ink.pour _ ?_ (tailp hv)) _) hv
   let I:= Beads α (r+1)× Beads α (s+1); let e : Equiv.Perm I := Equiv.prodCongr (gang u) (gang v)
   apply budget_mono (budget_scale (mul_nonneg (mul_nonneg hM (pow_nonneg hP b)) hN) (budget_pull e.symm e.symm.injective (budget_prod h hw))) (fun i=>mul_nonneg (zero_le_one.trans (tailp hv _)) (norm_nonneg _)); intro i
   obtain ⟨⟨x,y⟩,heq⟩:= e.surjective i; subst i
   let x':= gang u x; let y':=gang v y; let d:= (x' 0).1; let c':=(y' 0).1; let L:=(c'-d)
   let a:= ‖K (x' 0).2 (y' 0).2 L‖
   have hs : tailP k η (stemPair (x',y')) ≤ M*(tailP k 1 x*tailP k 1 y) := by
     apply le_trans (b:=tailP k η x'*tailP k η y') _ _
     · unfold tailP stemPair; rw [casks_p, Nat.cast_add,←mul_pow]; apply pow_le_pow_left₀ (by positivity)
       nlinarith only [mul_le_mul_of_nonneg_left (show (↑(girth (stem1 x')):ℝ)≤girth x' by exact_mod_cast stems_le x') hv,mul_le_mul_of_nonneg_left (show (↑(girth (stem1 y')):ℝ)≤girth y' by exact_mod_cast stems_le y') hv,show 0≤ η*girth x'*(η*girth y') by positivity]
     exact (mul_le_mul (groovy_p u x hv hy) (groovy_p v y hv hy) (zero_le_one.trans (tailp hv _)) (mul_nonneg (hu ..) (zero_le_one.trans (tailp zero_le_one _)))).trans_eq (mul_mul_mul_comm ..)
   have hz: size (u-v) ≤ girth x+girth y+size L := by
     have hh {b':ℕ}(q:Cover)(z:Beads α (b'+1)) : size (z 0).1 ≤ girth z:= single_le_sum (f:=fun i=> size (z i).1) (fun i _=>Nat.zero_le _) (mem_univ 0) -- b'
     rw [show u-v = (-(x 0).1+(y 0).1) + -L from (by change u-v = _+ - (((y 0).1+v)-((x 0).1+u)); abel)]
     exact le_trans (size_add ..) (Nat.add_le_add (le_trans (size_add ..) (by rw [size_neg]; exact Nat.add_le_add (hh u _) (hh v _))) (by rw [size_neg]))
   have hb: a ≤ p^b*N*(tailP b 1 x*tailP b 1 y):= by
     have hB : a*(1+(size L:ℝ))^b ≤ N := by rw [mul_comm]; exact budget_single (dith (hp (x' 0).2 (y' 0).2) he) L
     have hQ: 1≤ p*(1+(girth x:ℝ))*(1+(girth y:ℝ))*(1+(size L:ℝ)):= by
       have hG: (size (u-v):ℝ) ≤ girth x + (girth y:ℝ)+size L:= by exact_mod_cast hz
       apply ho.trans; simp only [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hP; nlinarith only [hG,show 0 ≤ (girth x:ℝ)*girth y by positivity,show 0 ≤ (girth y:ℝ)*size L by positivity, show 0 ≤ (girth x:ℝ)*(1+(girth y:ℝ))*size L by positivity]
     calc
       a ≤ a*(p*(1+(girth x:ℝ))*(1+(girth y:ℝ))*(1+(size L:ℝ)))^b := le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hQ)
       _ = (a*(1+(size L:ℝ))^b)*(p^b*(tailP b 1 x *tailP b 1 y)):= by unfold tailP; simp only [one_mul,mul_pow]; ring
       _ ≤ _:= (mul_le_mul_of_nonneg_right hB (mul_nonneg (pow_nonneg hP b) (mul_nonneg (zero_le_one.trans (tailp zero_le_one _)) (zero_le_one.trans (tailp zero_le_one _))))).trans_eq (by ring)
   simp only [Function.comp_apply,Pi.mul_apply,interU, e,Equiv.prodCongr_apply,roam,Equiv.symm_apply_apply]; rw [norm_mul,norm_mul]
   rw [show (gang u).symm (((gang u).prodCongr (gang v)) (x,y)).1=x from (gang u).symm_apply_apply x,show (gang v).symm (((gang u).prodCongr (gang v)) (x,y)).2=y from (gang v).symm_apply_apply y]
   change tailP k η (stemPair (x',y'))*(‖F x‖*‖W y‖*a) ≤ M*p^b*N*((tailP (k+b) 1 x*‖F x‖)*(tailP (k+b) 1 y*‖W y‖))
   apply le_trans (mul_le_mul hs (mul_le_mul_of_nonneg_left hb (by positivity)) (mul_nonneg (by positivity) (norm_nonneg _)) (mul_nonneg hM (mul_nonneg (zero_le_one.trans (tailp zero_le_one _)) (zero_le_one.trans (tailp zero_le_one _))))) (le_of_eq ?_)
   unfold tailP; simp only [pow_add]; ring
end sew
end YM.RG08.Bands
