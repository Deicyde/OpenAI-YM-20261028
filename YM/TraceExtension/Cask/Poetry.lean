import YM.TraceExtension.Cask.Savor
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L K J:Type}[DecidableEq V][DecidableEq L][DecidableEq K][DecidableEq J]{n:Side}[Fintype V][Fintype L][Fintype K][Fintype J]{G:Gauge}
variable (x:J→V)(B: K→Box n)
set_option quotPrecheck false
local notation "I!"=>Grain L K J
local notation "E"=>Config G n
local notation "F!"=>Rain V G
local notation "m!"=>freq V G
variable {P:Staff V (Grain L K J) n}(R:Rep G n)(F:Grain L K J→ Config G n→ Rain V G→ℂ){w:Duel V→ℝ}{e u:ℝ}
variable (M:Decked P R F w e u)(H:Roles P x B)
local notation "Y"=> lyrics P F
local notation "A"=> shore P R (lyrics P F)
include H M
lemma full_line (U:E): (shore P R (lyrics P F) U).part (Stock.final (Duel V))=∫ v, (Real.exp (R.exponent U):ℂ)*clothW x (fun p=>F p U v)*(∑ i,(-1:ℂ)^i.card * trump P B (flags R.p.threshold U) (fun p=>F p U v) i) ∂freq V G:=by
   let d:= Stock.final (Duel V); let f v s:= (swarm P (fun p=>robeT P F p U v) (flags R.p.threshold U) s).part d
   have hp(v:F!):∑ i,f v i=clothW x (fun p=>F p U v)*(∑ i,(-1:ℂ)^i.card*trump P B (flags R.p.threshold U) (fun p=> F p U v) i):= codeC P x B _ (fun p=> F p U v) H (fun i h=>M.pinch i U v h)
   have hf(s:Finset I!):Envelope (fun v=> f v s):= by
      by_cases h:Basic P (flags R.p.threshold U) s
      · simp_rw [f,swarm,if_pos h,shipP,Poly.part_send]; split; exact based (floorsV R F M s) (Prod.mk U) (measurable_const.prodMk measurable_id); exact constV _
      simp_rw [f,swarm,if_neg h,Poly.part_nil]; exact constV 0
   have ht(s): (swarm P (lyrics P F U) (flags R.p.threshold U) s).part d=∫ v,f v s∂m!:=by
      by_cases h:Basic P (flags R.p.threshold U) s; swap; · simp_rw [f,swarm,if_neg h,Poly.part_nil,integral_zero]
      simp_rw [f,swarm,if_pos h,shipP,Poly.part_send]; split_ifs with he h' <;> try rfl
      all_goals simp
   unfold shore; simp_rw [Poly.part_smul,Poly.part_sum,mul_assoc,← hp,integral_const_mul,integral_finsetSum _ (fun i _=> capped (hf i) m!)]; exact congr_arg (_ * ·) (sum_congr rfl (fun i _=>ht _))
omit H
lemma ode {a b p s t :ℝ} (hp:R.Lawful a b p s t): Integrable A (prior G n):= by
    refine integrable_pi_iff.mpr (fun i=> ?_); let h(v : Finset I!)(U:E):= (swarm P (lyrics P F U) (flags R.p.threshold U) v).part i; have he(v:Finset I!):Envelope (h v):=by
       obtain ⟨m,c,he⟩:= sealM (freq V G) (floorsV R F M v)
       unfold h; simp_rw [swarm]; have ht (v':Poly (Twin V))(U:E): (if Basic P (flags R.p.threshold U) v then v' else 0).part i=if Basic P (flags R.p.threshold U) v then v'.part i else 0:=by split<;>rfl
       simp_rw [ht,shipP,Poly.part_send]; have hm : {U:E|Basic P (flags R.p.threshold U) v}=⋃ k:{k:Support n//Basic P k v},{U:E|flags R.p.threshold U=k.val}:=by ext x; rw[Set.mem_iUnion]; constructor; intro H; exact ⟨⟨_,H⟩,rfl⟩; rintro ⟨k,h⟩; change Basic P (flags R.p.threshold x) v; exact (show flags _ x=k.val from h).symm ▸ k.property
       refine ⟨Measurable.ite (hm.symm ▸ MeasurableSet.iUnion (fun _=> flags_measurable_eq ..)) ?_ measurable_const,c,fun U=>?_⟩
       · split; exact m; exact measurable_const
       split_ifs; exact he U
       all_goals exact norm_zero.trans_le ((norm_nonneg _).trans (he U))
    change Integrable (fun U=>(shore _ _ _ U).part i) _; simp_rw[shore,Poly.part_smul,Poly.part_sum]; exact capped (envUmul (fromR (R.exponentEnv hp).exp) (envUsum univ h (fun p _=>he p))) (prior G n)
end YM.Trace.Cask
