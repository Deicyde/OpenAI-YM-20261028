import YM.FullVolume.Amp.Shelf
import Mathlib.Topology.MetricSpace.Contracting
/-! Invert cut finite on closed Beam. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Rally
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums Beam
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {n:ℕ}{A:Fin (n+1) → Type} [∀ i,NormedAddCommGroup (A i)][∀ i,NormedSpace ℝ (A i)][∀ i, CompleteSpace (A i)]
local notation "T"=> Fin (n+1)
local notation "ℒ"=> Fin.last n
local notation "I"=> Fin n
variable (K:Rally n A) {U V : Box n A} {b:Beam ℝ}
variable (hb:∀ i, ‖b‖≤ lux/4*K.w i)(h:‖U‖ ≤ lux)(ht:‖V‖ ≤ lux)
lemma perD (i:T) : ‖U.1 i-V.1 i‖≤‖U-V‖∧ ‖U.2 i-V.2 i‖≤‖U-V‖:=⟨(norm_le_pi_norm (U-V).1 i).trans (norm_fst_le _),(norm_le_pi_norm (U-V).2 i).trans (norm_snd_le _)⟩
lemma layY (i:T): ‖lay (U.1 i) (U.2 i)-lay (V.1 i) (V.2 i)‖ ≤ 2*‖U-V‖:= (layD ..).trans ((add_le_add (perD ..|>.1) (perD ..|>.2)).trans_eq (by rw [two_mul])) -- decr
include h ht K
lemma runD (i:T) : ‖K.runs U i-K.runs V i‖ ≤ (1/2:ℝ)*‖U-V‖:=by
 induction i using Fin.lastCases with
 | last=>
   unfold runs; rw [Fin.lastCases_last, Fin.lastCases_last]; apply (Pulse.liftD _ _ _ ((perN h _).1.trans (by norm_num [lux])) ((perN ht _).1.trans (by norm_num [lux]))).trans; exact mul_le_mul (by norm_num [glint]) (perD ℒ).1 (norm_nonneg _) (by norm_num)
 | cast i=>
   unfold runs; rw [Fin.lastCases_castSucc,Fin.lastCases_castSucc]; refine (Pulse.liftD _ _ _ (layH h _) (layH ht _)).trans ((mul_le_mul_of_nonneg_left (layY _) (show (0:ℝ)≤2*glint by norm_num [glint])).trans ?_); rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (by norm_num [glint]) (norm_nonneg _)
lemma sumD (i:T): ‖(∑ k∈prior n i, K.moveB U k)-∑ k∈prior n i,K.moveB V k‖ ≤ 4*glint*K.w i*‖U-V‖:=by
   rw [← sum_sub_distrib]; apply (norm_sum_le ..).trans
   have hz k: ‖K.moveB U k-K.moveB V k‖≤ K.span k*(4*‖U-V‖):=((K.lum k).liftD _ _ (layH h _) (layH ht _)).trans ((mul_le_mul_of_nonneg_left (layY _) (mul_nonneg (by norm_num) (K.lum _|>.cost))).trans_eq (by ring))
   refine (sum_le_sum (fun k _=>hz k)).trans ?_; rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (K.accounts i) (by positivity)).trans_eq (by ring)
lemma danceD (b:Beam ℝ) : ‖K.danceB b U-K.danceB b V‖≤(1/2:ℝ)*‖U-V‖:=by
  have he:0≤(1/2:ℝ)*‖U-V‖:= by positivity
  refine max_le ((pi_norm_le_iff_of_nonneg he).mpr (fun i=>?_)) ((pi_norm_le_iff_of_nonneg he).mpr (K.runD h ht)); dsimp only [danceB, Prod.fst_sub,Pi.sub_apply]; rw [← smul_sub, norm_smul, norm_inv]
  have ha:=K.fee₁ i; rw [Real.norm_of_nonneg (zero_le_one.trans ha)]
  apply (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ha)).trans
  let y U:=(∑ k∈prior n i,K.moveB U k)
  rw [sub_sub_sub_comm,←smul_sub,←smul_sub,sub_sub_sub_cancel_left]
  apply (norm_sub_le ..).trans; rw [norm_smul,norm_smul,norm_inv,Real.norm_of_nonneg (K.wPos i).le]; refine le_trans (b:=4*glint*‖U-V‖+2*lux*‖U-V‖) (add_le_add ?_ ?_) ?_
  · rw [norm_sub_rev]; exact show _ ≤ 4*glint*‖U-V‖ from (inv_mul_le_iff₀ (K.wPos i)).mpr ((K.sumD h ht i).trans_eq (by ring))
  · exact show _≤ 2*lux*‖U-V‖ from (mul_le_of_le_one_left (norm_nonneg _) (K.wtP i)).trans ((sprintD _ _ (perN h _).1 (perN ht _).1).trans (mul_le_mul_of_nonneg_left (perD _|>.1) (by norm_num [lux])))
  rw [←add_mul]; exact mul_le_mul_of_nonneg_right (by norm_num [lux,glint]) (norm_nonneg _)
omit h ht
include hb
lemma payable : ∃! U: Box n A, ‖U‖≤lux ∧ K.danceB b U=U:=by
  let S:=Metric.closedBall (0:Box n A) lux; let C:S→S:= fun x=> ⟨K.danceB b x,(mem_closedBall_zero_iff).2 (K.danceN hb ((mem_closedBall_zero_iff).mp x.property))⟩
  have hh:ContractingWith (1/2) C:= ⟨by norm_num,LipschitzWith.of_dist_le_mul fun x y=>by
    rw [Subtype.dist_eq,Subtype.dist_eq,dist_eq_norm,dist_eq_norm]; exact (K.danceD (mem_closedBall_zero_iff.mp x.property) (mem_closedBall_zero_iff.mp y.property) b).trans_eq (by norm_num)⟩
  haveI : Nonempty S:=⟨0,Metric.mem_closedBall_self tintP.2.le⟩
  haveI : CompleteSpace S := Metric.isClosed_closedBall.completeSpace_coe
  let x:= hh.fixedPoint C; refine ⟨x,⟨mem_closedBall_zero_iff.mp x.property,congr_arg Subtype.val (hh.fixedPoint_isFixedPt)⟩,fun y hy=>?_⟩; let z:S:= ⟨y,mem_closedBall_zero_iff.mpr hy.1⟩; exact congr_arg Subtype.val (hh.fixedPoint_unique (Subtype.ext hy.2 : C z=z))
omit hb
-- equations Recognizes real evaluations
variable (p:Fin (n+1) →ℝ) (f: (i:Fin (n+1)) → A i) (t:ℝ)
structure Facing : Prop where
   beck i : ‖p i‖ ≤ lux
   west i : ‖f i‖ ≤ lux
   startTag : f ℒ=sees K.initB (p ℒ)
   walks i : f (Fin.castSucc i)=sees (K.beams i) (p i.succ,f i.succ)
   finds i: p i=(K.feeB i)⁻¹ * ((K.w i)⁻¹*(t-∑ k∈prior n i,sees (K.lum k) (p k.succ,f k.succ))- K.wt i*(p i)^2)
lemma mount {U:Box n A}(h:‖U‖ ≤ lux)(v:sun)(hv:K.danceB b U=U): Facing K (fun i=>read ℝ v (U.1 i)) (fun i=> read (A i) v (U.2 i)) (read ℝ v b):=by
   refine ⟨fun i=> (price ..).trans (perN h i).1,fun i=> (price ..).trans (perN h i).2,?_,?_,?_⟩
   · conv_lhs => rw [← hv]
     simp only [danceB,runs, Fin.lastCases_last]; exact (K.initB).liftL _ ((perN h ℒ).1.trans (by norm_num [lux])) _
   · intro i; conv_lhs=> rw [←hv]
     simp only [danceB,runs, Fin.lastCases_castSucc]; rw [Pulse.liftL _ _ (layH h i.succ), layL]
   intro i; conv_lhs=> rw [←hv]
   simp only [danceB,moveB,sprintL,map_smul,map_sum,map_sub]; simp_rw [fun k=>(K.lum k).liftL _ (layH h k.succ) v,layL]; rfl
lemma pose {t:ℝ}(hv:Facing K p f t): let V:Box n A:= (fun i=>arm (p i),fun i=>arm (f i)); ‖V‖≤lux∧ K.danceB (arm t) V= V:=by
  intro V; have hp : ‖V‖ ≤ lux:=max_le ((pi_norm_le_iff_of_nonneg tintP.2.le).mpr (fun i=> armN _|>.trans_le (hv.beck i))) ((pi_norm_le_iff_of_nonneg tintP.2.le).mpr (fun i=> armN _|>.trans_le (hv.west i)))
  refine ⟨hp, Prod.ext (funext fun i=>?_ ) (funext fun i=>?_)⟩
  · apply soul; intro v; change read ℝ v ((K.danceB (arm t) V).fst i)=read ℝ v (arm _); simp only [danceB,moveB,map_smul,map_sum,map_sub,sprintL]; simp_rw [fun k=> (K.lum k).liftL _ (layH hp k.succ) v, layL]; unfold V; simp_rw [armL]; exact (hv.finds _).symm
  induction i using Fin.lastCases with
  | last=>
    change K.runs V _= _; rw [runs,Fin.lastCases_last]; apply soul; intro v; change read _ v (bead K.initB _)= read _ v _; rw [Pulse.liftL _ _ ((perN hp _).1.trans (by norm_num [lux]))]; unfold V; simp only [armL]; exact hv.startTag.symm
  | cast i=>
    change K.runs V _=_; rw [runs,Fin.lastCases_castSucc]; apply soul; intro v; change read _ v (bead (K.beams i) _)=read _ v _; rw [Pulse.liftL _ _ (layH hp i.succ), layL]; unfold V; simp only [armL]; exact (hv.walks i).symm
include hb h
lemma south {t:ℝ}(v:sun)(he: t=read ℝ v b)(hp:Facing K p f t)(hu:K.danceB b U=U)(i:T): p i=read ℝ v (U.1 i)∧ f i=read (A i) v (U.2 i):=by
    have hc:= K.payable (b:=arm t) (fun i=> (armN _).trans_le (he ▸ ((price ..).trans (hb i))))
    have hh :Facing K (fun i=>read ℝ v (U.1 i)) (fun i=>read (A i) v (U.2 i)) t:=he ▸ K.mount h v hu
    have hx:= hc.unique (K.pose p f hp) (K.pose _ _ hh)
    exact ⟨(armL v _).symm.trans ((congr_arg (read ℝ v) (congr_fun (congr_arg Prod.fst hx) i)).trans (armL v _)),(armL v _).symm.trans ((congr_arg (read _ v) (congr_fun (congr_arg Prod.snd hx) i)).trans (armL v _))⟩
end YM.FullVolume.Amp.Rally
