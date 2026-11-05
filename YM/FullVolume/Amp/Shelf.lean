import YM.FullVolume.Amp.Bright
/-! Concurrent finite inverse equations in parameter Beam. Lift estimates data and v. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums Beam
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y : Type} [NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
variable {v:sun}{n:ℕ} {t:ℝ}
structure Pulse (X Y:Type) [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] (v:ℝ) where
   poem : FormalMultilinearSeries ℝ X Y
   fares : ∀ i, ‖poem i‖ ≤ (1:ℝ)^i*v
variable (P:Pulse X Y t)
abbrev bead (Q:Pulse X Y t)(x:Beam X):= showB Q.poem x
abbrev sees (Q:Pulse X Y t)(x:X):= ∑' i:ℕ, Q.poem (i+1) fun _=>x
def lux :ℝ:=1/16
def Lux (v:ℝ):Prop:=v≤lux
def glint:ℝ:=1/128
lemma lush : Lux 0:= by norm_num [lux,Lux]
lemma tintP :0<glint∧0<lux:=by norm_num [glint,lux]
namespace Pulse
include P
lemma cost : 0≤t:=by have h:= P.fares 0; simp only [pow_zero,one_mul] at h; exact (norm_nonneg _).trans h
lemma liftN (x:Beam X)(h:‖x‖ ≤ 1/4): ‖bead P x‖≤ t/2 := by
   exact (Beam.showN _ _ zero_le_one P.fares h (by norm_num)).trans_eq (by ring)
lemma liftD (x y: Beam X)(h:‖x‖≤1/4)(he:‖y‖ ≤1/4): ‖bead P x-bead P y‖ ≤ 2*t*‖x-y‖:=by simpa only [mul_one] using Beam.showD _ _ zero_le_one P.fares h (by norm_num) y he
lemma liftL (x:Beam X)(h:‖x‖≤1/4)(v:sun): read Y v (bead P x)= sees P (read X v x):= Beam.showL _ _ zero_le_one P.fares h (by norm_num) _
lemma seesD {x y:X}(hx:‖x‖≤1/4)(hy:‖y‖ ≤1/4): ‖sees P x-sees P y‖ ≤ 2*t*‖x-y‖:= by
   have hx':‖arm x‖≤1/4:=by rwa [armN]
   have hy':‖arm y‖ ≤1/4:=by rwa [armN]
   let v:sun:= ⟨0,by norm_num [sun]⟩; conv_lhs => rw [← armL v x,← P.liftL _ hx',← armL v y,← P.liftL _ hy',← map_sub]
   apply (Beam.price ..).trans ((liftD P _ _ hx' hy').trans_eq ?_)
   rw [show arm x-arm y=arm (x-y) from ?_,armN]; exact (map_sub (lp.singleContinuousLinearMap (E:=fun _:ℕ=>X) (𝕜:=ℝ) (p:=1) 0) x y).symm
-- if Poem full from center, recognizes
lemma earned (y:X){B:Y}(hP:HasSum (fun n=>P.poem n fun _=>y) (B)) (z:Y)(ht:P.poem 0 (fun _=>0)=z): sees P y=B-z:=by -- B implicit binder
  unfold sees; rw [← hP.tsum_eq,← Summable.sum_add_tsum_nat_add 1 hP.summable]; simp only [sum_range_one]; rw [show (fun _:Fin 0=>y)=(fun _:Fin 0=> (0:X)) from Subsingleton.elim _ _,ht]; abel
end Pulse
section table
-- beta relative ± prices.Loom
variable (n:ℕ)(A:Fin (n+1) → Type) [∀ i,NormedAddCommGroup (A i)][∀ i,NormedSpace ℝ (A i)][∀ i, CompleteSpace (A i)]
local notation "T"=> Fin (n+1)
local notation "j"=> Fin.last n
local notation "I"=> Fin n
abbrev Box := (T → Beam ℝ) × ((i:T)→ Beam (A i))
def prior (i:T):Finset I:= univ.filter fun k=>k.val< i.val
structure Rally where
   initB : Pulse ℝ (A j) glint
   beams i : Pulse (ℝ × A (Fin.succ i)) (A (Fin.castSucc i)) glint
   w : T → ℝ -- weight scaled
   feeB : T → ℝ
   wt : T → ℝ
   span : I → ℝ
   lum (i:I): Pulse (ℝ × A (Fin.succ i)) ℝ (span i)
   wPos i : 0<w i
   fee₁ i : 1≤ feeB i
   wtP i : ‖wt i‖ ≤ 1 -- sqrt²
   accounts (i:T): ∑ k ∈ prior n i, span k ≤ glint*w i
namespace Rally
variable {n A}(K:Rally n A) {U V : Box n A} {b:Beam ℝ}
def sprint (a:Beam ℝ):= brave (ContinuousLinearMap.mul ℝ ℝ) a a
lemma sprintN (a:Beam ℝ): ‖sprint a‖≤ ‖a‖*‖a‖:=by
 apply (braveN ..).trans; apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)); exact ContinuousLinearMap.opNorm_mul_le _ _ -- lemma
lemma sprintL (a:Beam ℝ) (v:sun): read ℝ v (sprint a)= (read ℝ v a)^2:= Eq.trans (harp v _ _ _) (pow_two _|>.symm)
lemma sprintD (a b:Beam ℝ)(ha:‖a‖≤lux)(hb:‖b‖≤lux): ‖sprint a-sprint b‖≤ 2*lux*‖a-b‖:=by
 rw [show sprint a-sprint b=brave (ContinuousLinearMap.mul ℝ ℝ) (a+b) (a-b) from ?_]
 apply (braveN ..).trans; exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (ContinuousLinearMap.opNorm_mul_le _ _)).trans (mul_le_mul_of_nonneg_right ((norm_add_le ..).trans (by linarith)) (norm_nonneg _))
 refine Beam.soul _ _ fun v=>?_; change read ℝ v (sprint a-sprint b)=read ℝ v _; rw [map_sub,sprintL,sprintL, harp,map_add,map_sub]; rw [ContinuousLinearMap.mul_apply']; ring
-- Advent plans
def runs (K:Rally n A) (U:Box n A): (i:T) → Beam (A i):= Fin.lastCases (bead K.initB (U.1 j)) (fun i:I=> bead (K.beams i) (lay (U.1 i.succ) (U.2 i.succ)))
def moveB (K:Rally n A) (U:Box n A)(i:I) := bead (K.lum i) (lay (U.1 i.succ) (U.2 i.succ))
def danceB (K:Rally n A) (b:Beam ℝ)(U:Box n A):Box n A:= ⟨fun i=>(K.feeB i)⁻¹ • ((K.w i)⁻¹ • (b-∑ k∈prior n i, K.moveB U k) - K.wt i • sprint (U.1 i)), runs K U⟩
variable (hb:∀ i, ‖b‖≤ lux/4*K.w i)(h:‖U‖ ≤ lux)(ht:‖V‖ ≤ lux)
include h
lemma perN (i:T) : ‖U.1 i‖ ≤lux∧ ‖U.2 i‖≤lux:= ⟨(norm_le_pi_norm _ _).trans ((norm_fst_le _).trans h),(norm_le_pi_norm _ _).trans ((norm_snd_le _).trans h)⟩
lemma layH (i:T): ‖lay (U.1 i) (U.2 i)‖≤ 1/4:= (layN ..).trans ((add_le_add (perN h i).1 (perN h i).2).trans (by norm_num [lux]))
include K
lemma runsN (i:T): ‖K.runs U i‖ ≤ lux:= Fin.lastCases (motive:=fun i=>‖K.runs U i‖≤lux) (by rw [runs, Fin.lastCases_last]; exact (K.initB.liftN _ ((perN h _).1.trans (by norm_num [lux]))).trans (by norm_num [lux,glint])) (fun i=>by rw [runs,Fin.lastCases_castSucc]; exact ((K.beams i).liftN _ (layH h _)).trans (by norm_num [glint,lux])) i
lemma sumN (i:T): ‖∑ k∈prior n i, K.moveB U k‖≤ glint*K.w i:= (norm_sum_le ..).trans ((sum_le_sum (fun k _=> ((K.lum k).liftN _ (layH h _)).trans (half_le_self (K.lum k|>.cost)))).trans (K.accounts i))
include hb
lemma angleN (i:T) : ‖(K.danceB b U).1 i‖≤ lux := by
    let a:= K.feeB i; let c:= K.w i; have ha:1≤ a:=K.fee₁ i; have hc:0<c:= K.wPos i; have hp:= hb i; have hf:= (perN h i).1
    unfold danceB; dsimp only; rw [norm_smul,norm_inv,Real.norm_of_nonneg (zero_le_one.trans ha)]
    apply (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ ha)).trans; apply (norm_sub_le ..).trans
    rw [norm_smul,norm_smul,norm_inv,Real.norm_of_nonneg hc.le]; calc
      _ ≤ (lux/4+glint)+lux*lux:= add_le_add ?_ ?_
      _ ≤ _:= by norm_num [lux,glint]
    · rw [inv_mul_le_iff₀ hc]; exact (norm_sub_le ..).trans (((add_le_add hp (K.sumN h i))).trans_eq (by ring))
    exact (mul_le_of_le_one_left (norm_nonneg _) (K.wtP i)).trans ((sprintN ..).trans (mul_le_mul hf hf (norm_nonneg _) (tintP.2.le)))
lemma danceN : ‖K.danceB b U‖≤lux:= max_le ((pi_norm_le_iff_of_nonneg tintP.2.le).mpr (K.angleN hb h)) ((pi_norm_le_iff_of_nonneg tintP.2.le).mpr (K.runsN h))
end Rally
end table
end YM.FullVolume.Amp
