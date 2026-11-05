import YM.UVExtension.Camp.Motto
import YM.UVExtension.Oriel.Dial
import Mathlib.Topology.MetricSpace.Contracting

/-! # On any funded coupling Schedule. Cart is only an analytic engine,
    not assuming paths terminate; analytic curves & finite beta argument total
    all cutoffs. The Occupied Cart's trajectory must still be identified with
    the physical real solution. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Oriel.Charted Push Push.AbsoluteSums Metric RG.Shoot Complex
open scoped Topology ContDiff Matrix.Norms.Frobenius NNReal
variable {G : Gauge} (h:G.Simple)(T:Levels G)
variable (N:ℕ)(X : ℕ→Type)[∀ i,NormedAddCommGroup (X i)] [∀ i,NormedSpace ℂ (X i)]
-- consider pad.Heq arbitrary >N. Couplings offsets β relative to a real row *not changed through step*. startup on dummy x=0.
structure Seal {A E:Type}[NormedAddCommGroup A][NormedSpace ℂ A][NormedAddCommGroup E][NormedSpace ℂ E] (H:A→E)(R:ℝ):Prop where
   bumps : Bumps Grip H
   rises (x:A) : x∈Grip→ ‖H x‖≤R
   amounts (x:A): x∈Grip →∀ y∈Grip, ‖H x-H y‖ ≤ R*‖x-y‖
structure Cart where
    headA : ℂ × X N → X N
    car i : i<N → ℂ × X (i+1) → X i
    gain i : i<N → ℂ × X (i+1) → ℂ
    ace : Seal headA soft
    cargo (i) (hi:i<N): Seal (car i hi) soft
    coin i (hi:i<N): Seal (gain i hi) (worth T (i+1))

abbrev PlotN (N:ℕ):= Fin (N+1)→ℂ
abbrev Harbor (N:ℕ):Set (PlotN N):= closedBall 0 rad
namespace Cart
-- z extension arbitrary
variable (V : Cart T N X)

def play (z:PlotN N) (i:ℕ)(hi:i≤N): X i:= Nat.decreasingInduction (motive:=fun i _=> X i) (fun j hj x=> V.car j hj (z ⟨j+1,Nat.lt_add_one_iff.mpr hj⟩,x)) (V.headA (z ⟨N,Nat.lt_succ_self N⟩,0)) hi

def node (z:PlotN N)(i:ℕ)(hi:i≤N):= z (⟨i,Nat.lt_add_one_iff.mpr hi⟩: Fin (N+1))
def pivot (z:PlotN N)(i:ℕ)(hi:i≤N): ℂ × X i:= (node N z i hi,V.play T N X z i hi)
lemma roof (z:PlotN N): V.play T N X z N le_rfl=V.headA (node N z N le_rfl,0):=Nat.decreasingInduction_self ..
lemma edge (z:PlotN N)(i:ℕ)(h:i<N): V.play T N X z i h.le = V.car i h (pivot T N X V z (i+1) h) := Nat.decreasingInduction_succ_left _ _ _ _

variable {z v:PlotN N}(hx:z∈ Harbor N)(hv:v∈Harbor N)

include hx in
lemma parts (i)(hi:i≤N): |(node N z i hi).re| ≤ rim:= by
    have hp(i): ‖z i‖≤ rad:= (norm_le_pi_norm z i).trans (mem_closedBall_zero_iff.mp hx); exact ((abs_re_le_norm _).trans (hp _)).trans (by norm_num [rad,rim]) -- include
include hx
omit [∀ i,NormedSpace ℂ (X i)] in
private lemma introP : (node N z N le_rfl,(0:X N))∈ Grip:=by
    refine mem_ball_zero_iff.mpr ?_; exact max_lt ((norm_le_pi_norm z _).trans_lt ((mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num [rad,rim]))) (norm_zero.trans_lt (by norm_num [rim]))
lemma seats (i)(hi:i≤N):‖play T N X V z i hi‖≤ soft ∧ V.pivot T N X z i hi∈Grip:=by
    have hv(i)(hi:i≤N)(h : ‖play T N X V z i hi‖ ≤ soft): ‖play T N X V z i hi‖ ≤ soft ∧ V.pivot T N X z i hi ∈ Grip (X:=ℂ × X i):= ⟨h,mem_ball_zero_iff.mpr (max_lt ((norm_le_pi_norm z (⟨i,Nat.lt_add_one_iff.mpr hi⟩:Fin (N+1))).trans_lt ((mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num [rad,rim]))) (h.trans_lt (by norm_num [soft,rim])))⟩ -- cannot infer pair
    induction hi using Nat.decreasingInduction with
    | self=> apply hv; rw [roof]; exact V.ace.rises _ (introP N X hx)
    | of_succ i hi ih=> apply hv; rw [edge T N X V z i hi]; exact (V.cargo i hi).rises _ ih.2
include hv
lemma sharing (i)(hi:i≤N): ‖pivot T N X V z i hi-pivot T N X V v i hi‖≤‖z-v‖:= by
    have he (i hi): ‖node N z i hi-node N v i hi‖≤‖z-v‖:= norm_le_pi_norm (z-v) _
    induction hi using Nat.decreasingInduction with
    | self=>
      unfold pivot; simp only [roof]; refine max_le (he N le_rfl) ?_
      apply le_trans (V.ace.amounts _ (introP N X hx) _ (introP N X hv))
      exact (mul_le_mul_of_nonneg_left (max_le (he N le_rfl) (by simp)) (by norm_num [soft,rim])).trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [soft,rim]))
    | of_succ i hi ih=>
      unfold pivot; rw [edge T N X V z i hi, edge T N X V v i hi]; apply max_le (he _ hi.le)
      exact ((V.cargo i hi|>.amounts _ (V.seats T N X hx (i+1) hi).2 _ (V.seats T N X hv (i+1) hi).2).trans (mul_le_mul_of_nonneg_left ih (by norm_num [soft,rim]))).trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [soft,rim]))
omit hx hv
lemma music (i)(hi:i≤N): Bumps (Harbor N) (fun v=> play T N X V v i hi):= by
   intro S g hs he hg; have hV i hi:DifferentiableOn ℂ (fun x=> node N (g x) i hi) S:=fun x hx=> (differentiableWithinAt_pi.mp (hg _ hx)) _
   induction hi using Nat.decreasingInduction with
   | self => simp_rw [roof]; exact V.ace.bumps S _ hs (fun x hx=> introP N X (he hx)) ((hV N le_rfl).prodMk (differentiableOn_const _))
   | of_succ i hi ih=> simp_rw [edge T N X V _ i hi]; exact (V.cargo i hi).bumps S _ hs (fun x hx=> (V.seats T N X (he hx) _ hi).2) ((hV _ _).prodMk ih)

def tally (z: PlotN N) (i:ℕ):ℂ := if h:i<N then V.gain i h (pivot T N X V z _ h) else 0
lemma bills (i:ℕ): Bumps (Harbor N) (fun z=> tally T N X V z i):=by
   unfold tally; split
   next hi=>
     intro S g hs he hg
     let x(z: PlotN N):=(pivot T N X V z (i+1) hi)
     exact (V.coin i hi).bumps S (fun z=> x (g z)) hs (fun z hz=> (V.seats T N X (he hz) _ hi).2) ((DifferentiableOn.prodMk (f₁:=fun z=> node N (g z) (i+1) hi) (fun z hz=> differentiableWithinAt_pi.mp (hg z hz) _) (V.music T N X _ hi S _ hs he hg)))
   exact bumps _ _ (differentiableOn_const _)
include hx
lemma rates (i:ℕ) (hi:i<N): ‖tally T N X V z i‖≤ worth T (i+1):=by rw [tally,dif_pos hi]; exact (V.coin i hi).rises _ (V.seats T N X hx _ hi).2

include hv
lemma costs (i:ℕ) (hi:i<N): ‖tally T N X V z i-tally T N X V v i‖≤ worth T (i+1)*‖z-v‖:=by
 rw [tally,dif_pos hi,tally,dif_pos hi]; exact ((V.coin i hi).amounts _ (V.seats T N X hx _ hi).2 _ (V.seats T N X hv _ hi).2).trans (mul_le_mul_of_nonneg_left (V.sharing T N X hx hv _ hi) (worth_pos T _).le)
end Cart
end YM.UVExtension.Camp
