import YM.FullVolume.Fields.Timber
import YM.Push.CORRECTED_COLUMNS.Grows
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Eves
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Marker Extra.Histories Ac Bid Local
open Planned.GuardedAtom MergeProof MergeProof.Accent MergeProof.Menu Motion Extra.Multi Next.Rank Next.Rank.Spindle
open Extraction Difference Extraction.Lease Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} (A:Levels G){m n p:ℕ}
local notation "S"=> A.S
def ancestor (s:Schedule)(x:Points n):Prop:= ∃ k:ℕ, x=tag (s.a k) (address (s.a k) x)
lemma dense (s:Schedule)(n:ℕ): Dense (setOf (ancestor (n:=n) s)):=by
    intro x; apply mem_closure_of_tendsto (chosen («S»:=s) x); refine Eventually.of_forall (fun i=>?_); refine ⟨i,?_⟩; rw [address_matched (s.a_pos i)]
lemma lateAnch (x:Points n)(h:ancestor A.S x):∀ᶠ i in atTop,x=tag (A.S.a i) (address (A.S.a i) x):=by
    obtain ⟨i,hi⟩:= h
    filter_upwards [eventually_ge_atTop i] with k hk; induction k,hk using Nat.le_induction with
    | base=> exact hi
    | succ k hk ih=>
       let T:= A.S.block k; let t:= A.S.a (k+1); let z:=address (A.S.a k) x; let Q j:= T.val • z j
       have hx: tag t Q=x:= by
          rw [ih]; refine PiLp.ext fun i=> PiLp.ext fun j=> ?_ ; change t* ((T.val • z i) j:ℝ)=(S).a k * ((z i j):ℤ)
          rw [A.S.embeds_scale (A.S.oneStep k 0)|>.symm]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; change t * ((T.val:ℝ)*_)=t* T.val*_ ; ring
       exact hx ▸ (show tag t Q = tag (A.S.a (k+1)) (address (A.S.a (k+1)) (tag t Q)) from by rw [show A.S.a (k+1)= t from rfl,address_matched ((S).a_pos (k+1))])
-- full Schedule.B beta may be under .Growth.True. non Project weights. Need ensure n-point copy.Back.X and motion.
lemma turns (m:ℕ) (j:Points n)(hj:j=tag (A.S.a m) (address (A.S.a m) j)): (A.S.oneStep m p).embed ∘ ((wrap (A.S.side m p)) ∘ address (A.S.a m) j)= (wrap (A.S.side (m+1) p)) ∘ address (A.S.a (m+1)) j:=by
    let T:=A.S.oneStep m p; let f:= address (A.S.a m) j; let s:=A.S.a (m+1); let F i:= T.count.val • f i
    have h: tag s F=j:=by
        rw [hj]; refine PiLp.ext fun i=> PiLp.ext fun k=>?_ ; change s*((T.count.val • f i) k:ℝ)=(A.S.a m)* ((f i k):ℤ)
        rw [A.S.embeds_scale T|>.symm]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul, Int.cast_natCast]; change s*((T.count.val:ℝ)*_)=s*T.count.val*_; ring
    rw [show address s j=F from ((congr_arg (address _) h).symm.trans (address_matched (A.S.a_pos (m+1)) F))]; exact funext fun i=> T.embed_wrap _
lemma price (h:G.Simple): Tendsto (fun m=> (A.S.a m)* ((A.clock.coverSize m:ℝ)^2)) atTop (𝓝 0):=by
    obtain ⟨k,hk⟩:= eventually_atTop.mp (Push.Corrected.Grows.walls A h 2); let f m:= A.S.a m* (A.clock.coverSize m:ℝ)^2; let p:ℝ:= 2/3
    have hp(i):0≤ f i:= mul_nonneg (A.S.a_pos i).le (sq_nonneg _)
    have he(i:ℕ): f (k+i) ≤ p^i * f k:=by
        induction i with
        | zero=> simp only [Nat.add_zero,pow_zero,one_mul]; rfl
        | succ i hi=>
           let n:=k+i; let L:=A.S.block n; have hl:(3:ℝ) ≤ L.val:= by exact_mod_cast A.S.block_large _
           rw [pow_succ']; refine le_trans (b:=p*f n) ?_ ((mul_le_mul_of_nonneg_left hi (by unfold p; norm_num)).trans_eq (mul_assoc p _ _).symm); change f (n+1)≤p*f n; unfold f; have hn:(A.clock.coverSize (n+1):ℝ)^2 ≤ 2*(A.clock.coverSize n:ℝ)^2:= by exact_mod_cast hk n (Nat.le_add_right k i)
           refine (mul_le_mul (b:=A.S.a n/3) ?_ hn (sq_nonneg _) (div_nonneg (A.S.a_pos _|>.le) (by norm_num))).trans_eq (by unfold p; ring); rw [A.S.a_step]; exact div_le_div_of_nonneg_left (A.S.a_pos _|>.le) (by norm_num) hl
    apply PhysicalNext.Repeat.Lark.Pith.high k; refine squeeze_zero (g:=fun i=>p^i *f k) (fun i=>hp _) (fun i=>by
        change f (i+k)≤ _
        rw [Nat.add_comm i k]; exact he i) ?_
    have h:0 ≤ p:=by norm_num [p]
    simpa using! (tendsto_pow_atTop_nhds_zero_of_lt_one h (show p<1 from (by norm_num [p]))).mul_const (f k)
lemma positions (x:Points n)(hw: x ∈ NoHit A.S p n)(h:ancestor A.S x)(hG:G.Simple):∀ᶠ m in atTop, let f:= address (A.S.a m) x; let a:Fin n→Site (A.S.side m p):= wrap _ ∘ f
    ∀ i j,i≠j → (A.budget m).B^2 ≤ separation (a i) (a j):=by
    obtain ⟨r,hp,hS⟩:= Gaps.some A.S p (isCompact_singleton (x:=x)) (Set.singleton_subset_iff.mpr hw); have ht:= hS x (Set.mem_singleton _)
    filter_upwards [(price A hG).eventually (ge_mem_nhds hp), lateAnch _ x h] with m hm h a b i j hj
    have hh:= Gaps.gridSeparation A.S (p:=p) (wrap _ ∘ address (A.S.a m) x) rfl (by rwa [← h] : Gaps.someFine A.S p r (tag (A.S.a m) (address (A.S.a m) x))) _ _ (Ne.symm hj)
    have he:= le_of_mul_le_mul_left ((show A.S.a m* _ ≤ r from hm).trans hh) (A.S.a_pos m); change A.clock.coverSize m^2≤_; exact_mod_cast he
end YM.FullVolume.Eves
#print axioms YM.FullVolume.Eves.positions
#print axioms YM.FullVolume.Eves.turns
#print axioms YM.FullVolume.Eves.dense
