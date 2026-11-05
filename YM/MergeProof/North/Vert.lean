import YM.MergeProof.North.Prax
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories  Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge} {n:Side} (C:Family G) (J j m p k N d:ℕ)
set_option quotPrecheck false
local notation "H"=> C.path
local notation "Rb"=> C.path.levels.budget
local notation "P"=> hands C p J
local notation "V'"=> Site (C.side J p)
local notation "E"=> Mix.camp C p J
local notation "S"=> C.S
variable (a:Site (C.side j p))
local notation "o"=> bites C J j p a
local notation "v"=> loops C j p a
local notation "t"=> (Rb k).B
local notation "y"=> (C.S.place a)
def fuga (A:Levels G)(k:ℕ):=128*((A.budget k).B:ℝ)^2 * A.S.a k
def polls (A:Levels G)(k:ℕ):=1024*((A.budget k).B)^2
local notation "X"=> polls C.path.levels k
local notation "W"=> fuga C.path.levels k
lemma locC (i) : |y i| = C.S.a j *((lift a i).natAbs:ℝ):=by change |C.S.a j*((lift a i):ℝ)|=_; rw [abs_mul,abs_of_pos (C.S.a_pos j),← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] -- edit
lemma normC : C.S.a j * (separation a 0) ≤ ‖y‖ ∧ ‖y‖≤ 2*C.S.a j * (separation a 0):=by
    unfold separation; rw [sub_zero]; have hv : (‖y‖)^2=∑ i:Axis, (|y i|)^ (2:ℕ):=by rw [EuclideanSpace.real_norm_sq_eq]; simp only [sq_abs]
    let p':ℝ:= C.S.a j*pdist a; have hp:0 ≤ p':=mul_nonneg (C.S.a_pos j).le (Nat.cast_nonneg _)
    have ht:(∑ i:Axis, (|y i|)^ (2:ℕ)) ≤ ∑ i:Axis, p'^ (2:ℕ):= Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (abs_nonneg _) (by rw [locC]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast component_le a i) (C.S.a_pos _).le) _)
    constructor
    · obtain ⟨i,hi,he⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) (f:=fun i:Axis=>(lift a i).natAbs) Finset.univ_nonempty; have he:pdist a= (lift a i).natAbs:=he
      rw [he,← locC]; simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le y i) -- edit
    have hh:(∑ i:Axis, p'^(2:ℕ))=4*p'^2:=by simp -- edit
    rw [hh] at ht; rw [mul_assoc]; change ‖_‖ ≤ 2*p'; nlinarith only [hp,hv,ht]
variable (hk:k≤j)
include hk
lemma maximizing (hp:W/16≤ ‖C.S.place a‖)(hh:‖C.S.place a‖ ≤4*W) :
    t^2+1 ≤ separation (v k) 0 ∧ separation (v k) 0 ≤ X:=by
    obtain ⟨h₁,h₂⟩:= normC C j p a
    let Z:= C.S.toDepth hk p; let B:= separation (v k) 0; let c:= Z.count.val
    have hV: 2*separation a (Z.embed (v k))< c:= (by rw [vote C _ _ _ _ hk]; exact midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (v k)) 0 = c*B:=by nth_rw 1 [show _= v k from rfl]; nth_rw 1 [show (0:Site (C.side j p))=Z.embed 0 from Z.root.map_zero.symm]; exact Station.both ..
    have hL:= separation_triangle a (Z.embed (v k)) 0; have hq:= separation_triangle (Z.embed (v k)) a 0; rw [separation_comm (Z.embed (v k)) a,hz] at hq; rw [hz] at hL
    have hy : C.S.a j*c=C.S.a k:= C.S.embeds_scale Z; have ha:= C.S.a_pos j; have hp':= C.S.a_pos k; have hb:1 ≤ ((t:ℕ):ℝ):=by exact_mod_cast (Rb k).B_pos
    constructor
    · have hs: C.S.a j*(separation a 0:ℝ) ≤ C.S.a k*(B+1:ℝ):=by
         rw [← hy]; refine (mul_le_mul_of_nonneg_left (show (separation a 0:ℝ)≤ ((c*B+c:ℕ):ℝ) from ?_) ha.le).trans_eq (by push_cast; ring)
         exact_mod_cast (show separation a 0 ≤ c*B+c by omega)
      have hv : (128*(t:ℝ)^2*C.S.a k)/16 ≤ 2*(C.S.a k*(B+1:ℝ)):= hp.trans (h₂.trans (le_trans (le_of_eq (mul_assoc ..)) (mul_le_mul_of_nonneg_left hs zero_le_two)))
      have ht:8*((t:ℕ):ℝ)^2 ≤ 2*((B:ℝ)+1):= by apply le_of_mul_le_mul_right (a:=C.S.a k) _ hp'; linarith only [hv]
      exact_mod_cast (show ((t:ℕ):ℝ)^2+1≤ (B:ℝ) from by nlinarith only [ht,hb])
    have hR: C.S.a k*B ≤ C.S.a k+‖y‖:= by
       rw [← hy,mul_assoc]; have hx: ((c*B:ℕ):ℝ)≤ c+(separation a 0:ℝ):= by exact_mod_cast (show c*B≤ c+separation a 0 by omega)
       rw [Nat.cast_mul] at hx; exact (mul_le_mul_of_nonneg_left hx ha.le).trans (by rw [mul_add]; linarith only [h₁])
    change B ≤ 1024*t^2; suffices hu:(B:ℝ)≤1024*(t:ℝ)^2 by exact_mod_cast hu
    have hC : (B:ℝ)≤ 1+512*(t:ℝ)^2:= by
        apply le_of_mul_le_mul_left (a:=C.S.a k) _ hp'; change ‖y‖ ≤4*(128*((t:ℕ):ℝ)^2*C.S.a k) at hh; linarith only [hR,hh]
    nlinarith only [hC,hb]
end
end YM.MergeProof.Ribbons
