import YM.MergeProof.North.Brick

/-! Cutoff matching geometry using a patch enlarged to cover the preceding schedule jump. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Matching
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Extra.Histories Extra.Trajectories Cells MergeProof MergeProof.Ribbons
open Push.Local YM.Extra.Multi YM.Push.GridApprox.Nil YM.Next.Rank YM.Next.Rank.Spindle YM.PhysicalNext.Repeat.Lotus Merge
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge} {n:Side} (C:Family G) (J j m p k N d:ℕ) (q:Side)
local notation "H"=> C.path
local notation "Rb"=> C.path.levels.budget
local notation "P"=> hands C p J
local notation "V'"=> Site (C.side J p)
local notation "E"=> MergeProof.Mix.camp C p J
local notation "S"=> C.S
variable (a:Site (C.side j p))
local notation "o"=> bites C J j p a
local notation "v"=> loops C j p a
local notation "t"=> (Rb k).B
def extra (A:Levels G)(q:Side)(k:ℕ):ℕ:=1024*q.val*(A.budget k).B
def patch (A:Levels G)(q:Side)(k:ℕ):ℕ:=extra A q k*(A.budget k).B
def topZone (A:Levels G)(q:Side)(k:ℕ):= (q.val:ℝ)*fuga A k
local notation "W"=> fuga C.path.levels k
variable (hk:k≤j)
include hk
lemma wide (hp:W/16≤ ‖C.S.place a‖)(hh:‖C.S.place a‖ ≤4*topZone C.path.levels q k) :
    t^2+1 ≤ separation (v k) 0 ∧ separation (v k) 0 ≤ patch C.path.levels q k :=by -- adapts Vert
    obtain ⟨h₁,h₂⟩:= normC C j p a
    let Z:= C.S.toDepth hk p; let B:= separation (v k) 0; let c:= Z.count.val; let y:= C.S.place a
    have hV: 2*separation a (Z.embed (v k))< c:= (by rw [vote C _ _ _ _ hk]; exact Station.midway _ (C.S.toDepth_odd hk p) _)
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
    show separation (loops C j p a k) 0 ≤1024*q.val*t*t
    suffices hu:(B:ℝ) ≤1024*q.val*(t:ℝ)*(t:ℝ) by exact_mod_cast hu
    have hC : (B:ℝ)≤ 1+512*(t:ℝ)^2*q.val:= by
        apply le_of_mul_le_mul_left (a:=C.S.a k) _ hp'; change ‖y‖ ≤4*((q.val:ℝ)*(128*((t:ℕ):ℝ)^2*C.S.a k)) at hh; linarith only [hR,hh]
    have hx:1≤ (q.val:ℝ):=by exact_mod_cast q.pos
    have hv:= mul_le_mul_of_nonneg_right hx (sq_nonneg (↑(t):ℝ)); change (B:ℝ) ≤ _; nlinarith only [hC,hb,hv]
omit hk
lemma radii (hG:G.Simple)(m:ℕ): fuga C.path.levels m ≤ topZone C.path.levels (C.S.block m) (m+1):=by
    unfold fuga topZone fuga; set A:= C.path.levels
    have h:A.clock.hatBeta m ≤ A.clock.hatBeta (m+1):= by
         rw [Extra.Iteration.block_beta]; unfold YM.Pressure.betaF; exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos hG).le (Real.log_nonneg (by exact_mod_cast (A.S.block m).pos)))
    have hx : 1 < A.clock.hatBeta m := A.fits.delayed m
    have ht : (A.budget m).B ≤ (A.budget (m+1)).B :=by
        refine Nat.ceil_mono ?_; change ((Real.log (A.clock.hatBeta m))^(2:ℕ)) ≤ _
        exact pow_le_pow_left₀ (Real.log_nonneg hx.le) (Real.log_le_log (zero_lt_one.trans hx) h) _
    rw [C.S.a_step]; have hL : (↑(C.S.block m).val:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (C.S.block m).pos.ne'
    rw [show (↑(C.S.block m).val:ℝ) * (128 * _ * (C.S.a m/ (C.S.block m).val))=128*((Rb (m+1)).B:ℝ)^2*C.S.a m from by field_simp [A]; ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ht) _) (by norm_num)) (C.S.a_pos _).le
end YM.MultipleContact.Matching
