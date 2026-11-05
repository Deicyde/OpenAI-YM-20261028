import YM.UVExtension.Swell.Paddles
import YM.MergeProof.North.Lauder
/-!
 # Grid scale tools. Everything will be uniform over layouts and rays inside cylinders.
   Not freezing the grid J before choosing mesh here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tide
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable (S:Schedule)
lemma delay (m:ℕ): (m:ℝ)* Real.log 3≤ S.scale m:=by
    induction m with
    | zero=>simp
    | succ i ih=> rw [S.scale_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul]; exact add_le_add ih (Real.log_le_log (by norm_num) (by exact_mod_cast S.block_large i))
variable {G:Gauge} (A:Levels G)
open Stock
private lemma astep (i:ℕ): ((A.clock.J i):ℝ) ≤ (A.clock.J 0:ℝ)+ A.S.scale i/Real.log 3:=by
    have hp: A.clock.J i≤ A.clock.J 0+i:=by
       induction i with
       | zero=> rfl
       | succ n ih=> exact (A.fits.stepSlow _).trans ((Nat.add_le_add_right ih _).trans_eq (Nat.add_assoc ..))
    exact le_trans (show (A.clock.J i:ℝ)≤ (A.clock.J 0:ℝ)+(i:ℝ) by exact_mod_cast hp) (by gcongr; exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr (delay ..))

lemma ocean (r:ℕ): ∀ᶠ j in atTop, ∀ k≥j, 4*A.S.scale j ≤ A.S.scale k→ GridApprox.room A j k r := by
   let p(j):ℝ:= r+30*((A.clock.J j:ℝ)+5); let Q:= A.S
   have hF : ∀ᶠ k:ℕ in atTop, 2*p k ≤ expS Q (1/2) k:=by
       let f(k:ℕ):ℝ:= (A.clock.J 0:ℝ)+5+r/30; -- type casts Nat? edit
       let g x:= Real.exp ((1/2)*x); have hp : Tendsto g atTop atTop:= Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<1/2))
       let H(x:ℝ):= r+30*((A.clock.J 0:ℝ)+x/Real.log 3+5)
       have hx : Tendsto (fun x:ℝ=> x / g x) atTop (𝓝 0):=by
          simpa only [pow_one,g] using (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
       have he : Tendsto (fun x=> 2*H x /g x) atTop (𝓝 0):=by
          let z:= r+30*((A.clock.J 0:ℝ)+5); have ht : Tendsto (fun x=> z/g x) atTop (𝓝 0):= tendsto_const_nhds.div_atTop hp; have hg : Tendsto (fun x:ℝ=> 2*(z/g x+(x/g x)*(30/Real.log 3))) atTop (𝓝 0):=by simpa using! (ht.add (hx.mul_const (30/Real.log 3))).const_mul 2
          convert! hg using 1; ext; unfold H z; ring
       filter_upwards [(he.comp Q.divergent).eventually (ge_mem_nhds zero_lt_one)] with i hi
       refine le_trans (mul_le_mul_of_nonneg_left (show p i ≤ H (Q.scale i) from add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_left (astep A i) _) (by positivity)) _) zero_le_two) ?_; simpa only [expS,one_mul] using (div_le_iff₀ (Real.exp_pos _)).mp (show 2*H (Q.scale i)/g _ ≤ 1 from hi)
   obtain ⟨t,ht⟩:= eventually_atTop.mp hF; filter_upwards [eventually_ge_atTop t,Q.divergent.eventually_gt_atTop 0] with i hi he k hk hX
   let x:= Q.scale k; let b:= Q.scale i; have he0: b>0:= he; have hv:4*b ≤ x:= hX
   unfold GridApprox.room GridApprox.tail; change 2*(Q.a k*_+30*Q.a k*_ ) < Q.a i; rw [show 2*(Q.a k*(r:ℝ)+30*Q.a k*((A.clock.J k:ℝ)+5))= Q.a k*(2*p k) by unfold p;ring]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (ht k (hi.trans hk)) ((Q).a_pos _).le); change Q.a k*Real.exp (1/2*x)<Q.a i
   rw [Stock.a_log, Stock.a_log,←Real.exp_add]; exact Real.exp_lt_exp.mpr (show -x+1/2*x < -b by linarith only [hv,he0])

lemma clearance (C:Family G)(d N k J n:ℕ) (h:Vintage.YM.Family.Makes C) (hz:J ≤ k) (hq:k≤ N)(he:GridApprox.room C.path.levels J k (lensScope C d)) (F:C.label d): Interior ((Cells.center C.S n (hz.trans hq) 0).chamber 0) (C.O N n F 0):=by
    let r:= C.S.toDepth (hz.trans hq) n; let B:= stencilRadius C d
    have hp:2*B<r.count.val :=by -- replace
       have hs := C.S.embeds_scale r; have hx : 2*C.S.a N*(B:ℝ)<C.S.a J:=by
          unfold GridApprox.room at he; have hy:= GridApprox.tail_pos C.path.levels k; apply lt_of_le_of_lt _ he
          rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ zero_le_two; exact (mul_le_mul (C.S.strictAnti.antitone hq) (Nat.cast_le.mpr (show B ≤ lensScope C d from Nat.le_add_right ..)) (Nat.cast_nonneg _) (C.S.a_pos _|>.le)).trans (le_add_of_nonneg_right hy.le)
       change C.S.a N* _ = _ at hs; exact_mod_cast (show ((2*B:ℕ):ℝ) < (r.count.val:ℝ) from lt_of_mul_lt_mul_left (by rw [hs]; push_cast; linarith only [hx]) (C.S.a_pos _|>.le))
    have hc: (C.O N n F 0)= candidate C N n d ((C.factory d N n).terminal.symm F):= rfl
    have ht: Interior (window (anchor C.S n (hz.trans hq) 0) B) (C.O N n F 0):=by
       rw [show anchor C.S n (hz.trans hq) 0=0 from r.root.map_zero,hc]; exact Vintage.YM.Push.GridApprox.candidate_fits C h N n d _
    exact ht.enlarges (window_fits C.S n _ _ B hp)
end YM.UVExtension.Tide
