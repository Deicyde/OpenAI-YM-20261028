import YM.OPE.Prices.Stock
import YM.OPE.Sweep.Net
import YM.MergeProof.North.Burrough
/-! # Hall receipts for transporting centers in the sweep.

Uses the halo gate bought for this family after Rolls choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Filter Function Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open scoped Topology BigOperators
variable {G:Gauge}{C:Family G}{ι κ : Type*} {l : Filter ι} {f : Filter κ} {T : ι→ℝ} {a b c : ℝ}
variable {S : Schedule} {m k : ι→ℕ}
set_option quotPrecheck false
local notation "P'"=> C.path.levels
local notation "Λ" => C.S.scale
local notation "δ" => renal C.path.levels

lemma bought (hG:G.Simple) (h: HaloGate C.path.levels) (N : ℕ) (hn:0<N): Note C.S (fun i=> license C.path δ N (carpet C.path i) (i+1)) 0:=by
    let x i:= ((P'|>.budget (i+1)).supportExponent+1/2) * carpet C.path i
    have hp : Note C.S (fun i=> Real.exp (x i)) 0:=by
       refine ⟨fun i=> Real.exp_pos _,?_⟩; simp_rw [Real.log_exp]
       have he:Tendsto (fun i=>16*(Real.sqrt (C.path.levels.clock.hatBeta i)/Λ i)) atTop (𝓝 0):= by simpa only [mul_zero] using! ((whence C hG).const_mul 16)
       apply squeeze_zero' _ _ he
       · exact Eventually.of_forall fun i=>div_nonneg (mul_nonneg (add_nonneg (P'|>.budget (i+1)).exponent_pos.le (by norm_num)) (Nat.cast_nonneg _)) (Shoot.scale_nn _ _)
       filter_upwards with i; rw [← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (Shoot.scale_nn _ _); let v:= haloUnits (C.S.block i) (P'|>.budget i).B (P'|>.budget (i+1)).B
       calc _ ≤ 16*(( (P'|>.budget (i+1)).supportExponent+1) * v):= by unfold x carpet; push_cast; rw [mul_left_comm _ (16:ℝ)]; gcongr; norm_num
            _ ≤ _:= mul_le_mul_of_nonneg_left (h i) (by norm_num)
    have hr := (mintN C hG).1.scales C.path.levels.fits.mesh
    unfold license; apply ((((hr.splits (Note.notes C.S (N:ℝ) (by positivity))).mills hr).splits hp).swapP (by norm_num))

/-- Buy opacity toll through arbitrarily many intermediate buffer levels with a
uniform subpower expense. (`fee` scheduled here is subpower-small and can be used
as often as the fixed number of group operations requires.) -/
private lemma most {u:ℕ→ℝ}(h: Note S u 0) : ∃ v:ℕ→ℝ, Note S v 0 ∧ (∀ i,v i≤1) ∧ ∀ i j,j ≤ i→ v i ≤ u j:=by
    let w : ℕ→ℝ:= fun k=> Nat.rec (min (u 0) 1) (fun i x=> min x (u (i+1))) k
    have he(i):w (i+1)=min (w i) (u (i+1)):=rfl
    have hx(i):w i≤u i:=by cases i; exact min_le_left ..; exact min_le_right ..
    have hv:Antitone w:= antitone_nat_of_succ_le fun i=> min_le_left ..
    have hF(i):w i≤1:= (hv (Nat.zero_le _)).trans (show w 0≤1 from min_le_right ..)
    have hp(i):0<w i:=by
       induction i with
       | zero=> exact lt_min (h.pos _) zero_lt_one
       | succ i ih=> exact lt_min ih (h.pos _)
    refine ⟨w, ⟨hp,tendsto_order.mpr ⟨fun r hr=>?_,fun r hr=>?_⟩⟩, hF, fun i j hij=> (hv hij).trans (hx _)⟩
    · obtain ⟨t,ht,ht'⟩:= exists_between hr
      obtain ⟨k,hk⟩:= eventually_atTop.mp ((S.divergent.eventually_gt_atTop 0).and (h.pitch.eventually (lt_mem_nhds ht')))
      let y:= w k; have hU i(hi:k ≤ i): t < Real.log (u i) / S.scale i:= (hk i hi).2
      have hV i(hi:k ≤ i): min y (Real.exp (t*S.scale i)) ≤ w i:= by
          induction i,hi using Nat.le_induction with
          | base=> exact min_le_left ..
          | succ i hi ih=>
             have hg:=hi.trans i.le_succ; rw [he]; refine le_min ?_ ?_; exact (min_le_min_left y (Real.exp_monotone (mul_le_mul_of_nonpos_left ((scale_mono _).monotone i.le_succ) ht'.le))).trans ih
             exact (min_le_right ..).trans ((Real.le_log_iff_exp_le (h.pos _)).mp ((le_div_iff₀ (hk (i+1) hg|>.1)).mp (hU _ hg).le))
      filter_upwards [eventually_ge_atTop k, ((Note.bell_exp S t).outweigh (Note.notes S y (hp k)) ht')] with i hi hf
      apply lt_of_lt_of_le ht; rw [le_div_iff₀ (hk i hi|>.1), Real.le_log_iff_exp_le (hp i)]; exact min_eq_right hf ▸ hV i hi
    filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi using lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (hp i).le (hF i)) hi.le) hr

lemma halls (hG:G.Simple) (h: HaloGate C.path.levels) (N:ℕ)(hN:0<N): ∃ v:ℕ→ℝ, Note C.S v 0 ∧ (∀ i,v i≤1) ∧ ∀ i j,j ≤ i→ v i ≤ license C.path δ N (carpet C.path j) (j+1):=
    most (bought hG h N hN)
lemma height0 {v:ℕ→ℝ} (h:Note S v 0)(hh:Height S l T m a) : RateIs l T (fun i=> v (m i)) 0:=by simpa only [zero_mul] using Columns.rescale h hh.grows hh.pace
lemma gainRate (d:ℕ)(hm:Height C.S l T m a)(hk:Height C.S l T k b) :
     RateIs l T (fun i=> gainChart C.path (m i) (k i)) (1/8*(a-b)) ∧ RateIs l T (fun i=> ‖alto C.path (k i) d‖) (d*b):=by
    refine ⟨RateIs.exp' (( (hm.pace.sub hk.pace).const_mul (1/8:ℝ)).congr fun i=>?_ ),?_⟩
    · ring -- possibly timeout
    simp_rw [alto_norm]; exact ((hk.mesh.power d).inv).swap (by ring)
lemma flyRate (hG:G.Simple)(hk:Height C.S l T k b)(d:ℕ): RateIs l T (fun i=> (fly C.path.levels d) (k i)) 0:=by
    unfold fly fog; exact ((height0 (hut C hG) hk|>.power (winter G d)).inv).swap (by simp)
end YM.OPE
