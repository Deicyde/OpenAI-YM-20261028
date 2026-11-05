import YM.RG08.Creek.Reef
/-! # E capacity capture integrated fixed $D$ on profiles. Full W receipts with unused widths. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Summit Wings High Pill Taste Run PowerSeries Harvest MeasureTheory
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{X:Chain}{m N j i e E r D t k:ℕ}{R C w v A B:ℝ}{a b:I→ℕ}{p:List I}{ν:G.ColorIndex}{D':ChartRatio G}
section charges
-- fixed Halo. compact address ≤R accepted.
def haloR (D R:ℝ):ℕ:= circleP D R 1+4
lemma steps_z {D:ℕ}{φ:I→ Profile D}{x: Rest} (hp:∀ j:I,Spatial (φ j).val ((spanP X k i)*C))(h: 0≤ C): cope X k i φ ((spanP X k i) • x.val) R ⊆ Fintype.piFinset (fun _=> Lattice.box (haloR C R)) := by
   intro z hv
   let a:=spanP X k i; have he:0<a:=spanP_pos ..
   have ht : haloR C R=circleP (spanP X k i*C) R a+4:= by unfold haloR circleP; rw [div_one,mul_div_cancel_left₀ C he.ne']
   rw [ht]; exact Fintype.mem_piFinset.mpr fun j=> blush_ring (φ j) _ C h (hp j) (Fintype.mem_piFinset.mp hv _)
lemma sizes_v (i:Cover)(h:i∈ Lattice.box t): size i ≤ 4*t:= by
    have hp (j:Axis): (i j).natAbs ≤ t:=by obtain ⟨hv,H⟩:=box_test.mp h; have he:= hv j; have hk:=H j; omega
    apply le_trans (Finset.sum_le_sum (s:=univ) (fun i hi=>hp i)) (by simp [Axis])
def ketCost (I:Type)[Fintype I][DecidableEq I](v R:ℝ)(E k:ℕ):ℝ:=
    (↑(Fintype.piFinset (fun _ : I=>Lattice.box (haloR v R))).card:ℝ)*rope E k (Real.exp ((k*(4*haloR v R):ℕ):ℝ)) (univ:Finset I)
lemma ket_z (I:Type)[Fintype I][DecidableEq I](C R:ℝ)(k i:ℕ): 0≤ ketCost I C R k i:= mul_nonneg (Nat.cast_nonneg _) (rope_p _ _ _ (Real.exp_pos _|>.le) _) -- fix
lemma ket_s (x:Rest)(X:Chain)(V:Layouts I G D R)(φ:I→Profile D){U B': I→ℝ}(hp:0≤U)(hx:0≤B')(h:Sense a V)(he:∀ t', vanes a t'+E ≤ t)(hd:0≤ C)(hR:∀ i, Reads (φ i).val (U i))(hφ:∀ j:I,Spatial (φ j).val ((spanP X k i)*C))(hw:0≤w)(hk:w≤1)(hB:0≤B)(hy:1 ≤ spanP X k i)(hF:Fest w E 1 (boon B B') V)(hE:e≤E) :
    Quire.Lit (sang X V b φ k i ((spanP X k i) • x.val) e r) w ((spanP X k i)^ (4*Fintype.card I) * ketCost I C R E t * boon ((spanP X k i)^D*B) (U*B') univ):= by
   let K:=spanP X k i; have hY:0<K:=spanP_pos ..; let Q:= cope X k i φ (K • x.val) R; let D':= haloR C R
   let p i:= K^D * U i; let h₀:= 4*D'; let A:= Real.exp ((t*h₀:ℕ):ℝ); let S:= boon B B'; let H:= boon (K^D*B) (U*B'); have hh:Crease S:=boon_pos _ hx _ hB
   have hg:Crease H:=boon_pos _ (fun i=>mul_nonneg (hp i) (hx i)) _ (mul_nonneg (pow_nonneg hY.le _) hB); have hL:= rope_p E t A (Real.exp_pos _|>.le) (univ:Finset I)
   have ht(z)(hv:z∈Q) (b:Finset I): Quire.Lit (SolarPaper V z (chirpR X k i φ R (K • x.val) z) b e r) w (rope E t A b * H b):= by
       refine banner_lit hg (by simp [H,boon]) (h.stone z _) ?_ he hw (Real.exp_pos _|>.le) b e hE r
       intro T j hj r
       let x':= K • x.val; have hC(p'): ‖chirpR X k i φ R x' z p'‖≤p p':=campus (φ p').val _ _ (hR _) hy (hp _)
       let W (b:Finset I):= (∏ i∈b,p i)*(A * S b)
       have hb : Quire.Lit (access (chirpR X k i φ R x' z) (V z) T j r) w (W T):= coer_lit h hF hh hw hk z (fun i=> sizes_v _ (Fintype.mem_piFinset.mp (steps_z hφ hd hv) i)) _ hC he T j hj r
       apply Ink.raise hb (le_of_eq ?_); unfold W p S H boon A; simp only [prod_mul_distrib,prod_const,Pi.mul_apply, mul_pow,h₀, D']; ring
   have hp : ‖lone X k i b‖≤ K^(4*Fintype.card I):=by
      unfold lone; rw [norm_prod, Nat.mul_comm 4, pow_mul'] -- lemma
      rw [← card_univ (α:=I),← prod_const]; apply prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=>?_); unfold Plot.tariff; rw [Real.norm_of_nonneg (by have hP:=spanP_pos X k i; positivity)]; exact div_le_self (pow_nonneg hY.le _) (one_le_pow₀ hy)
   let W:= Fintype.piFinset fun _ : I=>Lattice.box (haloR C R); have hZ:0≤ H univ:= hg.pos _
   unfold sang; rw [Finset.sum_apply, Finset.sum_apply]; refine Ink.raise (Ink.additions (s:=Q) (f:=fun z => songPX X V b φ k i (K • x.val) z e r) (fun z hz=>(ht z hz _).scale (lone X k i b)) (fun i=>(ling_pos _ _).le)) ?_
   rw [sum_const,nsmul_eq_mul]; calc
    _≤ W.card*(K^(4*Fintype.card I)*(rope E t A (univ:Finset I)*H univ)):=mul_le_mul (Nat.cast_le.mpr (card_le_card (steps_z hφ hd))) (mul_le_mul_of_nonneg_right hp (mul_nonneg hL hZ)) (mul_nonneg (norm_nonneg _) (mul_nonneg hL hZ)) (Nat.cast_nonneg _)
    _= _:= by change _= K^_*((W.card:ℝ)*rope _ _ _ (univ:Finset I))*H univ; ring
lemma rip_mat {F: Rest→Tale G}(h:Via G k F)(hv:∀ i,Quire.Lit (F i e r) w C)(hp:1/2≤R): Quire.Lit (rip F hp D e r) w C:= by
   let L(b:Beads (Loc G 1) r)(i:Rest):= ling w b * ‖F i e r b‖; have hh b: Integrable (L b) abide:= Continuous.integrable_of_hasCompactSupport (continuous_const.mul ((generated h e r b).norm)) (HasCompactSupport.of_compactSpace _)
   let v(b:Beads (Loc G 1) r) := ling w b * ‖rip F hp D e r b‖; have hx(b):0≤v b:=mul_nonneg (ling_pos _ _|>.le) (norm_nonneg _)
   have hp(s:Finset (Beads (Loc G 1) r)):∑ i∈s,v i≤ C:= by
       calc _ ≤ ∑ i∈s,∫ x,L i x ∂abide:= sum_le_sum (fun i _=>by unfold L; rw [MeasureTheory.integral_const_mul]; exact mul_le_mul_of_nonneg_left ((holding (D:=D) (generated h e r i) hp).2) (ling_pos _ _|>.le))
            _≤ C:= by rw [← integral_finsetSum _ fun i _=> hh i]; refine (integral_mono (integrable_finsetSum _ (fun i _=>hh i)) (integrable_const C) (fun i=>?_)).trans_eq (by simp); exact (Summable.sum_le_tsum _ (fun j _=>(hv i).1 j) (hv i).2.1).trans (hv i).2.2
   exact ⟨hx,summable_of_sum_le hx hp, Real.tsum_le_of_sum_le hx hp⟩
end charges
end YM.RG08.Creek
