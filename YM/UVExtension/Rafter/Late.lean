import YM.UVExtension.Rafter.Canvas
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Lamppost Concert Local MergeProof Planned.GuardedAtom Guard Rainfall Eyelet Source Next.Foundations Wet Extra.Histories
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{d:ℕ}{ι D Z E:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    {T:Opening D Z}{A:Hol G}{U:Labels.Frame G d}{B:SectionData U}
variable {a' a t b w k c z σ ρ v:ℝ}
noncomputable def belaying (p:BudgetPoint)(X:ι→Support n) : Meter.{0} ι Unit:=shelf (Config G n) (fun i=>Real.exp (p.supportExponent*coverNumber p.B (X i))) (fun i=> Real.exp_pos _)
variable (p:BudgetPoint)(Q:D→Rep G n)(zD:D)(X:ℕ→Support n)(M:D→Raw U n)(K:∀ i: D,Keeper (Q i).p (Q i).activities) (hp:∀ i,(Q i).p=p)
variable (he:∀ i,(Q i).Lawful v t w σ ρ)(hv:∀ i, Valid (M i) X (Q i) ρ B A z k)(hX:∀ i,(M i).seed=0)(hh:∀ i,(Q i).activities.forced=(Q zD).activities.forced) (hr:Readable A B p n z)
    (hA: Stalk (shop (G:=G) p X) T (fun i j (γ:Tap p G 0 (X j))=> γ.read ((M i).bulk j)) a)
    (hB : Stalk (belaying (G:=G) p (Local.patch (Q zD).activities)) T (fun i j x=>(M i).forced j x) b)
    (hZ : Stalk (bell (Q zD).activities.forced p.B p.supportExponent) T (fun i j x=>↑((Q i).activities.K j x)) c)
include he hv hA hB hZ hh hX hr
lemma governs (ha:0 ≤ a)(hb:0≤ b)(hy:0 ≤ c)(hz:hitWidth p*c≤1)(hk:0<k) : let Y:= 4*factor A B p.supportExponent z*a; let W i:= Wet.warp (Q i) (wallet (K i) X B (M i) A) A k (hp i)
    ∃ g:Z→ Bucket U p A n,Bumps T.span g∧ (∀ d,g (T.call d)= W d)∧∀ z∈T.span, ‖g z‖ ≤ max (2*readPrice A U*a) (max (2*1*Y) (2*k⁻¹*(b+Y))):=by
   intro P W; have hT(i): Readable A B (Q i).p n z:=by rw [hp i]; exact hr
   have hM(i):=Rainfall.fits (hT i) (he i) hk (K i) (hv i); have hE(i):= Wet.worthT (Q i) (wallet (K i) X B (M i) A) (hM i) (hp i); let j:=joint B (0:Site n)∘ X
   have hs(d:D): Summable fun i=>weighted A U 0 (X i) p.threshold ((M d).bulk i):=by rw [← hp d]; exact (handles (hT d) hk (hv d)).2.1
   have hS(d:D)(i):p.Regular (X i) ((M d).bulk i):=by rw [←hp d]; exact (hv d).halo.regular _
   obtain ⟨⟨f,hf,hzP,ht⟩,hH,hq⟩:=hold p a z X (fun i=>(M i).bulk) (fun i=> (hv zD).halo.origin i) hr hS ha hA hs
   obtain ⟨g,hg,hg',hq1⟩:= larboard (B:=B) (fun i=> (W i).2.1) X (fun i=> (M i).bulk) (fun i=> (hM zD).form.origin i) hH (by intro i l v; unfold W; rw [(hE i).2.1]; apply congr_arg; apply congr_arg; rw [← hp i]; rfl) (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (atomPrice_ge_one _ _ hr.nonneg)))) ha)
   let H(i):=clipSum j (fun l=> rebate A B 0 (X l) p.threshold ((M i).bulk l))
   have hv'(i):=Rainfall.permitT (hT i) (he i) hk (K i) (hv i)
   let f' d:=profile (Q d).activities (M d).forced
   have h1: Stalk (boxGoal G n p) T f' b:=by
      let q:= barcode (Q zD).activities; have he(i):barcode (Q i).activities=q:=by unfold q barcode; simp_rw [hh i]
      unfold f' profile; simp_rw [he]; refine loop q (fun x=> Real.exp (p.supportExponent*coverNumber p.B x.1)) (fun _=>Real.one_le_exp (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg _))) (fun i=>(M i).forced) hb hB -- cast P.def
   have hzY:0≤P:= mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (atomPrice_ge_one _ _ hr.nonneg)))) ha
   have h2 : Stalk (bank (G:=G) p (id (α:=Support n))) T H P:=by
       exact loop j (fun i=> Real.exp ((p.supportExponent+2)*coverNumber p.B i)) (fun i=>Real.one_le_exp (mul_nonneg (add_nonneg p.exponent_pos.le zero_le_two) (Nat.cast_nonneg _))) (fun i l U=> rebate A B 0 (X l) p.threshold ((M i).bulk l) U) hzY hq -- apply/exact
   obtain ⟨ℓ,hℓ,hL,hvK⟩:= sails (p:=p) _ (fun i=> (W i).2.2) (h1.plus (hooksX (Q zD).activities (fun d=>(Q d).activities) hh H h2 hZ hy hzY hz (t:=p.threshold))) (by intro i x y; unfold W; rw [(hE i).2.2,hv' i]; refine congr_arg _ ?_; unfold coda; rw [hp i]; rfl) hk (add_nonneg hb hzY)
   refine ⟨fun z=> (f z,g z,ℓ z), fun s p h hA he=> (hf s p h hA he).prodMk ((hg s p h hA he).prodMk (hℓ s p h hA he)),fun i=>Prod.ext ?_ (Prod.ext (hg' i) (hL i)),fun z hz=>max_le_max (ht z hz) (max_le_max (hq1 z hz) (hvK z hz))⟩
   dsimp only; rw [hzP]; dsimp only [W]; rw [(hE i).1]; change _=(M i).seed+∑' j,(M i).row 0 X A _ j; rw [hX i,zero_add]; unfold Raw.row; change _= ∑' j,weighted A U 0 (X j) (Q i).p.threshold ((M i).bulk j); rw [hp]
end YM.UVExtension.Rafter
