import YM.TraceExtension.Perfect.Amaze

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {s:Stage}{G:Gauge}{q:KernelChoices}{P: Patch}{i:ℕ}
-- apply Start from same sheet; positivity-certified bn≥ etc choose region independent S path. no tilde
structure Stem (G:Gauge)(x:ℝ)(s:Stage) : Prop where
 bell : 1 ≤ Real.log x
 master : ∃ C,0 ≤ C∧ PayGrade G (east x) C ∧ C ≤ reed x 2
 enough : ∀ (R:PathData G)(v:ℝ), R.Bounds s.clip s.width s.paths v → ∀ b:Axis,∀ f:Side,∀ o: Site f,∀ i,i≤4→2 ≤ i→ cost (landW o) (east x) 4 0 (leaf (ballX (dust s.clip R b o)) 0 i) ≤ reed x i
lemma stem_ready (s:Stage)(G:Gauge): ∀ᶠ x:ℝ in atTop,Stem G x s:=by
 obtain ⟨a,C,h,p,H⟩:= paid_grade G; obtain ⟨v,D,pv,hv,Q⟩:= hatchY s.clip G s.width s.paths s.width_pos 4
 have ht:Tendsto east atTop (𝓝 0):= Real.tendsto_log_atTop.inv_tendsto_atTop
 have hs: Tendsto (fun x=>reed x 2) atTop atTop:= (tendsto_pow_atTop (by decide:(2:ℕ)≠0)).comp Real.tendsto_log_atTop
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1, ht.eventually (ge_mem_nhds h),ht.eventually (ge_mem_nhds pv),hs.eventually_ge_atTop C, hs.eventually_ge_atTop D] with x hx ha hq hS he
 have hE:0 ≤east x:=inv_nonneg.mpr (by linarith)
 exact ⟨hx,⟨C,p,H _ hE ha,hS⟩,fun R v hk b f o i h j=>(Q _ hE hq i h f o v R hk b).trans (he.trans (pow_le_pow_right₀ hx j))⟩
structure Eon (G:Gauge)(s:Stage)(q:KernelChoices)(P:Patch)(i:ℕ)(x y:ℝ) where
 C:ℝ
 H:ℝ
 D:ℝ
 α:ℝ
 B:ℝ
 shoe : 0< α
 fit : 0 ≤ B
 legal : 4 ≤ i
 smooth : 5 ≤ P.J
 bill (Z:Flight P.J i) (l:List Axis) : l.length ≤ P.J-2→ (advanceC Z.L (Carrier.linesOf Z q.penalty) l).strip α (B/(Z.L.val:ℝ)^(1+l.length))
 sA: SummitA P G q s.clip s.width s.paths α B (east x) H
 sB: SummitB P G q s.clip s.width s.paths α B (east x) D
 sized : Pressure.macroR P ≤ Nat.ceil ((Real.log x)^2)
 pays : PayGrade G (east y) C
 status : 1<x∧1<y∧0 ≤ C ∧0 ≤ D ∧ 0 ≤ H ∧ east x/(P.L.val:ℝ) ≤ east y
 bank n : Bank H D P.L C (reed y) (reed x) (vista n y) (vista (n+1) x)
 stem : Stem G y s
lemma post_phase (s:Stage)(G:Gauge)(q:KernelChoices)(j i:ℕ)(hj:5 ≤ j)(hi:4 ≤ i):∃ n:ℕ,∀ P:Patch,P.J=j→ n ≤ P.L.val → ∀ v:ℝ,∀ᶠ x:ℝ in atTop,Nonempty (Eon G s q P i x (x+v)):=by
 obtain ⟨a,B,h,h',H⟩:= Carrier.priced _ q.penalty_pos ((show 4 ≤5 by decide).trans hj) hi
 obtain ⟨u,C,c,p,P'⟩:= paid_grade G
 obtain ⟨T,hT,hM⟩:= early_to G s.width s.paths a B (a/2) (half_pos h) (half_lt_self h) h'.le j
 obtain ⟨n,hn⟩:= big_along T; refine ⟨n,fun X hx hX v=>?_⟩
 obtain ⟨b,D,t,hD,M⟩:= post_to G X q s.clip s.width s.paths a B h
 have hb:=bank_buys p hT hD (hn _ hX) v
 let i':= min b (a/2); have hi':0 < i':= lt_min t (half_pos h); have hm:Tendsto east atTop (𝓝 0):= Real.tendsto_log_atTop.inv_tendsto_atTop
 have ht:Tendsto (fun x:ℝ=>x+v) atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_id
 have hl : 1<(X.L.val:ℝ):=by exact_mod_cast (show 1< X.L.val from lt_of_lt_of_le (by decide) X.coarse)
 have hk:Tendsto (fun x:ℝ=>Nat.ceil (Real.log x ^2)) atTop atTop:= by
    apply tendsto_atTop.2;intro b; filter_upwards [((tendsto_pow_atTop (by decide:(2:ℕ)≠0)).comp Real.tendsto_log_atTop).eventually_ge_atTop (b:ℝ)] with x hx; dsimp only[Function.comp_apply] at hx; exact_mod_cast (hx.trans (Nat.le_ceil _))
 filter_upwards [eventually_gt_atTop (1:ℝ), hm.eventually (ge_mem_nhds hi'), (hm.comp ht).eventually (ge_mem_nhds c), ht.eventually (eventually_gt_atTop 1), (moor_log v).eventually (ge_mem_nhds hl),hk.eventually_ge_atTop (Pressure.macroR X),hb,ht.eventually (stem_ready s G)] with x hy hf hg H' hH hp H'' hs
 have hv:0<east (x+v):= inv_pos.mpr (Real.log_pos H'); have he':0<east x:= inv_pos.mpr (Real.log_pos hy)
 refine ⟨⟨C,T,D,a,B,h,h'.le,hi,?_,?_,?_,?_,hp,P' _ hv.le hg,⟨hy,H',p,hD,hT,?_⟩,H'',hs⟩⟩
 · rw [hx];exact hj
 · rw [hx];exact H
 · intro Y u o hq hs v hv hz; exact hM _ hx _ _ _ _ _ hq hs _ hv (hz.trans (hf.trans (min_le_right ..)))
 · intro Y u o hq v hv hz; exact M Y u o hq v hv (hz.trans (hf.trans (min_le_left ..)))
 have hp:= Real.log_pos H'; have hm:= Real.log_pos hy
 unfold east; rw [div_le_iff₀ (by linarith : 0 < (X.L.val:ℝ))]; field_simp; exact ((div_le_iff₀ hm).mp hH).trans_eq (mul_comm ..)
end YM.Trace.Perfect
