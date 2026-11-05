import YM.RG08.Orison.Kettle

/-! # Recovers wires and full coupling movement from cofinal apparatus. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {I J:Type}{G:Gauge}{E:ℕ}
lemma sawn {w:ℕ→ℕ→ℝ}{w':ℕ→ℝ}(h:∀ i ≤ E,0 < i → Tendsto (fun x=>w x i) atTop (𝓝 (w' i)))(n r i:ℕ)(hi:i-n ≤ E): Tendsto (fun x=>dues (w x) n r i) atTop (𝓝 (dues w' n r i)):=by
 let s:Finset ℕ:=(square (i-n)).erase 0
 let c:ℕ→ℕ→ℝ:=fun x j=>|w x j-w' j|
 have he(j)(hj:j∈s): hush.cheap (fun x=>c x j):=nicety (by
      have H:= ((h j ((Nacre.in_square .. |>.mp (mem_erase.mp hj).2).trans hi) (by have := (mem_erase.mp hj).1;omega)).sub (tendsto_const_nhds (x:=w' j))).abs;simpa using H) fun _=>abs_nonneg _
 let d(x:ℕ):=∑ j∈s,c x j
 have hd:hush.cheap d:=shells _ _ _ he
 have H:= Ducat.sizes (D:=hush) (tiny _ hd) i n r (w:=fun x=>w x) (w':=fun _=>w') ?s
 case s=>
    intro j hj hp;have hz:j∈s:=mem_erase.mpr ⟨hp.ne',Nacre.in_square .. |>.mpr hj⟩
    obtain ⟨_,hy⟩:= he _ hz;obtain ⟨A,hA⟩:=(he _ hz).1
    have hx:0 ≤ A:=(hA 0).1.trans (hA 0).2
    refine ⟨_,hush.steady (1+A+|w' j|) (by positivity),fun x=>?_⟩
    have hh:0≤ |w' j|:=abs_nonneg _;refine ⟨?_,by dsimp only;linarith,?_⟩
    · dsimp only; linarith only [abs_sub_abs_le_abs_sub (w x j) (w' j),show |w x j-w' j| ≤ A from (hA x).2]
    exact (show _≤ d x from Finset.single_le_sum (s:=s) (f:=fun j=> c x j) (fun j _=>abs_nonneg _) hz).trans (le_mul_of_one_le_left (tiny _ hd _) (by linarith))
 obtain ⟨p,hp,hQ⟩:=H
 rw [tendsto_iff_norm_sub_tendsto_zero];exact squeeze_zero (fun _=>norm_nonneg _) (fun j=>by rw [Real.norm_eq_abs];exact (hQ j).2.2) (show Tendsto (fun i=> p i*d i) atTop (𝓝 0) from (hush.awe _ _ hp hd).2)

lemma metered (hg:G.Simple){X:ℕ→Castle G}{V:Castle G}(h: Shade E X V):∀ j ≤ E,Tendsto (fun i=>torque (X i) hg j) atTop (𝓝 (torque V hg j)):=by
 intro j hj
 let t(i):= X i 0 j
 obtain ⟨σ,hσ,d,hd,a,ha,H⟩:=h.cost j 0 hj
 unfold torque Loop.reading
 apply Tendsto.div_const
 rw [tendsto_iff_norm_sub_tendsto_zero]
 refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>?_) (show Tendsto (fun i=>a i*d i) atTop (𝓝 0) from (hush.awe _ _ ha hd).2)
 rw [Real.norm_eq_abs,←Loop.var_meter (σ:=σ) hg (hush.safe _ ha i) (hush.safe _ ha i) hσ.le (H i|>.near) (H i|>.far)]
 exact Loop.bill_meter hg (mul_nonneg (hush.safe _ ha i) (tiny _ hd _)) hσ.le (H i|>.compare)

lemma replenished (hg:G.Simple){X:ℕ→Castle G}{V:Castle G}(h:Shade E X V){e r:ℕ}(he:e ≤ E)(i:Tape (RG08.Mount.rank r) (Market (Rudder.Tone G.ColorIndex))) : Tendsto (fun a=>send (X a) hg r e i) atTop (𝓝 (send V hg r e i)):=by
 have hM {n k:ℕ}(hn:n ≤ E)(i):Tendsto (fun a=> X a k n i) atTop (𝓝 (V k n i)):=by
    obtain ⟨u,hu,H⟩:=h.cost n k hn; exact Tone.field H (Nat.zero_lt_succ _) hu.le i
 unfold send Nacre.size; simp only [Finset.sum_apply];exact tendsto_finsetSum _ (fun j hj=> by
   have hx:Tendsto (fun a=> dues (torque (X a) hg) j (RG08.Mount.rank r) e) atTop (𝓝 (dues (torque V hg) j (RG08.Mount.rank r) e)):=sawn (fun i hi _=>metered hg h i hi) _ _ _ (by omega:e-j ≤ E)
   exact hx.mul (hM ((Nacre.in_square ..|>.mp hj).trans he) _))
end YM.RG08.Orison
