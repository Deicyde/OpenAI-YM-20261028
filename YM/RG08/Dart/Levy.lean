import YM.RG08.Dart.Blades
/-! # Leanable over Cover. Ward leading. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Classical Matrix
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{W:Type}{r i k:ℕ}{σ v C B:ℝ}{m:Side}{G:Gauge} {U: Shale (Loc G 1) r}
-- Ward condition on period ray
structure Toll (F:Shale (Loc G 1) r):Prop where
    frame (m:Side) : ∃ V: Link G m →ℝ, Stationary.force V ∧ AnalyticAt ℝ V 0 ∧ Stained G V ∧ Quiets V r ∧ Tensor.coeff V r 0=stitch F m 0
lemma through (h:Toll U)(p: Fin r→Link G m)(v:Fin r→ BaseSites G m): stitch U m 0 p=stitch U m 0 fun i=>p i-gradientA G m (v i):=by
    obtain ⟨V,h,hA,H,hz,hp⟩:= h.frame m; rw [← hp]; unfold Tensor.coeff; simp only [_root_.smul_apply]; exact congr_arg (_ • ·) ((adhesion V (fun i=>(v i,p i)) h hA hz).symm)
-- period lift arbitrary linear growth site colors; bound with pol moments.
lemma wrap_g (m:Side)(x:Cover):size (Lattice.lift (wrap m x))≤size x:= by
    obtain ⟨p,hp⟩:= cover_of_eq (Lattice.lift (wrap m x)) x (by exact wrap_lift _ (n:=m));
    unfold size; apply sum_le_sum; intro i _; let y:= Lattice.lift (wrap m x) i
    have hv:= lift_centers (wrap m x) i; have hh : x i = y + (m.val:ℤ)*p i := (congr_fun hp i).trans (by simp only [nsmul_eq_mul, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply,y]); change - _ < 2*y∧2*y≤(m.val:ℤ) at hv; change y.natAbs ≤ _
    rcases lt_trichotomy (p i) 0 with h|h|h
    · have he: (m.val:ℤ)*(p i) ≤ m.val*(-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity); omega
    · rw [hh,h]; simp
    have ht: (m.val:ℤ)*1≤ m.val*p i:= mul_le_mul_of_nonneg_left (by omega) (by positivity); omega
lemma wrap_o (p:ℕ→ Side)(hp:Tendsto (fun i=>(p i).val) atTop atTop)(x:Cover): ∀ᶠ i in atTop,Lattice.lift (wrap (p i) x)=x:=by
    let t:=(univ:Finset Axis).sup (fun i=>(x i).natAbs); have hx i : (x i).natAbs ≤ t:= le_sup (f:=fun i=> (x i).natAbs) (b:=i) (mem_univ i)
    filter_upwards [hp.eventually (eventually_gt_atTop (2*t))] with i hi; refine lift_eq_iff.mpr ⟨rfl,fun j=>?_⟩; have hp:=hx j; change 2*t<(p i).val at hi; omega
lemma budge_cost (m:Side)(x:Link G m)(k:G.ColorIndex)(z: Cover): ‖budge (vlines x k) z‖ ≤ size z * ‖x‖ := by
    have he (w: Walk)(b:Cover) : ‖linkSum (vlines x k) b w‖ ≤ w.length*‖x‖:= by
       induction w generalizing b with
       | nil=> simp [linkSum]
       | cons i s ih=>
          unfold linkSum; refine (norm_add_le ..).trans ((add_le_add (show ‖(if i.neg then -vlines x k (i.used b) else vlines x k (i.used b))‖≤ ‖x‖ from ?_) (ih _)).trans_eq ?_)
          · split; rw [norm_neg]; exact norm_le_pi_norm x _; exact norm_le_pi_norm x _
          simp; ring
    unfold budge; apply (he ..).trans; rw [cable,route_length,sub_zero] -- fix
-- transfer with v:F and x etc only
lemma incline_v (x:Leaf G) : size (x.1+step (axisEquiv.symm x.2.1)) ≤ size x.1+1:= (size_add ..).trans (show _ from Nat.add_le_add_left (size_vec (posDir (axisEquiv.symm x.2.1))).le _)
private def bank (n:ℕ): Side:= ⟨n+1,by omega⟩
private lemma cash : Tendsto (fun i=> (bank i).val) atTop atTop:= tendsto_add_atTop_nat _
lemma tollWallet (hv:Toll U)(ht:Polished U)(p:Fin r→ Link G m): wallet U (fun i=>vline (p i))= wallet U (fun i=>vline (p i)-spinD (pathField (p i))):=by
    let X n (i:Fin r): Link G (bank n):= fun z=> vline (p i) (Lattice.lift z.1,z.2)
    let Z n (i:Fin r) : BaseSites G (bank n):=fun t=> pathField (p i) (Lattice.lift t.1) t.2.2
    let V n i:= X n i-gradientA G (bank n) (Z n i)
    suffices hv:Tendsto (fun n=> stitch U (bank n) 0 (X n)) atTop (𝓝 (wallet U (fun i=>vline (p i)))) ∧ Tendsto (fun n=>stitch U (bank n) 0 (V n)) atTop (𝓝 (wallet U (fun i=>vline (p i)-spinD (pathField (p i))))) from tendsto_nhds_unique (by convert hv.1 using 1; exact funext fun n=> Eq.symm (through ‹_› _ (Z n))) hv.2 -- may infer
    have hx(i: Fin r)(z: Leaf G): ∀ᶠ n in atTop, X n i (wrap (bank n) z.1,z.2)=vline (p i) z:= by filter_upwards [wrap_o bank cash z.1] with n hn; unfold X; rw [hn]
    refine ⟨wallet_limit cash ht (fun i p=> tendsto_const_nhds.congr' (by exact (hx i p).mono fun n h=>h.symm)) 0 (C:=fun i=>‖p i‖) (fun _=>norm_nonneg _) (fun i b v n=> by unfold dime Carrier.liftCost; simp only [pow_zero,mul_one]; exact norm_le_pi_norm (p i) _),?_⟩
    let q (x:Leaf G):=x.1+step (axisEquiv.symm x.2.1)
    have hh n i (x:Leaf G): gradientA G (bank n) (Z n i) (wrap _ x.1,x.2)= pathField (p i) (Lattice.lift (wrap (bank n) (q x))) x.2.2 - pathField (p i) (Lattice.lift (wrap (bank n) x.1)) x.2.2:= by unfold q; rw [_root_.map_add,wrap_step]; rfl
    refine wallet_limit (v:=V) cash ht (fun i x=>?_) (C:=fun i=> 2*‖p i‖) 1 (fun i=>by dsimp; positivity) (fun i z a n=>?_)
    · refine tendsto_const_nhds.congr' ?_; filter_upwards [hx i x,wrap_o bank cash x.1,wrap_o bank cash (q x)] with n H H' Ht; change _= X n i _- gradientA G _ _ _; rw [H,hh n i x,H',Ht]; rfl
    let x: Leaf G:=(z,a); let T : ℝ:= ‖p i‖; have he:0≤T:=norm_nonneg _
    let A k:= Lattice.lift (wrap (bank n) k); let Y z:=pathField (p i) z x.2.2
    have hP(x): ‖Y (A x)‖ ≤ (size x:ℝ)*T:= le_trans (budge_cost ..) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (wrap_g (bank n) x)) he)
    have hz:size (q x) ≤ size z+1:= incline_v x
    change ‖X n i _-gradientA G _ _ (wrap _ x.1,x.2)‖ ≤ _; refine (norm_sub_le ..).trans ((add_le_add (d:=(size (q x):ℝ)*T+(size z:ℝ)*T) (show ‖X n i _‖ ≤ T from norm_le_pi_norm (p i) _) ?_).trans ?_)
    · rw [hh n i x]; apply le_trans (norm_sub_le ..); exact add_le_add (hP (q x)) (hP x.1)
    change T+ ((size (q x):ℝ)*T+ (size z:ℝ)*T) ≤ 2*T*dime 1 z
    unfold dime Carrier.liftCost; rw [pow_one]; have hx : (size (q x):ℝ) ≤ (size z:ℝ)+1:= by exact_mod_cast hz
    nlinarith
abbrev raze (x:Link G m) : PAC (Loc G 2) m:= fun i=> dColor G m 1 (arm G m 1 x) (i.1,i.2.1) i.2.2
lemma toll_eye (x: Fin r→Link G m)(h:Quire.Lit U (2*v) C)(hp:0<v)(he:Toll U): stitch U m 0 x=stitch (dart U) m 0 (fun i=> raze (x i)):=by
   have hs:= thorn h hp; have hx:= Ink.pens h (ling_one (by positivity)); have ht:=Ink.pens hs (ling_one hp.le)
   have hv (x:Fin r→ Link G m):stitch U m 0 x=wallet U (fun i=> vline (x i)):= by unfold wallet; rw [stitch_apply hx.of_norm]; apply tsum_congr; intro i; simp [rosary,silks,vline] -- wallet maybe unfold
   have hu: Polished U:= scarlet h (by positivity)
   let A(w:Link G m):= ∑ a: Lines G m 2,‖raze w a‖; have hA w:0 ≤ A w:= sum_nonneg fun _ _=>norm_nonneg _
   rw [hv,tollWallet he hu,show (fun i=> vline (x i)-spinD (pathField (x i)))=(fun i=> pursed (vein G) (hline (x i))) from funext fun j=>funext fun i=>spoke _ _, ← divulge (C:=C) (P:=fun _=>vein G) ?_ (fun i j=> vein_price j hp) ?_ ?_ (fun i=>hline (x i)) (fun i=>A (x i)) (fun i=>hA _) ?_]
   rotate_left
   · exact (show Quire.Ink (brocade (wool (2*v))) U C from Ink.shrink h (fun i=> ((ling_pos _ _).le.trans_eq (bro_lit ..))) fun i=> (bro_lit ..).ge)
   · exact fun i=> inv_nonneg.mpr hp.le
   · exact fun i=> Real.one_le_exp (mul_nonneg hp.le (Nat.cast_nonneg _))
   · intro i q; refine le_trans (b:= A (x i)) ?_ (le_mul_of_one_le_right (hA _) (Real.one_le_exp (mul_nonneg hp.le (Nat.cast_nonneg _))))
     change ‖raze (x i) (wrap m q.1,q.2)‖ ≤ A _; unfold A; exact single_le_sum (f:=fun a=> ‖raze (x i) a‖) (fun a _=>norm_nonneg _) (mem_univ (wrap m q.1,q.2))
   unfold wallet; rw [stitch_apply ht.of_norm]; exact tsum_congr fun p=>by simp only [rosary,silks,zero_add]; rfl
end YM.RG08.Dart
