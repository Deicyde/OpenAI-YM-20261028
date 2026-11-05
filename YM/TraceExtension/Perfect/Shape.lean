import YM.TraceExtension.Perfect.Arcs
import YM.Progress.STATIONARY_SCENES.Response

/-! # Collect multispectral charts, charging gauges too -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c : Side}{G:Gauge} {I J:Type} [Fintype I] [DecidableEq I] [Fintype J]
lemma sh_linear (L:Rays I→L[ℝ]ℝ)(A:I→ℕ)(α t) : cost A α t 0 (leaf L 0 1)= sh A α t 0 (fun z=>L (desk z)):=by
 let E := Equiv.funUnique (Fin 1) I
 unfold cost leaf bank
 simp_rw [iteratedFDeriv_one_apply, L.fderiv]
 have hx (z:Fin 1→ I): limitN A z=A (z 0):=by simp [limitN]
 simp_rw [hx]; exact E.sum_comp (fun i=>spot α t 0 (A i)*‖L (desk i)‖)

lemma color_skin (F:I×J → ℝ)(u:I→ℝ)(j:J)(A α t r)[DecidableEq J] (h:∀ a b, F (a,b)=if b=j then u a else 0): sh (A ∘ Prod.fst) α t r F=sh A α t r u:=by
 unfold sh; rw [Fintype.sum_prod_type];simp_rw [h,Function.comp_apply]; apply Finset.sum_congr rfl; intro i _; simp_rw [apply_ite (fun x:ℝ=> ‖x‖),norm_zero,mul_ite]; simp
lemma label_body (l:Lines G c 1)(j:G.ColorIndex)(i:Body 1 c) : parts G 1 (arm _ _ _ (desk l)) j i=desk l (i.1,i.2,j):=rfl
lemma gate_f {N : ℕ}{f:Side}(M:Matrix (Body N f) (Body 1 c) ℝ)(i:Body N f)(j:G.ColorIndex)(b:Body 1 c)(t:G.ColorIndex) :
    uniformM M (desk (b.1,b.2,t)) (i.1,i.2,j) = if t=j then M i b else 0:=by
 let e : Lines G c 1:=(b.1,b.2,t); let u:=desk e
 change (M*ᵥ parts G 1 (arm G c 1 u) j) i=_
 unfold u; split_ifs with h
 · rw [show parts G 1 (arm G c 1 (desk e)) j= desk b from ?_, desk,Matrix.mulVec_single_one];rfl
   ext1 i;rw [label_body]; rcases i with ⟨x,m⟩; rcases b with ⟨v,n⟩; simp [desk,e,Pi.single_apply,h]
 rw [show parts G 1 (arm G c 1 (desk e)) j=0 from ?_, Matrix.mulVec_zero];rfl
 funext i; rw [label_body]; simp [desk,e,Pi.single_apply,Ne.symm h]
lemma star_mesh {N : ℕ}{f:Side}(M:Matrix (Body N f) (Body 1 c) ℝ)(i:Body N f)(j:G.ColorIndex)(A:Site c→ℕ)(α t r) :
    sh (fun p:Lines G c 1=> A p.1) α t r (fun z=> uniformM M (desk z) (i.1,i.2,j))=sh (fun p:Body 1 c=> A p.1) α t r (M i):=by
    let H(z: Body 1 c × G.ColorIndex):= uniformM M (desk ((Equiv.prodAssoc ..) z)) (i.1,i.2,j)
    let F b := A (b : Body 1 c).1; refine Eq.trans ?_ (color_skin H (M i) j F α t r (gate_f M i j)); unfold sh; rw [← (Equiv.prodAssoc (Site c) (TypeFace 1) G.ColorIndex).sum_comp]; rfl

-- move therapy
namespace Lot
variable {P:Patch}{Y:KernelChoices}{p:Clip}{α D β v:ℝ} {W:Type*}(L:W→ Lot G P Y p α D)
  {N:ℕ}
set_option quotPrecheck false
variable (g:∀ w,Cross (L w).s.ratio.count (TypeFace 1) (TypeFace 1))
   (o:∀ w,Site (L w).f) (h:0 < β) (hw:∀ w,(g w).strip β (v/P.L.val))
include h hw
local notation "C!" => fun w=> installed (L w).s.ratio (g w)
local notation "K"=> fun w=>straighten (L w).s (L w).wood (C! w)
lemma locate_station (z:∀ w,Site (L w).f) : Calm (fromV L z) (fun w x=>switchSite (uniformM (K w) x) (z w)|> G.mat) N:=by
   let D w (x:Link G (L w).c)(i:G.ColorIndex):= uniformM (K w) x (z w,vac,i)
   let β':= β/P.L.val
   let H:=Progress.StationaryScenes.Response.correction P.J β v
   let Z:= fromV L z
   have hβ : 0< β':=div_pos h (side_pos _)
   have ht : Calm Z D N:=by
       refine Calm.piP D (fun i=>?_); let A w:= (ContinuousLinearMap.proj (φ:=fun _: Lines G (L w).f 0=>ℝ) (z w,vac,i)) ∘L uniformM (K w)
       refine ⟨fun w=> (A w).contDiff.contDiffAt,β',max 0 H,hβ,le_max_left ..,fun w k hk=>?_⟩
       change cost _ _ _ _ (leaf (A w) 0 k) ≤ _
       match k with
       | 0 => rw [zero_price,map_zero,norm_zero,mul_zero]; exact le_max_left ..
       | 1 =>
         rw [sh_linear]; let V:= fun y : Body 1 (L w).c=> K w (z w,vac) y
         let S:=(L w).s
         rw [show sh (Z w) β' 0 0 (fun x=> A w (desk x))= sh (fun p:Body 1 (L w).c=> separation (z w) (S.ratio.embed p.1)) β' 0 0 V from star_mesh (K w) (z w,vac) i (fun z'=> separation (z w) (S.ratio.embed z')) _ _ _]
         let E (y:Body 1 (L w).c) := Next.Free.crossW S.ratio β (z w) y.1
         let W y:= if 0≤V y then E y else - E y
         have he(i):0≤E i:=(Real.exp_pos _).le
         have hp(y: Body 1 (L w).c): |W y| ≤ E y:=by
            unfold W; split
            · rw [abs_of_nonneg (he y)]
            · rw [abs_neg,abs_of_nonneg (he y)]
         have hQ:(K w *ᵥ W) (z w,vac)= sh (fun p:Body 1 (L w).c=> separation (z w) (S.ratio.embed p.1)) β' 0 0 V :=by
            apply Finset.sum_congr rfl;intro i _; change V i*W i= _ * ‖V i‖
            have h': spot β' 0 0 (separation (z w) (S.ratio.embed i.1))= E i:=by
               simp [spot,shelter,E,β', Next.Free.crossW]; rw [show S.ratio.count=P.L from congr_arg Patch.L (L w).patch]; ring
            unfold W; rw [h']; split <;> rename_i hp <;> first|rw [Real.norm_of_nonneg hp, mul_comm]|rw [Real.norm_of_nonpos (le_of_not_ge hp)]; ring
         have hh:=Progress.StationaryScenes.Response.straighten_price S h.le (W:=g w) (C:=v) ?_ (L w).wood _ _ (separation_self (z w)|>.trans_le (Nat.zero_le 1)) W hp
         rotate_left; · rw [show (S.ratio.count.val:ℝ)=(P.L.val:ℝ) from congr_arg (fun p:Patch=>(p.L.val:ℝ)) (L w).patch]; exact hw _
         change |(K w *ᵥ W) (z w,vac)| ≤ _ at hh
         rw [← hQ]; apply (le_abs_self _).trans; unfold H; rw [show P.J=S.patch.J from congr_arg Patch.J (L w).patch.symm]; exact hh.trans (le_max_right ..)
       | n+2 => unfold cost leaf bank; rw [Finset.sum_eq_zero]; exact le_max_left ..; intro i _; rw [iteratedFDeriv_succ_apply_right,show fderiv ℝ (A w)=(fun _=> A w) from funext fun _=>(A w).fderiv, iteratedFDeriv_const_of_ne (by omega)]; simp
   let T:=LinearEquiv.toContinuousLinearEquiv ((WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).symm); exact (ht.maps T.toContinuousLinearMap).prop (fun v:G.Color=> G.mat (G.lieExp v)) (a:=0) G.exp_jet.contDiffAt (fun w=> by
        change gaugeColor (uniformM (K w) 0) (z w) = (0:G.Color); simp)
omit h hw in
lemma pay_d (n:ℕ)(u:∀ w, Body n (L w).f) (d:∀ w,Site (L w).f)(Q : ∀ w, Matrix (Body n (L w).f) (Body 1 (L w).c) ℝ) {η C:ℝ} (he:0<η)(hC:0 ≤ C) (t : ℕ)
   (hh : ∀ w, sh (fun i:Body 1 (L w).c=> separation (d w) ((L w).s.ratio.embed i.1)) η t 0 (Q w (u w)) ≤ C):
     Calm (fromV L d) (fun w x i=> uniformM (Q w) x ((u w).1,(u w).2,i)) N:=by
    apply Calm.piP (X:=G.ColorIndex); intro j
    let Wk w:= (ContinuousLinearMap.proj (φ:=fun _:Lines G (L w).f n=>ℝ) ((u w).1,(u w).2,j)) ∘L uniformM (Q w)
    refine ⟨fun w=> (Wk w).contDiff.contDiffAt,η,C,he,hC,fun w k hk=>?_⟩; change cost _ _ _ _ (leaf (Wk w) _ k) ≤ _
    let V:(I :(L w).tab) →ℕ:=fromV L d w
    match k with
    | 0=>rw [zero_price,map_zero,norm_zero,mul_zero]; exact hC
    | 1=>
       rw [sh_linear]; refine le_trans ?_ (le_trans (le_of_eq (show sh V η t 0 (fun x=>Wk w (desk x))=_ from star_mesh (Q w) (u w) j (fun i=>separation (d w) ((L w).s.ratio.embed i)) _ _ _)) (hh w)); exact Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (spot_tiny _ _ _ _ he.le le_rfl (Nat.zero_le _)) (norm_nonneg _)
    | n+2 => unfold cost leaf bank; rw [Finset.sum_eq_zero]; exact hC; intro i _; rw [iteratedFDeriv_succ_apply_right,show fderiv ℝ (Wk w)=(fun _=> Wk w) from funext fun _=>(Wk w).fderiv, iteratedFDeriv_const_of_ne (by omega)]; simp
lemma cut_station (z:∀ w,Site (L w).f) : let T:=fun w=>of (gaugePad (C! w) (o w) ((L w).s.ratio.count.val+1))
    Calm (fromV L z) (fun w x=> G.mat (switchSite (uniformM (T w) x) (z w))) N:=by
    intro A; let b:=P.L.val+1; let R w:= (L w).s.ratio
    have hb(w): (R w).count=P.L:=congr_arg Patch.L (L w).patch
    let e := β/P.L.val; let H:= max 0 v; have he:0< e:=div_pos h (side_pos _);have h0 : 0 ≤ H:= le_max_left ..
    let Q:= Real.exp (2*e*b)*Real.exp β*(Fintype.card (TypeFace 1)*(H/P.L.val)); have hL:= side_pos P.L
    have hQ : 0≤Q:=by unfold Q; positivity
    have hh(w:W): sh (fun i:Body 1 (L w).c=> separation (z w) ((R w).embed i.1)) e 0 0 (A w (z w,vac)) ≤ 4*b*Q:=by
       let Z(y:Body 1 (L w).c):= separation (z w) ((R w).embed y.1); set i:= z w
       let r:=(R w).count.val+1; have hr : r=b:= by unfold b r; rw [hb]
       change sh Z e 0 0 (gaugePad (C! w) (o w) r (z w,vac))≤_
       by_cases hp:2*r<separation (z w) (o w)
       · simp_rw [gaugePad, glow_far _ _ _ hp]; simp [sh_zero]; positivity
       unfold gaugePad; apply (sh_sum ..).trans; apply (le_trans (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>(b:ℝ)*Q) ?_))
       · simp [Axis]; apply le_of_eq; ring
       intro a _
       rw [sh_scale]; apply mul_le_mul
       · rw [abs_mul]; refine (mul_le_mul (glow_fee ..) (beam_size ..) (abs_nonneg _) zero_le_one).trans ?_; rw [one_mul,hr]
       · apply le_trans (b:= Real.exp (2*e*b)*(∑ j : Body 1 (L w).c, Next.Free.crossW (R w) β (o w) j.1* ‖C! w (o w,coord a) j‖))
         · unfold sh; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j _; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
           have ht : Z j≤2*b+separation (o w) ((R w).embed j.1):=(separation_triangle ..).trans (Nat.add_le_add_right (hr ▸ le_of_not_gt hp) _)
           apply le_trans (spot_mono e _ _ he.le ht); dsimp only [spot,shelter]; rw [sub_zero,max_eq_right (Nat.cast_nonneg _)]; unfold Next.Free.crossW; rw [hb]; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,pow_zero, one_mul, ← Real.exp_add]; apply Real.exp_monotone (le_of_eq ?_); unfold e; ring
         unfold Q; rw [mul_assoc (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
         have ht₀:= Next.Free.cross_sprawl (R w) (R:=g w) h.le (hw w) (o w,coord a)
         change _ ≤ Real.exp _*(↑(Fintype.card _)*(H/_)); refine ht₀.trans ?_; unfold H; gcongr; exact le_max_right ..
       · exact sh_nn ..
       positivity
    have he := pay_d (α:=α) L 0 (fun w=>(z w,vac)) z A (N:=N) he (show 0≤4*b*Q by positivity) 0 hh
    let T:=LinearEquiv.toContinuousLinearEquiv ((WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).symm); exact (he.maps T.toContinuousLinearMap).prop (fun v:G.Color=> G.mat (G.lieExp v)) (a:=0) G.exp_jet.contDiffAt (fun w=> by
        change gaugeColor (uniformM (A w) 0) (z w) = (0:G.Color); simp)
end Lot
end YM.Trace.Perfect
