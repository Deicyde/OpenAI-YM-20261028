import YM.RG08.Dart.Levy
/-! # Colors conserved on cover from periodic alignment. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Classical Matrix
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{W:Type}{r i j k:ℕ}{σ v C B:ℝ}{m:Side}{G:Gauge} {U: Shale (Loc G 1) r}

abbrev Rims (r k:ℕ):= Beads (TypeFace k) r
def staple (q: Rims r k)(x: Stationary.Ink G r): Beads (Loc G k) r := fun i=> ((q i).1,(q i).2,x i)
def spliceEq (G:Gauge)(r k:ℕ): Rims r k × Stationary.Ink G r ≃ Beads (Loc G k) r where
   toFun x:= staple x.1 x.2
   invFun y := (fun i=> ((y i).1,(y i).2.1), fun i=>(y i).2.2)
   left_inv _:=rfl
   right_inv _:=rfl
lemma girth_st (x : Rims r k) (p : Stationary.Ink G r): girth (staple x p)=girth x:= rfl
private def marbleC (q:Rims r 1)(x: Fin r→G.Color)(i:Fin r) (p: Leaf G): ℝ:= if (p.1,p.2.1)=q i then x i p.2.2 else 0
lemma purseC (q:Rims r 1)(x : Fin r→G.Color): wallet U (marbleC q x)= ∑ p: Stationary.Ink G r, U (staple q p)*∏ i,x i (p i):= by
   let F:=staple (G:=G) q; have hv: Injective F:= fun a b h=> (show (fun i=>(F a i).2.2)= _ from congr_arg (fun z:Beads (Loc G 1) r=> fun i=>(z i).2.2) h)
   unfold wallet; rw [tsum_eq_sum (s:= univ.image F)]; swap
   · intro b hp; by_contra hh; let H:=fun i=>(b i).2.2; have hs j: (b j).1= (q j).1 ∧ (b j).2.1=(q j).2:=by
         have hP: marbleC q x j (b j) ≠0:=fun h=>hh (by rw [prod_eq_zero (mem_univ j) h,mul_zero]); exact Prod.ext_iff.mp (not_not.mp (fun h=> hP (if_neg h)))
     exact hp (mem_image.mpr ⟨H,mem_univ H,funext fun i=> Prod.ext (hs i).1.symm (Prod.ext (hs i).2.symm rfl)⟩)
   rw [sum_image (fun _ _ _ _ hp=>hv hp)]; exact sum_congr rfl fun i _=>by simp [F,marbleC,staple]
private def crags (n:ℕ): Side:=⟨n+1,by omega⟩
private lemma cragC: Tendsto (fun i=> (crags i).val) atTop atTop:= tendsto_add_atTop_nat _
private def marble_s (p:Rims r 1)(x:Fin r→G.Color)(i:Fin r)(m:Side): Link G m:= fun q=>marbleC p x i (Lattice.lift q.1,q.2)
lemma chant_wallet (h:Polished U)(p:Rims r 1)(x:Fin r→ G.Color): Tendsto (fun i=>stitch U (crags i) 0 (fun j=>marble_s p x j (crags i))) atTop (𝓝 (wallet U (marbleC p x))):= by
   refine wallet_limit cragC h (fun j q=>?_) 0 (C:=fun i=> ‖x i‖) (fun j=>norm_nonneg _) fun i a z n=>?_
   · refine tendsto_const_nhds.congr' ?_; filter_upwards [wrap_o _ cragC q.1] with i he; unfold marble_s; rw [he]
   unfold dime Carrier.liftCost marble_s marbleC; rw [pow_zero,mul_one]; dsimp only; split; exact PiLp.norm_apply_le ..; rw [norm_zero]; exact norm_nonneg _
lemma stained_wallet (h:Polished U)(p:Rims r 1)(x:Fin r→ G.Color)(hv:Toll U)(s:G.El) : wallet U (marbleC p (fun i=> G.adjoint s (x i)))= wallet U (marbleC p x) := by
    have ht(m:Side)(i:Fin r): stain s (marble_s p x i m)= marble_s p (fun i=>G.adjoint s (x i)) i m := by
        apply (arm G m 1).injective; unfold stain; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
        funext z; have he(y:Fin r→G.Color): arm G m 1 (marble_s p y i m) z= if (Lattice.lift z.1,z.2)=p i then y i else 0:= by ext1 k; split; exact if_pos (by assumption); exact if_neg (by assumption)
        change G.adjoint s (arm G m 1 _ z)=_; rw [he,he]; split; rfl; exact map_zero _
    have hQ i:stitch U (crags i) 0 (fun j=> marble_s p x j (crags i))= stitch U (crags i) 0 (fun j=>marble_s p (fun i=> G.adjoint s (x i)) j (crags i)) := by
       obtain ⟨V,h,H,hz,hV,hp⟩:=hv.frame (crags i); simp_rw [← ht]; rw [← hp]; unfold Tensor.coeff; simp only [_root_.smul_apply]
       have he:iteratedFDeriv ℝ r (V ∘ (stain s)) 0= iteratedFDeriv ℝ r V 0:= ((hz s).iteratedFDeriv ℝ r).eq_of_nhds
       nth_rw 1 [← he]; rw [wired _ (by rw [map_zero]; exact H), map_zero]; rfl
    have hh:= chant_wallet h p (fun i=> G.adjoint s (x i)); simp_rw [← hQ] at hh; exact tendsto_nhds_unique hh (chant_wallet h p x)
lemma tint_paint (h:Toll U)(he:Polished U)(p:Rims r 1): (fun x:Stationary.Ink G r=> U (staple p x)) ∈ paints G r:= fun u a=> by rw [← purseC,← purseC]; exact stained_wallet he p a h u
private def pli {G: Gauge}(x:Rims r 1)(y:Rims r 2)(v:Stationary.Ink G r):ℝ:= bulb (fun _=>vein G) (staple x v,staple y v)
private lemma pli_cell (p:Rims r 1)(q:Rims r 2)(v u:Stationary.Ink G r) : pli p q v=pli p q u:= by unfold pli bulb; refine prod_congr rfl (fun i _=> vein_self (p i).1 (q i).1 (p i).2 (q i).2 (v i) (u i))
private lemma sunless (p:Rims r 1)(q:Rims r 2)(v u:Stationary.Ink G r)(h:v≠u): bulb (fun _=>vein G) (staple p v,staple q u)=0:= by
   obtain ⟨i,hi⟩:= not_forall.mp (mt funext h); exact prod_eq_zero (mem_univ i) (vein_o _ _ (fun h=>hi (Eq.symm h)))
lemma vested (p:Rims r 2)(h:Toll U)(he:Quire.Lit U (2*v) C)(hp:0<v) : (fun i:Stationary.Ink G r=> dart U (staple p i))∈ paints G r:=by
   let L:=sires U (bulb (fun _=> vein G)); have hu:=thorn_p he hp; have hs(q : Stationary.Ink G r): Summable fun x:Rims r 1 × Stationary.Ink G r=> L (spliceEq G r 1 x,staple p q):= (hu.of_norm.prod_symm.prod_factor (staple p q)).comp_injective (spliceEq ..).injective
   let F(s:Rims r 1)(a:Stationary.Ink G r):= pli s p a * U (staple s a)
   have hP q (s:Rims r 1): (∑' i:Stationary.Ink G r,L (staple s i, staple p q)) = F s q:= tsum_eq_single q fun v hv=> by unfold L sires; rw [sunless s p v q hv,zero_smul] -- value target
   have he' (q:Stationary.Ink G r) : HasSum (fun x:Rims r 1=> F x q) (dart U (staple p q)):= by
       have H (s:Rims r 1): (∑' i:Stationary.Ink G r,L ((spliceEq ..) (s,i),staple p q))=F s q:= hP _ s
       simp_rw [← H]; unfold dart revolve; rw [← Equiv.tsum_eq (spliceEq G r 1) (fun i=> L (i,staple p q))]; exact (hs q).hasSum.prod_fiberwise (fun b=> (hs q|>.prod_factor b).hasSum)
   have hx(q:Rims r 1): F q∈ paints G r:= by
       classical
       by_cases hh:Nonempty (Stationary.Ink G r); swap; · have H:= not_nonempty_iff.mp hh; rw [show F q=0 from funext fun i=> isEmptyElim i]; exact Submodule.zero_mem _
       let v:= Classical.choice hh
       rw [show F q=pli q p v • (fun i=> U (staple q i)) from funext fun i=> congr_arg (·*_) (pli_cell q p i v)]; exact (paints G r).smul_mem _ (tint_paint h (scarlet he (by positivity)) q)
   exact (Submodule.closed_of_finiteDimensional (paints G r)).mem_of_tendsto ((Pi.hasSum.mpr he')) (Eventually.of_forall (fun s=> (paints G r).sum_mem fun j _=> hx _)) -- lemma name
end YM.RG08.Dart
