import YM.RG08.Dart.Maison
/-! # Extract true Taylor stencil from analytic local atom. Absolute guarantees after each operation fixed-order. No translating base. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter Work.F02
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {W:Type}{r i j k:ℕ}{w σ v C B:ℝ}{m:Side}{G:Gauge}
section snap
abbrev Scope (G:Gauge)(k d:ℕ):= Fin k→Lines G (village d) 1
private def inkBody (k d:ℕ)(f:CoverConfig G→ℝ) (p:Scope G k d): ℝ := Tensor.coeff (localAtom (G:=G) f (0:Site (village d))) k 0 (fun i=> Pi.single (p i) 1)
private def stool (p:Scope G k r): Beads (Loc G 1) k:= fun i=> (Lattice.lift (p i).1,(p i).2)
-- no symmetry assumed. yields Tidy via sew. complete root payout.
def castleP (b:Atom G k)(r:ℕ): Rooted ℝ (Loc G 1) r:= sew (tub (inkBody r b.length (aTerm b)) stool)
lemma castle_t (b: Atom G k)(r:ℕ): Tidy (castleP b r):= Tidy.sewn ((Pens.pours _ (show Pens (inkBody r b.length (aTerm b)) from (hasSum_fintype _).summable)))
lemma castle_i (b:Atom G k)(r:ℕ)(x:Site m): AnalyticAt ℝ (localAtom (aTerm b) x) 0 ∧ stitch (castleP b r) m x=Tensor.coeff (localAtom (aTerm b) x) r 0:=by
    obtain ⟨R,hR,H⟩:=term_vault G (σ:=1) zero_lt_one; have he (m:Side)(x:Site m):= (H _ b).native _ x -- ns; order impl
    refine ⟨he _ x,Tensor.ext_diag _ _ ((castle_t b r).sym x) (Tensor.coeff_symm (he _ x|>.contDiffAt)) (funext fun a=>?_)⟩
    have ht : Pens (inkBody r b.length (aTerm b)):= (hasSum_fintype _).summable; let n:=b.length; let f(m: Side)(i:Site m):= localAtom (aTerm b) i
    let g:=patchCopy (G:=G) (B:=ℝ) n x; let T : Tensor.T (Link G (village n)) ℝ r:= Tensor.coeff (f _ 0) r 0
    have hv : Tensor.coeff (localAtom (aTerm b) x) r 0 (fun _=> a) = T (fun _=> g a):= by
       let p:=g.toContinuousLinearMap
       rw [inhabit n (aTerm b) (aTerm_at b) x]; unfold Tensor.coeff; rw [_root_.smul_apply]; change ((r.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ r ((localAtom (aTerm b) 0)∘ p) 0 _=_; rw [wired p ?_,map_zero]; rfl
       rw [map_zero]; exact he _ 0
    have hh:= expand_coord T.toMultilinearMap (fun _=>g a); rw [recording_apply] at hh
    change rootSong (sew _) m x a= Tensor.coeff _ r 0 _; rw [sew_diagonal (ht.pours _) x,rootSong,Tensor.diagonal,st_tub _ _ ht,tsum_fintype,hv]; apply Eq.trans _ hh
    apply sum_congr rfl; intro i _; unfold rosary stool inkBody
    simp only [silks]
    -- θ balance
    change _*(∏ i',a (x+_,_))=(∏ i', a (wrap m (lift _)+x,_))*_
    rw [mul_comm]; congr 1; apply prod_congr rfl; intro j _; rw [add_comm x]
-- card count. choose τ pre. Real tax.
def homePrice (G:Gauge)(k r:ℕ)(σ R:ℝ)(d:ℕ)(w:ℝ):= (Fintype.card (Scope G r d):ℝ)*Real.exp (w*(r*(4*d):ℕ))*(priceSlot G^k*costNote r R) -- anchor d here
lemma captured (b: Atom G k)(hw:0 ≤ w)(h:VaultOn G (aTerm b) B (b.budget σ * priceSlot G^k))(hp:0<B)(v:Scope G r b.length): ‖inkBody r b.length (aTerm b) v‖ ≤ b.budget σ*(priceSlot G^k*costNote r B) := by
   let d:=b.length; obtain ⟨g,hg,H,hV⟩:= h (village d) 0
   let x (i:Fin r): Link G (village b.length) := Pi.single (v i) 1
   have hx:= mixtape_cost hp hg H hV r (axes∘x) -- binders
   rw [note_real] at hx
   change ‖((inkBody r b.length (aTerm b) v:ℝ):ℂ)‖ ≤ _ at hx
   simp only [Complex.norm_real] at hx; refine hx.trans (le_of_eq ?_)
   have he i : ‖(axes∘x) i‖=1:= by
       rw [show (axes∘x) i= Pi.single (v i) (1:ℂ) from ?_, Pi.norm_single]; simp
       ext1 j; simp [Function.comp_apply,axes, x,Pi.single_apply,apply_ite Complex.ofReal]
   simp_rw [he]; rw [prod_const_one, mul_one]; unfold costNote; ring
lemma castle_price (b:Atom G k)(r:ℕ)(hw:0 ≤ w)(h:VaultOn G (aTerm b) B (b.budget σ * priceSlot G^k))(hp:0<B): Quire.Lit (castleP b r) w (homePrice G k r σ B b.length w*b.budget σ):=by
   let A:= inkBody r b.length (aTerm b)
   have ht (p:Scope G r b.length): girth (stool p) ≤ r*(4*b.length):= by
      unfold girth; rw [show r*(4*b.length)= ∑ i:Fin r,(4*b.length) by simp]; exact sum_le_sum (fun i hi=> farsum _)
   refine stitching (Ink.pour (stool (G:=G) (k:=r) (r:=b.length)) (?_ : Quire.Ink (fun i:Scope G r b.length=> ling w (stool i)) A _) (ling_one hw))
   unfold Quire.Ink; apply budget_finite (fun i=> mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _))
   refine le_trans (sum_le_sum (g:=fun i:Scope G r b.length=> Real.exp (w*((r*(4*b.length):ℕ):ℝ)) *(b.budget σ*(priceSlot G^k*costNote r B))) (fun i hi=>?_)) (le_of_eq ?_)
   · exact mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (ht i)) hw)) (captured b hw h hp i) (norm_nonneg _) (Real.exp_pos _|>.le)
   unfold homePrice; simp only [sum_const,card_univ,nsmul_eq_mul]; ring
end snap
end YM.RG08.Dart
