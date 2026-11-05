import YM.RG08.Cell.Contrast

/-!
# From common-cell back to the fine cover. Exponential width measured at distance/(L one step)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
variable {α β:Type} {c f L:Side}{K:Kernel (Co L α) (Co L β)}{p σ:ℝ}

theorem row_release (hs:0≤σ)(h:RowCost σ 1 K p)(hp:0≤p) : RowCost (σ / L.val) 1 (Cell.spread L K) (((L.val:ℝ)^4*Real.exp (8*σ))*p):=by
  intro x i
  rw [← (colony L).tsum_eq _,ENNReal.tsum_prod (f:=fun (z:Site L)(v:Cover)=> bill (Cell.spread L K x (colony L (z,v),i)) (σ/L.val*delta 1 x.1 (colony L (z,v))))]
  let X:= (column L α).symm x
  have he (z:Site L)(v:Cover): ((column L _ (v,z,i)) : Market β)=(colony L (z,v),i) := rfl
  let w:=8*σ
  have hA (z:Site L)(v:Cover): (σ / L.val:ℝ)*delta 1 x.1 (colony L (z,v)) ≤ σ*delta 1 X.1 v + w := by
    have hh:= separation_from X ((v,z,i):Market (Co L β))
    rw [he,show column L α X=x from (column L α).apply_symm_apply x] at hh; dsimp only at hh
    rw [delta_one,delta_one]
    have hL : 0 < (L.val:ℝ):=by positivity
    exact (mul_le_mul_of_nonneg_left hh (div_nonneg hs hL.le)).trans_eq (by unfold w; field_simp)
  apply (ENNReal.tsum_le_tsum (g:=fun _=> ENNReal.ofReal (Real.exp w*p)) ?_).trans_eq
  · simp only [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,site_card,Nat.cast_pow]
    rw [mul_assoc,ENNReal.ofReal_mul (by positivity : 0≤(L.val:ℝ)^4), ENNReal.ofReal_pow (by positivity : 0≤(L.val:ℝ)),ENNReal.ofReal_natCast]
  intro z
  calc _ ≤ ∑'v, bill (K X (v,z,i)) (σ*delta 1 X.1 v+w) := by
         apply ENNReal.tsum_le_tsum; intro v; unfold Cell.spread; rw [← he,Equiv.symm_apply_apply]
         exact bill_mono le_rfl (hA z v)
       _ ≤ ENNReal.ofReal p*ENNReal.ofReal (Real.exp w):= by simp_rw [bill_add,ENNReal.tsum_mul_right]; gcongr; exact h X (z,i)
       _ = _:= by rw [← ENNReal.ofReal_mul hp,mul_comm]

/-- Gamma and projectors are only block-translation covariant even on the fine cover. Do not
turn the `Priced.city` property in *cell coordinates* into a fine Priceds assertion. -/
def marketBill (L:Side)(K:Kernel α β) (σ A:ℝ):Prop:=
    RowCost (σ/L.val) 1 K A ∧ ColCost (σ/L.val) 1 K A ∧
    ∀ x y u,K (pass (L.val • u) x) (pass (L.val • u) y)=K x y

def laneTax (L:Side):= (L.val:ℝ)^4*Real.exp 8
lemma market_release (h: Priced σ p K)(hs:0 ≤ σ)(hσ:σ ≤ 1): marketBill L (Cell.spread L K) σ (laneTax L*p):=by
  let a:= ((L.val:ℝ)^4*Real.exp (8*σ))*p
  have ht := row_release hs h.row h.pos
  have hh := row_release (K:=Function.swap K) hs (h.row_t hs) h.pos
  have hv : a ≤ laneTax L*p:= by unfold a laneTax; have hP:=h.pos; gcongr; linarith
  refine ⟨fun x i=> (ht x i).trans (ENNReal.ofReal_le_ofReal hv),fun i x=> ?_, fun x y u=> ?_⟩
  · simpa only [Cell.spread, Function.swap,delta_one, Pert.Bulk.sep_comm x.1] using (hh x i).trans (ENNReal.ofReal_le_ofReal hv)
  unfold Cell.spread
  let X:=(column L α).symm x; let Y:=(column L β).symm y
  rw [show pass (L.val • u) x=column L _ (pass u X) by rw [column_map,Equiv.apply_symm_apply],show pass (L.val • u) y=column L _ (pass u Y) by rw [column_map,Equiv.apply_symm_apply], Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  simpa only [show ((1:Side).val • u)=u from one_nsmul u] using h.city X Y u

lemma release_match (S:StepData c f){K:Kernel (Co S.patch.L α) (Co S.patch.L β)}{H:Matrix (Co f α) (Co f β) ℝ}(h:Matches K (repackM (splitCo S.ratio _) (splitCo S.ratio _) H)) : Matches (Cell.spread S.patch.L K) H:=by
  intro x y
  let L:=S.patch.L
  let X := (column L α).symm x
  let Y:= (splitCo S.ratio β) y
  have hx : x=column L α X:=(Equiv.apply_symm_apply _ x).symm
  have hy : y=(splitCo S.ratio β).symm Y := (Equiv.symm_apply_apply _ y).symm
  have he := h X Y
  unfold repackM at he; rw [Matrix.submatrix_apply] at he
  erw [convert_origin S,←hx] at he -- wrong
  erw [← hy] at he
  rw [← he,circuit,circuit]
  let a:= column L β ((lift Y.1,Y.2):Market _) -- a.val vs lift y: a=lift y + f.val • t
  have hz := convert_target S Y
  have hi : wrap f a.1=y.1:= by have H:= congr_arg Prod.fst hz; change ((splitCo S.ratio β).symm Y).1 = wrap f a.1 at H; erw [← hy] at H; exact H.symm
  let s:=rent f a.1
  rw [← (Equiv.addRight s).tsum_eq (fun z:Cover=> Cell.spread L K x (lift y.1+f.val • z,y.2))]
  refine tsum_congr fun z=>?_ ; unfold Cell.spread; congr 1
  refine (column L β).injective ?_
  erw [Equiv.apply_symm_apply, show (lift Y.1+c.val • z,Y.2)=pass (c.val • z) ((lift Y.1,Y.2):Market _) from rfl,column_map, ← mul_smul,mul_comm L.val,← S.sizes]
  change (_,y.2)= (a.1+f.val • z,a.2)
  refine Prod.ext ?_ (by change y.2=Y.2.2; rw [hy,convert_target S Y])
  change lift y.1+f.val • (z+s)=a.1+f.val • z
  have hh : a.1= lift y.1+f.val • s:= (rent_balance f a.1).trans (by rw [hi])
  rw [smul_add, add_comm (f.val • z), ← add_assoc, ← hh]
end YM.RG08.Cell
