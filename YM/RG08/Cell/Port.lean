import YM.RG08.Cell.Basis

/-!
# One-way (fine<-coarse) finance
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
variable {α β:Type} {c f L:Side}{K:Kernel (Co L α) β}{p σ:ℝ}

def out (K:Kernel (Co L α) β) : Kernel α β:= fun x y=> K ((Cell.column L α).symm x) y

structure outward (K:Kernel α β)(L:Side)(σ p : ℝ) : Prop where
  row : RowCost σ L K p
  col : ColCost σ L K p
  marked : city L K

lemma out_delta (x : Market (Co L α))(y:Market β) :
    Pert.Bulk.delta L (Cell.column L _ x).1 y.1 ≤ 4 + Pert.Bulk.sep x.1 y.1:=by
  have he := Pert.Bulk.delta_fine L (Cell.column L _ x).1 (L.val • x.1) y.1
  simp only [Pert.Bulk.delta,column_pos, Pert.Bulk.sep, add_sub_cancel_right] at he ⊢
  have ht : (L.val:ℝ)≠ 0:=by exact_mod_cast L.pos.ne'
  have hx:= Pert.Bulk.length_lift L x.2.1
  rw [← smul_sub,length_nsmul,mul_div_cancel_left₀ _ ht] at he -- name
  exact he.trans (add_le_add_left hx _)

lemma out_bill (hs:0 ≤ σ)(h:Priced σ p K): outward (Cell.out K) L σ (((L.val:ℝ)^4*Real.exp (4*σ))*p):=by
  let w:=4*σ
  have h0 : 1 ≤ (L.val:ℝ)^4:=one_le_pow₀ (by exact_mod_cast L.pos)
  refine ⟨fun x i=>?_,fun i x=>?_,fun x y u=>?_⟩
  · let X := (Cell.column L α).symm x
    have he (y:Cover): Pert.Bulk.delta L x.1 y ≤ 4+ Pert.Bulk.sep X.1 y := by
      have he := out_delta X ((y,i):Market β)
      erw [(Cell.column L α).apply_symm_apply x] at he; exact he
    have hp:=h.pos
    calc _ ≤ ∑' y:Cover,bill (K X (y,i)) (σ*delta 1 X.1 y+w):= by
           refine ENNReal.tsum_le_tsum fun y=>bill_mono (x:=Cell.out K x (y,i)) le_rfl ?_
           rw [delta_one]; exact (mul_le_mul_of_nonneg_left (he y) hs).trans_eq (by unfold w; ring)
         _ ≤ ENNReal.ofReal (p*Real.exp w):=by
           simp_rw [bill_add,ENNReal.tsum_mul_right, ENNReal.ofReal_mul hp]; gcongr; exact h.row X i
         _ ≤ _:= by apply ENNReal.ofReal_le_ofReal; unfold w; nlinarith [Real.exp_pos (4*σ),mul_nonneg hp (Real.exp_pos (4*σ)).le]
  · rw [← (colony L).tsum_eq _, ENNReal.tsum_prod (f:=fun (v:Site L)(u:Cover)=>bill (Cell.out K (colony L (v,u),i) x) (σ*delta L (colony L (v,u)) x.1))] -- _ metavars
    have he (v:Site L) (u:Cover) : Cell.column L α (u,v,i)=(colony L (v,u),i):=rfl
    have hx (v:Site L) : ∑' u:Cover,bill (Cell.out K (colony L (v,u),i) x) (σ * delta L (colony L (v,u)) x.1) ≤ ENNReal.ofReal (Real.exp w*p) := by
      simp_rw [Cell.out,← he, Equiv.symm_apply_apply]
      refine (ENNReal.tsum_le_tsum (g:=fun u : Cover=>bill (K (u,v,i) x) (σ*delta 1 u x.1+w)) ?_).trans ?_
      · intro u; apply bill_mono le_rfl; rw [delta_one];
        have hx := out_delta ((u,v,i):Market (Co L α)) x; rw [he] at hx
        exact (mul_le_mul_of_nonneg_left hx hs).trans_eq (by unfold w; dsimp only; ring)
      simp_rw [bill_add,ENNReal.tsum_mul_right,mul_comm (Real.exp w) p,ENNReal.ofReal_mul h.pos]; gcongr; exact h.col (v,i) x
    calc _ ≤ ∑' _:Site L, ENNReal.ofReal (Real.exp w*p) := ENNReal.tsum_le_tsum hx
         _ = _:= by simp only [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,site_card,Nat.cast_pow]; rw [mul_assoc,ENNReal.ofReal_mul (by positivity : 0 ≤ (L.val:ℝ)^4),ENNReal.ofReal_pow (by positivity : 0≤(L.val:ℝ)), ENNReal.ofReal_natCast]
  let X := (Cell.column L α).symm x
  unfold Cell.out
  rw [show pass (L.val • u) x=Cell.column L _ (pass u X) by rw [column_map, Equiv.apply_symm_apply],Equiv.symm_apply_apply]
  simpa only [show ((1:Side).val • u)=u from one_nsmul u] using h.city X y u

lemma out_hall (S:StepData c f){K:Kernel (Co S.patch.L α) β}{H:Matrix (Co f α) (Co c β) ℝ}(h: Matches K (repackM (splitCo S.ratio _) (Equiv.refl _) H)): Matches (Cell.out K) H:= by
  intro x y
  let X := (Cell.column S.patch.L α).symm x
  have he:=h X y
  change _= H ((splitCo S.ratio _).symm _) y at he
  erw [convert_origin S X,Equiv.apply_symm_apply] at he
  exact he
end YM.RG08.Cell
