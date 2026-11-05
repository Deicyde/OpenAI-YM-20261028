import YM.RG08.Line.Recipe

/-!
# Cell packing on cover and all period sides. Accounting for phase-origin offsets.
-/
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
set_option autoImplicit false
variable {α β : Type} {L c f: Side}

def column (L : Side)(α:Type) : Market (Co L α) ≃ Market α :=
 { toFun x:=(lift x.2.1+L.val • x.1,x.2.2)
   invFun x:=(rent L x.1,wrap L x.1,x.2)
   left_inv x:= by
     obtain ⟨h₁,h₂⟩ := rent_raw (L:=L) x.1 _ x.2.1 rfl
     simp only [h₁,h₂]
   right_inv x:= by change (lift _ + _,_)=_; rw [← rent_balance L] }

lemma column_pos (x : Market (Co L α)) : (column L _ x).1=lift x.2.1+L.val • x.1:=rfl

lemma column_map (x : Market (Co L α)) (v:Cover) : column L _ (pass v x)=pass (L.val • v) (column L _ x):= by
  ext1
  · dsimp [column,pass]; rw [smul_add]; abel
  rfl

def tile (L : Side)(K:Kernel α β) : Kernel (Co L α) (Co L β):= fun x y=> K (column L _ x) (column L _ y)
def spread (L : Side)(K:Kernel (Co L α) (Co L β)): Kernel α β:= fun x y=> K ((column L _).symm x) ((column L _).symm y)

lemma tile_city {K:Kernel α β} (L:Side) (h:city 1 K): city 1 (tile L K) := by
  intro x y v
  unfold tile; rw [show (1:Side).val=1 from rfl,one_smul,column_map,column_map]; simpa only [show (1:Side).val=1 from rfl,one_smul] using h (column L _ x) (column L _ y) (L.val • v)

lemma separation_to (x:Market (Co L α))(y:Market (Co L β)):
    Pert.Bulk.sep x.1 y.1 ≤ Pert.Bulk.sep (column L _ x).1 (column L _ y).1 / (L.val:ℝ) + 8:=by
  have hL : 0 < (L.val:ℝ):=by positivity
  have hx:=length_lift L x.2.1; have hy:=length_lift L y.2.1
  have he:=sep_triangle (L.val • x.1) (column L _ x).1 (L.val • y.1)
  have hi:=(sep_triangle (column L _ x).1 (column L _ y).1 (L.val • y.1))
  rw [scale_sep,sep_comm (L.val • x.1),column_pos] at he; rw [column_pos,column_pos] at hi
  have hh v (u:Cover): Pert.Bulk.sep (v+L.val • u) (L.val • u)=Pert.Bulk.length v:=by unfold Pert.Bulk.sep; rw [add_sub_cancel_right]
  rw [hh] at he hi
  field_simp at hx hy ⊢; unfold Pert.Bulk.length at *; rw [column_pos,column_pos]; linarith

lemma separation_from (x:Market (Co L α))(y:Market (Co L β)):
    Pert.Bulk.sep (column L _ x).1 (column L _ y).1 ≤ (L.val:ℝ)*(Pert.Bulk.sep x.1 y.1 + 8):=by
  rw [column_pos,column_pos]
  have he:=sep_triangle (lift x.2.1+L.val • x.1) (L.val • x.1) (lift y.2.1+L.val • y.1)
  have hg:=sep_triangle (L.val • x.1) (L.val • y.1) (lift y.2.1+L.val • y.1)
  rw [scale_sep,sep_comm (L.val • y.1)] at hg
  have hh (v u:Cover):Pert.Bulk.sep (v+L.val • u) (L.val • u)=Pert.Bulk.length v:=by unfold Pert.Bulk.sep; rw [add_sub_cancel_right]
  rw [hh] at he hg
  have hL : 0 < (L.val:ℝ):=by positivity
  have hx:=length_lift L x.2.1; have hy:=length_lift L y.2.1
  field_simp at hx hy; linarith

variable {σ τ p : ℝ}

theorem route {K:Kernel α β} (L:Side) (hτ : 0 ≤ τ)(ht : τ ≤ L.val * σ)(h : RowCost σ 1 K p):
    RowCost τ 1 (tile L K) (Real.exp (8*τ)*p):=by
  rw [mul_comm]
  intro x i
  have hf : Function.Injective (fun z : Cover=> (column L β (z,i)).1) := fun _ _ hi=> congr_arg Prod.fst ((column L β).injective (Prod.ext hi rfl))
  let H (v:Cover):= bill (K (column L _ x) (v,i.2)) (σ*delta 1 (column L _ x).1 v)
  let w:=8*τ
  have he (y:Market (Co L β)): τ * delta 1 x.1 y.1 ≤ σ*delta 1 (column L _ x).1 (column L _ y).1+w := by
    rw [delta_one,delta_one]; unfold w
    let s:=Pert.Bulk.sep (column L α x).1 (column L β y).1
    have hL:0 < (L.val:ℝ):=by positivity
    calc _ ≤ τ*(s/L.val+8):=mul_le_mul_of_nonneg_left (separation_to x y) hτ
         _ ≤ _:= by
           rw [mul_add,mul_comm τ 8]; apply add_le_add_left
           rw [show τ * (s / (L.val:ℝ))= τ/L.val*s by ring]; unfold s; gcongr
           · exact sep_nonneg ..
           rw [div_le_iff₀ hL]; linarith only [ht]
  calc _ ≤ ∑' z:Cover, ENNReal.ofReal (Real.exp w) * H ((column L β (z,i)).1):= by
          apply ENNReal.tsum_le_tsum; intro z; unfold H; rw [mul_comm (ENNReal.ofReal _),← bill_add]; apply bill_mono (x:=tile L K x (z,i)) le_rfl (he (z,i))
       _ ≤ ENNReal.ofReal (Real.exp w)* ENNReal.ofReal p:= by rw [ENNReal.tsum_mul_left]; gcongr; exact (ENNReal.tsum_comp_le_tsum_of_injective hf H).trans (h ..)
       _ = _:= by rw [mul_comm p, ENNReal.ofReal_mul (Real.exp_pos _).le]

lemma tile_price {K:Kernel α β} (L:Side)(hτ:0≤τ)(ht:τ≤L.val*σ)(h: Priced σ p K) : Priced τ (Real.exp (8*τ)*p) (tile L K) := by
  have hs: 0 ≤ σ := nonneg_of_mul_nonneg_right (hτ.trans ht) (by positivity : (0:ℝ)<L.val)
  have hp:=h.pos
  refine ⟨by positivity,tile_city L h.city,route L hτ ht h.row,fun i x=>?_⟩
  simpa only [tile,swap,delta_one,sep_comm x.1] using (route L hτ ht (h.row_t hs) x i)

lemma tile_torus {K:Kernel α β}{H:Matrix (Co f α) (Co f β) ℝ}(S:StepData c f)(h: Matches K H):Matches (tile S.patch.L K) (repackM (splitCo S.ratio _) (splitCo S.ratio _) H):= by
  have hratio (g : Ratio c f) :
      Matches (tile g.count K)
        (repackM (splitCo g α) (splitCo g β) H) := by
    have hcolumn (γ : Type) (u : Market (Co g.count γ)) :
        (splitCo g γ).symm (wrap c u.1,u.2) =
          (wrap f (column g.count γ u).1,(column g.count γ u).2) := by
      change (g.assemble (wrap c u.1,u.2.1),u.2.2) =
        (wrap f (lift u.2.1 + g.count.val • u.1),u.2.2)
      apply Prod.ext
      · change g.embed (wrap c u.1) + wrap f (lift u.2.1) =
          wrap f (lift u.2.1 + g.count.val • u.1)
        rw [g.embed_wrap, map_add]
        exact add_comm _ _
      · rfl
    intro x y
    let b : Market β := column g.count β (lift y.1,y.2)
    have hy : (splitCo g β).symm y = (wrap f b.1,b.2) := by
      simpa only [wrap_lift] using hcolumn β (lift y.1,y.2)
    have hsize : g.count.val * c.val = f.val :=
      (Nat.mul_comm _ _).trans g.exact_size.symm
    have hperiod (z : Cover) :
        column g.count β (lift y.1 + c.val • z,y.2) =
          (lift (wrap f b.1) + f.val • (z + rent f b.1),b.2) := by
      apply Prod.ext
      · change lift y.2.1 + g.count.val • (lift y.1 + c.val • z) =
          lift (wrap f b.1) + f.val • (z + rent f b.1)
        calc
          _ = b.1 + f.val • z := by
            change lift y.2.1 + g.count.val • (lift y.1 + c.val • z) =
              (lift y.2.1 + g.count.val • lift y.1) + f.val • z
            rw [smul_add, ← mul_smul, hsize]
            exact (add_assoc _ _ _).symm
          _ = (lift (wrap f b.1) + f.val • rent f b.1) + f.val • z :=
            congrArg (fun v : Cover => v + f.val • z) (rent_balance f b.1)
          _ = lift (wrap f b.1) + f.val • (z + rent f b.1) := by
            rw [smul_add]
            abel
      · rfl
    change display (tile g.count K) c x y =
      H ((splitCo g α).symm (wrap c x.1,x.2)) ((splitCo g β).symm y)
    rw [hcolumn α x, hy, ← h (column g.count α x) (wrap f b.1,b.2)]
    rw [circuit, circuit]
    change (∑' z : Cover,
      K (column g.count α x) (column g.count β (lift y.1 + c.val • z,y.2))) =
      ∑' z : Cover, K (column g.count α x) (lift (wrap f b.1) + f.val • z,b.2)
    rw [← (Equiv.addRight (rent f b.1)).tsum_eq
      (fun z : Cover => K (column g.count α x) (lift (wrap f b.1) + f.val • z,b.2))]
    apply tsum_congr
    intro z
    change K (column g.count α x) (column g.count β (lift y.1 + c.val • z,y.2)) =
      K (column g.count α x) (lift (wrap f b.1) + f.val • (z + rent f b.1),b.2)
    exact congrArg (K (column g.count α x)) (hperiod z)
  exact hratio S.ratio
end YM.RG08.Cell
