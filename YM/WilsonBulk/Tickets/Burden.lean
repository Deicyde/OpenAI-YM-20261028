import YM.WilsonBulk.Tickets.Sink

/-!
# Paying linearized gauge-LHS Ticket attenuation by earlier grades in V.

`Burden` (Lei tone) consumes only strict operations. Null d when appending
more fields uses old null degree at least one higher than the new desired
one. Rank-price solution is built separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open Function Filter Equiv Finset Lattice Laurent RG Pert.Bulk Parapet
open scoped Topology BigOperators Classical ENNReal
open Taylor (lineRead league)
open MvPolynomial (X C eval rename aeval)
variable {α β γ : Type} {σ τ p q : ℝ} {n d k m : ℕ} {P U : Text α (n+1)}
-- tassel support, exactly one vector under t fixed.
lemma TicketNull.bonnet (h : TicketNull d P) (x y : Market α) (t : Legs α (n+m)) (f : Formula (Keys (n+m))) (hF : f.totalDegree < d) (v : Legs (Market α) m) :
    HasSum (fun i : Slip (n+m)=> tassel v (margin P y) (put x.1 t i)*lineRead i f) 0 := by
  refine legs_plus (fun t : Legs α (n+m)=> HasSum (fun i=> tassel v (margin P y) (put x.1 t i)*lineRead i f) 0) (fun u t=> ?_) t
  have hr : Injective (put x.1 t) := fun a b h=> congr_arg Prod.snd ((around (α:=α) x.1).injective (show around (n:=m) x.1 (t,a)= around x.1 (t,b) from h))
  by_cases he : ∃ z,put x.1 t z=v; swap
  · apply (harbor n m).hasSum_iff.mp; simp [Function.comp_def,harbor,asset,tassel_pay,show ∀ z,put x.1 t z≠v from fun z H=>he ⟨z,H⟩]
  obtain ⟨z,rfl⟩:= he
  let e (v:Slip n):= vaults v z; have hI : Injective e:= fun a b h=> congr_arg Prod.fst ((harbor n m).injective (show harbor n m (a,z)=harbor n m (b,z) from h))
  refine (Function.Injective.hasSum_iff hI ?_).1 ?_
  · intro i hi; obtain ⟨⟨b,z'⟩,rfl⟩:= (harbor n m).surjective i
    have hz : z'≠ z := fun H=> hi ⟨b,H ▸ rfl⟩
    change tassel _ _ (put x.1 _ (vaults b z')) *_=_; rw [asset,tassel_pay,if_neg (hr.ne hz),zero_mul]
  obtain ⟨p',hs,hp⟩:= slants z f
  refine (horizon_tail h y x.1 u p' (hs.trans_lt hF)).congr_fun fun z'=> ?_; dsimp only [Function.comp_apply,e]; rw [asset,tassel_pay,if_pos rfl,hp]; rfl

-- rank reindex and tail-only polish while KEEP actual original root/clothes.
def privateShift (v : Perm (Fin n)) := Equiv.arrowCongr (prodCongr v (Equiv.refl Axis)) (Equiv.refl ℤ) -- domain
lemma TicketNull.posting (v : Equiv (Fin n) (Fin k)) (hp : TicketNull d P) : TicketNull d (postage v P) := by
  obtain rfl : n=k := Fintype.card_fin n |>.symm.trans ((Fintype.card_congr v).trans (Fintype.card_fin _))
  intro x t u hh; let g:= prodCongr v (Equiv.refl Axis); let z: Formula (Keys n):= rename g.symm u
  apply (privateShift v).hasSum_iff.mp
  refine (hp x (t∘ v) z ((MvPolynomial.totalDegree_rename_le _ _).trans_lt hh)).congr_fun fun i=>?_
  dsimp only [Function.comp_apply]; unfold postage castTail; rw [hitch_zero,crop_hitch]; unfold Sheet.escort; congr 1
  · apply congr_arg (margin P x); ext1 j; simp [privateShift,put]
  simp [lineRead,z,MvPolynomial.eval_rename,privateShift]; rfl
lemma TicketNull.tailBuffs (hp : TicketNull d P) : TicketNull d (tailBuff P) := by
  rw [show tailBuff P=((Fintype.card (Grouping n):ℝ))⁻¹ • ∑ i:Grouping n, postage i P from ?_]
  · exact TicketNull.scale (TicketNull.snipped _ _ fun i _=> hp.posting i) _
  apply margin_force; intro x; simp only [postage,tailBuff,margin_scale,margin_grabs, post_mark]; rfl
variable {G : Gauge} {V : Text (Cloth G) (n+1)}
lemma TicketNull.plume (M : Bool→ PotentialForm→Cover→ Cover) (t a u i) (s : Legs G.ColorIndex k) (h : TicketNull d V) : TicketNull d (plume M t a u i s V) := by
  intro x w p hp; unfold Parapet.plume castTail; simp only [hitch_zero,crop_hitch]; by_cases H : x.2=(Exterior.coord 0,i)
  · simp_rw [if_pos H]; exact h.bonnet x (selvedge (cameo M t a x.1) u) w p hp _
  simp [H]
lemma TicketNull.spiro (M : Bool→PotentialForm→Cover→ Cover) (t) (h : TicketNull d V) : TicketNull d (spiro M V t) := by
  let a:= t; apply TicketNull.tailBuffs
  refine TicketNull.snipped _ _ (fun i _=>TicketNull.snipped _ _ (fun j _=>TicketNull.snipped _ _ (fun k _=>?_)))
  refine TicketNull.snipped _ _ (fun u _=> TicketNull.snipped _ _ (fun v _=> TicketNull.scale (TicketNull.plume M i j u k (v:Legs G.ColorIndex t) h) _)) -- metavars
lemma TicketNull.proceeding (M : Bool→PotentialForm→Cover→ Cover) (j n q) (I : Library G) (h : q≤j → q≤ n → TicketNull d (I (j-q) (n-q+1))) : TicketNull d (proceeding M I j n q) := by
  rw [Parapet.proceeding]; split
  next he=> exact TicketNull.scale (TicketNull.posting _ (TicketNull.spiro M q (h he.1 he.2))) _
  exact TicketNull.zero _
end Sheet
end YM.WilsonBulk
