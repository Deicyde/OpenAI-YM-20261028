import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Read
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Rebate
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Wiggle

/-!
# Uniform price of the actual affine *mean* response

Mean is on the portrait at every slot. CAB prediction and CAB
matrix system estimate its actions; rebase and pay Row bump-vs-Aff
separately. No-hole here means remote frame, not global empty or a
lift identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps AnalyticBridge.Annulus1AD
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β C d t : ℝ} {X : Config G f}

section
variable (p : Prices G (Active A x F)) (Y : LinkArray G (Frozen A x F)) (k : S.Choices) (q : Chi)
lemma held_tape (j : Active A x F) : Aff.lie ((cabin T V k q Y).μ+switchCab T V k q Y p) j.val.val=tape p j := by
  ext b
  change (cabin T V k q Y).μ _ + switchCab T V k q Y p _=_
  unfold switchCab; rw [dif_pos ((stillActive ..).2 j.property)]
  change _=p (j,b); abel
lemma cumulus (hi : i ∉ A.dome (40*radiusB x)) (he : 0 < radiusB x) (a : Bond f) (h : separation i (Aff.home S a) ≤ radiusB x) :
    let u:=cabin T V k q Y
    u.road (u.μ+switchCab T V k q Y p) a=basisArray x A F q d V Y p a := by
  intro u
  rcases Aff.environs F A x a _ i hi (by omega) with hk|hk
  · exact (u.on_trunk _ a hk).1.trans (wood x A F q d V Y p a hk).symm
  let j:=fundedB (x:=x) a hk
  exact (u.on_active _ a hk).1.trans ((held_tape p Y k q (T:=T) j).trans (clear_basis ..).symm)
lemma sub_cab (he : 0 ≤ t) (i : Aff.Vars G f) (h : ∀ j : Active A x F,j.val.val=i.1 →
    ‖tape p j - Aff.lie (cabin T V k q Y).μ i.1‖ ≤ t) : |switchCab T V k q Y p i| ≤ t:= by
  unfold switchCab; split
  next ht=> let j:=fundedB (x:=x) i.1 ht
            exact (PiLp.norm_apply_le (tape p j-Aff.lie (cabin T V k q Y).μ i.1) i.2).trans (h j rfl)
  rw [abs_zero]; exact he
end

private lemma smashes {g v : ℝ} (hg : 0<g) (h : 0 < v) : ∀ᶠ x : ℝ in atTop,
    v*x^(-(3/4):ℝ)/g + x^(-(3/4):ℝ) ≤ x^(-(2/3):ℝ):=by
  filter_upwards [const_allow (show 0 ≤ v/g+1 by positivity) (show (-(3/4):ℝ)< -(2/3) by norm_num)] with x hx
  apply le_trans _ hx; apply le_of_eq; ring

lemma voice (P : Teller G) (D : Patch) (hD : D.Branches P.bind G) :
    ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T → Larger (G:=G) S →
    ∀ (A : Stores S) (V : Config G c), Aff.cert S x A V → ∀ H K, Aff.Alongside H K T →
     ∀ (F : Forest S.ratio) (k : S.Choices) (χ : Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)) (i : Slots S),
       Aff.base S i ∉ A.dome (50*radiusB x) →
       let m:=portrait T A F k x V .endpoint χ d Y
       ‖lands T x V k (shots S x) A F χ d Y m i‖ ≤ x^(-(2/3):ℝ) := by
  obtain ⟨C,hC⟩:=Aff.reserves P; obtain ⟨B,r,hB,H⟩:= Aff.install_promises P D hD
  obtain ⟨w,hw,hW⟩:= Aff.gram_budget P D hD
  let z:= (Fintype.card G.ColorIndex:ℝ)
  let g:=Real.sqrt Aff.weight; have hg : 0<g:=Real.sqrt_pos.mpr Aff.weight_pos
  let v := z*(1+w)+1; have h1 : 0≤z:= Nat.cast_nonneg _; have hv:0<v:=add_pos_of_nonneg_of_pos (mul_nonneg h1 (by positivity)) zero_lt_one
  have he : ∀ᶠ x in atTop, x^(-(3/4):ℝ) ≤ fiery G x D.L:= by
    filter_upwards [threshold_large G D.L 1 zero_le_one,eventually_gt_atTop (0:ℝ)] with x ha hx
    rwa [linkRoom_sq hx,one_mul] at ha
  filter_upwards [H, Work.E01.radiusB_tendsto.eventually_ge_atTop 1,
    Aff.prepare D, bump_at P D hD 17, peers hC D hD r,
    Jewels.guard_broad P C hC D hD 1 zero_le_one r,
    Aff.shifted P C hC D hD r, he, trim_rate G D 2 (12+17) (1/4) (by norm_num), smashes hg hv, eventually_gt_atTop (0:ℝ)] with
    x h he hS hQ hs hρ hx hw hq hm hp c f S T hv hT hR A V hA D0 D1 H F k χ d Y i hi m
  let L:= cabin T V k χ Y; let y:=switchCab T V k χ Y m; let a:=L.μ+y; let z₀:=basisArray x A F χ d V Y m; let e:=x^(-(3/4):ℝ)
  have hgA:r.Takes (Aff.eyes S G (radiusB x)) L.sheet (Aff.dcol S) (Aff.paceR x):=(h.2 c f S T V A F hT hv hA).2
  have hF: Booth P S T:=by
    obtain ⟨i,j,o,p,hv₁,hv₂⟩:= H.budgets
    exact ⟨hT,D0,D1,i,j,o,p,hv₁,hv₂,H.inbound,H.outbound,H.old,H.new,H.together,H.sails⟩
  let o:=Aff.base S i
  have he':0≤e:=by unfold e; positivity
  have hζ:4* Aff.stencilD S.patch (till x)+10≤radiusB x / 4:=hv.symm ▸ hS.1
  have ht (a : Aff.Vars G f) (he : separation o (Aff.dcol S a) ≤ radiusB x) : |y a| ≤ e:= by
    apply sub_cab (Y:=Y) m k χ he'; intro u hf
    have hs := hs c f S T hT hv hR D0 D1 H hF F A L hA hgA u ?_ χ d Y
    · exact hf ▸ hs
    rw [hf]; apply Aff.exclude A _ _ _ _ hi; change separation o (Aff.home S _) ≤ _ at he; unfold o at he; omega
  have h0 : o∉ A.dome (40*radiusB x):= fun h=>hi (Aff.placed A _ _ (by omega) h)
  have ha j (hf : separation o (Aff.home S j) ≤ radiusB x) := cumulus m Y k χ (V:=V) (d:=d) (T:=T) h0 he j hf
  have hj (j : Bond f) (he : separation o (Aff.home S j) ≤ radiusB x) : ‖z₀ j‖ ≤ Rates.allowance G D x 1 17:= by
    rw [show z₀ j=_ from (ha j he).symm]
    rcases Aff.environs F A x j _ o hi (by omega) with hF|hf
    · rw [show Aff.Mint.road _ _ _=0 from (L.on_trunk a j hF).1,norm_zero]; exact Rates.allowance_nn ..
    rw [(L.on_active a j hf).1]
    exact hρ c f S T hT hv A F L hA hgA (by unfold L cabin; dsimp only; rw [hv]) y j fun b => le_trans (ht (j,b) he) ((show e≤_ from hw).trans_eq (one_mul _).symm)
  let q:=Aff.target T (till x) (temp x) i k V (replica S.ratio V)+Aff.derivative T (till x) i V z₀
  have ht' : Aff.descend (L.actions a) i= g • q:=by
    rw [L.roads a i (mem_filter.mpr ⟨mem_univ _,fun hz=>hi (Aff.placed A _ _ (by omega) hz)⟩) hT]; unfold q
    rw [show Aff.derivative T (till x) i L.V (L.road a)= Aff.derivative T (till x) i V z₀ from Aff.derivative_range T _ i L.V (funds_branch hT) _ z₀ (fun j h=> ha j (h.trans (by omega)))]; rfl
  have hY: ‖q‖ ≤ v*e/g:= by
    apply (le_div_iff₀ hg).mpr; rw [mul_comm _ g,← Real.norm_of_nonneg hg.le, ← norm_smul,← ht']
    have hh : z*((1+w)*e) ≤ v*e:= by unfold v; nlinarith only [he']
    apply le_trans _ hh; apply UVNext.PricedKernels.color_count
    · exact mul_nonneg (by linarith only [‹0<w›]) he'
    intro j
    have he₁ := hx c f S T hT hv D0 D1 H F A L hA hgA (i,j) (show Aff.base S i ∉ _ from fun h=> hi (Aff.placed A _ _ (by omega) h))
    have hη : Rates.allowance G D x 2 29 ≤ e:= hq.trans_eq (by unfold e; push_cast; norm_num)
    have h₁ : |(L.D *ᵥ y) (i,j)| ≤ w*e:= Aff.row_ball _ _ _ (hW c f S T hT hv F A V x).affine.1 (half_pos P.top.width_pos).le y he' (i,j) fun k' hk' => ht k' ((Aff.spring L _ _ hk' hT).trans (by omega))
    have h₂ : L.actions a=L.actions L.μ+L.D *ᵥ y := by unfold Aff.Mint.actions a; rw [Matrix.mulVec_add]; abel
    rw [h₂]; exact (abs_add_le ..).trans ((add_le_add (he₁.trans hη) h₁).trans_eq (by ring))
  apply (norm_le_norm_sub_add _ q).trans
  refine (add_le_add (b:=e) ?_ hY).trans (by linarith only [show v*e/g+e≤_ from hm])
  change ‖(Rows.base T x V k i + Rows.bump T x V k z₀ i)- q‖≤ e; unfold q
  rw [tallyBase,add_sub_add_left_eq_sub]
  apply (hQ S T hv hT A V hA i k z₀ (fun h=>hi (Aff.placed A _ _ (by omega) h)) hj).trans
  refine hq.trans_eq ?_; unfold e; push_cast; norm_num
end YM.PhysicalNext.InteractingRank.Milk
