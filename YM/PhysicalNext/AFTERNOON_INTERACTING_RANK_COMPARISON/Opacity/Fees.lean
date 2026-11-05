import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Domain
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Horizon
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Turbine
/-! # Distributed scalar proposition at each exterior lattice anchor. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps AnalyticBridge.Annulus1AD Oriented
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β C r t : ℝ}
section galaxy
abbrev Bars (_S : StepData c f) := Cell f ⊕ Bond c ⊕ Cell c ⊕ Co c Gain
abbrev Grain (S : StepData c f) := Signed × Bars S

def seedPlace (S : StepData c f) : Bars S → Site c
 | .inl p=> S.ratio.parent p.1
 | .inr (.inl p)=> p.1
 | .inr (.inr (.inl p))=>p.1
 | .inr (.inr (.inr p))=>p.1

def grantPlace (S : StepData c f) (i : Grain S) := i.1.act (seedPlace S i.2)
variable (T : Tube G S) (x : ℝ) (V : Config G c) (Y : LinkArray G (Frozen A x F)) (k : S.Choices) (χ : Chi) (d : ℝ)

def coinMeter (p : Prices G (Active A x F)) (i : Grain S) :=
  i.2.elim (fun j => ∑ t : Bool, chargedUp T x V k (shots S x) A F χ d Y p i.1 (j,t))
    (Sum.elim (fun j => chargedSide T x V k (shots S x) A F χ d Y p i.1 j) fun _ => 0)
lemma coin_nn (p : Prices G (Active A x F)) (i : Grain S) : 0≤ coinMeter T x V Y k χ d p i:= by
  unfold coinMeter; rcases i with ⟨s,j|j|j⟩ <;> dsimp only [Sum.elim_inl,Sum.elim_inr]
  · refine sum_nonneg fun i _=> ?_; unfold chargedUp; split <;> positivity
  · unfold chargedSide; split <;> positivity
  exact le_rfl

def outer (t : ℝ) (U : Config G f) (i : Grain S) :=
    let W:=pull i.1 0 V; let Q:=pull i.1 0 U; let X:= S.prediction Q (choice i.1 k); let r:=till x; let z:=temp x
    i.2.elim (fun p=>T.workF r Q W t z p) (Sum.elim (fun p=> T.workI r X W z p) (Sum.elim (fun p=>
      T.workC r W z p+(T.workL r Q X W z p+T.workD r W z p)) fun p=>T.workN r W z p))

def levy (t : ℝ) (p : Prices G (Active A x F)) (i : Grain S) :=
    outer T x V k t (AnalyticBridge.Annulus1AD.landed x A F V Y p) i-coinMeter T x V Y k χ d p i+
      coinMeter T x V Y k χ d (portrait T A F k x V .endpoint χ d Y) i
end galaxy
lemma till_rate (P : Teller G) (D : Patch) (hp : D.Branches P.bind G) :
   ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T → Larger (G:=G) S →
    ∀ (A : Stores S) (V : Config G c), Aff.cert S x A V → ∀ H K, Aff.Alongside H K T →
     ∀ (F : Forest S.ratio) (k : S.Choices) χ d (Y : LinkArray G (Frozen A x F)) (t : ℝ) (p : Prices G (Active A x F)) (W : ℝ),
       Seeded A (AnalyticBridge.Annulus1AD.landed x A F V Y p) k V x W → (∀ u, ‖tape p u‖ ≤ Rates.allowance G D x 1 7) →
       fiery G x S.patch.L/2 ≤ t → ∀ i : Grain S, grantPlace S i ∉ A.dome (100 * radiusB x) →
         |levy T x V Y k χ d t p i| ≤ x^(-(5/4):ℝ) := by
  obtain ⟨C,hC⟩:= Aff.reserves P
  have hh (n) (m) (h : 3 ≤ n) : ∀ᶠ x in atTop, Rates.allowance G D x n m≤ x^(-(4/3):ℝ):= by
    filter_upwards [trim_rate G D n m (1/6) (by norm_num),eventually_ge_atTop (1:ℝ)] with x hx hv
    exact hx.trans (Real.rpow_le_rpow_of_exponent_le hv (by linarith only [show (3:ℝ)≤n by exact_mod_cast h]))
  filter_upwards [voice P D hp,Aff.currency (G:=G) (P.top.clip.direct/2) D 1, Aff.currency (G:=G) (P.bind.penalty/2) D 13,
    Rates.grow G D 1 (show 0<1 by decide) 1,still_kept P D,fronts P D hp hC, Aff.alerts P C hC D hp 7 le_rfl,
    Aff.earnsLD P C hC D hp 7 le_rfl, Aff.earnsC P D, Aff.earnsN P C hC D hp,
    hh 3 23 le_rfl, hh 4 5 (by omega),hh 3 34 le_rfl, hh 4 34 (by omega), hh 4 (13+13+13+13+1) (by omega),
    const_allow (show 0≤(6:ℝ) by norm_num) (show -(4/3:ℝ) < -(5/4) by norm_num),Work.E01.radiusB_tendsto.eventually_ge_atTop 2,
    eventually_gt_atTop (0:ℝ)] with x ht ha hw h hl hv hF hW hC' hN h1 h2 h3 h4 h5 h6 he hx c f S T hp hT hL A V hV H K hk F k χ d Y t p W H₁ H₂ H₃ i hi
  let U:= AnalyticBridge.Annulus1AD.landed x A F V Y p; let e:= Rates.allowance G D x 1 7
  let y:=x^(-(2/3):ℝ); let a:= x^(-(4/3):ℝ)
  have hy : y^2=a:= by unfold y a; rw [← Real.rpow_natCast (_:ℝ) 2,← Real.rpow_mul hx.le]; push_cast; norm_num
  have hh (p : G.Color) (h : ‖p‖ ≤ y) : ‖p‖^2/2≤a := (half_le_self (sq_nonneg _)).trans ((pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq hy)
  let B:=radiusB x; let q:=basisArray x A F χ d V Y p; let m := portrait T A F k x V .endpoint χ d Y
  have he' :0≤a:= by unfold a; positivity
  have hD : grantPlace S i∉ A.dome (50*B):= fun h=>hi (Aff.placed A _ _ (by omega) h)
  have hη (j : Slots S) (hp' : Aff.base S j = grantPlace S i) := hh _ (ht S T hp hT hL A V hV H K hk F k χ d Y j (hp'.symm ▸ hD))
  have h₀:Aff.Stops S q V U (grantPlace S i) (radiusB x) e:=halo_stops χ p Y (by omega) (Rates.allowance_nn ..) hi (fun j _=>H₂ j)
  have hπ (j : Slots S) (hp' : Aff.base S j=grantPlace S i) := (hv S T hp hT A V hV F j k χ d Y p (hp'.symm ▸ h₀) (hp'.symm ▸ hD)).trans h3
  have hU :0≤ coinMeter T x V Y k χ d m i:= coin_nn ..
  have hD' : grantPlace S i∉ A.dome (2*B) := fun h=>hi (Aff.placed A _ _ (by omega) h)
  have h0 : 1<c.val:=by linarith only [hV.1]
  unfold levy outer coinMeter
  rcases i with ⟨s,j|j|j|j⟩ <;> dsimp only [Sum.elim_inr,Sum.elim_inl]
  · let Z:=pull s 0 V; let X:=pull s 0 U; let M:=turnStore s A
    let ν:=fiery G x S.patch.L; have hJ : ν/2≤ν:=half_le_self (temp_nonneg _)
    have hs : Seeded M X (choice s k) Z x W:= pull_seeded s (funds_branch hT) H₁
    have hK : S.ratio.parent j.1 ∉ M.dome (2*radiusB x):= fun h=>hD' ((dome_turn ..).1 h)
    rw [reelF T s j V U k t x (hl S T M hp hT _ _ _ _ _ hs H₃ j hK) (hl S T M hp hT _ _ _ _ _ hs hJ j hK)]
    have hΔ : G.chord (faceValue X j) ≤ Rates.allowance G D x 1 1:= by
      apply le_trans (SectorNext.Remainder.exterior_fine hs (fun h=> hK (halo_subset _ _ h)))
      apply le_trans hJ; unfold ν; rw [hp]; simpa [Rates.allowance,Rates.pieces] using h
    unfold Aff.Fextend chargedUp
    have hm := rim_taken (S:=S) h0 (by omega) (Sum.inl j) F s hD
    simp_rw [if_pos hm,Fintype.sum_bool]
    rw [abs_le]; have hh : |T.high.direct/2*Aff.missed G (faceValue X j)|≤a:= hT.high.symm ▸ (ha _ hΔ).trans h2
    have hh' i : (0:ℝ) ≤ ‖lands T x V k (shots S x) A F χ d Y m (s,.inl (j,i))‖^2/2:= by positivity
    unfold Aff.squareOf at hπ ⊢
    constructor <;> linarith only [hh' true,hh' false,hη (s,.inl (j,true)) rfl,hη (s,.inl (j,false)) rfl,hπ (s,.inl (j,true)) rfl|> abs_le.mp,hπ (s,.inl (j,false)) rfl|> abs_le.mp, h6,he',abs_le.mp hh]
  · have hm := rim_taken (S:=S) h0 (by omega) (Sum.inr j) F s hD
    let u := S.prediction (pull s 0 U) (choice s k); let Z:=pull s 0 V; let q' := Z j*(u j)⁻¹

    have hw : |S.kernel.penalty/2*Aff.missed G q'|≤a:= hT.knobs.symm ▸ ((hw q' ((hF c f S T hp hT V A F hV k U j s q hD' h₀).1)).trans h5)
    simp only [Aff.work_expandI,chargedSide,if_pos hm]; rw [add_sub_assoc]
    apply (abs_add_le ..).trans
    let j' : Slots S := (s,Sum.inr j)
    have hz : (0:ℝ) ≤ ‖lands T x V k (shots S x) A F χ d Y m j'‖^2/2:= by positivity
    apply le_trans (add_le_add (b:=a+a) _ (d:=a) ((abs_of_nonneg hz).trans_le (hη (s,.inr j) rfl))) (by linarith only [h6,he'])
    exact (abs_add_le ..).trans (add_le_add hw (hπ (s,.inr j) rfl))
  · rw [sub_zero,add_zero]; exact (abs_add_le ..).trans ((add_le_add ((hC' c f S T V A hT hV s j hD').trans h2) ((abs_add_le ..).trans ((hW c f S T hp hT V A F hV k U j s _ hD' h₀).trans h1))).trans (by linarith only [h6,he']))
  rw [sub_zero,add_zero,abs_of_nonneg (show 0 ≤ T.workN _ (pull s 0 V) _ _ from div_nonneg (sq_nonneg _) (by norm_num))]
  apply ((hN c f S T V A F hp hT hV H K hk s j hD').trans h4).trans (by linarith only [h6,he'])
end YM.PhysicalNext.InteractingRank.Milk
