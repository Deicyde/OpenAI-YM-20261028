import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Wisteria
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
open Next.Foundations
variable (p:Clusters H.ThinP) (χ' : Chi)
-- Primal partners through actual pre-mask terms.Earn without waiting.We could keep unrot. covariance later.
def libs (V:Config G c)(i:H.ThinP) := escort M χ' Q.table i.val Q.halo T W x o.K o.a V
def matin (V:Config G c):ℝ:= coefficient H.seam p.2 /↑(p.1+1).factorial *∑ i, (∏ j∈ univ.erase i, leaflet H χ' V (p.2 j))* libs M H χ' V (p.2 i)
lemma shoots (h: Herd H N.conduit A B n) (V:Config G c) : HasDerivAt (fun t=> H.trainedMill (color M H χ V t) p) (masked (Pressure.temp x) (H.bookFoot (.inr p)) (matin M H p χ) V) 0:=by
  let d:ℝ:=coefficient H.seam p.2/(p.1+1).factorial; let f i t:= color M H χ V t (p.2 i).val; let f' i:= M.lotus T x χ o.K W o.a Q.table Q.halo V (p.2 i).val
  have hp i : HasDerivAt (f i) (f' i) 0:=by
    simpa [f,f',color] using! (((hasDerivAt_id' (0:ℝ)).mul_const (f' i)).const_add (H.spawn χ V (p.2 i).val))
  have hx:= (HasDerivAt.fun_finsetProd (u:= Finset.univ) (fun i _=>hp i)).const_mul d
  have ht t : H.trainedMill (color M H χ V t) p=d*∏ i,f i t:=by unfold Cash.trainedMill Gas.term d f; unfold Cash.entriesMill; ring
  simp_rw [ht]
  suffices hf : masked (Pressure.temp x) (H.bookFoot (.inr p)) (matin M H p χ) V=d * ∑ i,(∏ b ∈ univ.erase i, f b 0) • f' i by rw [hf]; exact hx
  let H' i:= H.smallAt (p.2 i); let Q':= H.bookFoot (.inr p)
  have hc i : H' i⊆ Q':= subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ i)
  have hh(i): f i 0 = masked (Pressure.temp x) (H' i) (fun V=> leaflet H χ V (p.2 i)) V:= by unfold f; rw [color0]; exact (N.collective ..).1
  have hM(i): f' i = masked (Pressure.temp x) (H' i) (fun V=>libs M H χ V (p.2 i)) V:=congr_fun (debtor M H (N:=N) (p:=(p.2 i).val) h (p.2 i).2.2).2.2.2.1 V
  by_cases hu:Healthy (Pressure.temp x) Q' V
  · have hp i : Healthy (Pressure.temp x) (H' i) V:=Finset.disjoint_of_subset_left (hc i) hu
    rw [masked_eq _ _ _ _ hu]; unfold matin; simp_rw [hh,hM,masked_eq _ _ _ _ (hp _), smul_eq_mul]; rfl
  rw [masked_ne _ _ _ _ hu]; obtain ⟨j,hj,hq⟩:= Finset.not_disjoint_iff.mp hu
  rw [Finset.sum_eq_zero,mul_zero]; intro i hi
  obtain ⟨k,hk,hv⟩:= mem_biUnion.mp hj
  have he : ¬ Healthy (Pressure.temp x) (H' k) V:=fun h=>Finset.disjoint_left.mp h hv hq
  rcases eq_or_ne k i with rfl|hq
  · rw [hM,RG.masked_ne _ _ _ _ he,smul_zero]
  exact smul_eq_zero.mpr (Or.inl (Finset.prod_eq_zero (mem_erase.mpr ⟨hq,hk⟩) ((hh k).trans (masked_ne _ _ _ _ he))))
-- price at fortified Zoe full support
include H N h
lemma heeds :
    let Z:= H.bookFoot (.inr p)
    LocalOn Z (matin M H p χ)∧ Measurable (matin M H p χ) ∧ GaugeInvariant (matin M H p χ) ∧
      ∀ V, Healthy (Pressure.temp x) Z V→ Ore V (matin M H p χ) v (d0*oval M H N p) j:=by
  intro Z; let f(p:H.ThinP) V := leaflet H χ V p; let g (p:H.ThinP)V:=libs M H χ V p
  have hx i:= N.collective i; have hb i:= Captain.arrived (H:=H) (χ:=χ) i
  have he (i:H.ThinP):= debtor M H (p:=i.val) h i.2.2
  have ht i : H.smallAt (p.2 i)⊆ Z:=subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ _)
  refine ⟨?_,?_,?_,?_⟩
  · intro V U hV; unfold matin; apply congr_arg; exact sum_congr rfl fun i _=> congr_arg₂ (·*·) (prod_congr rfl fun j _=> (hb (p.2 j)).2.1 V U (agrees_mono hV (coe_subset.mpr (ht _)))) ((he (p.2 i)).1 V U (agrees_mono hV (coe_subset.mpr (ht _))))
  · exact measurable_const.mul (Finset.measurable_fun_sum _ (fun i _=> (Finset.measurable_fun_prod _ fun j _=> (hb (p.2 j)).1).mul (he (p.2 i)).2.1))
  · intro t V; unfold matin; exact congr_arg _ (sum_congr rfl fun i _=> congr_arg₂ (·*·) (prod_congr rfl fun j _=> (hb (p.2 j)).2.2 t V) ((he (p.2 i)).2.2.1 t V))
  intro V hV E _ _ _ U y hy hu
  let c:ℝ:= coefficient H.seam p.2/↑(p.1+1).factorial; let A(i:H.ThinP):=momentS H N i +2*sip M H N i
  let K i t:= (∏ b∈univ.erase i,f (p.2 b) (U t))*g (p.2 i) (U t)
  have hg i : Healthy (Pressure.temp x) (H.smallAt (p.2 i)) V:=Finset.disjoint_of_subset_left (ht i) hV
  have hA i:Brush j (A (p.2 i)) 1 (f (p.2 i) ∘ U) y:= (((hx (p.2 i) V).2 (hg i)) E U y hy hu).climb (le_add_of_nonneg_right (mul_nonneg zero_le_two (rise M H N (p.2 i)))) le_rfl
  have hQ' := (dew M H).2.1
  have hi(t':H.ThinP):0 ≤ A t':= add_nonneg (right H N _) (mul_nonneg zero_le_two (rise M H N _))
  have hM i:Brush j (d0*A (p.2 i)) 1 (g (p.2 i) ∘ U) y:= ((he (p.2 i)).2.2.2.2 V (hg i) E U y hy hu).climb (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left (rise M H N _) (show (1:ℝ)≤2 by norm_num)).trans (le_add_of_nonneg_left (right H N _))) hQ') le_rfl
  let a':=∏ i,A (p.2 i); let l:ℕ:= p.1+1
  have hK(i): Brush j ((a'*d0)*(1+(l:ℝ))^j) 1 (K i) y:=by
    apply (((Brush.all_prod (univ.erase i) (fun i=> f (p.2 i) ∘ U) _ _ (fun i _=> hA i)).paints (hM i)).trim).climb _ le_rfl
    have hp : (univ.erase i).card=p.1:=by rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_option,Fintype.card_fin]; omega
    simp only [sum_const, nsmul_eq_mul, hp,mul_one]; apply le_of_eq; unfold a' l; rw [← Finset.mul_prod_erase _ _ (mem_univ i)]; push_cast; ring
  apply ((Brush.spree _ K _ zero_le_one (fun i (_:i∈univ)=> hK i)).smul c).climb _ le_rfl; rw [sum_const,nsmul_eq_mul]
  have hc : (l:ℝ) * (1+(l:ℝ))^j≤ (2^(j+2):ℝ)^l:=by
    have hj : 1+(l:ℝ)≤ 2^l:= by rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=l)
    calc
      (l:ℝ)*_ ≤ 2^(2*l)*((2^l:ℝ)^j) := by gcongr; exact (le_add_of_nonneg_left zero_le_one).trans (hj.trans (pow_le_pow_right₀ (by norm_num) (by omega))) -- issue
      _ = _:=by simp_rw [← pow_mul, ← pow_add]; ring_nf
  simp only [card_univ,Fintype.card_option,Fintype.card_fin]
  unfold oval clusters; conv_rhs=> arg 2; arg 1; arg 2; change ∏ i, 2^(j+2)*A (p.2 i); rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
  calc
    _ = (‖c‖*(a'*d0))*((l:ℝ)*(1+(l:ℝ))^j) := by unfold l; push_cast; ring
    _ ≤ (‖c‖*(a'*d0))*(2^(j+2))^l := mul_le_mul_of_nonneg_left hc (mul_nonneg (norm_nonneg _) (mul_nonneg (Finset.prod_nonneg fun _ _=>hi _) hQ'))
    _ = _ := by unfold c l a'; rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0<((p.1+1).factorial:ℝ))]; ring

end Charity
end YM.PhysicalNext.Repeat.Daisy
