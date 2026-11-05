import YM.UVExtension.Wet.Polka
import YM.UVExtension.Wet.Capes
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a ag u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
open Polar Silica Shield Score Flux Matter
open Wren Wren.Choir Gala Graph Badge Next.Foundations Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Daisy Charity
variable [NeBot v][v.IsCountablyGenerated]{H:∀ i:ι,Cash w s q L Q U C (T i) (R i)}
variable {D:(i:ι)→ Lotus.Leaf (R i)}(p:Choir v T H k χ) (h:StableR v R)(g:Constant (v:=v) D)(j:ι)
local notation "P"=> H j
local notation "T!"=> p.sails j
local notation "X0"=> p.laws
local notation "q'"=> p.u
set_option quotPrecheck false
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
include p h j g
set_option maxHeartbeats 720000 in
lemma choirO (o:Site c) : ∃ f:ι→(H j).ThinP→ℝ, Swift v f ∧ ∀ᶠ n in v,∀ (m:(H j).fragrances) V, Healthy (temp s) (locus (D j) (H j) o m) V→
    Ore V (froth p h j D m n) p.u (((m.fst+1:ℝ))* (|sailsW (H:=H) j m| *((∏ l, f n (m.2 l))*(1+(m.fst+1:ℝ))^k))) k :=by
   obtain ⟨U',hp⟩:=delegates p.laws h (p.sails j).position.le; obtain ⟨L',hL⟩:= arrest p.laws g (p.sails j).position.le h
   obtain ⟨c',hc⟩:= hp.swift.books; obtain ⟨c₁,h₁⟩:=hL.swift.books; let f n(i:(H j).ThinP):= U' n i.val+ L' n i.val
   let hF:= (hp.swift.plus hL.swift).letters (fun i:(H j).ThinP=>i.val) Subtype.val_injective; refine ⟨f,hF,?_⟩
   filter_upwards [hc,h₁,hp.laws,hL.laws] with n hn hr hu hh m V hV E _ _ _ Y τ ht hs
   let B i:=f n (m.2 i); have hb i:0 ≤ B i:=add_nonneg (hn.1 _) (hr.1 _)
   by_cases hk:speaks (D j) (H j) m
   · let F i y := p.tables h j n (m.2 i) (Y y); let J i y:= libs (D n) (H n) χ (Y y) (p.ice h j n (m.2 i))
     unfold locus at hV;rw [if_pos hk] at hV; have hv i: Healthy (temp s) ((H n).unionP (m.2 i).val) V:= p.laws.riders h.toKept j n (m.2 i).val ▸ (Finset.disjoint_of_subset_left (subset_biUnion_of_mem ((H j).smallAt ∘ m.2) (mem_univ i)) hV)
     let L(l:Reserve S):= prism (T n) s χ U.K V (Greenbelt.allot l); let Z i l y:= Stained.fringe (vary (L l) (Y y)) w U.a (m.2 i).val (R n) Q.table Q.halo; let G' i l y:= (D n).picture (vary (L l) (Y y)) (m.2 i).val w U.a Q.table Q.halo
     letI :=Tree.select S.ratio S.patch.odd_side
     have hA(i): Brush k (B i) 1 (J i) τ:=by
        have he l : Brush k (L' n (m.2 i).val) 1 (G' i l) τ := (hh _ _ (L l) rfl rfl rfl).2 E Y τ (m.2 i).property.2 (hv i) ht hs
        refine ((Captain.avgBrush (G' i) _ _ he).climb (le_add_of_nonneg_left (hn.1 _)) le_rfl).shimmy (Eventually.of_forall ?_)
        intro y; unfold J libs escort; rw [p.ice_all h j]; rfl
     have hY(i): Brush k (B i) 1 (F i) τ:=by
        have he l : Brush k (U' n (m.2 i).val) 1 (Z i l) τ := (hu _ _ (L l) rfl rfl rfl).2 E Y τ (m.2 i).property.2 (hv i) ht hs; exact (((Captain.avgBrush (Z i) _ _ he).climb (le_add_of_nonneg_right (hr.1 _)) le_rfl)).shimmy (Eventually.of_forall fun y=> p.coins h j _ V (Y y) (m.2 i))
     let X i y:= (∏ l∈ univ.erase i,F l y)*J i y; let A:= (∏ l,B l)*(1+(m.fst+1:ℝ))^k
     have hX i : Brush k A 1 (X i) τ:= by
        have hf:= ((Brush.all_prod (univ.erase i) F _ _ (fun i _=>hY i)).paints (hA i)).trim; apply hf.climb _ le_rfl
        rw [sum_const,nsmul_eq_mul, card_erase_of_mem (mem_univ i),card_univ,Fintype.card_option,Fintype.card_fin,Nat.add_sub_cancel, mul_one]; unfold A; rw [Finset.prod_erase_mul (h:=(mem_univ i))]
     refine (Brush.shimmy (((Brush.spree Finset.univ X _ zero_le_one (fun i _=> hX i)).smul (sailsW (H:=H) j m)).climb ?_ le_rfl) (Eventually.of_forall fun y=> Wet.fortune p h j n m _))
     · rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin]; unfold A B; rw [Nat.cast_add,Nat.cast_one,Real.norm_eq_abs,mul_left_comm _ (_+1:ℝ)]
   rw [show froth p h j D m n=0 from quiet _ _ _ _ (mt (melts p h g j m n).mp hk)]; exact Brush.zi EventuallyEq.rfl (mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) (mul_nonneg (prod_nonneg (fun i _=>hb _)) (by positivity)))) zero_le_one

omit g
lemma smallW (f:ι→ (H j).ThinP→ℝ)(hr:Swift v f)(Y:ℕ):Swift v (fun n (m:(H j).fragrances)=> if m.fst≤Y then ((m.fst+1:ℝ))* (|sailsW (H:=H) j m| * ((∏ l,f n (m.2 l))*(1+(m.fst+1:ℝ))^k)) else 0):=by
    simp_rw [← Nat.lt_succ_iff,← Finset.mem_range]
    obtain ⟨c,hc⟩:=hr.books
    refine floored _ _ fun i=> ?_
    let Z:=∑ z:Network (Option (Fin i)), |mass z /((i+1).factorial:ℝ)|; let s:=(i+1:ℝ)*Z*(1+(i+1:ℝ))^k; let F n (x:Tuple (H j).ThinP i) := ∏ l, f n (x l)
    have hp:0 ≤ s:= by unfold s Z; positivity
    apply ((Swift.items (fun _=>f) (fun _=> hr):Swift v F).scales s hp).le; filter_upwards [hc] with n hn x; have hh:0≤ F n x:=prod_nonneg (fun i _=> hn.1 _); let u:ℝ:=i+1 -- elaboration
    change 0≤(i+1:ℝ)*(_*(F n x*_)) ∧ (i+1:ℝ)*(|mass (pot _ x) /((i+1).factorial:ℝ)| * (F n x*(1+(i+1:ℝ))^k)) ≤ _; constructor
    · positivity
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun z=>|mass z/((i+1).factorial:ℝ)|) (fun _ _=>abs_nonneg _) (mem_univ (pot (H j).seam x))) (mul_nonneg hh (by positivity))) (show 0 ≤(i+1:ℝ) by positivity)).trans_eq; change _= s*F n x; unfold s; ring
end YM.UVExtension.Wet
