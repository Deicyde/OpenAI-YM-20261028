import YM.RemainderComparison.Lyric.Plectrum
import YM.RemainderComparison.Beacon.Prices

/-!
# Orchestral bills of full switched Boltzmann response
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell
open Merge Palette Next.Foundations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ c₀ C : ℝ} {O:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)
variable {Sg:H.ThinP→Drums M S→ℝ} {N:Captain H j q d v u A b r B e n χ} (hV:Paid M H χ N Sg)
variable (z:H.fragrances) (w:Syllable M H z)
def adjectives (f : H.ThinP→Drums M S→ℝ) (j:ℕ):ℝ:= ‖cadence H z‖ * ∏ i,(2^j*f (z.2 i) (w i))

def dividend (f : H.ThinP→Drums M S→ℝ) (j l:ℕ):= (shiftG x*(1+(coverNumber (radiusB x) (reachability z):ℝ)))^(l*j)*adjectives M H z w f j
omit [Fintype ι] in
lemma grown (V:Config G c)(hp : string M H χ z w V≠0) : Ursell.coefficient H.seam z.2≠0 ∧
       (∀ i, Ac.Spark H.supportP (z.2 i).val ∧ troupe T R Q.halo (radiusB x) (z.2 i).val ∧ (w i).reach⊆(z.2 i).val) ∧
       ∀ i∈ page M H z w, (M i).crest.image S.ratio.parent ⊆ reachability z:=by
   have hq i:= lead M H χ (z.2 i) (w i) V (fun h=> hp (by unfold string; rw [prod_eq_zero (mem_univ i) h,mul_zero]))
   refine ⟨fun h=> hp (by unfold string cadence; rw [h,zero_div,zero_mul]),fun i=> ⟨(hq i).1,(hq i).2.1,(hq i).2.2.1⟩,fun i hi=>?_⟩
   obtain ⟨a,ha,hv⟩:= mem_biUnion.mp hi; exact ((hq a).2.2.2 i hv).trans (subset_biUnion_of_mem (H.smallAt ∘ z.2) ha)
include hV
omit [Fintype ι] in
lemma expense :
    let Z:= reachability (H:=H) z
    let L:= string M H χ z w
    LocalOn Z L ∧ Measurable L ∧ GaugeInvariant L ∧ ∀ V,Healthy (Pressure.temp x) Z V → Ore V L v (adjectives M H z w Sg j) j:=by
   intro Z L
   let p i (V: Config G c):= toe M H χ (z.2 i) (w i) V
   have hf i := shows M H hV (z.2 i) (w i)
   have hs i: H.smallAt (z.2 i)⊆ Z := subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ _)
   refine ⟨fun U V h=>congr_arg (cadence H z*·) (Finset.prod_congr rfl fun i _=> (hf i).1 U V (agrees_mono h (hs i))),
     measurable_const.mul (Finset.measurable_fun_prod _ (fun i _=> (hf i).2.1)), fun t V=> congr_arg (cadence H z*·) (Finset.prod_congr rfl fun i _=>(hf i).2.2.1 t V), fun V h E _ _ _ Y y hY hQ=> ?_⟩
   let f i:= Sg (z.snd i) (w i); let k:=cadence H z
   have hh:= Brush.all_prod univ (fun i t=> p i (Y t)) f (fun _=>1) (fun i _=> ((hf i).2.2.2.2 V (Finset.disjoint_of_subset_left (hs i) h)) E Y y hY hQ)
   apply (hh.trim.smul k).climb _ le_rfl
   simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]; unfold adjectives
   have he : (1+((z.fst+1:ℕ):ℝ))^j ≤ (2^j : ℝ)^(z.fst+1) := by
     rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=z.fst+1)
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (show 0 ≤ ∏ i,f i from prod_nonneg
    (fun i _=> hV.fare ..))) (norm_nonneg _)).trans_eq ?_
   rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_option,Fintype.card_fin]; unfold k f; ring
omit [Fintype ι] in
lemma direction (P:BudgetPoint) (hu:P.threshold=Pressure.temp x)(hk:P.order≤j) (n:ℕ) (hp:P.power≤ n):
   let L:=string M H χ z w; let S':= reachability (H:=H) z
   P.Regular S' L ∧ ∀ s∈ S',P.supBounds s S' L (dividend M H z w Sg j n) := by
  intro L S'; obtain ⟨hx,hY,hF,h⟩:= expense M H χ hV z w
  let K:= adjectives M H z w Sg j
  have hP:0≤K:= mul_nonneg (norm_nonneg _) (prod_nonneg fun i _=>mul_nonneg (by positivity) (hV.fare ..))
  have hL V (hh : Healthy P.threshold S' V) : Ore V L v K j:= h V (hu ▸ hh)
  have hh (V) (ht : Healthy P.threshold S' V) : ContDiffAt ℝ (↑P.order) (L ∘ increment V) 0 := (charted (hL V ht) N.position).of_le (Nat.cast_le.mpr hk)
  have ha : Sailor G P.threshold e j := ⟨fun c _ hb => N.weigh.stroke c _ (hb.trans (hu.trans_le N.talent))⟩
  refine ⟨⟨hx,hY,hF,hh,fun V hV A l hl=> left_has A hl (hh V hV)⟩,fun y hy=>?_⟩
  let D:= radiusB x; let b:ℝ:= coverNumber D S'; let Y':= shiftG x*(1+b)
  have ht : 0≤b:= Nat.cast_nonneg _
  have hi : 1≤ Y':= one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) (le_add_of_nonneg_right ht)
  refine ⟨mul_nonneg (pow_nonneg (zero_le_one.trans hi) _) hP,fun V hV l hl hq=>?_⟩
  apply (costsD (g:=L) hx ha N.income y _ N.near (hL V hV) (Y:=Y') ?_ hi l (hl.trans hk) hq).trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hi (Nat.mul_le_mul_right j hp)) hP))
  intro p hy'; have hf : (separation p y:ℝ) ≤ b*(4*(D:ℝ)+2)+2*(D:ℝ) := by unfold b; exact_mod_cast Corona.extent S' D hy' hy
  unfold Y' shiftG; change _≤ 4*(2*(D:ℝ)+1)*(1+b); nlinarith [Nat.cast_nonneg (α:=ℝ) D]

omit [Fintype ι] in
lemma dividend_nonneg : 0≤ dividend M H z w Sg j m := mul_nonneg (pow_nonneg (by unfold shiftG; positivity) _)
        (mul_nonneg (norm_nonneg _) (prod_nonneg fun i _=> mul_nonneg (by positivity) (hV.fare ..))) -- χ via include
end YM.RemainderComparison.Lyric
