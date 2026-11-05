import YM.UVExtension.Wren.Letters
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
open Badge Song Strata Gala Concert Graph
variable (j:ι) (D:(H j).fragrances→ RegularAddress c) (hd:∀ m,(D m).support=perf (H j) m)
    (P:BudgetPoint)(hp:P.threshold=temp s)(hu:P.order ≤ k)
 -- any fixed brushes. Include all logs receipts. post numbers scanf

def rates (i:ι) (m:(H j).fragrances):= (p.sails i).markΦ (p.casts h j i m) P.power
lemma payable (i:ι) (m:(H j).fragrances) : 0≤ rates p h j P i m:=by
   unfold rates Captain.markΦ; refine mul_nonneg (pow_nonneg ?_ _) ((p.sails _).pvc _); unfold shiftG; positivity
include hp hd hu
lemma landsW (i:ι) (m:(H j).fragrances): P.supBounds (D m).site (D m).support (rings p h j i m) (rates p h j P i m):=by
    have hh : (D m).support=perf (H i) (p.casts h j i m):=(hd m).trans (p.landscapes h j _ i).symm; rw [hh]; exact ((p.sails _).gloryBudget _ _ hp hu).2.2 P.power le_rfl (D m).site (show (D m).site ∈ perf (H i) (p.casts h j i m) from hh ▸ (D m).anchor)

omit hp hd hu
-- δ decay high cluster order. cost pX etc
private def bloom (n:ℕ) := (Fintype.card (Site c):ℝ)*(collars G p.i s k P.power*(salary Q L q p.B' s k p.k'*(1/2:ℝ)^n*(1-1/2)⁻¹))
lemma mapsV {ι κ:Type}(p:ι≃κ) (w:κ→ ℝ)(f:ι→ℝ)(y:ℝ)(h:∀ i,w (p i)=f i)(hp:SumBudget w y): SumBudget f y:= by rw [← funext h]; exact budget_pull _ p.injective hp
lemma capMark (i:ι) (Y:ℕ) : SumBudget (fun z=> if Y ≤ Sigma.fst z then (p.sails i).markΦ z P.power else 0) (bloom p P Y):=by
    refine Swift.spared (p.amasses.applies (p.sails i) P.power Y) p.amasses.gain ?_ (fun z _=> Song.crest _ _)
    intro k; split; next => unfold Captain.markΦ shiftG; refine mul_nonneg (pow_nonneg (by positivity) _) ((p.sails _).pvc _)
    exact le_rfl
lemma grassK (u z:Molecule S→Support c)(h:u=z) (x): (grass u z h x).fst=x.fst:=by subst z; rw [grass_self]
lemma lengthy (Y:ℕ)(i:ι): SumBudget (fun m=> if Y ≤ Sigma.fst m then rates p h j P i m else 0) (bloom p P Y) :=by
    refine mapsV (p.casts h j i) _ _ _ ?_ (capMark p P i Y); intro m; unfold rates; split
    next hx=> exact (if_pos ((grassK _ _ _ _ : (p.casts h j i m).fst=m.fst) ▸ hx)).symm
    next hx=> exact (if_neg (fun hy=>hx ((grassK _ _ _ _ : (p.casts h j i m).fst=m.fst).symm ▸ hy))).symm
lemma springing (ε:ℝ) (he:0<ε):∃ N:ℕ,bloom p P N≤ ε := by
    let c':ℝ:= salary Q L q p.B' s k p.k'; let w:ℝ:=(1-1/2)⁻¹; let r:=collars G p.i s k P.power ; let V n:=(Fintype.card (Site c):ℝ)*(r*(c'*(1/2:ℝ)^n*w)); have ht:Tendsto V atTop (𝓝 0):= by simpa only [mul_zero,zero_mul] using! ((((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (show (1/2:ℝ)<1 by norm_num)).const_mul c').mul_const w).const_mul r).const_mul (Fintype.card (Site c):ℝ)
    exact (ht.eventually_le_const he).exists

-- low-degree cluster tails among tuples. posts cheap receipts may vary.
lemma floored {κ α:Type*}{A:κ→Type*}{v:Filter α}[DecidableEq κ](Q:Finset κ)(f:α→ Sigma A→ℝ) (h:∀ i,Swift v (fun a j=>f a ⟨i,j⟩)): Swift v (fun a j=> if j.1∈Q then f a j else 0):=by
   choose b hb he using fun i=> (h i).tills
   let B i:=if i∈Q then b i else 0; have hh:Swift v (fun _=>B):=by
       refine Swift.nil B (show SumBudget B (∑ i∈ Q,b i) from budget_of_sum ?_ ?_); intro j; unfold B; split; exact (hb _).le; exact le_rfl
       intro s; unfold B; rw [← sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun i hi=> (mem_filter.mp hi).2) (fun a _ _=> (hb _).le)
   refine Swift.finances hh ?_ ?_
   · intro i; by_cases hi: i ∈ Q; exact (h i).eq (Eventually.of_forall (fun n=> funext fun j=> (if_pos hi).symm)); exact (Swift.nil (fun j:A i=>0) (u:=0) (by simp [SumBudget])).eq (Eventually.of_forall (fun n=> funext fun j=> (if_neg hi).symm))
   filter_upwards [(eventually_all_finset Q).mpr (fun i _=> he i)] with n hn i; let g(j:A i):= if i∈Q then f n ⟨i,j⟩ else 0; change SumBudget g (B i); by_cases hi:i∈Q
   · rw [show g=_ from funext fun j:A i=> if_pos hi]; unfold B; rw [if_pos hi]; exact hn i hi
   rw [show g=(fun _=>0) from funext fun j=> if_neg hi]; unfold B; rw [if_neg hi]; simp [SumBudget]
variable [NeBot v](L':ι→Molecule S→ℝ)(hr: Polish.Defines (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=p.u) L')
include hr
lemma subsongs (Y:ℕ): Swift v (fun n (m:(H j).fragrances)=> if m.fst<Y then charm (k:=k) j L' n m else 0):=by
    let f n:=charm (H:=H) (k:=k) j L' n; simp_rw [← Finset.mem_range]; refine floored _ f fun i=> ?_
    let J n (z:(H j).ThinP):= L' n z.val; have he:Swift v J:= hr.swift.letters (fun z:(H j).ThinP=> z.val) Subtype.val_injective
    let s:=(1+((i+1:ℕ):ℝ))^k; let Z:=∑ z:Network (Option (Fin i)), |mass z /((i+1).factorial:ℝ)|; have hh : 0≤ s :=by unfold s; positivity
    obtain ⟨w,hw⟩:=he.books; let g n (t:Tuple (H j).ThinP i):=∏ k, J n (t k)
    have h':Swift v g:=Swift.items (fun _=> J) (fun _=>he)
    apply (h'.scales (Z*s) (mul_nonneg (by unfold Z; positivity) hh)).le; filter_upwards [hw] with n ht x; have hb:0≤ g n x:= prod_nonneg (fun z _=> ht.1 _)
    change 0≤ |mass (pot _ x) /((i+1).factorial:ℝ)| * (g n x * s) ∧ |mass _ /_| * (g n x * s) ≤ _
    exact ⟨mul_nonneg (abs_nonneg _) (mul_nonneg hb hh),(mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun z=>|mass z/((i+1).factorial:ℝ)|) (fun _ _=> abs_nonneg _) (mem_univ (pot (H j).seam x))) (mul_nonneg hb hh)).trans_eq (by unfold Z; change (∑ _,_)*(g _ _*s)= _; ring)⟩

omit hr
include hp hu hd
abbrev onstage (p:BudgetPoint) {Y:Type} (A:Y→ RegularAddress c)(x:Y)(G:Gauge) := Tap p G (A x).site (A x).support
def lyrics (n:ι) (m:(H j).fragrances)(z:onstage P D m G):= z.read (p.rings h j n m)
lemma harvest : ∃ f,Swift v f∧ ∀ᶠ n in v,∀ (m:(H j).fragrances) (x:onstage P D m G), ‖lyrics p h j D P n m x‖≤ f n m:=by
    obtain ⟨X,hX⟩:= Polish.delegates p.laws h (p.sails j).position.le
    obtain ⟨c,hc,hK⟩:= hymns p h j X hX D hd P hp hu
    let a i m:=c*charm (H:=H) (k:=k) j X i m; let b n m:=min (rates p h j P n m) (a n m)
    have hp : ∀ᶠ n in v,∀ m,0≤ b n m∧∀ x, ‖lyrics p h j D P n m x‖≤ b n m:=by
        filter_upwards [hK] with i hi m; have hv:= tap_bound.mp (landsW p h j D hd P hp hu i m); have hh:=tap_bound.mp (hi m); exact ⟨le_min hv.1 hh.1,fun x=>le_min (hv.2 x) (hh.2 x)⟩
    have hz i:SumBudget (rates p h j P i) (bloom p P 0):=by simpa only [Nat.zero_le,if_true] using lengthy p h j P 0 i
    refine ⟨b,Swift.absorbs ⟨_,hp.mono fun i hi=> budget_mono (hz i) (fun j=> (hi j).1) (fun j=>min_le_left ..)⟩ ?_,hp.mono fun n hn j=> (hn j).2⟩
    intro ε he; obtain ⟨Y,hy⟩:= p.springing P ε he; refine ⟨_,fun n m=> if Y ≤ m.fst then rates p h j P n m else 0,(subsongs p j X hX Y).scales c hc.le, Eventually.of_forall (fun n=> budget_loosen (lengthy p h j P Y n) hy),?_⟩
    filter_upwards with n m; unfold b; split
    next hx=> rw [if_neg (not_le.mpr hx),add_zero]; exact min_le_right ..
    next hx=> rw [if_pos (not_lt.mp hx),mul_zero,zero_add]; exact min_le_left ..
end Choir
end YM.UVExtension.Wren
