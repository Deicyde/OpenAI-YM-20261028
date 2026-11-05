import YM.RemainderComparison.Halo.Graft
import YM.RemainderComparison.Lyric.Finale
/-!
 # Genuine expenses at Halo Booth

 Roots remain in their original grammar (keep Turns & occupied). No
 bound by bare exponential partition ratios. Multi
 allocation supported when M costs render through RU. The budgets here
 answer for ANY mask/family with that witness, no erasure of global
 forced attaches implied by omission. Use regular growth and reassemble
 all mask changes downstream.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Graft Cascade Lyric Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
-- semantic invoice

def melod (f':Head S→ℝ)(B:ℝ)(j:ℕ)(i:H.ThinP)(x:Drums M S) := if Ac.Spark H.supportP i.val ∧ x.reach ⊆ i.val then B*(team M x).weight*(∏ j∈i.val\x.reach,f' j)*(1+H.shapeW i.val)^j else 0
variable (f' g:Head S→ℝ)(n':ℕ) (s':ℝ) {b':ℝ}
omit [Fintype ι] in
lemma melody_nn (hv:0≤ s') (hh:∀i,0≤f' i) (i:H.ThinP)(p:Drums M S) : 0≤ melod M H f' s' n' i p:=by
   unfold melod; split
   · exact mul_nonneg (mul_nonneg (mul_nonneg hv (Team.profit _)) (prod_nonneg fun i _=> hh _)) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
   exact le_rfl
omit [Fintype ι] in
lemma earns (hv:0≤ s') (hh:∀i,0≤f' i) (he:∀(M:Team R)(p:Molecule S),Seminar M H p j A χ (s'*M.weight*(∏ i∈p\M.signs S,f' i)*(1+H.shapeW p)^n') v) : Lyric.Paid M H χ N (melod M H f' s' n') :=by
   refine ⟨melody_nn M H f' n' s' hv hh,?_⟩; intro p x E _ _ _ F X U y hF hv hX hK hh hT hS hx
   rw [Palette.label] at hx
   unfold melod; rw [if_pos ⟨hS,hx⟩]
   have hh':=(he (team M x) p.val) E F X U y hF hv hX hK hh hT hS (show (team M x).signs S⊆ _ from by rw [Palette.label]; exact hx)
   rwa [Palette.label] at hh'
variable (l:ι→ℝ)
def merit (x:H.ThinP)(t:Drums M S):=∏ i∈x.val\t.reach,g i
local notation "f₀" => (combined M (fun i=>g i*f' i) l)
lemma envelopes (z:H.ThinP) (j:ℕ): Lyric.roof M H (melod M H f' s' n') l (merit M H g) z j = if Ac.Spark H.supportP z.val then
     2^j*s'*((∏ i∈z.val,f₀ i)*(1+H.shapeW z.val)^n') else 0:=by
   unfold Lyric.roof merit
   by_cases hz:Ac.Spark H.supportP z.val
   · rw [if_pos hz]; unfold Lyric.combined; rw [Lyric.accredits M l]
     rw [mul_assoc,Finset.sum_mul]; apply congrArg; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t (_:t∈univ)=> ?_
     simp only [melod,hz,true_and,prod_mul_distrib]; split_ifs <;> ring
   rw [if_neg hz]; simp [melod,hz]

local notation "Z" => radiusB x
local notation "T'" => Q.costs L μ R.beta x q
local notation "LT" => (Mixed.lengths S T' (ConnectedActivityE6.lengths T R))
variable (hl:∀ i,0≤ l i)
def rebate (Q:ConnectedActivityE6.Target G P)(F χ:ℝ)(j l:ℕ) := (1+2^j*F)*(polyPrice Q.ε l * treeYield χ (1/2) 0)
lemma boats (hv:0≤ s') (hg:∀i,0≤ f₀ i) {S' : ℝ}(hc:0<L')(he:a+L'+L'≤ Q.exp)
    (hq:Ready H.supportP Z (tariff f₀ LT 0 Q.ε) (Q.exp+2*Q.ε) S' Q.δ (1/2))
    (hS:degreePrice Z (rebate Q s' S' j n') L' ≤ 1/2):
     Ready H.smallAt Z (fun u=>Lyric.roof M H (melod M H f' s' n') l (merit M H g) u j) (a+L') (rebate Q s' S' j n') L' (1/2):=by
   let c:= polyPrice Q.ε n' * treeYield S' (1/2) 0
   have hu:0<c:=by
      unfold c polyPrice treeYield; have ht:= Q.usable; have hv':0 < S':= hq.1
      exact mul_pos (by positivity) (mul_pos (mul_pos hv' (by positivity)) (by norm_num))
   have hv':0 ≤ 2^j*s':=mul_nonneg (by positivity) hv
   have hh z:0≤Lyric.roof M H (melod M H f' s' n') l (merit M H g) z j:=by
      rw [envelopes]; split; exact mul_nonneg hv' (mul_nonneg (prod_nonneg fun i _=>hg i) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)); exact le_rfl
   refine ⟨mul_pos (add_pos_of_pos_of_nonneg zero_lt_one hv') hu,hc,hS,by norm_num,hh,fun i=>?_⟩
   have hz (i : Head S): 0 ≤ LT i := by
     rcases i with i | i
     · exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _)
     exact Nat.cast_nonneg _
   have h' := budget_scale hv' (budget_pull (fun x:H.ThinP=>x.val) Subtype.val_injective (Lyric.extraction H.supportP Z f₀ LT Q.exp Q.ε Q.bound Q.usable hq hg hz i n'))
   refine budget_loosen (budget_mono h' (fun z=>?_) (fun z=>?_)) ?_
   · dsimp only; split; exact mul_nonneg (hh _) (Real.exp_pos _).le; exact le_rfl
   · dsimp only; split
     next h=>
       apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (hh z)).trans
       rw [envelopes]; split
       next hp=>
         unfold Reserves.rooted; rw [if_pos ⟨hp,h⟩,currency,show setPrice H.supportP Z LT z.val=H.shapeW z.val from rfl, show z.val.biUnion H.supportP=H.smallAt z from rfl]
         -- cancel trailing exp ≥1
         let p:=H.shapeW z.val; let f:=(∏ j∈z.val,f₀ j)*(1+p)^n'; have hp:0≤p:=H.positive_volume z.val
         have hy:= Real.one_le_exp (mul_nonneg Q.usable.le hp)
         rw [mul_assoc (2^j*s')]; apply mul_le_mul_of_nonneg_left _ hv'; apply le_trans _ (le_mul_of_one_le_right _ hy)
         · apply le_of_eq; ring
         exact mul_nonneg (mul_nonneg (prod_nonneg fun i _=>hg i) (Real.exp_pos _).le) (pow_nonneg (by positivity : 0 ≤ 1+p) _)
       next hp=>rw [zero_mul]; exact h'.1 z
     next=> exact h'.1 z
   exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hu.le

lemma pricingL (hp:Ac.Hit H.birth Z (Reserves.tariff (Tickets.extra (Palette.mark (c:=c) M) (Palette.wages M l)) (ConnectedActivityE6.lengths T R) 0 Q.ε) Q.relative s') :
     Ac.Hit H.supportP Z (Reserves.tariff (Tickets.extra (Palette.sign M S) (Palette.wages M l)) LT 0 Q.ε) Q.relative s':=by
  let u:= (Reserves.tariff (Tickets.extra (Palette.mark (c:=c) M) (Palette.wages M l)) (ConnectedActivityE6.lengths T R) 0 Q.ε)
  rw [show Reserves.tariff _ _ _ _= Sum.elim (fun _:Stores S=>0) u from ?_]
  · simpa only [zero_add] using! Labels.together (fun x:Stores S=> H.supportP (.inl x)) _ _ (A:=Q.relative) (w:=fun _=>0) (show Ac.Hit (fun x:Stores S=> H.supportP (.inl x)) Z (fun _=>0) Q.relative 0 from (by intro x; simp [SumBudget])) hp
  ext i; rcases i with i|i
  · unfold tariff; rw [show Tickets.extra (Palette.sign M S) (Palette.wages M l) (.inl i)=0 from sum_eq_zero fun j _=> if_neg (by rw [sign, ← sparkPath]; simp),zero_mul]; rfl
  unfold u Tickets.extra tariff Mixed.lengths; simp only [Sum.elim,add_zero,Pi.zero_apply]
  apply congr_arg₂ (·*·) _ rfl; refine Finset.sum_congr rfl fun j _=> ?_; unfold sign; rw [← sparkPath]; simp_rw [Palette.mark]; simp

lemma fare_hit : Ac.Hit H.supportP Z (tariff Ξ.fare LT 0 Q.ε) Q.relative (T').rootHit :=by
  have hx:= Mixed.ready_vertices _ _ _ _ _ _ _ _ Ξ.lives Ξ.accrues
  refine Labels.raise_prices _ _ ?_ hx.2.2.2.2.2 ?_ -- edit
  · exact fun i=>mul_nonneg (Ξ.fares i) (Real.exp_pos _).le
  intro i; apply mul_le_mul_of_nonneg_left _ (Ξ.fares i)
  exact Real.exp_monotone (add_le_add_right (mul_nonneg Ξ.lives.marked (Nat.cast_nonneg _)) _) -- add_le orientation check
variable {E:Set ℕ} {w:ℕ→ℝ} {δ:ℝ}
lemma ink_hit (h:Presents R E w δ)(hp: Sales Z Q.relative Q.ε (regularFoot S.ratio Q.halo Z R) w (regularExtra R) v) : Ac.Hit H.supportP Z (tariff (weather S E w 0) LT 0 Q.ε) Q.relative v:=by
   intro x
   let f(z:Head S):= if x∈H.supportP z then tariff (weather S E w 0) LT 0 Q.ε z * Real.exp (Q.relative*coverNumber Z (H.supportP z)) else 0
   have hh: ∀ z:Head S,0≤ f z:= by
      intro z; unfold f; split; next=> exact mul_nonneg (mul_nonneg (snow_pos (w:=w) (fun _=>le_refl 0) (fun i _=> h.pay i) z) (Real.exp_pos _).le) (Real.exp_pos _).le
      next=> exact le_rfl
   refine budget_of_sum hh ?_
   intro s; let u:=s.filter fun z=> inherited S E z
   change ∑ z∈s,f z≤v
   rw [← Finset.sum_subset (s₁:=u) (s₂:=s) (filter_subset ..) (fun i hi hn=> ?_)] -- signature
   swap; · unfold f; split; next he=>unfold tariff weather; rw [dif_neg fun h'=>hn (mem_filter.mpr ⟨hi,h'⟩), Pi.zero_apply,zero_mul,zero_mul]
           next=>rfl
   let g z:= if h:inherited S E z then h.choose else 0
   apply le_trans _ (budget_sum (hp.hit x) (u.image g)); rw [Finset.sum_image]; swap
   · intro a ha b hb; have hA : inherited S E a := (mem_filter.mp ha).2; have hB : inherited S E b:= (mem_filter.mp hb).2
     intro hv; unfold g at hv; rw [dif_pos hA,dif_pos hB] at hv
     exact hA.choose_spec.2.trans ((congrArg (key S) hv).trans hB.choose_spec.2.symm)
   apply le_of_eq; refine Finset.sum_congr rfl fun i hi=> ?_
   have he : inherited S E i:=(mem_filter.mp hi).2
   unfold f g; rw [dif_pos he]
   let j:=he.choose; have hj:j∈E:=he.choose_spec.1
   -- simplify defeq of f support
   generalize ha : Exists.choose he=m; rw [show i=Opacity.key S m from ha ▸ he.choose_spec.2] -- he in goal?
   simp_rw [tariff, weather_at _ (show m∈E from ha ▸ he.choose_spec.1)]
   rfl
end YM.RemainderComparison.Halo
