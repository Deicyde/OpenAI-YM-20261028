import YM.RG08.Aura.Breaker

/-! # Actual pairing kit to use in marked Ward replacement. κ from physical geometry. -/
noncomputable section
namespace YM.RG08.Aura
open Function Lattice Laurent Pert.Bulk Forms Carrel Steam Rows RG Stationary Bloch Tack Anchor Spar Sedan Precision Finset Exterior Packets Ducat Mason Flat
open Next.Free Planned.PrimaryIntegral295
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {G:Gauge}
local notation "Lin"=>Loc G 1
lemma torque {I:Type}{K D:Kernel Lin I}(h:Pert.Bulk.bind (heat G) K=Pert.Bulk.bind (heat G) D):Pert.Bulk.bind (heat G) (K-D)=0:=by
 -- finite cobound support proved by explicit curls, linear. `paid_curl`
 funext ⟨x,b,j⟩ y
 change _ = 0
 have hx:= congrFun (congrFun h (x,b,j)) y
 rw [paid_curl,paid_curl] at hx
 rw [paid_curl];apply Eq.trans ?_ (sub_eq_zero.mpr hx);rw [← sum_sub_distrib];apply Finset.sum_congr rfl;intro i hi;split<;>simp [mul_sub];ring
-- for actual application need post AND pre width of φ! derivative event uses μ only with sharper widths, previous grant etc ask. φ estimate from `charged` at width min(J,neighbor), prelength, yes p cost post. curvature novel.Reel post figure R.K vs κ. 

def sprout (G:Gauge)(a:Levels G)(H:Horizon a)(N m:ℕ):Kernel G.ColorIndex (Loc G 1):= frost (rootK G a H N m-oracle G a N m)
-- stage width must be fixed before L even wrt differing history or smoother supplies. 
lemma guide (G:Gauge)(K:KernelChoices)(P:MapPrices)(j t:ℕ)(hj:4 ≤ j)(ht:4≤t):∃ s:ℝ,0<s∧∃ (A:ℝ),0<A∧∃ (C : ℕ→Patch→ℝ), (∀ n T,0 ≤ C n T) ∧
    -- V=family demands at overlap and licensed. radius j-2 all. origin.V 
    ∀ (a:Levels G)(H:Horizon a)(N m:ℕ), H.Suffices P→ licensed a H→ m<N→ a.clock.kernel=K→ a.clock.J (m+1)=j→ a.clock.J m=t→
    let L:=a.S.block m;let T:=RG08.Supplies.stone a m; let p:= sprout G a H N m;let f:=oracle G a N m;let S:=rootK G a H N m
    ; (∀ w:List Axis,w.length ≤ j-2→RowCost s L (prism G.ColorIndex (install (advanceC L (Carrier.linesOf (destination a N m) a.clock.kernel.penalty) w))) (A/(L.val:ℝ)^(1+w.length))) ∧ RowCost s L S (C L.val T) ∧ RowCost s L p (C L.val T) ∧ ∀ (y : Market (Loc G 1))(z:Cover)(i:Axis)(c:G.ColorIndex),S (z,coord i,c) y=f (z,coord i,c) y+(p (z+step i,c) y-p (z,c) y):=by
 obtain ⟨u,A',hu,hA,Hlens⟩:=Aura.price K G hj ht
 let v:= RG08.Supplies.PlanCurve G K P j;let s:ℝ:=min u v
 have hv:0<v:= (RG08.Supplies.plan_hr G K P j).1;have hm:v ≤ 1:= (RG08.Supplies.plan_hr G K P j).2.1
 have hθ:0<s := lt_min hu hv
 let q(L:Side):=RG08.Supplies.planSupply G K P j L
 let A:=Real.exp (4*u)*A';have hB:0<A:=by unfold A; positivity
 let p(L:Side)(T:Patch):ℝ:=Cell.laneTax L*(q L*Cell.key G T K)
 let qR(T:Patch):=max 0 (p T.L T)
 let D(T:Patch):ℝ:=qR T+((qR T+A/(T.L.val:ℝ))* max 0 (Aura.fee T.L s))
 refine ⟨s/2,half_pos hθ,A,hB,fun _ T=> D T,fun _ T=>?_ ,?_⟩
 · unfold D qR; have h0:0 ≤ max 0 (p T.L T):=le_max_left ..; have h1:0 ≤ max 0 (Aura.fee T.L s):=le_max_left ..;positivity
 intro a H N m hT hK he hα hj' ht' L T y f W
 have hQ(w:List Axis)(h:w.length ≤ j-2):RowCost u L (prism G.ColorIndex (install (advanceC L (Carrier.linesOf (destination a N m) a.clock.kernel.penalty) w))) (A/(L.val:ℝ)^(1+w.length)):=by
    subst hj' ht' K;exact Hlens (destination a N m) _ h
 have hs: s/2 ≤ s:=half_le_self hθ.le
 refine ⟨fun w ht=> (hQ w ht).mono (hs.trans (min_le_left ..)),?_⟩
 have hf:RowCost s L f (A/L.val):= RowCost.mono (θ:=u) (by simpa only [List.length_nil,add_zero,pow_one] using! hQ [] (Nat.zero_le _)) (min_le_left ..)
 have hz:Cell.Warm G a.clock.kernel T (H.H N (m+1)) v (q L):=by unfold v q;subst j K; exact Yamen.warms hT N m he
 have hw:= (RG08.Supplies.outbound hz hθ.le (min_le_right ..) hm).2
 have hx:RowCost s L W (p L T) := by unfold p;subst K; exact hw.row
 have hN: 0 ≤ qR T:=le_max_left ..
 have hw0:RowCost s L W (qR T) := fun u i=> (hx u i).trans (ENNReal.ofReal_le_ofReal (le_max_right .. : p L T ≤ qR T))
 have hF0:0 ≤ A/(L.val:ℝ):=div_nonneg hB.le (Nat.cast_nonneg _)
 have hh:RowCost s L (W-f) (qR T + A/L.val):= RG08.Flat.subtract_row hw0 hf hN hF0 -- name
 obtain ⟨hy,H⟩:=Aura.sealife hθ (add_nonneg hN hF0) hh (torque (Aura.equality hT hK he))
 exact ⟨fun i j=> ((hw0.mono hs) i j).trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (mul_nonneg (add_nonneg hN hF0) (le_max_left ..)))),fun i j=> (hy i j).trans (ENNReal.ofReal_le_ofReal (le_trans (mul_le_mul_of_nonneg_left (le_max_right ..) (add_nonneg hN hF0)) (le_add_of_nonneg_left hN))), fun i j x c=> by have hh:= H i j x c;unfold Aura.menu at hh;rw [Pi.sub_apply,Pi.sub_apply] at hh; exact eq_add_of_sub_eq' hh⟩
end YM.RG08.Aura
